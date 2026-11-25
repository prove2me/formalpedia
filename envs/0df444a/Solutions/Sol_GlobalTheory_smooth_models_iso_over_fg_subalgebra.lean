-- Prove2me | solution 1 for GlobalTheory.smooth_models_iso_over_fg_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:33:42.024947+00:00
-- url     : https://prove2.me/submissions/887cb945-ba96-4d8c-9efd-a5ee9448698c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothModelsIsoOverFgSubalgebra
import Theorems.Thm_GlobalTheory_Spread_eq_isoPullback_hom_comp_bcMap
import Theorems.Thm_GlobalTheory_Spread_comp_eq_id_of_models
import Theorems.Thm_GlobalTheory_Spread_exists_fg_comp_eq
import Theorems.Thm_GlobalTheory_Spread_exists_fg_forall_comp_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory
open Spread
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (P Q T : Scheme.{0}) (p : P ⟶ Sp k) (q : Q ⟶ Sp k) (t : T ⟶ Sp V) (τ : T ⟶ P) (τ' : T ⟶ Q), Smooth p → IsSeparated p → QuasiCompact p → Smooth q → IsSeparated q → QuasiCompact q → IsPullback τ t p (spMap (algebraMap k V)) → IsPullback τ' t q (spMap (algebraMap k V)) → ∃ (R : Subalgebra k V) (e : pullback p (spMap (algebraMap k R)) ≅ pullback q (spMap (algebraMap k R))), R.FG ∧ e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ ∀ σ : T ⟶ pullback p (spMap (algebraMap k R)), σ ≫ pullback.fst _ _ = τ → σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom → σ ≫ e.hom ≫ pullback.fst _ _ = τ' := by
  intro k V _ _ _ P Q T p q t τ τ' _ _ _ _ _ _ hτ hτ'

  have hΦ : (hτ.isoPullback.inv ≫ τ') ≫ q = pullback.fst _ _ ≫ p := by
    rw [← hτ.isoPullback_inv_fst]
    simp only [Category.assoc, hτ.w, hτ'.w]
  have hΨ : (hτ'.isoPullback.inv ≫ τ) ≫ p = pullback.fst _ _ ≫ q := by
    rw [← hτ'.isoPullback_inv_fst]
    simp only [Category.assoc, hτ.w, hτ'.w]

  obtain ⟨R₁, ψ₁, hR₁, hψ₁, hψ₁'⟩ := exists_fg_comp_eq p q _ hΦ
  obtain ⟨R, ψ₂, hR, hle, hψ₂⟩ :=
    exists_fg_forall_comp_eq q p (fun _ : Unit ↦ hτ'.isoPullback.inv ≫ τ) (fun _ ↦ hΨ) R₁ hR₁

  have ha : (bcMap p (Subalgebra.inclusion hle) ≫ ψ₁) ≫ q =
      pullback.snd _ _ ≫ spMap (algebraMap k R) := by
    rw [Category.assoc, hψ₁, bcMap_fst_assoc, pullback.condition]
  have hb : ψ₂ () ≫ p = pullback.snd _ _ ≫ spMap (algebraMap k R) := by
    rw [(hψ₂ ()).1, pullback.condition]
  obtain ⟨f, hf₁, hf₂⟩ : ∃ f : pullback p (spMap (algebraMap k R)) ⟶
      pullback q (spMap (algebraMap k R)),
      f ≫ pullback.fst _ _ = bcMap p (Subalgebra.inclusion hle) ≫ ψ₁ ∧
        f ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift _ _ ha, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨g, hg₁, hg₂⟩ : ∃ g : pullback q (spMap (algebraMap k R)) ⟶
      pullback p (spMap (algebraMap k R)),
      g ≫ pullback.fst _ _ = ψ₂ () ∧ g ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift _ _ hb, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  have hf' : hτ.isoPullback.hom ≫ bcMap p R.val ≫ f ≫ pullback.fst _ _ = τ' := by
    rw [hf₁, bcMap_comp_of_eq_assoc p (Subalgebra.inclusion hle) R.val R₁.val (fun _ ↦ rfl), hψ₁',
      Iso.hom_inv_id_assoc]
  have hg' : hτ'.isoPullback.hom ≫ bcMap q R.val ≫ g ≫ pullback.fst _ _ = τ := by
    rw [hg₁, (hψ₂ ()).2, Iso.hom_inv_id_assoc]
  refine ⟨R, ⟨f, g, comp_eq_id_of_models hτ hτ' R f g hf₂ hg₂ hf' hg',
    comp_eq_id_of_models hτ' hτ R g f hg₂ hf₂ hg' hf'⟩, hR, hf₂, ?_⟩
  intro σ h₁ h₂
  rw [eq_isoPullback_hom_comp_bcMap hτ R σ h₁ h₂, Category.assoc]
  exact hf'
end GlobalTheory
