-- Prove2me | solution 1 for GlobalTheory.morphisms_descend_to_large_subfield
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:39:58.672459+00:00
-- url     : https://prove2.me/submissions/c4863617-dcd6-4bb6-b642-7b38edf19db9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MorphismsDescendToLargeSubfield
import Theorems.Thm_GlobalTheory_Spread_exists_fg_forall_comp_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) (Z : Scheme.{0}) (q : Z ⟶ Sp K₀) [QuasiCompact p₀] [QuasiSeparated p₀] [LocallyOfFinitePresentation q] (I : Type) [Finite I] (f : I → (X ⟶ Z)), IsPullback φ p p₀ (spMap K₀.subtype) → (∀ j, f j ≫ q = φ ≫ p₀) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ f₁ : I → (X₁ ⟶ Z), ∀ j, ψ ≫ f₁ j = f j ∧ f₁ j ≫ q = φ₁ ≫ p₀ := by
  intro K _ K₀ X₀ X p₀ p φ Z q _ _ _ I _ f hX hf
  have hX' : IsPullback φ p p₀ (spMap (algebraMap K₀ K)) := hX
  obtain ⟨R, g, ⟨s, rfl⟩, -, hg⟩ := Spread.exists_fg_forall_comp_eq (A := K) p₀ q
    (fun j ↦ hX'.isoPullback.inv ≫ f j)
    (fun j ↦ by rw [Category.assoc, hf, IsPullback.isoPullback_inv_fst_assoc]) ⊥ Subalgebra.fg_bot
  refine ⟨s, fun K₁ h hs X₁ p₁ φ₁ ψ h₁ hψ₁ hψ₂ ↦ ?_⟩
  have hle : ∀ x ∈ Algebra.adjoin K₀ (s : Set K), x ∈ K₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h r.2
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  let e : Algebra.adjoin K₀ (s : Set K) →+* K₁ :=
    (Algebra.adjoin K₀ (s : Set K)).val.toRingHom.codRestrict K₁ fun x ↦ hle x x.2
  have he₁ : spMap e ≫ spMap (algebraMap K₀ (Algebra.adjoin K₀ (s : Set K))) =
      spMap (Subfield.inclusion h) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have he₂ : spMap K₁.subtype ≫ spMap e =
      spMap (Algebra.adjoin K₀ (s : Set K)).val.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let u : X₁ ⟶ pullback p₀ (spMap (algebraMap K₀ (Algebra.adjoin K₀ (s : Set K)))) :=
    pullback.lift φ₁ (p₁ ≫ spMap e) (by rw [Category.assoc, he₁, h₁.w])
  have hu : ψ ≫ u = hX'.isoPullback.hom ≫ Spread.bcMap p₀ (Algebra.adjoin K₀ (s : Set K)).val := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Spread.bcMap_fst, IsPullback.isoPullback_hom_fst,
        pullback.lift_fst, hψ₁]
    · rw [Category.assoc, Category.assoc, Spread.bcMap_snd, IsPullback.isoPullback_hom_snd_assoc,
        pullback.lift_snd, ← Category.assoc, hψ₂, Category.assoc, he₂]
  refine ⟨fun j ↦ u ≫ g j, fun j ↦ ⟨?_, ?_⟩⟩
  · rw [← Category.assoc, hu, Category.assoc, (hg j).2, Iso.hom_inv_id_assoc]
  · rw [Category.assoc, (hg j).1, pullback.lift_fst_assoc]
end GlobalTheory
