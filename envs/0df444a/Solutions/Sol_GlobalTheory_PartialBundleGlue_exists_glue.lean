-- Prove2me | solution 1 for GlobalTheory.PartialBundleGlue.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:35:25.606044+00:00
-- url     : https://prove2.me/submissions/6b60acae-193c-44f1-ad35-1709364efb7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RigidifiedPartialLineBundleIsoCocycleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPartialBundleIsoNormalisedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGlueRigidifiedPartialLineBundles
import Theorems.Thm_GlobalTheory_PartialBundleGlue_iso_isGen_iff
import Theorems.Thm_GlobalTheory_PartialBundleGlue_pull_isGen_of
import Theorems.Thm_GlobalTheory_T_exists_partialBundle_iso_normalised
import Theorems.Thm_GlobalTheory_T_rigidified_partialLineBundle_iso_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.PartialBundleGlue
namespace GlobalTheory.PartialBundleGlue
theorem _root_.solution : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (I : Type) (U : I → S.Opens) (M : I → LB X), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → iSup U = ⊤ → (∀ i, ⨆ a, (M i).U a = p ⁻¹ᵁ U i) → (∀ i, ∀ (a : (M i).ι) (x : X), x ∈ (M i).U a → gm (𝟙 X) x ((M i).U a ⊓ (M i).U a) ((M i).g a a) = 1) → (∀ i, ∃ r : ((M i).pull e).Gen, r.IsGen) → (∀ i j, LBIso (M i) (M j)) → ∃ L : LB X, L.IsLB ∧ (∃ r : (L.pull e).Gen, r.IsGen) ∧ ∀ i, LBIso (M i) L := by
  intro X S p e I U M hep hrig hU hM hself hr hiso
  choose r hr using hr
  choose w hw hn using fun i j => GlobalTheory.T.exists_partialBundle_iso_normalised X S p e (U i) (U j) (M i) (M j) (r i) (r j) hep (hM i) (hM j)
    (hr i) (hr j) (hiso j i)
  have hc : ∀ i j k (y : X) a b c, y ∈ (M i).U a → y ∈ (M j).U b → y ∈ (M k).U c →
      gm (𝟙 X) y ((M i).U a ⊓ (M j).U b) ((w i j).s (a, b)) *
        gm (𝟙 X) y ((M j).U b ⊓ (M k).U c) ((w j k).s (b, c)) =
        gm (𝟙 X) y ((M i).U a ⊓ (M k).U c) ((w i k).s (a, c)) := by
    intro i j k
    refine GlobalTheory.T.rigidified_partialLineBundle_iso_cocycle X S p e (U i) (U j) (U k) (M i) (M j) (M k) (w i j) (w j k) (w i k) hep hrig
      (hM i) (hM j) (hM k) (hw i j) (hw j k) (hw i k) ?_
    intro x a b c ha hb hc
    have h₁ := hn i j x a b ha hb
    have h₂ := hn j k x b c hb hc
    have h₃ := hn i k x a c ha hc
    rw [h₁, h₂, ← _root_.mul_assoc] at h₃
    exact mul_right_cancel h₃
  let L : LB X := ⟨Σ i, (M i).ι, fun q => (M q.1).U q.2, fun q q' => (w q.1 q'.1).s (q.2, q'.2)⟩
  refine ⟨L, ⟨?_, ?_, ?_⟩, ⟨⟨fun J => (r (J PUnit.unit).1).s fun _ => (J PUnit.unit).2⟩, ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p x ∈ iSup U by rw [hU]; trivial)
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ a, (M i).U a by rw [hM i]; exact hi)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, a⟩, ha⟩
  · rintro ⟨i, a⟩
    apply unit_ext
    intro x hx
    rw [map_one]
    exact (gm_res (𝟙 X) x _ hx _).trans (mul_eq_left.1 (hc i i i x a a a hx hx hx))
  · rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩
    apply unit_ext
    intro x hx
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    exact hc i j k x a b c hx.1.1 hx.1.2 hx.2
  · apply pull_isGen_of
    rintro x ⟨i, a⟩ ⟨j, b⟩ ha hb
    exact hn i j x a b ha hb
  · intro i
    refine ⟨⟨fun q => (w q.1.1 i).s (q.1.2, q.2)⟩, (iso_isGen_iff _).2 ?_⟩
    rintro x ⟨j, b⟩ ⟨j', b'⟩ a a' hb hb' ha ha'
    have h₁ := hc j j' i x b b' a hb hb' ha
    have h₂ := (iso_isGen_iff (w j' i)).1 (hw j' i) x b' b' a a' hb' hb' ha ha'
    rw [hself j' b' x hb', _root_.one_mul] at h₂
    rw [h₂, ← _root_.mul_assoc] at h₁
    exact h₁.symm
end GlobalTheory.PartialBundleGlue
