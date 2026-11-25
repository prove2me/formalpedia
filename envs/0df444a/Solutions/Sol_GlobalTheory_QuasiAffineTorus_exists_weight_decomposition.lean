-- Prove2me | solution 1 for GlobalTheory.QuasiAffineTorus.exists_weight_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:04:05.25549+00:00
-- url     : https://prove2.me/submissions/233f3aab-51a4-4e57-a5c1-17e9244b27fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiAffineSubgroupContainingTorusEqTorus
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_linearIndependent_chars
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_GlobalTheory_torusCoord_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.restrictPoints_val
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.QuasiAffineTorus
variable {k : Type} [Field k] [IsAlgClosed k] {X : Type} [AddCommGroup X]
variable {H : Type} [CommGroup H] (τ : (Multiplicative X →* kˣ) →* H) (A : Subalgebra k (H → k))
namespace GlobalTheory.QuasiAffineTorus
theorem _root_.solution [Module.Free ℤ X] {U : Type} (j : U → H)
    (hU : ∀ f ∈ A, (∀ u, f (j u) = 0) → f = 0)
    (htr : ∀ f ∈ A, ∀ t, (fun y => f (τ t * y)) ∈ A) {f : H → k} (hf : f ∈ A) (S : Finset X)
    (a : X → U → k)
    (ha : ∀ u t, f (τ t * j u) = ∑ χ ∈ S, (t (Multiplicative.ofAdd χ) : k) * a χ u) :
    ∃ g : S → H → k, (∀ χ, g χ ∈ A ∧
      ∀ t y, g χ (τ t * y) = (t (Multiplicative.ofAdd (χ : X)) : k) * g χ y) ∧ f = ∑ χ, g χ := by
  classical
  have hsp := span_flip_eq_top_iff_linearIndependent.2
    ((linearIndependent_chars (k := k) (X := X)).comp (Subtype.val : S → X) Subtype.val_injective)
  have key : ∀ w : S → k, ∃ g ∈ A, ∀ u t, g (τ t * j u) =
      ∑ χ : S, w χ * ((t (Multiplicative.ofAdd (χ : X)) : k) * a χ u) := by
    intro w
    have hw : w ∈ (⊤ : Submodule k (S → k)) := trivial
    rw [← hsp] at hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨s, rfl⟩ := hw
      refine ⟨_, htr f hf s, fun u t => ?_⟩
      rw [← _root_.mul_assoc, ← map_mul, ha u, ← Finset.sum_coe_sort]
      simp [flip, _root_.mul_assoc]
    | zero => exact ⟨0, A.zero_mem, fun u t => by simp⟩
    | add w w' _ _ h h' =>
      obtain ⟨g, hg, h⟩ := h
      obtain ⟨g', hg', h'⟩ := h'
      exact ⟨g + g', A.add_mem hg hg', fun u t => by
        simp [h u, h' u, add_mul, Finset.sum_add_distrib]⟩
    | smul c w _ h =>
      obtain ⟨g, hg, h⟩ := h
      exact ⟨c • g, A.smul_mem hg c, fun u t => by
        simp [h u, Finset.mul_sum, _root_.mul_assoc]⟩
  choose g hgA hg using fun χ : S => key (Pi.single χ 1)
  have hg' : ∀ χ : S, ∀ u t, g χ (τ t * j u) =
      (t (Multiplicative.ofAdd (χ : X)) : k) * a χ u := fun χ u t => by
    rw [hg χ u, Finset.sum_eq_single χ (fun ψ _ h => by simp [h]) (by simp)]
    simp
  have hg1 : ∀ χ : S, ∀ u, g χ (j u) = a χ u := fun χ u => by simpa using hg' χ u 1
  refine ⟨g, fun χ => ⟨hgA χ, fun t y => ?_⟩, ?_⟩
  · have := hU _ (A.sub_mem (htr _ (hgA χ) t)
      (A.smul_mem (hgA χ) (t (Multiplicative.ofAdd (χ : X)) : k))) fun u => by
        simp [hg' χ u, hg1 χ u]
    simpa [sub_eq_zero] using congrFun this y
  · rw [← sub_eq_zero]
    refine hU _ (A.sub_mem hf (A.sum_mem fun χ _ => hgA χ)) fun u => ?_
    have := ha u 1
    rw [← Finset.sum_coe_sort] at this
    simpa [sub_eq_zero, hg1 _ u] using this
end GlobalTheory.QuasiAffineTorus
