-- Prove2me | solution 1 for GlobalTheory.isIntegrallyClosedIn_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:10.337251+00:00
-- url     : https://prove2.me/submissions/0b6f4e6b-f690-413b-a869-16edddae2d83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway
import Theorems.Thm_GlobalTheory_isIntegrallyClosedIn_of_injective_fractionRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] [IsIntegrallyClosed R]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R) (R' : Type*) [CommRing R'] [Algebra R R']
    [IsLocalization M R'] : IsIntegrallyClosedIn R R' := by
  let K := FractionRing R
  let _ : Algebra R' K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe R' K M (nonZeroDivisors R) hM
  have : IsScalarTower R R' K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le R' K M (nonZeroDivisors R) hM
  refine isIntegrallyClosedIn_of_injective_fractionRing R R' K ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  have h0 : algebraMap R K r = 0 := by
    have h2 := congrArg (algebraMap R' K) (IsLocalization.mk'_spec R' r m)
    rw [map_mul, hx, zero_mul, ← IsScalarTower.algebraMap_apply] at h2
    exact h2.symm
  have hr : r = 0 := IsFractionRing.injective R K (by rw [h0, map_zero])
  simp [hr]
end GlobalTheory
