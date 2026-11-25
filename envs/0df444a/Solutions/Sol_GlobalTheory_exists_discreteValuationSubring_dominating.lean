-- Prove2me | solution 1 for GlobalTheory.exists_discreteValuationSubring_dominating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:23.914898+00:00
-- url     : https://prove2.me/submissions/833a99e4-78e7-40f5-b140-2d44a088e46d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_dominating_of_essFiniteType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
namespace GlobalTheory
theorem _root_.solution (L : Type w) [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] (hR : ¬ IsField R) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring := by
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K))
  have : Algebra.EssFiniteType R K := .of_isLocalization K (nonZeroDivisors R)
  have : Algebra.EssFiniteType R L := .comp R K L
  exact exists_discreteValuationSubring_dominating_of_essFiniteType hR
end GlobalTheory
