-- Prove2me | solution 1 for GlobalTheory.PrimeElement.exists_unit_algebraMap_eq_of_valuation_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:54.169226+00:00
-- url     : https://prove2.me/submissions/530d1da0-58e8-4ed0-8f16-ba2a4577f1b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Theorems.Thm_GlobalTheory_PrimeElement_exists_unit_algebraMap_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PrimeElement
variable {R : Type*} [CommRing R] {π : R}
variable [(Ideal.span {π}).IsPrime]
  {A : Type*} [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  [IsDomain S] [IsDiscreteValuationRing S]
  (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K] [IsFractionRing S K]
namespace GlobalTheory.PrimeElement
theorem _root_.solution (hπ : π ≠ 0) {y : A} (hy : IsUnit y)
    (h : (IsDiscreteValuationRing.maximalIdeal S).valuation K (algebraMap A K y) = 1) :
    ∃ r : R, IsUnit r ∧ algebraMap R A r = y := by
  obtain ⟨z, hz⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h.le
  refine exists_unit_algebraMap_eq K hπ hy (z := z) ?_ hz.symm
  rw [← hz, IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem] at h
  exact notMem_maximalIdeal.1 h
end GlobalTheory.PrimeElement
