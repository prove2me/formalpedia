-- Prove2me | solution 1 for GlobalTheory.exists_associated_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:55:10.547403+00:00
-- url     : https://prove2.me/submissions/dcd607a5-9a7e-4349-8821-4a5005c74d21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialMapMaximalIdealIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingOfFlatOfFormallyUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Theorems.Thm_GlobalTheory_valuationRing_exists_associated_of_sum_eq_zero
import Theorems.Thm_GlobalTheory_associated_of_associated_mul_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O K W V : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K]
    [CommRing W] [CommRing V] [IsDomain V] [ValuationRing V] [Algebra W V] (ψ : O →+* W)
    (hinj : ∀ w : W, w ≠ 0 → algebraMap W V w ≠ 0)
    (hW : ∀ w : W, w ≠ 0 → ∃ π : O, Associated w (ψ π)) (b : V) (hb : b ≠ 0)
    (halg : IsAlgebraic W b) : ∃ π : O, Associated b (algebraMap W V (ψ π)) := by
  obtain ⟨P, hP, hPb⟩ := halg
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum] at hPb
  obtain ⟨i, hi, j, hj, hij, h⟩ := valuationRing_exists_associated_of_sum_eq_zero _ _
    (Polynomial.support_nonempty.2 hP)
    (fun i hi => mul_ne_zero (hinj _ (Polynomial.mem_support_iff.1 hi)) (pow_ne_zero _ hb)) hPb
  have hi' := Polynomial.mem_support_iff.1 hi
  have hj' := Polynomial.mem_support_iff.1 hj
  obtain ⟨p, hp⟩ := hW _ hi'
  obtain ⟨q, hq⟩ := hW _ hj'
  have hp0 := hinj _ (hp.ne_zero_iff.1 hi')
  have hq0 := hinj _ (hq.ne_zero_iff.1 hj')
  have h' : Associated (algebraMap W V (ψ p) * b ^ i) (algebraMap W V (ψ q) * b ^ j) :=
    (((hp.map (algebraMap W V)).mul_right _).symm.trans h).trans
      ((hq.map (algebraMap W V)).mul_right _)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact associated_of_associated_mul_pow O K V ((algebraMap W V).comp ψ) b hb p q hlt hp0 hq0 h'
  · exact associated_of_associated_mul_pow O K V ((algebraMap W V).comp ψ) b hb q p hlt hq0 hp0
      h'.symm
end GlobalTheory
