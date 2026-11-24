-- Prove2me | solution 1 for GlobalTheory.HilbFam.lag_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:30:41.685751+00:00
-- url     : https://prove2.me/submissions/d2847146-901e-44a0-8fe5-2e22b952e95f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LagHomogeneous
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
namespace GlobalTheory.HilbFam
theorem _root_.solution : ∀ (k n : ℕ) (c y v : ℂ), lag k n (v * c) (v * y) = v ^ n * lag k n c y ∧ lag k n 0 y = y ^ n := by
  intro k n c y v
  refine ⟨?_, ?_⟩
  · unfold lag
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have h : v ^ n = v ^ (n - m) * v ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
    rw [h, mul_pow, mul_pow]; ring
  · unfold lag
    rw [Finset.sum_range_succ, Finset.sum_eq_zero]
    · simp [rco]
    · intro m hm
      have hmn : n - m ≠ 0 := Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hm)
      simp [hmn]
end GlobalTheory.HilbFam
