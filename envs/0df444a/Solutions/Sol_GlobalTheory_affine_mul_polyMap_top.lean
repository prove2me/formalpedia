-- Prove2me | solution 1 for GlobalTheory.affine_mul_polyMap_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:11.729195+00:00
-- url     : https://prove2.me/submissions/12315cb6-c966-4396-8de2-6fe3dfb42a6c

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QdetPolyMapMonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] (d : ℕ) (p q : A) (c : ℕ → A) :
    ∃ c' : ℕ → A, c' (d + 1) = p * c d ∧ ∀ u : ℂ, (u • p + q) * (∑ i ∈ range (d + 1), u ^ i • c i)
      = ∑ i ∈ range (d + 1 + 1), u ^ i • c' i := by
  refine ⟨fun i => (Nat.casesOn i 0 (fun j => p * c j) : A)
    + (if i < d + 1 then q * c i else 0), by simp, fun u => ?_⟩
  simp only [smul_add, sum_add_distrib, add_mul]
  congr 1
  · rw [sum_range_succ' _ (d + 1), mul_sum]
    simp only [Nat.rec_zero, smul_zero, add_zero]
    refine sum_congr rfl fun i _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]
  · rw [sum_range_succ _ (d + 1), mul_sum]
    simp only [lt_irrefl, if_false, smul_zero, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [if_pos (mem_range.mp hi), mul_smul_comm]
end GlobalTheory
