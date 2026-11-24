-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LatticeCount.summable_prod_inv_one_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:05:27.805139+00:00
-- url     : https://prove2.me/submissions/0d1650bb-c36a-4fcc-a726-6ac6c675a7d4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SummableOfLatticeDecay
import Theorems.Thm_GlobalTheory_CompanionTheory_LatticeCount_summable_inv_one_add_sq_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LatticeCount
namespace GlobalTheory.CompanionTheory.LatticeCount
theorem _root_.solution (d : ℕ) :
    Summable (fun n : Fin d → ℤ => ∏ k, ((1 : ℝ) + (n k : ℝ) ^ 2)⁻¹) := by
  induction d with
  | zero => exact Summable.of_finite
  | succ d ih =>
    have h2 := summable_inv_one_add_sq_int.mul_of_nonneg ih
      (fun m => by positivity) (fun n => Finset.prod_nonneg (fun k _ => by positivity))
    rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ)).summable_iff]
    refine h2.congr ?_
    intro x
    simp [Fin.prod_univ_succ, Fin.consEquiv]
    exact mul_comm _ _
end GlobalTheory.CompanionTheory.LatticeCount
