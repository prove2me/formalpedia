-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.norm_sq_le_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:11.915817+00:00
-- url     : https://prove2.me/submissions/5482e51e-06ec-413c-892f-21f94895ced0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PolynomialTimesGaussianBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution (ι : Type) [Fintype ι] (y : ι → ℝ) :
    ‖y‖ ^ 2 ≤ ∑ i, y i ^ 2 := by
  have hs : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hn : ‖y‖ ≤ Real.sqrt (∑ i, y i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun i => y i ^ 2)
      (fun i _ => sq_nonneg (y i)) (Finset.mem_univ i)
  calc ‖y‖ ^ 2 ≤ Real.sqrt (∑ i, y i ^ 2) ^ 2 := by gcongr
    _ = ∑ i, y i ^ 2 := Real.sq_sqrt hs
end GlobalTheory.CompanionTheory.EisTube
