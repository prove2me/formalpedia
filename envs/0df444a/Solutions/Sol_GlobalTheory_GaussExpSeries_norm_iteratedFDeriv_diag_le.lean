-- Prove2me | solution 1 for GlobalTheory.GaussExpSeries.norm_iteratedFDeriv_diag_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:32:49.014232+00:00
-- url     : https://prove2.me/submissions/1a40e533-8271-4c52-b86b-60f4f6ef8679

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolyMulGaussianBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivTruncExpICompLe
import Theorems.Thm_GlobalTheory_GaussExpSeries_norm_iteratedFDeriv_id_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped Nat
noncomputable section
open GlobalTheory GlobalTheory.GaussExpSeries
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.GaussExpSeries
theorem _root_.solution (B : V →L[ℝ] V →L[ℝ] ℂ) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y => B y y) x‖ ≤ ‖B‖ * (2 ^ n * (1 + ‖x‖) ^ 2) := by
  have h := B.norm_iteratedFDeriv_le_of_bilinear (f := id) (g := id) (N := (n : WithTop ℕ∞))
    contDiff_id contDiff_id x le_rfl
  simp only [id] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : V => y) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : V => y) x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + ‖x‖) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [mul_assoc, sq]
        gcongr
        · exact norm_iteratedFDeriv_id_le i x
        · exact norm_iteratedFDeriv_id_le (n - i) x
    _ = 2 ^ n * (1 + ‖x‖) ^ 2 := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
end GlobalTheory.GaussExpSeries
