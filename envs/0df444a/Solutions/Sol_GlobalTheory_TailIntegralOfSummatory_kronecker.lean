-- Prove2me | solution 1 for GlobalTheory.TailIntegralOfSummatory.kronecker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:36.854808+00:00
-- url     : https://prove2.me/submissions/0d9d210f-9449-4fb3-b924-05e12b4856ac

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal
import Theorems.Thm_GlobalTheory_TailIntegralOfSummatory_sum_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open Formalism.HermitianLattices.GL2PrimeSums
open GlobalTheory GlobalTheory.TailIntegralOfSummatory
namespace GlobalTheory.TailIntegralOfSummatory
theorem _root_.solution (a : ℕ → ℂ) (S : ℂ) (h : Tendsto (recSum a) atTop (𝓝 S)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, a n) / (N : ℂ)) atTop (𝓝 0) := by
  have h2 := h.sub h.cesaro_smul
  rw [sub_self] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [sum_eq, Complex.real_smul]
  push_cast
  field_simp
end GlobalTheory.TailIntegralOfSummatory
