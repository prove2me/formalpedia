-- Prove2me | solution 1 for GlobalTheory.TailIntegralOfSummatory.sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:02:29.010047+00:00
-- url     : https://prove2.me/submissions/aca5d14a-799a-4106-a371-b6e3ba3596a8

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal
import Theorems.Thm_GlobalTheory_TailIntegralOfSummatory_recSum_succ

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
theorem _root_.solution (a : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, a n = N * recSum a N - ∑ k ∈ range N, recSum a k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, recSum_succ]
    have h : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    field_simp
    push_cast
    ring
end GlobalTheory.TailIntegralOfSummatory
