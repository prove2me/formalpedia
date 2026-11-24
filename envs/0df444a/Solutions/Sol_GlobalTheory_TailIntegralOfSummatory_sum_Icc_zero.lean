-- Prove2me | solution 1 for GlobalTheory.TailIntegralOfSummatory.sum_Icc_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:54:18.584573+00:00
-- url     : https://prove2.me/submissions/c5d6a3de-a5e1-416b-94fd-e1aba3bcbe94

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal

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
    ∑ k ∈ Icc 0 N, (if k = 0 then 0 else a k) = ∑ k ∈ Icc 1 N, a k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Icc_succ_top (by omega)]
    simp
end GlobalTheory.TailIntegralOfSummatory
