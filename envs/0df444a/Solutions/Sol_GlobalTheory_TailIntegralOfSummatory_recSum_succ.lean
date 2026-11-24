-- Prove2me | solution 1 for GlobalTheory.TailIntegralOfSummatory.recSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:54:16.79494+00:00
-- url     : https://prove2.me/submissions/0dc9bea6-61b0-4a79-9852-4c619faca9ec

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
    recSum a (N + 1) = recSum a N + a (N + 1) / ((N + 1 : ℕ) : ℂ) := by
  unfold recSum
  rw [Finset.sum_Icc_succ_top (by omega)]
end GlobalTheory.TailIntegralOfSummatory
