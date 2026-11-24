-- Prove2me | solution 1 for GlobalTheory.JR.Step.MatchNotIm.conj_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:09:42.162311+00:00
-- url     : https://prove2.me/submissions/00ee494f-892e-4698-8995-dc081f81acf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedInvariantsAndHankelDetMapRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftWithLastBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.MatchNotIm
namespace GlobalTheory.JR.Step.MatchNotIm
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {k : Type} [CommRing k] (P Q N : Matrix n n k)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (i : ℕ) : (P * N * Q) ^ i = P * N ^ i * Q := by
  induction i with
  | zero => simp [hPQ]
  | succ i ih =>
    rw [pow_succ, ih, pow_succ]
    calc P * N ^ i * Q * (P * N * Q) = P * N ^ i * (Q * P) * N * Q := by simp only [Matrix.mul_assoc]
      _ = P * (N ^ i * N) * Q := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P]
end GlobalTheory.JR.Step.MatchNotIm
