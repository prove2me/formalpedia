-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MidConj.mul_single_one_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:52:47.886405+00:00
-- url     : https://prove2.me/submissions/10d547ac-87dc-4340-8d52-d2757915c8a2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_AdaptedFrameOrthogonalSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MidConj
namespace GlobalTheory.CompanionTheory.MidConj
theorem _root_.solution {l m o s : Type*} [Fintype m] [Fintype o] [DecidableEq m] [DecidableEq o]
    (A : Matrix l m ℂ) (C : Matrix o s ℂ) (x : m) (y : o) (i : l) (k : s) :
    (A * Matrix.single x y (1 : ℂ) * C) i k = A i x * C y k := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, mul_ite, ite_mul]
end GlobalTheory.CompanionTheory.MidConj
