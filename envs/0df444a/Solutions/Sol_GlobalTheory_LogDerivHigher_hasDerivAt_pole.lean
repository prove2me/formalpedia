-- Prove2me | solution 1 for GlobalTheory.LogDerivHigher.hasDerivAt_pole
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:49:09.573231+00:00
-- url     : https://prove2.me/submissions/afc2949b-785f-414b-9c58-c20089fc3372

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.LogDerivHigher
namespace GlobalTheory.LogDerivHigher
theorem _root_.solution (c w s : ℂ) (k : ℕ) (h : s ≠ w) :
    HasDerivAt (fun z => c / (z - w) ^ (k + 1)) (-((k + 1 : ℕ) : ℂ) * (c / (s - w) ^ (k + 1 + 1))) s := by
  have h0 : s - w ≠ 0 := sub_ne_zero.2 h
  have h1 := (hasDerivAt_const s c).fun_div (((hasDerivAt_id' s).sub_const w).fun_pow (k + 1))
    (pow_ne_zero _ h0)
  refine h1.congr_deriv ?_
  simp only [Nat.add_sub_cancel]
  field_simp
  push_cast
  ring
end GlobalTheory.LogDerivHigher
