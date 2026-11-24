-- Prove2me | solution 1 for GlobalTheory.ZetaLeft.differentiable_emE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:21.952893+00:00
-- url     : https://prove2.me/submissions/70be813a-0e57-42fb-8338-31a8a57c372c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Theorems.Thm_GlobalTheory_ZetaLeft_differentiable_emT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZetaLeft
namespace GlobalTheory.ZetaLeft
theorem _root_.solution {x : ℝ} (hx : 0 < x) : Differentiable ℂ (emE x) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have : NeZero (x : ℂ) := ⟨hx'⟩
  have h1 := differentiable_emT hx
  have h2 := differentiable_emT (x := x + 1) (by linarith)
  unfold emE
  fun_prop
end GlobalTheory.ZetaLeft
