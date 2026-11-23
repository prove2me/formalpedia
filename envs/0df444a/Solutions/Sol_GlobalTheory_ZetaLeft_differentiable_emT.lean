-- Prove2me | solution 1 for GlobalTheory.ZetaLeft.differentiable_emT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:44.212852+00:00
-- url     : https://prove2.me/submissions/ea6bbd90-f66a-48d6-9901-aaf8a0126cb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe

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
theorem _root_.solution {x : ℝ} (hx : 0 < x) : Differentiable ℂ (emT x) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have : NeZero (x : ℂ) := ⟨hx'⟩
  unfold emT
  fun_prop
end GlobalTheory.ZetaLeft
