-- Prove2me | solution 1 for GlobalTheory.PeriodicCousin.dbar_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:21.61854+00:00
-- url     : https://prove2.me/submissions/59abbc95-c593-40f2-8347-7c376655dc16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DbarSolveComplexTorusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicPeriodicCocycleCoboundary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real Topology
open GlobalTheory GlobalTheory.PeriodicCousin
variable {g : ℕ}
namespace GlobalTheory.PeriodicCousin
theorem _root_.solution {a : Fin g} {f f' : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : DifferentiableAt ℝ f z) (h' : DifferentiableAt ℝ f' z) :
    dbar a (fun x => f x - f' x) z = dbar a f z - dbar a f' z := by
  unfold dbar
  rw [fderiv_fun_sub h h']
  simp only [ContinuousLinearMap.sub_apply]
  ring
end GlobalTheory.PeriodicCousin
