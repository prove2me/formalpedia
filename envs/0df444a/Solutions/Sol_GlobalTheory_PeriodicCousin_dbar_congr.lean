-- Prove2me | solution 1 for GlobalTheory.PeriodicCousin.dbar_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:24:38.68379+00:00
-- url     : https://prove2.me/submissions/956e731f-dc48-4c76-b643-7621231b30df

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
theorem _root_.solution {a : Fin g} {f f' : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ} (h : f =ᶠ[𝓝 z] f') :
    dbar a f z = dbar a f' z := by
  unfold dbar; rw [h.fderiv_eq]
end GlobalTheory.PeriodicCousin
