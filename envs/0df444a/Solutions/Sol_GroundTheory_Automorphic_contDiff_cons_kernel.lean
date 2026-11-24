-- Prove2me | solution 1 for GroundTheory.Automorphic.contDiff_cons_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:14.297062+00:00
-- url     : https://prove2.me/submissions/9e493cb9-b960-43c8-9f78-0c4fc72ccbda

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinProducts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
theorem _root_.solution {d : ℕ} {a : ℝ → ℂ} {K : (Fin d → ℝ) → ℂ} (ha : ContDiff ℝ ∞ a)
    (hK : ContDiff ℝ ∞ K) : ContDiff ℝ ∞ (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t)) :=
  (ha.comp (contDiff_apply ℝ ℝ 0)).mul
    (hK.comp (contDiff_pi.2 fun j => contDiff_apply ℝ ℝ j.succ))
end GroundTheory.Automorphic
