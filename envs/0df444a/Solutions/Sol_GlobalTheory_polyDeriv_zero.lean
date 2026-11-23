-- Prove2me | solution 1 for GlobalTheory.polyDeriv_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:58.291155+00:00
-- url     : https://prove2.me/submissions/67c140e4-8c1c-44e7-8144-5438ba3ef83b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
namespace GlobalTheory
theorem _root_.solution (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (0 : MvPolynomial ι 𝕜) F a = 0 := (polyDerivLinear F a).map_zero
end GlobalTheory
