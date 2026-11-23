-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.limPunctured_eq_of_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:56.199152+00:00
-- url     : https://prove2.me/submissions/7ee29800-4cc0-424a-8205-5d2d395a0308

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E]
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → E} {z : ℂ} (h : ContinuousAt f z) :
    limPunctured f z = f z :=
  (tendsto_nhdsWithin_of_tendsto_nhds h.tendsto).limUnder_eq
end GroundTheory.Global.Elliptic
