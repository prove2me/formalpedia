-- Prove2me | solution 1 for Neutral.B1.localIdele_isSupportedAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:16.065302+00:00
-- url     : https://prove2.me/submissions/8400a8c6-8eb0-4db8-8555-d50522df4a18

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Topology
open Neutral Neutral.B1
variable (K : Type*) [Field K] [NumberField K]
namespace Neutral.B1
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    IsSupportedAt K (localIdele K v x) v := by
  classical
  refine ⟨fun w => rfl, fun v' hv' => ?_⟩
  show Pi.mulSingle v (x : v.adicCompletion K) v' = 1
  exact Pi.mulSingle_eq_of_ne hv' _
end Neutral.B1
