-- Prove2me | solution 1 for Neutral.B1.localIdele_snd_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:55.440897+00:00
-- url     : https://prove2.me/submissions/e1d03e05-6e45-4aeb-a975-150615cad9a1

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
    (localIdele K v x : AdeleRing (𝓞 K) K).2 v = x := by
  classical
  show Pi.mulSingle v (x : v.adicCompletion K) v = _
  exact Pi.mulSingle_eq_same v _
end Neutral.B1
