-- Prove2me | solution 1 for Neutral.B1.isAlgHecke_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:49:33.762803+00:00
-- url     : https://prove2.me/submissions/ccecfe86-62fb-4450-806d-d1cc2ae8c8ca

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open Neutral Neutral.B1
variable (K : Type) [Field K] [NumberField K]
variable {K}
namespace Neutral.B1
theorem _root_.solution : IsAlgHecke (1 : Ideles K →* ℂˣ) (fun _ => 0) := by
  refine ⟨continuous_const, fun _ => rfl, fun x _ _ => ?_⟩
  simp
end Neutral.B1
