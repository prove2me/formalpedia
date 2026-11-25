-- Prove2me | solution 1 for GroundTheory.Global.mem_idealDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:50:47.79481+00:00
-- url     : https://prove2.me/submissions/75726ebe-cb44-4d10-9847-e1ae348bd4ca

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NonvanishingDivisorSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Complex Filter Topology
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) : J ∈ idealDivisors I ↔ I ≤ J := by
  rw [idealDivisors, dif_neg hI, Set.Finite.mem_toFinset]
  rfl
end GroundTheory.Global
