-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.limPunctured_eventuallyEq_of_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:15.19511+00:00
-- url     : https://prove2.me/submissions/bff167f1-900e-4d74-b72f-dbb89d3cff48

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Theorems.Thm_GroundTheory_Global_Elliptic_limPunctured_eq_of_continuousAt

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
theorem _root_.solution [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {w : ℂ} (hw : AnalyticAt ℂ f w) :
    limPunctured f =ᶠ[𝓝 w] f := by
  filter_upwards [(isOpen_analyticAt ℂ f).mem_nhds hw] with u hu
  exact limPunctured_eq_of_continuousAt hu.continuousAt
end GroundTheory.Global.Elliptic
