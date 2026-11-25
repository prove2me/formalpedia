-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.eq_of_differentiable_of_isPeriodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:13:29.715087+00:00
-- url     : https://prove2.me/submissions/d7e16c67-5b9a-49de-8756-8412ee6dde4e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Theorems.Thm_GroundTheory_Global_Elliptic_isCompact_range_of_isPeriodic

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
variable (L : PeriodPair)
variable {L}
variable (L)
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hd : Differentiable ℂ f) (hf : IsPeriodic L f) (z w : ℂ) : f z = f w :=
  hd.apply_eq_apply_of_bounded (isCompact_range_of_isPeriodic L hd.continuous hf).isBounded z w
end GroundTheory.Global.Elliptic
