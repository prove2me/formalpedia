-- Prove2me | solution 1 for GlobalTheory.Mem.Chr.Model.infIdele_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:04:31.921685+00:00
-- url     : https://prove2.me/submissions/7101c607-f882-4741-8e15-1ebcb61623e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_DiagUnitsEqLocalIdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]
namespace GlobalTheory.Mem.Chr.Model
theorem _root_.solution (w : InfinitePlace L) : Continuous (infIdele L w) := by
  classical
  exact Continuous.units_map _ ((continuous_mulSingle w).prodMk continuous_const)
end GlobalTheory.Mem.Chr.Model
