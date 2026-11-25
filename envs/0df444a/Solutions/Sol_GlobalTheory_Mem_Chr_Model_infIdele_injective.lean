-- Prove2me | solution 1 for GlobalTheory.Mem.Chr.Model.infIdele_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:04:33.344859+00:00
-- url     : https://prove2.me/submissions/4ea6d813-cb94-47fe-92d3-eb1ce2e199f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_DiagUnitsEqLocalIdele
import Theorems.Thm_GlobalTheory_Mem_Chr_Model_infIdele_fst_self

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
theorem _root_.solution (w : InfinitePlace L) : Function.Injective (infIdele L w) := by
  intro x y hxy
  apply Units.ext
  have h := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).1 w) hxy
  simpa only [infIdele_fst_self] using h
end GlobalTheory.Mem.Chr.Model
