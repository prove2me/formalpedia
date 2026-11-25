-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.Mram_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:58:48.796381+00:00
-- url     : https://prove2.me/submissions/e52b9c39-bc11-4c14-8e19-3d15817ed654

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Theorems.Thm_GlobalTheory_LatPair_mem_Mram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.LatPair.Model
theorem _root_.solution [Subsingleton 𝓀[k]ˣ] : Mram k n M = ⊥ := by
  letI := Fintype.ofFinite 𝓀[k]ˣ
  refine eq_bot_iff.2 fun φ h => funext fun P => ?_
  have := (mem_Mram φ).1 h P
  rwa [Fintype.sum_subsingleton _ 1, one_smul] at this
end GlobalTheory.LatPair.Model
