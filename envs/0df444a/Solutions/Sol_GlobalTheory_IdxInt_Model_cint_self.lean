-- Prove2me | solution 1 for GlobalTheory.IdxInt.Model.cint_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:59:28.01087+00:00
-- url     : https://prove2.me/submissions/ea222591-e06b-4615-b6b2-a353af5af485

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumRefine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Theorems.Thm_GlobalTheory_IdxInt_Model_cint_ind

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open GlobalTheory GlobalTheory.IdxInt GlobalTheory.IdxInt.Model
open GlobalTheory.IdxInt
variable {W : Type} [AddCommGroup W]
namespace GlobalTheory.IdxInt.Model
theorem _root_.solution (A : AddSubgroup W) : cint A (ind (· ∈ A)) = 1 := by
  rw [cint_ind le_rfl (by simp)]; simp
end GlobalTheory.IdxInt.Model
