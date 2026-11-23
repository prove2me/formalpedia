-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.remb_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:36.107545+00:00
-- url     : https://prove2.me/submissions/5a3518d2-87f3-415b-ac09-b79e22d56fcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors
open GlobalTheory GlobalTheory.LipschitzTR
variable (F : Type) [Field F] [NumberField F]
variable {F}
namespace GlobalTheory.LipschitzTR
theorem _root_.solution (a : F) (τ : F →+* ℝ) : remb F a τ = τ a := rfl
end GlobalTheory.LipschitzTR
