-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.mem_latOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:04:13.89484+00:00
-- url     : https://prove2.me/submissions/0d08be10-8ab2-4f8f-be00-f8d09e5be2d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply

set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors
open GlobalTheory GlobalTheory.LipschitzTR
variable (F : Type) [Field F] [NumberField F]
variable {F}
namespace GlobalTheory.LipschitzTR
theorem _root_.solution (N : FractionalIdeal (𝓞 F)⁰ F) (x : RSp F) :
    x ∈ latOf N ↔ ∃ a ∈ N, remb F a = x := by
  simp [latOf]
end GlobalTheory.LipschitzTR
