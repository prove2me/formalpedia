-- Prove2me | solution 1 for GlobalTheory.SgGlob.mul_mem_dInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:13.870742+00:00
-- url     : https://prove2.me/submissions/b6ac0575-407d-4e3b-805d-bd10dda8a5dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob
variable {E : Type} [Field E] [NumberField E]
variable {n r : ℕ}
namespace GlobalTheory.SgGlob
theorem _root_.solution {i j : ℕ} {a b : E} (ha : a ∈ dInv E i) (hb : b ∈ dInv E j) :
    a * b ∈ dInv E (i + j) := by
  rw [dInv, pow_add]
  exact FractionalIdeal.mul_mem_mul ha hb
end GlobalTheory.SgGlob
