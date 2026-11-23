-- Prove2me | solution 1 for GlobalTheory.DCIndex.normal_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:36.104091+00:00
-- url     : https://prove2.me/submissions/89442491-299e-444a-8bc3-40e63f2f4675

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetCardDivCardInfCommutativeSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
open GlobalTheory GlobalTheory.DCIndex
variable {A : Type} [Group A]
namespace GlobalTheory.DCIndex
theorem _root_.solution (hc : ∀ a b : A, a * b = b * a) (V : Subgroup A) : V.Normal :=
  ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩
end GlobalTheory.DCIndex
