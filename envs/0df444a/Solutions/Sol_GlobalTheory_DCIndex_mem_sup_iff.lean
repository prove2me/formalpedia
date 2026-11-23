-- Prove2me | solution 1 for GlobalTheory.DCIndex.mem_sup_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:36.662774+00:00
-- url     : https://prove2.me/submissions/d3cb6a22-d5fa-4075-8667-9e05ca11b17b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetCardDivCardInfCommutativeSubgroup
import Theorems.Thm_GlobalTheory_DCIndex_normal_of_comm

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
theorem _root_.solution (hc : ∀ a b : A, a * b = b * a) (P Q : Subgroup A) {x : A} :
    x ∈ P ⊔ Q ↔ ∃ p ∈ P, ∃ q ∈ Q, p * q = x := by
  haveI : Q.Normal := normal_of_comm hc Q
  rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul]
  simp only [SetLike.mem_coe]
end GlobalTheory.DCIndex
