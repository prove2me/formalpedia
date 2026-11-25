-- Prove2me | solution 1 for GlobalTheory.Nef.OrdCalc.nrm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:04:33.923209+00:00
-- url     : https://prove2.me/submissions/42b05fc2-d5ba-4a57-9522-4bb1da441d95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculus
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.OrdCalc
variable {k F : Type} [Field k] [Field F] [Algebra k F]
namespace GlobalTheory.Nef.OrdCalc
theorem _root_.solution (v : Place k F) (n : ℕ) (x : Fin n → F) (c : F) :
    nrm v (c • x) = v.1 c * nrm v x := by
  unfold nrm
  apply le_antisymm
  · apply Finset.sup_le; intro i _
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_mul' le_rfl (Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ i))
  · rcases isEmpty_or_nonempty (Fin n) with h | h
    · simp [Finset.univ_eq_empty]
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => v.1 (x i))
      rw [hi]
      calc v.1 c * v.1 (x i) = v.1 ((c • x) i) := by simp
      _ ≤ _ := Finset.le_sup (f := fun i => v.1 ((c • x) i)) (Finset.mem_univ i)
end GlobalTheory.Nef.OrdCalc
