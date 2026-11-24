-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.mem_R_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:07.101721+00:00
-- url     : https://prove2.me/submissions/a0539d41-fb38-489f-b708-a37ca0a98577

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_GlobalTheory_RootEx_VolN_val_embX
import Theorems.Thm_GlobalTheory_RootEx_VolN_inR_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.VolN
theorem _root_.solution {p : ℕ} {g : GL (n ⊕ Fin c) k} : g ∈ R k n c p ↔ InR p g ∧ InR p g⁻¹ := by
  refine ⟨fun h => ⟨inR_of_mem h, inR_of_mem (inv_mem h)⟩, fun ⟨h1, h2⟩ => ?_⟩
  have e : (g⁻¹).val.toBlocks₁₁ * g.val.toBlocks₁₁ = 1 := by
    ext a b
    have h3 := congrFun (congrFun g.inv_mul (Sum.inl a)) (Sum.inl b)
    rw [Matrix.mul_apply, Fintype.sum_sum_type] at h3
    have h4 : ∑ i : Fin c, (g⁻¹).val (Sum.inl a) (Sum.inr i) * g.val (Sum.inr i) (Sum.inl b) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases le_total (i.val + 1) p with hi | hi
      · rw [h2 (Sum.inl a) (Sum.inr i) hi (by simp)]; simp
      · rw [h1 (Sum.inr i) (Sum.inl b) hi (by simp)]; simp
    rw [h4, add_zero] at h3
    rw [Matrix.mul_apply]
    simpa [Matrix.one_apply, toBlocks₁₁] using h3
  let y : GL n k := ⟨_, _, e, mul_eq_one_comm.1 e⟩
  have hy : embX c y * g ∈ N k n c p := by
    rw [mem_N_iff]
    rintro (r | r) (s | s) h
    · have := congrFun (congrFun e r) s
      rw [Matrix.mul_apply] at this
      simpa [val_embX, Matrix.mul_apply, y, Matrix.one_apply, toBlocks₁₁] using this
    · have : ∀ t, g.val (Sum.inl t) (Sum.inr s) = 0 := fun t => by
        simpa using h1 (Sum.inl t) (Sum.inr s) h (by simp)
      simp [val_embX, Matrix.mul_apply, this]
    · rw [← h1 _ _ h (by simp)]; simp [val_embX, Matrix.mul_apply, Matrix.one_apply]
    · rw [← h1 _ _ h (by simp)]; simp [val_embX, Matrix.mul_apply, Matrix.one_apply]
  have : g = embX c y⁻¹ * (embX c y * g) := by simp
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right hy)
end GlobalTheory.RootEx.VolN
