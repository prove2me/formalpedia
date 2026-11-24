-- Prove2me | solution 1 for GlobalTheory.RootExchangeFixed.exists_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:24:35.888913+00:00
-- url     : https://prove2.me/submissions/017651ae-b5ad-4a3b-9afe-844079c84966

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonarchimedeanLocalFieldSecondCountableT2Space
import Theorems.Thm_GlobalTheory_RootExchangeFixed_lowU_neg_mul
import Theorems.Thm_GlobalTheory_RootExchangeFixed_conj_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
open GlobalTheory GlobalTheory.RootExchangeFixed
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootExchangeFixed
theorem _root_.solution (h1 : 1 ≤ p) (hc : p < c) (u β : n → k) :
    ∃ g ∈ N k n c p, simpleSum g = ∑ r, u r * β r ∧
      rowE c p u * colE c (p + 1) β = g * rowE c p u := by
  set C : Matrix (Fin c) n k := Matrix.of fun l s => if l.val + 1 = p then u s else 0 with hC
  set B : Matrix n (Fin c) k := Matrix.of fun r i => if i.val + 1 = p + 1 then β r else 0 with hB
  have hBC : B * C = 0 := by
    ext r s
    simp only [hB, hC, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with a b
    · omega
    all_goals simp
  have hCB : ∀ l i, (C * B) l i = if l.val + 1 = p ∧ i.val = p then ∑ r, u r * β r else 0 := by
    intro l i
    simp only [hB, hC, Matrix.mul_apply, Matrix.of_apply]
    by_cases a : l.val + 1 = p <;> by_cases b : i.val = p <;> simp [a, b]
  have hv := conj_val C B hBC
  refine ⟨lowU C * upU B * lowU (-C), Subgroup.subset_closure ?_, ?_, ?_⟩
  · intro r s hrs
    rw [hv]
    rcases r with r | r <;> rcases s with s | s
    · simp [Matrix.one_apply]
    · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
      simp only [fromBlocks_apply₁₂, hB, Matrix.of_apply]
      rw [if_neg (by omega)]; simp
    · simp
    · simp only [lev, Sum.elim_inr] at hrs
      simp only [fromBlocks_apply₂₂, Matrix.add_apply, hCB]
      rw [if_neg (by omega)]; simp [Matrix.one_apply]
  · unfold simpleSum
    rw [hv]
    simp only [fromBlocks_apply₂₂, Matrix.add_apply, hCB]
    rw [Finset.sum_eq_single (⟨p - 1, by omega⟩ : Fin c), Finset.sum_eq_single (⟨p, hc⟩ : Fin c)]
    · rw [if_pos (by simp; omega), if_pos (by simp; omega), Matrix.one_apply_ne, add_zero]
      intro h
      have := congrArg Fin.val h
      simp at this; omega
    · intro j _ hj
      rw [if_neg]
      intro h
      apply hj
      ext
      simp at h ⊢; omega
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs with a b
      · exfalso
        apply hi
        ext
        simp; omega
      · rw [Matrix.one_apply_ne, add_zero]
        intro h
        have := congrArg Fin.val h
        omega
      · rfl
    · simp
  · show lowU C * upU B = _ * lowU C
    rw [mul_assoc, lowU_neg_mul, mul_one]
end GlobalTheory.RootExchangeFixed
