-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.exists_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:55:19.514687+00:00
-- url     : https://prove2.me/submissions/068a8859-c7fa-413c-88b9-46641919d312

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons
import Theorems.Thm_GlobalTheory_GLFirstColumn_continuous_detM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn
namespace GlobalTheory.GLFirstColumn
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) :
    ∃ s : (Fin (k + 1) → ℂ) → Fin (k + 1) → Fin (k + 1) → ℂ, Measurable s ∧
      ∀ x, x ≠ 0 → (Matrix.of (s x)).det = 1 ∧ ∀ a, s x a 0 = x a := by
  classical
  let B : Fin (k + 1) → (Fin (k + 1) → ℂ) → Fin (k + 1) → Fin (k + 1) → ℂ := fun i x =>
    ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).updateCol i x).submatrix id (Equiv.swap 0 i)
  have hBm : ∀ i, Measurable (B i) := fun i => by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    simp only [B, submatrix_apply, updateCol_apply, id]
    split_ifs
    · exact measurable_pi_apply a
    · exact measurable_const
  have hBd : ∀ i x, x i ≠ 0 → (Matrix.of (B i x)).det ≠ 0 := fun i x hx => by
    show (((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).updateCol i x).submatrix id
      (Equiv.swap 0 i)).det ≠ 0
    rw [det_permute', ← cramer_apply, cramer_one]
    refine mul_ne_zero ?_ hx
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 i)) with h | h <;> simp [h]
  have hex : ∀ x : Fin (k + 1) → ℂ, ∃ n : ℕ, x = 0 ∨ x (Fin.ofNat (k + 1) n) ≠ 0 := fun x => by
    by_cases h : x = 0
    · exact ⟨0, Or.inl h⟩
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      exact ⟨i, Or.inr (by simpa using hi)⟩
  let C : (Fin (k + 1) → ℂ) → Fin (k + 1) → Fin (k + 1) → ℂ := fun x =>
    B (Fin.ofNat (k + 1) (Nat.find (hex x))) x
  have hCm : Measurable C := by
    refine Measurable.find (f := fun n x => B (Fin.ofNat (k + 1) n) x)
      (p := fun n x => x = 0 ∨ x (Fin.ofNat (k + 1) n) ≠ 0) (fun n => hBm _) (fun n => ?_) hex
    have h1 : Measurable fun x : Fin (k + 1) → ℂ => x (Fin.ofNat (k + 1) n) :=
      measurable_pi_apply _
    exact (measurableSet_singleton 0).union (h1 (measurableSet_singleton (0 : ℂ)).compl)
  have hl : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  refine ⟨fun x => (Matrix.of (C x)).updateCol (Fin.last k)
    (((Matrix.of (C x)).det)⁻¹ • fun a => C x a (Fin.last k)), ?_, fun x hx => ⟨?_, fun a => ?_⟩⟩
  · refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    have h1 : ∀ b, Measurable fun x => C x a b := fun b =>
      (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hCm)
    simp only [updateCol_apply, of_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · exact (continuous_detM.measurable.comp hCm).inv.mul (h1 _)
    · exact h1 _
  · have hd : (Matrix.of (C x)).det ≠ 0 := hBd _ x ((Nat.find_spec (hex x)).resolve_left hx)
    show ((Matrix.of (C x)).updateCol (Fin.last k)
      (((Matrix.of (C x)).det)⁻¹ • fun a => (Matrix.of (C x)) a (Fin.last k))).det = 1
    rw [det_updateCol_smul, updateCol_eq_self, inv_mul_cancel₀ hd]
  · refine (updateCol_ne hl).trans ?_
    show (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).updateCol _ x a (Equiv.swap 0 _ 0) = x a
    rw [Equiv.swap_apply_left, updateCol_self]
end GlobalTheory.GLFirstColumn
