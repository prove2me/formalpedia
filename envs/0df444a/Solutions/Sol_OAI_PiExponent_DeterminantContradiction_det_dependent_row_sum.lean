-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.det_dependent_row_sum
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:04:06.470971+00:00
-- url     : https://prove2.me/submissions/c3517553-52be-4fa5-9263-e72928e3882b

import Mathlib

open scoped BigOperators

theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (α : ι → Type) [∀ i, Fintype (α i)]
    (w : ∀ i, α i → ℂ)
    (N : (∀ i, α i) → Matrix ι ι ℂ)
    (f0 : ∀ i, α i)
    (M : Matrix ι ι ℂ)
    (hM : ∀ i j, M i j =
      ∑ a : α i, w i a * N (Function.update f0 i a) i j),
    M.det =
      ∑ f : (∀ i, α i), (∏ i, w i (f i)) * (N f).det) := by
  intro h
  have key := h (ι := Fin 2) (fun _ => Bool) (fun _ _ => 1)
    (fun f => if f = (fun _ => true) then 0 else 1) (fun _ => false)
    ((2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (by
      intro i j
      rw [Fintype.sum_bool]
      have h1 : Function.update (fun _ : Fin 2 => false) i true ≠ (fun _ => true) := by
        intro e
        have := congrFun e (if i = 0 then 1 else 0)
        fin_cases i <;> simp [Function.update] at this
      have h2 : Function.update (fun _ : Fin 2 => false) i false ≠ (fun _ => true) := by
        intro e
        have := congrFun e i
        simp at this
      simp only [h1, h2, if_false, one_mul]
      simp [Matrix.smul_apply, two_mul])
  rw [Fintype.sum_eq_add_sum_compl (fun _ => true)] at key
  simp only [if_true, Matrix.det_zero, Finset.prod_const_one, one_mul, mul_zero, zero_add] at key
  have hc : ∀ f ∈ ({fun _ => true} : Finset (Fin 2 → Bool))ᶜ,
      (if f = (fun _ => true) then (0 : Matrix (Fin 2) (Fin 2) ℂ) else 1).det = 1 := by
    intro f hf
    rw [Finset.mem_compl, Finset.mem_singleton] at hf
    simp [hf]
  rw [Finset.sum_congr rfl hc] at key
  simp [Matrix.det_smul, Finset.card_compl] at key
  norm_num at key
