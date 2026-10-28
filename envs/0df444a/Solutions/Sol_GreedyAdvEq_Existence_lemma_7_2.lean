-- Prove2me | solution 1 for GreedyAdvEq.Existence.lemma_7_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:54:24.549356+00:00
-- url     : https://prove2.me/submissions/81785567-77f3-422c-aa16-b274c4435c88

import Mathlib
import Definitions.Def_GreedyAdvEq_Existence_Setting
import Definitions.Def_GreedyAdvEq_Existence_Algorithm1

open GreedyAdvEq.Existence in
theorem solution (d : ℕ) (f : E d → E d → ℝ) (b L : ℝ) (hb : 0 < b) (hL : 0 < L)
    (hf : IsModel f b L) (Eig : E d → E d → ℝ × E d) (μ₁ μ₃ μ₄ : ℝ)
    (hμ₁ : 0 < μ₁) (hμ₃ : 0 < μ₃) (hμ₄ : 0 ≤ μ₄) (hEig : IsEigOracle f Eig μ₄)
    (x y0 : E d) (ε' : ℝ) (hε' : 0 < ε') (hterm : Alg1Terminates f L Eig μ₁ μ₃ x y0 ε') :
    ‖gradY f x (alg1Out f L Eig μ₁ μ₃ x y0 ε')‖ ≤ ε' ∧
      ∀ v : E d, hessY f x (alg1Out f L Eig μ₁ μ₃ x y0 ε') v v ≤
        (Real.sqrt (L * ε') + μ₄) * ‖v‖ ^ 2 := by
  have hstop : alg1Stop f L Eig x ε' (alg1Out f L Eig μ₁ μ₃ x y0 ε') := by
    unfold alg1Out alg1Len
    classical
    rw [dif_pos hterm]
    exact Nat.find_spec hterm
  refine ⟨hstop.1, fun v => ?_⟩
  have h1 := (hEig x (alg1Out f L Eig μ₁ μ₃ x y0 ε')).2.2 v
  have h2 : ((Eig x (alg1Out f L Eig μ₁ μ₃ x y0 ε')).1 + μ₄) * ‖v‖ ^ 2 ≤
      (Real.sqrt (L * ε') + μ₄) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hstop.2]) (sq_nonneg _)
  exact h1.trans h2
