-- Prove2me | solution 1 for MDPFinance.Stationary.stochastic_lq_solution
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:16:04.009539+00:00
-- url     : https://prove2.me/submissions/999e79bd-ddb2-40c7-8701-41f042d872d1

import Mathlib
import Definitions.Def_MDPFinance_Stationary_NSValueFunction
import Definitions.Def_MDPFinance_Stationary_LQHelpers

open MeasureTheory
open scoped Matrix
open MDPFinance.Stationary

namespace LQCex

noncomputable def M0 : NSMarkovDecisionModel (Fin 1 → ℝ) (Fin 1 → ℝ) 0 where
  D := fun _ => Set.univ
  hD_meas := fun n hn => absurd hn (Nat.not_lt_zero n)
  hD_sel := fun n hn => absurd hn (Nat.not_lt_zero n)
  Q := fun _ => 0
  hQ_prob := fun n hn => absurd hn (Nat.not_lt_zero n)
  r := fun _ _ => 0
  hr_meas := fun _ _ => measurable_const
  g := fun x => -(xQx (1 : Matrix (Fin 1) (Fin 1) ℝ) x)
  hg_meas := by
    unfold xQx
    simp only [Matrix.one_mulVec]
    exact (Continuous.measurable (by fun_prop)).neg

end LQCex

open LQCex in
theorem solution : ¬ (∀ {m d N : ℕ} (M : NSMarkovDecisionModel (Fin m → ℝ) (Fin d → ℝ) N)
    (Qs : ℕ → Matrix (Fin m) (Fin m) ℝ) (hQs_sym : ∀ n ≤ N, (Qs n).IsSymm)
    (hQs_pd : ∀ n ≤ N, (Qs n).PosDef)
    (ν : ℕ → Measure (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin d) ℝ))
    (hPD : ∀ n < N, ∀ Q : Matrix (Fin m) (Fin m) ℝ, Q.IsSymm → Q.PosDef →
      (jointMatMean (ν (n + 1)) (fun A B => Bᵀ * Q * B)).PosDef)
    (hDn : ∀ n < N, M.D n = Set.univ)
    (hν_mom : ∀ n, 1 ≤ n → n ≤ N → (∀ i j, MemLp (fun p => p.1 i j) 2 (ν n)) ∧
      ∀ i j, MemLp (fun p => p.2 i j) 2 (ν n))
    (hQ : ∀ n < N, ∀ x a, M.Q n (x, a) = (ν (n + 1)).map (fun p => p.1.mulVec x + p.2.mulVec a))
    (hr : ∀ n < N, ∀ x a, M.r n (x, a) = -(xQx (Qs n) x))
    (hg : ∀ x, M.g x = -(xQx (Qs N) x))
    (Qtilde : ℕ → Matrix (Fin m) (Fin m) ℝ) (hQtilde_N : Qtilde N = Qs N)
    (hQtilde_rec : ∀ n < N, Qtilde n = Qs n +
      jointMatMean (ν (n + 1)) (fun A _ => Aᵀ * Qtilde (n + 1) * A) -
        jointMatMean (ν (n + 1)) (fun A B => Aᵀ * Qtilde (n + 1) * B) *
          (jointMatMean (ν (n + 1)) (fun _ B => Bᵀ * Qtilde (n + 1) * B))⁻¹ *
            jointMatMean (ν (n + 1)) (fun A B => Bᵀ * Qtilde (n + 1) * A)),
    (∀ n ≤ N, (Qtilde n).IsSymm ∧ Matrix.PosSemidef (Qtilde n)) ∧
      (∀ n ≤ N, ∀ x, NSV M n x = ((xQx (Qtilde n) x : ℝ) : EReal)) ∧
      (∃ fstar : ℕ → (Fin m → ℝ) → (Fin d → ℝ),
        (∀ n < N, fstar n = fun x =>
          -((jointMatMean (ν (n + 1)) (fun _ B => Bᵀ * Qtilde (n + 1) * B))⁻¹.mulVec
            ((jointMatMean (ν (n + 1)) (fun A B => Bᵀ * Qtilde (n + 1) * A)).mulVec x))) ∧
        (∀ n < N, ∀ x, NSL M n (NSV M (n + 1)) (x, fstar n x) = NST M n (NSV M (n + 1)) x) ∧
        NSIsPolicy M fstar ∧ NSVpi M fstar 0 = NSV M 0)) := by
  intro h
  have H := (h M0 (fun _ => 1) (fun _ _ => Matrix.isSymm_one) (fun _ _ => Matrix.PosDef.one)
    (fun _ => 0) (fun n hn => absurd hn (Nat.not_lt_zero n))
    (fun n hn => absurd hn (Nat.not_lt_zero n))
    (fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num))
    (fun n hn => absurd hn (Nat.not_lt_zero n)) (fun n hn => absurd hn (Nat.not_lt_zero n))
    (fun _ => rfl) (fun _ => 1) rfl (fun n hn => absurd hn (Nat.not_lt_zero n))).2.1 0 le_rfl
    (fun _ => 1)
  have hV : NSV M0 0 (fun _ => 1) = ((-(xQx (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 1)) : ℝ) :
      EReal) := rfl
  rw [hV] at H
  have hx : xQx (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 1) = 1 := by
    simp [xQx, dotProduct, Matrix.one_mulVec]
  rw [hx] at H
  have : (-1 : ℝ) = 1 := by exact_mod_cast H
  norm_num at this

#print axioms solution
