-- Prove2me | solution 1 for Hirsch.larman_high_dimension
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:52:23.061472+00:00
-- url     : https://prove2.me/submissions/f0994f04-9e73-45d3-93fc-fc8962f126e9

-- Port of elmismisimoxhunca submission daeb2fd4-5934-45f9-a5a6-78620650f831, from Mathlib c5ea003 to 0df444a.
import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_klee_three_dimensional_bound
import Theorems.Thm_Hirsch_larman_dimension_step

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace HirschLarmanTop

/-- Padding a walk with stationary steps: `DiamLE` is monotone in the bound. -/
theorem diamLE_mono {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) {B B' : ℕ}
    (hB : B ≤ B') (h : DiamLE P B) : DiamLE P B' := by
  intro u hu v hv
  obtain ⟨w, h0, hB0, hstep⟩ := h u hu v hv
  refine ⟨fun i => w (min i B), ?_, ?_, ?_⟩
  · show w (min 0 B) = u
    rw [Nat.min_eq_left (Nat.zero_le B), h0]
  · show w (min B' B) = v
    rw [Nat.min_eq_right hB, hB0]
  · intro i hi
    show w (min i B) = w (min (i + 1) B) ∨ Adj P (w (min i B)) (w (min (i + 1) B))
    by_cases hiB : i < B
    · rw [Nat.min_eq_left hiB.le, Nat.min_eq_left (by omega)]
      exact hstep i hiB
    · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
      exact Or.inl rfl

/-- The strong form of Larman's bound, `2^(d-3) n - 1`, for every `d ≥ 3`, by induction
on the dimension with Klee's theorem as base and `larman_dimension_step` as step. -/
theorem larman_strong : ∀ (e : ℕ) (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin (e + 3)))
    (b : Fin n → ℝ), (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
    DiamLE (Hpoly a b) (2 ^ e * n - 1) := by
  intro e
  induction e with
  | zero =>
      intro n a b hne hbd
      have h := Hirsch.klee_three_dimensional_bound n a b hne hbd
      exact diamLE_mono _ (by omega) h
  | succ e ih =>
      intro n a b hne hbd
      have hstep := Hirsch.larman_dimension_step (e + 3) n (by omega)
        (fun m a' b' hne' hbd' => by
          have := ih m a' b' hne' hbd'
          simpa using this) a b hne hbd
      have heq : 2 ^ (e + 3 - 2) * n - 1 = 2 ^ (e + 1) * n - 1 := by
        congr 2
      rw [heq] at hstep
      exact hstep

end HirschLarmanTop

open HirschLarmanTop

/-- **Larman's bound in dimension at least 4.**  Induction on the dimension from Klee's
three-dimensional theorem through the layer recursion `larman_dimension_step`, which
carries the sharper invariant `2^(d-3) n - 1`. -/
theorem solution (d n : ℕ) (hd : 4 ≤ d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n * 2 ^ (d - 3)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
  have h := larman_strong e n a b hne hbd
  have heq : e + 3 - 3 = e := by omega
  rw [heq]
  exact diamLE_mono _ (by rw [mul_comm]; omega) h

#print axioms solution
