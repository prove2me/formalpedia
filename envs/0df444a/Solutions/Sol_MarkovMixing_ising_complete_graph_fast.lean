-- Prove2me | solution 1 for MarkovMixing.ising_complete_graph_fast
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T01:59:56.621179+00:00
-- url     : https://prove2.me/submissions/7f11732e-ae9e-4782-b0f1-a3c707c2e7bc

import Theorems.Thm_MarkovMixing_ising_high_temperature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Fast mixing of the Curie–Weiss Glauber dynamics (LPW Theorem 15.3(i))
-/

namespace MarkovMixing

noncomputable section

/-- `tanh x ≤ x` for `x ≥ 0`: the function `x cosh x − sinh x` has derivative
`x sinh x ≥ 0` and vanishes at `0`. -/
private lemma tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => u * Real.cosh u - Real.sinh u)
      (t * Real.sinh t) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => u * Real.cosh u)
        (1 * Real.cosh t + t * Real.sinh t) t :=
      (hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)
    exact (h1.fun_sub (Real.hasDerivAt_sinh t)).congr_deriv (by ring)
  have hdiff : Differentiable ℝ (fun u : ℝ => u * Real.cosh u - Real.sinh u) :=
    fun t => (hd t).differentiableAt
  have hmono : Monotone (fun u : ℝ => u * Real.cosh u - Real.sinh u) := by
    refine monotone_of_deriv_nonneg hdiff fun t => ?_
    rw [(hd t).deriv]
    rcases le_total 0 t with h | h
    · have hs : 0 ≤ Real.sinh t := by
        rw [← Real.sinh_zero]
        exact Real.sinh_le_sinh.mpr h
      exact mul_nonneg h hs
    · have hs : Real.sinh t ≤ 0 := by
        rw [← Real.sinh_zero]
        exact Real.sinh_le_sinh.mpr h
      nlinarith
  have h0 := hmono hx
  simp only [Real.cosh_zero, Real.sinh_zero, zero_mul, sub_zero, sub_self] at h0
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos x)]
  linarith

end

end MarkovMixing

open MarkovMixing

/-- **Theorem 15.3(i)** (LPW): for the Glauber dynamics of the Ising model
on the complete graph on `n` vertices at `β = α/n` with `α < 1`,
`t_mix(ε) ≤ ⌈n(log n + log(1/ε))/(1−α)⌉`. -/
theorem solution (n : ℕ) (hn : 2 ≤ n)
    (α : ℝ) (hα0 : 0 < α) (hα : α < 1) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (mixingTime (glauber (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)))
        (isingDist (⊤ : SimpleGraph (Fin n)) (α / n)) ε : ℝ) ≤
      ⌈(n : ℝ) * (Real.log n + Real.log (1 / ε)) / (1 - α)⌉₊ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hβ : (0 : ℝ) < α / n := by positivity
  have hΔ : ((⊤ : SimpleGraph (Fin n)).maxDegree : ℝ) = (n : ℝ) - 1 := by
    rw [SimpleGraph.maxDegree_top, Fintype.card_fin, Nat.cast_sub (by omega : 1 ≤ n),
      Nat.cast_one]
  have ht : Real.tanh (α / n) ≤ α / n := tanh_le_self (by positivity)
  have ht0 : 0 ≤ Real.tanh (α / n) := by
    rw [← Real.tanh_zero]
    have : Real.tanh 0 ≤ Real.tanh (α / n) := by
      rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
      rw [div_le_div_iff₀ (Real.cosh_pos 0) (Real.cosh_pos _)]
      have h1 : Real.sinh 0 ≤ Real.sinh (α / n) := Real.sinh_le_sinh.mpr hβ.le
      simp only [Real.sinh_zero, zero_mul]
      positivity
    simpa using this
  have hkey : ((⊤ : SimpleGraph (Fin n)).maxDegree : ℝ) * Real.tanh (α / n) ≤ α := by
    rw [hΔ]
    have h1 : ((n : ℝ) - 1) * Real.tanh (α / n) ≤ ((n : ℝ) - 1) * (α / n) :=
      mul_le_mul_of_nonneg_left ht (by linarith)
    have h2 : ((n : ℝ) - 1) * (α / n) ≤ α := by
      have he : ((n : ℝ) - 1) * (α / n) = α - α / n := by field_simp
      have hp : 0 ≤ α / (n : ℝ) := by positivity
      rw [he]; linarith
    linarith
  have hDob : ((⊤ : SimpleGraph (Fin n)).maxDegree : ℝ) * Real.tanh (α / n) < 1 := by
    linarith
  have hmain := (ising_high_temperature (⊤ : SimpleGraph (Fin n)) (α / n) hβ ε hε hε1).1 hDob
  refine hmain.trans ?_
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  rw [hcard]
  have hnum : 0 ≤ (n : ℝ) * (Real.log n + Real.log (1 / ε)) := by
    have h1 : 0 ≤ Real.log n := Real.log_nonneg hn1
    have h2 : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
    positivity
  have hcmp : (n : ℝ) * (Real.log n + Real.log (1 / ε))
        / (1 - ((⊤ : SimpleGraph (Fin n)).maxDegree : ℝ) * Real.tanh (α / n))
      ≤ (n : ℝ) * (Real.log n + Real.log (1 / ε)) / (1 - α) :=
    div_le_div_of_nonneg_left hnum (by linarith) (by linarith)
  exact_mod_cast Nat.ceil_mono hcmp
