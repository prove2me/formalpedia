-- Prove2me | solution 1 for KellyStochasticNetworks.primal_lyapunov_deriv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:24:30.887997+00:00
-- url     : https://prove2.me/submissions/55579d0d-aa04-48cc-ad19-e7f0b56ca9ef

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

theorem pr_lyapunov_deriv {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hκ : ∀ r, 0 < κ r)
    (hp : ∀ j, Continuous (p j))
    (x : ℝ → Fin R → ℝ) (t : ℝ) (hpos : ∀ r, 0 < x t r)
    (hode : ∀ r, HasDerivAt (fun s => x s r) (primalDrift A w κ p (x t) r) t) :
    HasDerivAt (fun s => primalUtility A w p (x s))
        (∑ r, (κ r / x t r)
          * (w r - x t r * ∑ j, A j r * p j (linkFlow A (x t) j)) ^ 2) t
      ∧ 0 ≤ ∑ r, (κ r / x t r)
          * (w r - x t r * ∑ j, A j r * p j (linkFlow A (x t) j)) ^ 2 := by
  set D : Fin R → ℝ := fun r => primalDrift A w κ p (x t) r with hD
  have h1 : HasDerivAt (fun s => ∑ r, w r * Real.log (x s r))
      (∑ r, w r * (D r / x t r)) t :=
    HasDerivAt.fun_sum fun r _ => ((hode r).log (hpos r).ne').const_mul (w r)
  have hL : ∀ j, HasDerivAt (fun s => linkFlow A (x s) j) (∑ r, A j r * D r) t :=
    fun j => HasDerivAt.fun_sum fun r _ => (hode r).const_mul (A j r)
  have h2 : HasDerivAt (fun s => ∑ j, ∫ y in (0:ℝ)..(linkFlow A (x s) j), p j y)
      (∑ j, p j (linkFlow A (x t) j) * ∑ r, A j r * D r) t := by
    apply HasDerivAt.fun_sum
    intro j _
    have hF := ((hp j).integral_hasStrictDerivAt 0 (linkFlow A (x t) j)).hasDerivAt
    exact hF.comp t (hL j)
  have h := h1.sub h2
  have hval : (∑ r, w r * (D r / x t r)) - ∑ j, p j (linkFlow A (x t) j) * ∑ r, A j r * D r =
      ∑ r, (κ r / x t r) * (w r - x t r * ∑ j, A j r * p j (linkFlow A (x t) j)) ^ 2 := by
    have e1 : ∑ j, p j (linkFlow A (x t) j) * ∑ r, A j r * D r =
        ∑ r, D r * ∑ j, A j r * p j (linkFlow A (x t) j) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hx0 := (hpos r).ne'
    simp only [hD, primalDrift]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [← hval]
    unfold primalUtility
    exact h
  · exact Finset.sum_nonneg fun r _ =>
      mul_nonneg (div_nonneg (hκ r).le (hpos r).le) (sq_nonneg _)

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hκ : ∀ r, 0 < κ r)
    (hp : ∀ j, Continuous (p j))
    (x : ℝ → Fin R → ℝ) (t : ℝ) (hpos : ∀ r, 0 < x t r)
    (hode : ∀ r, HasDerivAt (fun s => x s r) (primalDrift A w κ p (x t) r) t) :
    HasDerivAt (fun s => primalUtility A w p (x s))
        (∑ r, (κ r / x t r)
          * (w r - x t r * ∑ j, A j r * p j (linkFlow A (x t) j)) ^ 2) t
      ∧ 0 ≤ ∑ r, (κ r / x t r)
          * (w r - x t r * ∑ j, A j r * p j (linkFlow A (x t) j)) ^ 2 := by
  exact pr_lyapunov_deriv A w κ p hκ hp x t hpos hode
