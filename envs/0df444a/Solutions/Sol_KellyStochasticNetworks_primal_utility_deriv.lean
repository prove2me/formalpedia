-- Prove2me | solution 1 for KellyStochasticNetworks.primal_utility_deriv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:24:29.852296+00:00
-- url     : https://prove2.me/submissions/d224ffd6-4420-425b-bbb4-4724c0be431a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

lemma pr_upd_deriv {R : ℕ} (x : Fin R → ℝ) (r : Fin R) (F : Fin R → ℝ → ℝ) (F' : ℝ)
    (hF : HasDerivAt (F r) F' (x r)) :
    HasDerivAt (fun t => ∑ r', F r' (Function.update x r t r')) F' (x r) := by
  have hd : ∀ r' ∈ Finset.univ, HasDerivAt (fun t => F r' (Function.update x r t r'))
      (if r' = r then F' else 0) (x r) := by
    intro r' _
    by_cases hr : r' = r
    · subst hr; simp only [Function.update_self, if_true]; exact hF
    · simp only [Function.update_of_ne hr, hr, if_false]; exact hasDerivAt_const _ _
  have := HasDerivAt.fun_sum hd
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  exact this

theorem pr_utility_deriv {J R : ℕ} (A : Fin J → Fin R → ℝ) (w : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hp : ∀ j, Continuous (p j)) (x : Fin R → ℝ) (hx : ∀ r, 0 < x r)
    (r : Fin R) :
    HasDerivAt (fun t : ℝ => primalUtility A w p (Function.update x r t))
      (w r / x r - ∑ j, A j r * p j (linkFlow A x j)) (x r) := by
  have h1 : HasDerivAt (fun t : ℝ => ∑ r', w r' * Real.log (Function.update x r t r'))
      (w r / x r) (x r) := by
    have := (Real.hasDerivAt_log (hx r).ne').const_mul (w r)
    rw [← div_eq_mul_inv] at this
    exact pr_upd_deriv x r (fun r' s => w r' * Real.log s) (w r / x r) this
  have hL : ∀ j, HasDerivAt (fun t : ℝ => linkFlow A (Function.update x r t) j) (A j r) (x r) := by
    intro j
    have := (hasDerivAt_id (x r)).const_mul (A j r)
    rw [mul_one] at this
    exact pr_upd_deriv x r (fun r' s => A j r' * s) (A j r) this
  have h2 : HasDerivAt (fun t : ℝ => ∑ j, ∫ y in (0:ℝ)..(linkFlow A (Function.update x r t) j), p j y)
      (∑ j, p j (linkFlow A x j) * A j r) (x r) := by
    apply HasDerivAt.fun_sum
    intro j _
    have hF := ((hp j).integral_hasStrictDerivAt 0
      (linkFlow A (Function.update x r (x r)) j)).hasDerivAt
    have := hF.comp (x r) (hL j)
    rw [Function.update_eq_self] at this
    exact this
  have := h1.sub h2
  have e : (w r / x r - ∑ j, A j r * p j (linkFlow A x j)) =
      w r / x r - ∑ j, p j (linkFlow A x j) * A j r := by
    congr 1; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e]
  unfold primalUtility
  exact this

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℝ) (w : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hp : ∀ j, Continuous (p j)) (x : Fin R → ℝ) (hx : ∀ r, 0 < x r) (r : Fin R) :
    HasDerivAt (fun t : ℝ => primalUtility A w p (Function.update x r t))
      (w r / x r - ∑ j, A j r * p j (linkFlow A x j)) (x r) := by
  exact pr_utility_deriv A w p hp x hx r
