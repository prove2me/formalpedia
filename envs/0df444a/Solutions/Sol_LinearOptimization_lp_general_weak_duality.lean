-- Prove2me | solution 1 for LinearOptimization.lp_general_weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-10T02:46:56.702863+00:00
-- url     : https://prove2.me/submissions/bc827792-356a-4511-bdf4-bd2e329c08cd

import Definitions.Def_LinearOptimization_LagrangeanDual
import Mathlib.Tactic

open Matrix
open LinearOptimization

/-- Bertsimas--Tsitsiklis, Theorem 4.17, p. 184. -/
theorem solution {m₁ m₂ n : ℕ}
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ) (c : Fin n → ℝ)
    (D : Matrix (Fin m₂) (Fin n) ℝ) (d : Fin m₂ → ℝ)
    (x : Fin n → ℝ) (hxA : b ≤ A.mulVec x) (hxP : x ∈ polyhedron D d)
    (p : Fin m₁ → ℝ) (hp : 0 ≤ p) :
    lagrangeanObjective A b c (polyhedron D d) p ≤ ((c ⬝ᵥ x : ℝ) : EReal) := by
  have hlag : lagrangeanObjective A b c (polyhedron D d) p ≤
      ((c ⬝ᵥ x + p ⬝ᵥ (b - A.mulVec x) : ℝ) : EReal) := by
    unfold lagrangeanObjective
    exact iInf_le_of_le x (iInf_le_of_le hxP le_rfl)
  apply hlag.trans
  norm_cast
  have hdiff : b - A.mulVec x ≤ 0 := sub_nonpos.mpr hxA
  have hpen : p ⬝ᵥ (b - A.mulVec x) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (hp i) (hdiff i)
  linarith
