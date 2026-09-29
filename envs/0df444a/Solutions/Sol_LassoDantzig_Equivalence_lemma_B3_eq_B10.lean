-- Prove2me | solution 1 for LassoDantzig.Equivalence.lemma_B3_eq_B10
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:49:36.468011+00:00
-- url     : https://prove2.me/submissions/a1e6ad9a-a6ac-4eda-8d23-8360ce94d4da

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

theorem aux_b3b10_colNorm_le_fmax {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) :
    colNorm X j ≤ fmax X := by
  unfold fmax
  exact le_ciSup (Set.finite_range _).bddAbove j

end LassoDantzig.Equivalence

open LassoDantzig.Equivalence

theorem solution {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (f w : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hw : NoiseEvent X r w) (βD : Fin M → ℝ) (hD : IsDantzig X (fun i => f i + w i) r βD) :
    ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * (f i - X.mulVec βD i)| ≤ 2 * r * fmax X := by
  intro j
  have h1 := hD.1 j
  have h2 := hw j
  have h3 := aux_b3b10_colNorm_le_fmax X j
  have hsplit : (1 / (n : ℝ)) * ∑ i, X i j * (f i - X.mulVec βD i)
      = (1 / (n : ℝ)) * ∑ i, X i j * ((fun i => f i + w i) i - X.mulVec βD i)
        - (1 / (n : ℝ)) * ∑ i, X i j * w i := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hsplit]
  calc |(1 / (n : ℝ)) * ∑ i, X i j * ((fun i => f i + w i) i - X.mulVec βD i)
        - (1 / (n : ℝ)) * ∑ i, X i j * w i|
      ≤ |(1 / (n : ℝ)) * ∑ i, X i j * ((fun i => f i + w i) i - X.mulVec βD i)|
        + |(1 / (n : ℝ)) * ∑ i, X i j * w i| := abs_sub _ _
    _ ≤ r * colNorm X j + r * colNorm X j := add_le_add h1 h2
    _ = 2 * r * colNorm X j := by ring
    _ ≤ 2 * r * fmax X := by
        apply mul_le_mul_of_nonneg_left h3
        linarith
