-- Prove2me | solution 1 for GeneralCK.Comparison.nonpos_of_deriv_nonpos_when_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:21:22.623793+00:00
-- url     : https://prove2.me/submissions/d734c97c-1b3d-4c20-b807-02d613e93f10

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace GeneralCK.Comparison
end GeneralCK.Comparison

open GeneralCK GeneralCK.Comparison in
open Set in
theorem solution {g g' : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn g (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt g (g' t) (Ici t) t)
    (h0 : g 0 ≤ 0)
    (hbound : ∀ t ∈ Ico 0 T, 0 < g t → g' t ≤ 0) : g T ≤ 0 := by
  by_contra hn
  have hp : 0 < g T := lt_of_not_ge hn
  let e := g T / (2 * (T + 1))
  have he : 0 < e := div_pos hp (by positivity)
  have hB : ∀ t : ℝ, HasDerivAt (fun s => e * (s + 1)) e t := by
    intro t
    simpa using ((hasDerivAt_id t).add_const 1).const_mul e
  have hb := image_le_of_deriv_right_lt_deriv_boundary hc hd
    (B := fun t => e * (t + 1)) (B' := fun _ => e)
    (by simpa using h0.trans he.le) hB (by
      intro t ht htB
      have hg : 0 < g t := by rw [htB]; exact mul_pos he (by linarith [ht.1])
      exact (hbound t ht hg).trans_lt he)
    (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩)
  have heq : e * (T + 1) = g T / 2 := by
    dsimp [e]
    field_simp
  rw [heq] at hb
  linarith
