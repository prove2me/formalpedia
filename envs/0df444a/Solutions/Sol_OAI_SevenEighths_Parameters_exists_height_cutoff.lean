-- Prove2me | solution 1 for OAI.SevenEighths.Parameters.exists_height_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:30.343598+00:00
-- url     : https://prove2.me/submissions/6a126712-80e4-4279-9d83-36ef7b09f96b

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_OAI_NumberTheory_DirichletL_Parameters

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Parameters
namespace OAI.SevenEighths.Parameters
theorem _root_.solution {dmin allowance A : ℝ}
    (hd : 0 < dmin) (ha : 0 < allowance) (hA : 0 ≤ A) :
    ∃ τ : ℝ, 0 < τ ∧ τ < dmin / 100 ∧
      A * τ < dmin * allowance / 100 := by
  have hden : 0 < 200 * (1 + A) := by positivity
  let τ := min (dmin / 200) (dmin * allowance / (200 * (1 + A)))
  have ht : 0 < τ := lt_min (by positivity) (by positivity)
  have h1 : τ ≤ dmin / 200 := min_le_left _ _
  have h2 : τ ≤ dmin * allowance / (200 * (1 + A)) := min_le_right _ _
  have h2' : τ * (200 * (1 + A)) ≤ dmin * allowance :=
    (le_div_iff₀ hden).mp h2
  refine ⟨τ, ht, by linarith, ?_⟩
  have hp : 0 < dmin * allowance := mul_pos hd ha
  nlinarith
end OAI.SevenEighths.Parameters
