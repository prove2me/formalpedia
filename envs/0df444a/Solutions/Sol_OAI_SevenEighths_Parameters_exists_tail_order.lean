-- Prove2me | solution 1 for OAI.SevenEighths.Parameters.exists_tail_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:33.043207+00:00
-- url     : https://prove2.me/submissions/1d770fd7-0775-405b-850c-f16797240d44

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
theorem _root_.solution {τ B saving : ℝ} (hτ : 0 < τ) :
    ∃ N : ℕ, B - τ * N < -saving := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((B + saving) / τ)
  have h := (div_lt_iff₀ hτ).mp hN
  exact ⟨N, by nlinarith⟩
end OAI.SevenEighths.Parameters
