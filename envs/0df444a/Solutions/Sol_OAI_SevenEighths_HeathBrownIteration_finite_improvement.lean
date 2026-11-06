-- Prove2me | solution 1 for OAI.SevenEighths.HeathBrownIteration.finite_improvement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:01.085082+00:00
-- url     : https://prove2.me/submissions/cf9d9172-7b3c-4d2a-b295-32053399d2bd

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_HeathBrownIteration
import Theorems.Thm_OAI_SevenEighths_HeathBrownIteration_exponent_bounds
import Theorems.Thm_OAI_SevenEighths_HeathBrownIteration_exists_exponent_lt

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.HeathBrownIteration
noncomputable section
namespace OAI.SevenEighths.HeathBrownIteration
theorem _root_.solution {P : ℝ → Prop} (hstart : P 2)
    (himprove : ∀ x : ℝ, (4 / 3 : ℝ) < x → x ≤ 2 → P x → P (step x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, (4 / 3 : ℝ) < x ∧ x ≤ 2 ∧ x < 4 / 3 + ε ∧ P x := by
  have hp (n : ℕ) : P (exponent n) := by
    induction n with
    | zero => exact hstart
    | succ n ih => exact himprove _ (exponent_bounds n).1 (exponent_bounds n).2 ih
  obtain ⟨n, hn⟩ := exists_exponent_lt hε
  exact ⟨exponent n, (exponent_bounds n).1, (exponent_bounds n).2, hn, hp n⟩
end OAI.SevenEighths.HeathBrownIteration
