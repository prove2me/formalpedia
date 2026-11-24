-- Prove2me | solution 1 for MomentComparison.complexNoise_contract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:36.773796+00:00
-- url     : https://prove2.me/submissions/df440e2e-23cd-44c2-a649-1e909511779d

module
public import Definitions.Def_MomentComparison_MomentNorm
public import Definitions.Def_MomentComparison_NoisePolynomial
public import Definitions.Def_MomentComparison_TwoPointReduction
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Hypercontractivity
public import Theorems.Thm_MomentComparison_complexNoise_contract_of_twoPoint
public import Theorems.Thm_MomentComparison_twoPoint_contract


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
namespace MomentComparison
theorem _root_.solution {p : ℝ} (hp : 2 < p) {w : ℂ} (hw : inLens p w)
    {n : ℕ} (f : Cube n → ℂ) :
    complexMomentNorm p (complexNoise w f) ≤ complexMomentNorm (p / (p - 1)) f := by
  have hp' : 0 < p := by linarith
  have hden : 0 < p - 1 := by linarith
  have hq : 0 < p / (p - 1) := div_pos hp' hden
  have hqp : p / (p - 1) ≤ p :=
    (div_le_iff₀ hden).2 (by nlinarith [mul_nonneg hp'.le (show 0 ≤ p - 2 by linarith)])
  exact complexNoise_contract_of_twoPoint hq hqp (twoPoint_contract hp hw) f
end MomentComparison
