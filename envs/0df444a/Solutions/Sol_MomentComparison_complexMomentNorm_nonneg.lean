-- Prove2me | solution 1 for MomentComparison.complexMomentNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:31:34.620621+00:00
-- url     : https://prove2.me/submissions/386385e9-055b-46fb-a146-7ef3423d9232

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_MomentNorm
public import Theorems.Thm_MomentComparison_cubeAverage_nonneg

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
namespace MomentComparison
theorem _root_.solution {n : ℕ} (p : ℝ) (f : Cube n → ℂ) :
    0 ≤ complexMomentNorm p f :=
  Real.rpow_nonneg (cubeAverage_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _
end MomentComparison
