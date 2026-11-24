-- Prove2me | solution 1 for MomentComparison.cubeAverage_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:15:02.877615+00:00
-- url     : https://prove2.me/submissions/813228e6-e3a7-48c0-96ae-809ccc9dd358

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_MomentNorm

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
namespace MomentComparison
theorem _root_.solution {n : ℕ} {f : Cube n → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ cubeAverage f :=
  div_nonneg (Finset.sum_nonneg fun x _ => hf x) (by positivity)
end MomentComparison
