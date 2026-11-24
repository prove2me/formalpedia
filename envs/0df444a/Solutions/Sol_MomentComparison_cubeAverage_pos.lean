-- Prove2me | solution 1 for MomentComparison.cubeAverage_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:07:51.624399+00:00
-- url     : https://prove2.me/submissions/97ea513c-6cad-427c-b9dc-352f2f751729

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
theorem _root_.solution {n : ℕ} {f : Cube n → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hpos : ∃ x, 0 < f x) : 0 < cubeAverage f := by
  obtain ⟨x, hx⟩ := hpos
  exact div_pos (Finset.sum_pos' (fun x _ => hf x) ⟨x, Finset.mem_univ _, hx⟩)
    (by positivity)
end MomentComparison
