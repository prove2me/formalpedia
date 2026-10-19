-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.latticeWeight_summable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:21:15.110241+00:00
-- url     : https://prove2.me/submissions/66a46552-098b-4783-8284-a147cc9f2084

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/QuadraticTail.lean:L325-L336
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.latticeWeight_summable. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail

-- ---- from OAI.Analysis.Littlewood.QuadraticTail ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
namespace OAI

universe uI uZ

namespace AsymptoticallyMinimalLittlewood
namespace QuadraticTail
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

lemma latticeWeight_summable : Summable latticeWeight := by
  have hn : Summable (fun n : ℕ ↦ 1/(1+(n:ℝ))^2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ)))
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using h
  have hpos : (fun n : ℕ ↦ latticeWeight (n : ℤ)) = (fun n : ℕ ↦ 1/(1+(n:ℝ))^2) := by
    funext n
    simp [latticeWeight]
  have hneg : (fun n : ℕ ↦ latticeWeight (-(n : ℤ))) = (fun n : ℕ ↦ 1/(1+(n:ℝ))^2) := by
    funext n
    simp [latticeWeight]
  exact Summable.of_nat_of_neg (hpos ▸ hn) (hneg ▸ hn)

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.latticeWeight_summable := @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.latticeWeight_summable
