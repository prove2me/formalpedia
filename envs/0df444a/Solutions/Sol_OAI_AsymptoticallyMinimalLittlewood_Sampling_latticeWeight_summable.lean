-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Sampling.latticeWeight_summable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:43:05.133546+00:00
-- url     : https://prove2.me/submissions/4c7e00ea-49fd-4138-987d-8d7163311500

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SamplingTail.lean:L21-L32
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Sampling.latticeWeight_summable. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail

-- ---- from OAI.Analysis.Littlewood.SamplingTail ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open MeasureTheory FourierTransform Filter Topology Complex
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open QuadraticTail

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
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open MeasureTheory FourierTransform Filter Topology Complex
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open QuadraticTail


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.latticeWeight_summable := @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.latticeWeight_summable
