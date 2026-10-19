-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Sampling.block_value_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:02:08.586808+00:00
-- url     : https://prove2.me/submissions/546c0526-da53-4f40-98d3-86be85cd26c2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/BlockSampling.lean:L203-L219
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Sampling.block_value_bound. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy
import Definitions.Def_OAI_Analysis_Littlewood_ModeSampling

-- ---- from OAI.Analysis.Littlewood.BlockSampling ----
namespace OAI

universe uP uJ uI

namespace AsymptoticallyMinimalLittlewood.Cutoff
noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology ContDiff

end
end AsymptoticallyMinimalLittlewood.Cutoff

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators ComplexConjugate
open Complex UnitAddTorus
namespace Sampling
open QuadraticTail

/-- Disjointly supported block values preserve the [-1,1] constraint. -/
lemma block_value_bound {H : ℕ} (χ : Fin H → ℝ) (F : Fin H → ℂ)
    (hχ : ∀ h, 0≤χ h ∧ χ h≤1) (hF : ∀ h, ‖F h‖≤1)
    (hdisj : ∀ i j, i≠j → χ i*χ j=0) :
    ‖∑ h, (χ h : ℂ)*F h‖≤1 := by
  classical
  by_cases hn : ∃ h, χ h≠0
  · obtain ⟨h,hh⟩ := hn
    rw [Finset.sum_eq_single h]
    · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hχ h).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hχ h).2).trans (hF h)
    · intro j _ hj
      have hz : χ j=0 := (mul_eq_zero.mp (hdisj j h hj)).resolve_right hh
      simp [hz]
    · simp
  · push Not at hn
    simp [hn]

end Sampling
end
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
-- [generator] trimmed: open MeasureTheory Filter Complex QuadraticTail UnitAddTorus Packing Cutoff
open MeasureTheory Filter Complex QuadraticTail UnitAddTorus Packing

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open scoped BigOperators ComplexConjugate
open Complex UnitAddTorus
open QuadraticTail


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.block_value_bound := @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.block_value_bound
