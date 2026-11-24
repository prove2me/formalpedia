-- Prove2me | solution 1 for GlobalTheory.SplitFlip.IsUnif.maximalIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:17.791812+00:00
-- url     : https://prove2.me/submissions/f4be750a-47f4-4f1c-97c4-64336b92b742

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitFlip
namespace IsUnif
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) :
    IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {(⟨ϖ, hϖ.mem⟩ : 𝒪[k])} := by
  ext y
  rw [Ideal.mem_span_singleton, ← (Valuation.integer.integers (valuation k)).le_iff_dvd,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  show _ ↔ valuation k (y : k) ≤ valuation k (ϖ : k)
  rw [hϖ, le_uniformizer_iff]
end IsUnif
end GlobalTheory.SplitFlip
