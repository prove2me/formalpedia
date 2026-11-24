-- Prove2me | solution 1 for GlobalTheory.SplitFlip.IsCoeffRing.inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:45.864987+00:00
-- url     : https://prove2.me/submissions/858297bd-5378-44ed-9194-ce6fd627e808

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
namespace IsCoeffRing
theorem _root_.solution {ϖ : kˣ} {ψ : AddChar k Circle} {α β : kˣ →* ℂˣ} {e : ℕ} {R : Subring ℂ}
    (h : IsCoeffRing ϖ ψ α β e R) : IsCoeffRing ϖ ψ⁻¹ α β e R :=
  { h with psi := fun x hx => h.psi (-x) (by rwa [mul_neg, Valuation.map_neg]) }
end IsCoeffRing
end GlobalTheory.SplitFlip
