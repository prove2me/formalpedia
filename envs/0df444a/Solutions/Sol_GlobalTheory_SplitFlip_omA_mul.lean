-- Prove2me | solution 1 for GlobalTheory.SplitFlip.omA_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:19.756245+00:00
-- url     : https://prove2.me/submissions/2ecf93aa-8290-40e8-8b52-10c6ffac4474

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
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
namespace GlobalTheory.SplitFlip
theorem _root_.solution (ν β : kˣ →* ℂˣ) (g g' : GL A k) (h h' : GL D k) (Φ : Matrix A D k → ℂ) :
    omA ν β (g * g') (h * h') Φ = omA ν β g h (omA ν β g' h' Φ) :=
  LinearMap.congr_fun ((repA ν β).map_mul (g, h) (g', h')) Φ
end GlobalTheory.SplitFlip
