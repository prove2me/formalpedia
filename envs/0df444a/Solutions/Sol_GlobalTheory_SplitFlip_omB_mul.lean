-- Prove2me | solution 1 for GlobalTheory.SplitFlip.omB_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:42:35.705641+00:00
-- url     : https://prove2.me/submissions/7b3d60a2-875f-494b-b833-d4eb9999581b

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
theorem _root_.solution (ν α : kˣ →* ℂˣ) (g g' : GL A' k) (h h' : GL D k) (Ψ : Matrix A' D k → ℂ) :
    omB ν α (g * g') (h * h') Ψ = omB ν α g h (omB ν α g' h' Ψ) :=
  LinearMap.congr_fun ((repB ν α).map_mul (g, h) (g', h')) Ψ
end GlobalTheory.SplitFlip
