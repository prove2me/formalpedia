-- Prove2me | solution 1 for GlobalTheory.SplitFlip.omA_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:47.309101+00:00
-- url     : https://prove2.me/submissions/7489f4fd-a285-4e7c-8c21-0180650b2f7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_comp_mul_mem_SB

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
theorem _root_.solution (ν β : kˣ →* ℂˣ) (g : GL A k) (h : GL D k) {Φ : Matrix A D k → ℂ}
    (hΦ : Φ ∈ SB (Matrix A D k)) : omA ν β g h Φ ∈ SB (Matrix A D k) :=
  (SB (Matrix A D k)).smul_mem _ (comp_mul_mem_SB g⁻¹ (invT h) hΦ)
end GlobalTheory.SplitFlip
