-- Prove2me | solution 1 for GlobalTheory.SplitFlip.latA_blockLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:19:37.845598+00:00
-- url     : https://prove2.me/submissions/8a102879-3ca4-420f-b80d-a516a8b87d65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_smul_diagLat
import Theorems.Thm_GlobalTheory_SplitFlip_dualLat_diagLat

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
variable {A D : Type*}
variable [Fintype D]
variable [DecidableEq D]
namespace GlobalTheory.SplitFlip
theorem _root_.solution (ϖ : kˣ) (e : ℕ) (P : Finset D) : latA ϖ e (blockLat ϖ e P) = blockLat ϖ e Pᶜ := by
  rw [latA, blockLat, dualLat_diagLat, smul_diagLat, blockLat]
  congr 1
  funext j
  by_cases h : j ∈ P <;> simp [blockUnits, h]
end GlobalTheory.SplitFlip
