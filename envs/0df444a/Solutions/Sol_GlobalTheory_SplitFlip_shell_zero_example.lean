-- Prove2me | solution 1 for GlobalTheory.SplitFlip.shell_zero_example
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:12:00.944313+00:00
-- url     : https://prove2.me/submissions/43f78bbc-65df-4a1c-8689-a8a86b421293

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_apow_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_SplitFlip_valuation_gdet_of_mem_KO
import Theorems.Thm_GlobalTheory_SplitFlip_shellSet_zero
import Theorems.Thm_GlobalTheory_SplitFlip_haarVol_self


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
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitFlip
theorem _root_.solution (ϖ : kˣ) (ν : kˣ →* ℂˣ) (z : ℂ) (φ : Matrix A A k → ℂ)
    (hφ : ∀ g ∈ KO k A, φ g.val * (ν (gdet g) : ℂ) = 1) : shell (haarVol (KO k A)) ϖ ν z φ 0 = 1 := by
  rw [shell, shellSet_zero, setIntegral_congr_fun isOpen_KO.measurableSet (g := fun _ => (1 : ℂ))]
  · simp [Measure.real, haarVol_self isOpen_KO le_rfl]
  · intro g hg
    simp only [hφ g hg, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), one_mul]
end GlobalTheory.SplitFlip
