-- Prove2me | solution 1 for GlobalTheory.theta_fromBlocks_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:24.725374+00:00
-- url     : https://prove2.me/submissions/fa668a7c-edf8-4262-9e17-1c78847f2c45

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_riemannTheta_fromBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ]
open ReciprocityTheory.PTheta
namespace GlobalTheory
theorem _root_.solution {τ₁ : Matrix ι ι ℂ} {τ₂ : Matrix κ κ ℂ} (h₁ : τ₁ ∈ SiegelH ι)
    (h₂ : τ₂ ∈ SiegelH κ) (a₁ b₁ : ι → ℝ) (a₂ b₂ : κ → ℝ) (z₁ : ι → ℂ) (z₂ : κ → ℂ) :
    theta (Sum.elim a₁ a₂) (Sum.elim b₁ b₂) (Sum.elim z₁ z₂) (fromBlocks τ₁ 0 0 τ₂) =
      theta a₁ b₁ z₁ τ₁ * theta a₂ b₂ z₂ τ₂ :=
  riemannTheta_fromBlocks h₁ h₂ a₁ b₁ a₂ b₂ z₁ z₂
end GlobalTheory
