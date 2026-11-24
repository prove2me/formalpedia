-- Prove2me | solution 1 for GlobalTheory.riemannTheta_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:38:13.612126+00:00
-- url     : https://prove2.me/submissions/1042d1e1-cecc-48c0-8b37-26ecfdee6ebd

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_riemannThetaTerm_fromBlocks

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
namespace GlobalTheory
theorem _root_.solution {Ω₁ : Matrix ι ι ℂ} {Ω₂ : Matrix κ κ ℂ} (h₁ : IsSiegel Ω₁)
    (h₂ : IsSiegel Ω₂) (a₁ b₁ : ι → ℝ) (a₂ b₂ : κ → ℝ) (v₁ : ι → ℂ) (v₂ : κ → ℂ) :
    riemannTheta (Sum.elim a₁ a₂) (Sum.elim b₁ b₂) (fromBlocks Ω₁ 0 0 Ω₂) (Sum.elim v₁ v₂) =
      riemannTheta a₁ b₁ Ω₁ v₁ * riemannTheta a₂ b₂ Ω₂ v₂ := by
  rw [riemannTheta_def, riemannTheta_def, riemannTheta_def, tsum_mul_tsum_of_summable_norm
    (h₁.summable_norm_riemannThetaTerm a₁ b₁ v₁) (h₂.summable_norm_riemannThetaTerm a₂ b₂ v₂),
    ← (Equiv.sumArrowEquivProdArrow ι κ ℤ).symm.tsum_eq]
  exact tsum_congr fun n => riemannThetaTerm_fromBlocks ..
end GlobalTheory
