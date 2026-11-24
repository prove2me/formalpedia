-- Prove2me | solution 1 for GlobalTheory.riemannThetaTerm_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:32:45.685827+00:00
-- url     : https://prove2.me/submissions/5cd00e41-c61b-418a-89c2-26e1efed5b41

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe

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
theorem _root_.solution (a₁ b₁ : ι → ℝ) (a₂ b₂ : κ → ℝ) (Ω₁ : Matrix ι ι ℂ)
    (Ω₂ : Matrix κ κ ℂ) (v₁ : ι → ℂ) (v₂ : κ → ℂ) (n₁ : ι → ℤ) (n₂ : κ → ℤ) :
    riemannThetaTerm (Sum.elim a₁ a₂) (Sum.elim b₁ b₂) (fromBlocks Ω₁ 0 0 Ω₂) (Sum.elim v₁ v₂)
        (Sum.elim n₁ n₂) =
      riemannThetaTerm a₁ b₁ Ω₁ v₁ n₁ * riemannThetaTerm a₂ b₂ Ω₂ v₂ n₂ := by
  simp only [riemannThetaTerm_eq_sum, ← Complex.exp_add, Fintype.sum_sum_type]
  congr 1
  simp
  ring
end GlobalTheory
