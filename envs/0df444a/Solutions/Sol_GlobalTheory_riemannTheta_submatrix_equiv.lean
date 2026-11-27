-- Prove2me | solution 1 for GlobalTheory.riemannTheta_submatrix_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:19.574919+00:00
-- url     : https://prove2.me/submissions/159b0129-6dfe-4d2a-af85-df5afca8fc2c

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
theorem _root_.solution (e : κ ≃ ι) (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) :
    riemannTheta (a ∘ e) (b ∘ e) (Ω.submatrix e e) (v ∘ e) = riemannTheta a b Ω v := by
  rw [riemannTheta_def, riemannTheta_def, ← (Equiv.arrowCongr e (Equiv.refl ℤ)).symm.tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [riemannThetaTerm_eq_sum, ← e.sum_comp]
  simp
end GlobalTheory
