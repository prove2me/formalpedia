-- Prove2me | solution 1 for GlobalTheory.integral_theta_mul_eC_of_mem_siegelH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:39:13.90726+00:00
-- url     : https://prove2.me/submissions/fbbdeda2-c639-45b0-967e-d97c128dd9fd

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
open ReciprocityTheory.PTheta
namespace GlobalTheory
theorem _root_.solution {τ : Matrix ι ι ℂ} (h : τ ∈ SiegelH ι)
    (a b : ι → ℝ) (z : ι → ℂ) (l : ι → ℤ) :
    ∫ x in Set.Icc (0 : ι → ℝ) 1, theta a b (z + ofRealVec x) τ *
        eC (-(shiftVec a l ⬝ᵥ ofRealVec x)) = thetaTerm a b z τ l := by
  have := IsSiegel.integral_riemannTheta_mul_cexp h a b z l
  simp only [neg_mul] at this
  simp only [eC, mul_neg]
  exact this
end GlobalTheory
