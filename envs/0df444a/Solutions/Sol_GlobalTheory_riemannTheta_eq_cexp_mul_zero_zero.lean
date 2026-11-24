-- Prove2me | solution 1 for GlobalTheory.riemannTheta_eq_cexp_mul_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:32:46.871654+00:00
-- url     : https://prove2.me/submissions/8b4c4672-4f64-4d6b-9c5a-07a207b2487d

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
theorem _root_.solution {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) (a b : ι → ℝ)
    (v : ι → ℂ) :
    riemannTheta a b Ω v =
      cexp (2 * π * I * (((fun i => (a i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (a i : ℂ))) / 2 +
        (fun i => (a i : ℂ)) ⬝ᵥ fun i => v i + b i)) *
        riemannTheta 0 0 Ω (v + (fun i => (b i : ℂ)) + Ω *ᵥ fun i => (a i : ℂ)) := by
  rw [riemannTheta_add_mulVec_ofReal h, riemannTheta_add_ofReal, ← mul_assoc, ← Complex.exp_add]
  simp
end GlobalTheory
