-- Prove2me | solution 1 for GlobalTheory.riemannTheta_add_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:32:46.243579+00:00
-- url     : https://prove2.me/submissions/758eb50b-ce15-4514-b0c2-beaf06cde94d

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
    (v : ι → ℂ) (m k : ι → ℤ) :
    riemannTheta a b Ω (v + ((fun i => (m i : ℂ)) + Ω *ᵥ fun i => (k i : ℂ))) =
      cexp (2 * π * I * (((fun i => (a i : ℂ)) ⬝ᵥ fun i => (m i : ℂ)) -
        ((fun i => (b i : ℂ)) ⬝ᵥ fun i => (k i : ℂ)) -
        ((fun i => (k i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (k i : ℂ))) / 2 - (fun i => (k i : ℂ)) ⬝ᵥ v)) *
        riemannTheta a b Ω v := by
  have : (fun i => v i + (b i : ℂ)) = v + fun i => (b i : ℂ) := rfl
  rw [add_comm (fun i => (m i : ℂ)), ← add_assoc, riemannTheta_add_intCast,
    riemannTheta_add_mulVec_intCast h, ← mul_assoc, ← Complex.exp_add, this, dotProduct_add,
    dotProduct_comm (fun i => (k i : ℂ)) fun i => (b i : ℂ)]
  congr 2
  ring
end GlobalTheory
