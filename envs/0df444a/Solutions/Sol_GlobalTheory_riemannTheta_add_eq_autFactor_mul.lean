-- Prove2me | solution 1 for GlobalTheory.riemannTheta_add_eq_autFactor_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:16.215862+00:00
-- url     : https://prove2.me/submissions/fa154ef5-457d-45cb-93b0-8eb1bd515706

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_riemannTheta_add_lattice

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
theorem _root_.solution {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) (a b : ι → ℝ)
    (v : ι → ℂ) (k m : ι → ℤ) :
    riemannTheta a b Ω (v + Ω *ᵥ ofIntVec k + ofIntVec m) =
      autFactor a b Ω k m v * riemannTheta a b Ω v := by
  rw [add_assoc, add_comm (Ω *ᵥ _), autFactor, eC, eC, ← Complex.exp_add]
  refine (riemannTheta_add_lattice h a b v m k).trans ?_
  congr 2
  unfold ofRealVec ofIntVec
  ring
end GlobalTheory
