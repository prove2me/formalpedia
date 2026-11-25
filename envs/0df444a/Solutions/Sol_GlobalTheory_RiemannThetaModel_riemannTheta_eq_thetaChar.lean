-- Prove2me | solution 1 for GlobalTheory.RiemannThetaModel.riemannTheta_eq_thetaChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:06:24.818743+00:00
-- url     : https://prove2.me/submissions/7abd1f29-8dd3-4f1d-875e-9071a62f0105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.RiemannThetaModel
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.RiemannThetaModel
theorem _root_.solution {g : ℕ} (a b : Fin g → ℝ) (Ω : Matrix (Fin g) (Fin g) ℂ)
    (v : Fin g → ℂ) :
    riemannTheta a b Ω v = ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar Ω (fun i => a i) (fun i => b i) v := by
  change ∑' n, riemannThetaTerm a b Ω v n = _
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar
  refine tsum_congr fun n => ?_
  change cexp (2 * π * I * (((fun i => (n i : ℂ) + a i) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ) + a i)) / 2 +
    (fun i => (n i : ℂ) + a i) ⬝ᵥ fun i => v i + b i)) = _
  congr 1
  have e1 : ((fun i => (n i : ℂ)) + fun i => (a i : ℂ)) = fun i => (n i : ℂ) + a i := rfl
  have e2 : (v + fun i => (b i : ℂ)) = fun i => v i + b i := rfl
  rw [e1, e2]
  ring
end GlobalTheory.RiemannThetaModel
