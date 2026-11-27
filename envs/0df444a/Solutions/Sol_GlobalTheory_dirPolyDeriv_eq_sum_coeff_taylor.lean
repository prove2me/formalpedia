-- Prove2me | solution 1 for GlobalTheory.dirPolyDeriv_eq_sum_coeff_taylor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:38:16.988732+00:00
-- url     : https://prove2.me/submissions/33b3c8e6-8581-4289-ab34-00b2d50c80ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Theorems.Thm_GlobalTheory_dirPolyDeriv_eq_sum_coeff_taylorDir

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {f g : (σ → ℂ) → ℂ}
namespace GlobalTheory
theorem _root_.solution (P : MvPolynomial σ ℂ) (f : (σ → ℂ) → ℂ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun i => (Pi.single i 1 : σ → ℂ)) f 0 = ∑ m ∈ P.support,
      P.coeff m * ((∏ i, (m i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff m (taylor f) :=
  dirPolyDeriv_eq_sum_coeff_taylorDir _ P f
end GlobalTheory
