-- Prove2me | solution 1 for GlobalTheory.coeff_taylor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:36:42.239277+00:00
-- url     : https://prove2.me/submissions/7873c3ab-597d-4451-adeb-8050d3d59826

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt

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
theorem _root_.solution (f : (σ → ℂ) → ℂ) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m (taylor f) = ((∏ i, (m i).factorial : ℕ) : ℂ)⁻¹ *
      ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1)
        (fun i => (Pi.single i 1 : σ → ℂ)) f 0 := rfl
end GlobalTheory
