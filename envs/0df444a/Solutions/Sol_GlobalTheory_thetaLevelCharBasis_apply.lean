-- Prove2me | solution 1 for GlobalTheory.thetaLevelCharBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:43:14.371962+00:00
-- url     : https://prove2.me/submissions/6f064707-c56a-4578-9523-b9dd4777007f

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open GlobalTheory
variable {ι : Type} [Fintype ι]
variable {N M : ℕ} {τ : Matrix ι ι ℂ} {a b : ι → ℝ} {f g : (ι → ℂ) → ℂ}
namespace GlobalTheory
theorem _root_.solution (hτ : τ ∈ SiegelH ι) (hN : 0 < N) {κ : Type*}
    {r : κ → ι → ℤ} (hr : Function.Bijective fun k i => (r k i : ZMod N)) (k : κ) :
    (thetaLevelCharBasis a b hτ hN hr k : (ι → ℂ) → ℂ) = levelTheta a b N τ (r k) := by
  simp [thetaLevelCharBasis]
end GlobalTheory
