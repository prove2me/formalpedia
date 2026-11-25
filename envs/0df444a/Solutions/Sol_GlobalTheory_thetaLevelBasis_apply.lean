-- Prove2me | solution 1 for GlobalTheory.thetaLevelBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:53:34.180312+00:00
-- url     : https://prove2.me/submissions/66afa7d1-a40a-4b78-b18b-e68ed73d25d1

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply

set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open GlobalTheory
variable {ι : Type} [Fintype ι]
variable {N M : ℕ} {τ : Matrix ι ι ℂ} {a b : ι → ℝ} {f g : (ι → ℂ) → ℂ}
namespace GlobalTheory
theorem _root_.solution (hτ : τ ∈ SiegelH ι) (hN : 0 < N) {κ : Type*}
    {r : κ → ι → ℤ} (hr : Function.Bijective fun k i => (r k i : ZMod N)) (k : κ) :
    (thetaLevelBasis hτ hN hr k : (ι → ℂ) → ℂ) =
      fun z => theta (fun i => (r k i : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) := by
  funext z
  simp [thetaLevelBasis, levelTheta_zero_zero]
end GlobalTheory
