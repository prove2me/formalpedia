-- Prove2me | solution 1 for GlobalTheory.LeadBound.IsDom.of_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:19.414476+00:00
-- url     : https://prove2.me/submissions/73bc6990-c07d-4246-bb30-af1a6cfc7480

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MulProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LeadBound
open ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r) (g : Frame X.Ψ r → ℝ)
variable {X g}
namespace GlobalTheory.LeadBound
namespace IsDom
theorem _root_.solution {W : Frame X.Ψ r → ℝ} {la : Wt X.Ψ r}
    {P : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) {K : ℝ} (hW : ∀ x, 0 ≤ W x)
    (hK : ∀ x ∈ X.dom, X.pnorm la P x ^ 2 ≤ K * W x) :
    IsDom X (fun x => Real.sqrt (W x)) la 1 P := by
  refine ⟨hP, Real.sqrt K, fun x hx => ?_⟩
  rw [pow_one, ← Real.sqrt_mul' _ (hW x)]
  exact Real.le_sqrt_of_sq_le (hK x hx)
end IsDom
end GlobalTheory.LeadBound
