-- Prove2me | solution 1 for GlobalTheory.LeadBound.IsDom.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:18.158999+00:00
-- url     : https://prove2.me/submissions/bc31bb9a-d402-46eb-aa21-274d4926e703

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MulProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_bdd_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_nfac_nonneg


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
theorem _root_.solution {la : Wt X.Ψ r} {n : ℕ} {P Q : Frame X.Ψ r → ℂ} (hP : IsDom X g la n P)
    (hQ : IsDom X g la n Q) : IsDom X g la n (P + Q) := by
  obtain ⟨C, hC⟩ := hP.2
  obtain ⟨C', hC'⟩ := hQ.2
  refine ⟨bdd_add X hP.1 hQ.1, C + C', fun x hx => ?_⟩
  calc X.pnorm la (P + Q) x ≤ (‖P x‖ + ‖Q x‖) * X.nfac la x :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) (nfac_nonneg X la x)
    _ = X.pnorm la P x + X.pnorm la Q x := by rw [add_mul]; rfl
    _ ≤ C * g x ^ n + C' * g x ^ n := add_le_add (hC x hx) (hC' x hx)
    _ = (C + C') * g x ^ n := by ring
end IsDom
end GlobalTheory.LeadBound
