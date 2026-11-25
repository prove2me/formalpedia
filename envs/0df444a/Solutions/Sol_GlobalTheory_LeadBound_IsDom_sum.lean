-- Prove2me | solution 1 for GlobalTheory.LeadBound.IsDom.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:23.851428+00:00
-- url     : https://prove2.me/submissions/18c175d3-ebb1-4c10-aa6d-0948f63f9e69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MulProd
import Theorems.Thm_GlobalTheory_LeadBound_IsDom_zero
import Theorems.Thm_GlobalTheory_LeadBound_IsDom_add

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
theorem _root_.solution {ι : Type*} (S : Finset ι) {la : Wt X.Ψ r} {n : ℕ} {P : ι → Frame X.Ψ r → ℂ}
    (hP : ∀ i ∈ S, IsDom X g la n (P i)) : IsDom X g la n (∑ i ∈ S, P i) :=
  Finset.sum_induction P (IsDom X g la n) (fun _ _ ha hb => ha.add hb) (IsDom.zero la n) hP
end IsDom
end GlobalTheory.LeadBound
