-- Prove2me | solution 1 for GlobalTheory.LeadBound.IsDom.zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:40:38.158517+00:00
-- url     : https://prove2.me/submissions/85a76d51-ad18-41ec-bbb4-fdf006ac0e83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MulProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_bdd_zero


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
theorem _root_.solution (la : Wt X.Ψ r) (n : ℕ) : IsDom X g la n 0 :=
  ⟨bdd_zero X la, 0, fun x _ => by simp [Data.pnorm]⟩
end IsDom
end GlobalTheory.LeadBound
