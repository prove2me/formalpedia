-- Prove2me | solution 1 for GlobalTheory.LeadBound.IsDom.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:51:11.770823+00:00
-- url     : https://prove2.me/submissions/92e359d7-52d9-49a3-9116-03c8b833266e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MulProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_bdd_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_pnorm_eq


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
theorem _root_.solution {la : Wt X.Ψ r} {n : ℕ} {P : Frame X.Ψ r → ℂ} (a : ℂ) (hP : IsDom X g la n P) :
    IsDom X g la n (a • P) := by
  obtain ⟨C, hC⟩ := hP.2
  refine ⟨bdd_smul X a hP.1, ‖a‖ * C, fun x hx => ?_⟩
  calc X.pnorm la (a • P) x = ‖a‖ * X.pnorm la P x := by
        rw [pnorm_eq, pnorm_eq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    _ ≤ ‖a‖ * (C * g x ^ n) := mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg a)
    _ = ‖a‖ * C * g x ^ n := by ring
end IsDom
end GlobalTheory.LeadBound
