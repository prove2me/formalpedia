-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobHaarR.haarForm_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:31.518534+00:00
-- url     : https://prove2.me/submissions/23f03a74-fb89-458d-ad2b-b1d5120f0af4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultiple
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_haarForm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_integral_mul_right_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobHaarR
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable [LocallyCompactSpace G]
namespace GlobalTheory.CompanionTheory.FrobHaarR
theorem _root_.solution (hU : IsUnimod G) (μ : Measure G) [μ.IsHaarMeasure] (g : G) (α : SB G) :
    haarForm μ (pullHomeo (Homeomorph.mulRight g) α) = haarForm μ α := by
  have hc : Continuous (α : G → ℂ) := α.2.1.continuous
  have hcs : HasCompactSupport (α : G → ℂ) := α.2.2
  have hre := integral_mul_right_real hU μ g (u := fun x => RCLike.re ((α : G → ℂ) x))
    (RCLike.continuous_re.comp hc) (hcs.comp_left (g := RCLike.re) (map_zero _))
  have him := integral_mul_right_real hU μ g (u := fun x => RCLike.im ((α : G → ℂ) x))
    (RCLike.continuous_im.comp hc) (hcs.comp_left (g := RCLike.im) (map_zero _))
  rw [haarForm_apply, haarForm_apply,
    ← integral_re_add_im (integrable_sb μ (pullHomeo (Homeomorph.mulRight g) α)),
    ← integral_re_add_im (integrable_sb μ α)]
  simp only [pullHomeo_apply, Homeomorph.coe_mulRight]
  rw [hre, him]
end GlobalTheory.CompanionTheory.FrobHaarR
