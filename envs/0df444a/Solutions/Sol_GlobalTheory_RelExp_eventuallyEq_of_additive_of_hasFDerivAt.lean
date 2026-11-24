-- Prove2me | solution 1 for GlobalTheory.RelExp.eventuallyEq_of_additive_of_hasFDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:55:18.259208+00:00
-- url     : https://prove2.me/submissions/876c3433-0bf2-4fc6-9577-1089f67b233c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Theorems.Thm_GlobalTheory_exists_addMonoidHom_eventuallyEq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.RelExp
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {Z Y : Scheme.{0}}
namespace GlobalTheory.RelExp
theorem _root_.solution {ζ : E → E'} {T : E →L[ℂ] E'} (hT : HasFDerivAt ζ T 0)
    (hζ : ∀ᶠ p in 𝓝 (0 : E × E), ζ (p.1 + p.2) = ζ p.1 + ζ p.2) : ζ =ᶠ[𝓝 0] T := by
  obtain ⟨l, hl⟩ := exists_addMonoidHom_eventuallyEq (V := E) hζ
  have h1 : HasFDerivAt l T 0 := hT.congr_of_eventuallyEq hl
  have hc : Continuous l := continuous_of_continuousAt_zero l h1.continuousAt
  have h2 : (l.toRealLinearMap hc) = T.restrictScalars ℝ :=
    (l.toRealLinearMap hc).hasFDerivAt.unique (h1.restrictScalars ℝ)
  filter_upwards [hl] with v hv
  rw [← hv]
  exact DFunLike.congr_fun h2 v
end GlobalTheory.RelExp
