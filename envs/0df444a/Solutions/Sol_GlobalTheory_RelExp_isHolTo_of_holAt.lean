-- Prove2me | solution 1 for GlobalTheory.RelExp.isHolTo_of_holAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:57:43.123891+00:00
-- url     : https://prove2.me/submissions/36d9bf28-2958-4e53-aa55-66ee334fb145

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Theorems.Thm_GlobalTheory_RelExp_HolAt_eventually_mem

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
theorem _root_.solution {a : E → (Sp ℂ ⟶ Z)} {W : Set E} (hW : IsOpen W) (h : ∀ w ∈ W, HolAt a w) :
    IsHolTo W a := by
  intro U f
  have key : ∀ w ∈ {b ∈ W | ⊤ ≤ a b ⁻¹ᵁ U}, {b ∈ W | ⊤ ≤ a b ⁻¹ᵁ U} ∈ 𝓝 w := fun w hw =>
    Filter.Eventually.and (hW.mem_nhds hw.1) ((h w hw.1).eventually_mem hw.2)
  refine ⟨isOpen_iff_mem_nhds.2 key, fun w hw => ?_⟩
  obtain ⟨W', -, hw', h'⟩ := h w hw.1
  exact ((h' U f).2.differentiableAt ((h' U f).1.mem_nhds ⟨hw', hw.2⟩)).differentiableWithinAt
end GlobalTheory.RelExp
