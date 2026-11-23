-- Prove2me | solution 1 for GlobalTheory.RelExp.HolAt.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:17.279916+00:00
-- url     : https://prove2.me/submissions/06062b7e-c72a-4aa4-be3e-0f8ae98354f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Theorems.Thm_GlobalTheory_RelExp_HolAt_eventually

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
open GlobalTheory.RelExp.HolAt
variable {a a' : E → (Sp ℂ ⟶ Z)} {w₀ : E}
namespace GlobalTheory.RelExp.HolAt
theorem _root_.solution [CompleteSpace E] {φ : E' → E} {v₀ : E'} (h : HolAt a (φ v₀)) (hφ : AnalyticAt ℂ φ v₀) :
    HolAt (fun v => a (φ v)) v₀ := by
  obtain ⟨W, hW, hw, h⟩ := h
  obtain ⟨S, hS, hSo, hS0⟩ := eventually_nhds_iff.1
    (hφ.eventually_analyticAt.and (hφ.continuousAt.eventually (hW.mem_nhds hw)))
  have hd : DifferentiableOn ℂ φ S := fun v hv => (hS v hv).1.differentiableAt.differentiableWithinAt
  refine ⟨S, hSo, hS0, fun U f => ?_⟩
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, h2.comp (hd.mono fun w hw => hw.1) fun w hw => ⟨(hS w hw.1).2, hw.2⟩⟩
  convert hd.continuousOn.isOpen_inter_preimage hSo h1 using 1
  ext w
  exact ⟨fun hw => ⟨hw.1, (hS w hw.1).2, hw.2⟩, fun hw => ⟨hw.1, hw.2.2⟩⟩
end GlobalTheory.RelExp.HolAt
