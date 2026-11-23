-- Prove2me | solution 1 for GlobalTheory.RelExp.HolAt.congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:18.906139+00:00
-- url     : https://prove2.me/submissions/ca820682-7820-46d8-a183-81b2cc3b5453

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Theorems.Thm_GlobalTheory_RelExp_isHolTo_mono

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
theorem _root_.solution (h : HolAt a w₀) (e : a =ᶠ[𝓝 w₀] a') : HolAt a' w₀ := by
  obtain ⟨W, hW, hw, h⟩ := h
  obtain ⟨S, hS, hSo, hS0⟩ := eventually_nhds_iff.1 e
  have h' := isHolTo_mono h (hW.inter hSo) Set.inter_subset_left
  refine ⟨W ∩ S, hW.inter hSo, ⟨hw, hS0⟩, fun U f => ?_⟩
  have : {b ∈ W ∩ S | ⊤ ≤ a' b ⁻¹ᵁ U} = {b ∈ W ∩ S | ⊤ ≤ a b ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [hS b hb.2]
  rw [this]
  exact ⟨(h' U f).1, (h' U f).2.congr fun b hb => by rw [hS b hb.1.2]⟩
end GlobalTheory.RelExp.HolAt
