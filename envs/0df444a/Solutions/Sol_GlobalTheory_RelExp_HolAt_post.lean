-- Prove2me | solution 1 for GlobalTheory.RelExp.HolAt.post
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:57.689804+00:00
-- url     : https://prove2.me/submissions/2450c6b0-50cb-4334-9b60-0d8092fb0c69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Theorems.Thm_GlobalTheory_RelExp_HolAt_congr
import Theorems.Thm_P2M_GlobalTheory_valAt__comp_7a5ff8fa895a


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
theorem _root_.solution (h : HolAt a w₀) (q : Z ⟶ Y) : HolAt (fun w => a w ≫ q) w₀ := by
  obtain ⟨W, hW, hw, h⟩ := h
  refine ⟨W, hW, hw, fun U f => ?_⟩
  obtain ⟨h1, h2⟩ := h (q ⁻¹ᵁ U) ((q.app U).hom f)
  exact ⟨h1, h2.congr fun w _ => (valAt'_comp _ _ _ _).symm⟩
end GlobalTheory.RelExp.HolAt
