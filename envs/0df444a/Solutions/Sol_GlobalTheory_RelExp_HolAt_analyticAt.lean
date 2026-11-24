-- Prove2me | solution 1 for GlobalTheory.RelExp.HolAt.analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:27:40.346968+00:00
-- url     : https://prove2.me/submissions/2a5a49fa-1708-42e4-89de-56fe0896e49f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Theorems.Thm_GlobalTheory_SCV_analyticAt_of_differentiableOn


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
theorem _root_.solution [FiniteDimensional ℂ E] (h : HolAt a w₀) {U : Z.Opens} (hU : ⊤ ≤ a w₀ ⁻¹ᵁ U) (f : Γ(Z, U)) :
    AnalyticAt ℂ (fun w => valAt' (a w) U f) w₀ := by
  obtain ⟨W, -, hw, h⟩ := h
  exact SCV.analyticAt_of_differentiableOn (h U f).2 ((h U f).1.mem_nhds ⟨hw, hU⟩)
end GlobalTheory.RelExp.HolAt
