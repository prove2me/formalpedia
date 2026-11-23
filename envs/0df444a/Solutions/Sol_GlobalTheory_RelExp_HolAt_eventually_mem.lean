-- Prove2me | solution 1 for GlobalTheory.RelExp.HolAt.eventually_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:14.194045+00:00
-- url     : https://prove2.me/submissions/c20467e8-7cfa-49bc-8b7e-ce059464c46c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt

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
theorem _root_.solution (h : HolAt a w₀) {U : Z.Opens} (hU : ⊤ ≤ a w₀ ⁻¹ᵁ U) : ∀ᶠ w in 𝓝 w₀, ⊤ ≤ a w ⁻¹ᵁ U := by
  obtain ⟨W, -, hw, h⟩ := h
  filter_upwards [(h U 0).1.mem_nhds ⟨hw, hU⟩] with w hw using hw.2
end GlobalTheory.RelExp.HolAt
