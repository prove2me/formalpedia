-- Prove2me | solution 1 for GlobalTheory.RelExp.HolAt.const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:10:14.723253+00:00
-- url     : https://prove2.me/submissions/764f3af2-9e13-415e-8d22-51bcd0bffaae

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
namespace GlobalTheory.RelExp
namespace HolAt
theorem _root_.solution (x : Sp ℂ ⟶ Z) (w₀ : E) : HolAt (fun _ => x) w₀ := by
  refine ⟨Set.univ, isOpen_univ, trivial, fun U f => ⟨?_, differentiableOn_const _⟩⟩
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U <;> simp [h]
end HolAt
end GlobalTheory.RelExp
