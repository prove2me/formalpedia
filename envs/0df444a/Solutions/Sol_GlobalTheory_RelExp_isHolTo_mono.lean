-- Prove2me | solution 1 for GlobalTheory.RelExp.isHolTo_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:29.045839+00:00
-- url     : https://prove2.me/submissions/e022b94b-c1e9-4a16-9c2b-f284aa5b3f56

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
theorem _root_.solution {a : E → (Sp ℂ ⟶ Z)} {W W' : Set E} (h : IsHolTo W a) (hW' : IsOpen W') (hs : W' ⊆ W) :
    IsHolTo W' a := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, h2.mono fun w hw => ⟨hs hw.1, hw.2⟩⟩
  convert hW'.inter h1 using 1
  ext w
  exact ⟨fun hw => ⟨hw.1, hs hw.1, hw.2⟩, fun hw => ⟨hw.1, hw.2.2⟩⟩
end GlobalTheory.RelExp
