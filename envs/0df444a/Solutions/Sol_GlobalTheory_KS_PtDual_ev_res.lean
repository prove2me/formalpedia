-- Prove2me | solution 1 for GlobalTheory.KS.PtDual.ev_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:36.600061+00:00
-- url     : https://prove2.me/submissions/0b33fec4-ebdb-4de9-a562-9521d8a57323

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.PtDual
variable {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]
namespace GlobalTheory.KS.PtDual
theorem _root_.solution (v : Sp R ⟶ X) {W W' : X.Opens} (e : W' ≤ W) (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ v ⁻¹ᵁ W') (f : Γ(X, W)) :
    ev v W' h' (resG X e f) = ev v W h f := by
  have : X.presheaf.map (homOfLE e).op ≫ v.appLE W' ⊤ h' = v.appLE W ⊤ h := Scheme.Hom.map_appLE ..
  unfold ev
  rw [← this]
  rfl
end GlobalTheory.KS.PtDual
