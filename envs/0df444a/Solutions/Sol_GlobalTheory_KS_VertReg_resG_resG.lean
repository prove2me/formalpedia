-- Prove2me | solution 1 for GlobalTheory.KS.VertReg.resG_resG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:32:58.669538+00:00
-- url     : https://prove2.me/submissions/e861c807-0e65-4e65-a7e1-64d399192868

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreCoordsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldAbelianVarietyAlgebraicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LocDerRegularCoeff

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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.VertReg
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {W₀ : X.Opens} {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
namespace GlobalTheory.KS.VertReg
theorem _root_.solution {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  show (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op).hom f = _
  rw [← Functor.map_comp]
  rfl
end GlobalTheory.KS.VertReg
