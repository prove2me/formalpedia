-- Prove2me | solution 1 for GlobalTheory.KS.DerMor.appLE_cH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:02.64987+00:00
-- url     : https://prove2.me/submissions/525ea305-4b08-4001-a2af-92609a6906f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomFromConstThickeningOfDerivation

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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.DerMor
namespace GlobalTheory.KS.DerMor
theorem _root_.solution {R : Type} [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp R) (f : Y ⟶ X) (U : X.Opens)
    (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V e).hom (cH p U a) = cH (f ≫ p) V a := by
  unfold cH
  have key := Scheme.Hom.appLE_comp_appLE f p ⊤ U V le_top e
  rw [← CommRingCat.comp_apply, Category.assoc]
  exact congrArg (fun φ => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ).hom a) key
end GlobalTheory.KS.DerMor
