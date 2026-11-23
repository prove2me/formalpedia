-- Prove2me | solution 1 for GlobalTheory.KS.DerMorK.appLE_constFn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:22.792842+00:00
-- url     : https://prove2.me/submissions/3173a05b-9622-48f3-84ef-cbe4c8bac2f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomOfDerivation

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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.DerMorK
namespace GlobalTheory.KS.DerMorK
theorem _root_.solution {R : Type} [CommRing R] {Z X : Scheme.{0}} (f : Z ⟶ X) (p : X ⟶ Sp R)
    {U : X.Opens} {V : Z.Opens} (e : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V e).hom (constFn p U a) = constFn (f ≫ p) V a := by
  unfold constFn
  rw [← Scheme.Hom.appLE_comp_appLE f p ⊤ U V (fun _ _ => trivial) e]
  rfl
end GlobalTheory.KS.DerMorK
