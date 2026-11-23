-- Prove2me | solution 1 for GlobalTheory.KS.Primitive.rs_pbT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:37.105816+00:00
-- url     : https://prove2.me/submissions/14907cf7-20f4-45c9-a822-2306705c25b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenInfOfIsSeparated
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CechPrimitive
import Theorems.Thm_GlobalTheory_KS_Primitive_pbT_eq

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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Primitive
open GlobalTheory.KuennethOne
variable {T Z A : Scheme.{0}} {I : Type} {U : I → A.Opens} {c : C1 U}
namespace GlobalTheory.KS.Primitive
theorem _root_.solution (f : T ⟶ A) {O₀ : A.Opens} (s : Γ(A, O₀)) {O O' : T.Opens} (h : O ≤ f ⁻¹ᵁ O₀)
    (h' : O' ≤ O) : rs h' (pbT f s O) = pbT f s O' := by
  rw [pbT_eq f s h, pbT_eq f s (h'.trans h)]
  show (T.presheaf.map (homOfLE h').op).hom ((f.appLE O₀ O h).hom s) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
end GlobalTheory.KS.Primitive
