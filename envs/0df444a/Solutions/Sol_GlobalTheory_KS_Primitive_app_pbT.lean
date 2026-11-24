-- Prove2me | solution 1 for GlobalTheory.KS.Primitive.app_pbT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:42:20.660852+00:00
-- url     : https://prove2.me/submissions/905c6372-c1e2-490d-9881-a065e5da941a

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
theorem _root_.solution (r : T ⟶ Z) (f : Z ⟶ A) (g : T ⟶ A) (e : r ≫ f = g) {O₀ : A.Opens} (s : Γ(A, O₀))
    {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) : (r.app O).hom (pbT f s O) = pbT g s (r ⁻¹ᵁ O) := by
  subst e
  rw [pbT_eq f s h, pbT_eq (r ≫ f) s (r.preimage_mono h)]
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
end GlobalTheory.KS.Primitive
