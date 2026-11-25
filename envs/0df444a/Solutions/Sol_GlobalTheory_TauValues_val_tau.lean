-- Prove2me | solution 1 for GlobalTheory.TauValues.val_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:56:12.49684+00:00
-- url     : https://prove2.me/submissions/8984c6e1-1825-422b-8d9a-a619d8e01ef1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CorrOfValFieldExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultPsiEvenOverExtensionField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.TauValues
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.TauValues
theorem _root_.solution {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) (a b : D.X) :
    val (D.tau a b) r z J =
      val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ * (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
end GlobalTheory.TauValues
