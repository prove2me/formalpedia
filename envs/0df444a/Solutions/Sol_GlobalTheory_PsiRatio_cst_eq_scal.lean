-- Prove2me | solution 1 for GlobalTheory.PsiRatio.cst_eq_scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:31:32.849102+00:00
-- url     : https://prove2.me/submissions/0714bb3e-3ddb-43a6-a97e-b7ff35b50818

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulPullSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_JKAppTopInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PsiScalarEqExpansionCoefRatio
import Theorems.Thm_GlobalTheory_PsiRatio_exists_cstHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
open GlobalTheory GlobalTheory.PsiRatio
namespace GlobalTheory.PsiRatio
theorem _root_.solution {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (c : F) :
    cst p z c = gs (𝟙 _) z ⊤ (scal p c) := by
  obtain ⟨φ, h₁, h₂⟩ := exists_cstHom p z
  rw [h₁, h₂]
end GlobalTheory.PsiRatio
