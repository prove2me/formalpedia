-- Prove2me | solution 1 for GlobalTheory.VVRank.comp_linComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:04.261846+00:00
-- url     : https://prove2.me/submissions/a7eeaad6-e7ec-4395-8824-51beeb2a5eaf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
omit [GrpObj A]
namespace GlobalTheory.VVRank
theorem _root_.solution {A : Over S} [GrpObj A] {T T' : Over S} (h : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (a : Fin n → ℕ) : h ≫ linComb y a = linComb (fun i => h ≫ y i) a := by
  let F : (T ⟶ A) →* (T' ⟶ A) := MonoidHom.mk' (h ≫ ·) fun x y => MonObj.comp_mul h x y
  refine (map_list_prod F _).trans (congrArg List.prod ?_)
  rw [List.map_ofFn]
  exact congrArg List.ofFn (funext fun i => map_pow F _ _)
end GlobalTheory.VVRank
