-- Prove2me | solution 1 for GlobalTheory.ValGenExtend.exists_isGen_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:58:37.900076+00:00
-- url     : https://prove2.me/submissions/e4ca417c-c603-4e92-afbb-2aafbb9eeda7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorExtendsFromGenericFibreValuationRing
import Theorems.Thm_GlobalTheory_ValGenExtend_isGen_inv_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.ValGenExtend
namespace GlobalTheory.ValGenExtend
theorem _root_.solution {X Y : Scheme.{0}} {I : Type} {U : I → X.Opens}
    (g g' : ∀ a b, Γ(X, U a ⊓ U b)ˣ) (hg : ∀ a b, g' a b = (g a b)⁻¹) (j : Y ⟶ X)
    (t : LB.Gen ((⟨I, U, g⟩ : LB X).pull j)) (ht : t.IsGen) :
    ∃ t' : LB.Gen ((⟨I, U, g'⟩ : LB X).pull j), t'.IsGen ∧ ∀ i : I,
      rs Y (le_pull ⟨I, U, g⟩ j (W := U i) (i := i) le_rfl) (t.s fun _ => i).val *
        rs Y (le_pull ⟨I, U, g'⟩ j (W := U i) (i := i) le_rfl) (t'.s fun _ => i).val = 1 := by
  refine ⟨⟨fun i => (t.s i)⁻¹⟩,
    isGen_inv_of_eq t ht ((⟨I, U, g'⟩ : LB X).pull j).g fun a b => ?_, fun i => ?_⟩
  · dsimp only [LB.pull, LB.LinComb]
    simp only [hg, map_inv, zpow_one, Finset.prod_inv_distrib]
    try rfl
  · exact (map_mul _ _ _).symm.trans ((congrArg _ (Units.mul_inv _)).trans (map_one _))
end GlobalTheory.ValGenExtend
