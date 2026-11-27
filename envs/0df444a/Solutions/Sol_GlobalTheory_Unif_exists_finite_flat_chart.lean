-- Prove2me | solution 1 for GlobalTheory.Unif.exists_finite_flat_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:36:42.228106+00:00
-- url     : https://prove2.me/submissions/be098b16-a95c-4ac2-b6b3-dfadae407b9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FinFlatChartOfOpenImmersion
import Theorems.Thm_GlobalTheory_Unif_finFlatChart_of_openImmersion
import Theorems.Thm_GlobalTheory_Unif_exists_finFlat_away
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct
open GlobalTheory GlobalTheory.Unif
namespace GlobalTheory.Unif
theorem _root_.solution : ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f], ∃ (g : ℕ) (W : X.Opens) (V : (Spec (CommRingCat.of (MvPolynomial (Fin g) K))).Opens) (π : W.toScheme ⟶ V.toScheme), (W : Set X).Nonempty ∧ IsFinite π ∧ Flat π ∧ Surjective π ∧ π ≫ V.ι ≫ (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K)))) = W.ι ≫ f := by
  intro K _ X _ f _
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  replace hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  have hft : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  have hft' : ψ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft
  letI : Algebra K Γ(X, U) := ψ.hom.toAlgebra
  have : Algebra.FiniteType K Γ(X, U) := hft'
  obtain ⟨g, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K Γ(X, U)
  obtain ⟨Y, Z, j, i, p, _, _, _, _, _, _, h⟩ :=
    exists_finFlat_away _ _ φ.toRingHom hfin hinj
  refine ⟨g, finFlatChart_of_openImmersion f _ (j ≫ hU.fromSpec) i p ?_⟩
  rw [reassoc_of% h, Category.assoc, ← hψ, ← Spec.map_comp]
  congr 2
  ext x
  exact φ.commutes x
end GlobalTheory.Unif
