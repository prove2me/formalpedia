-- Prove2me | solution 1 for GlobalTheory.ZM.NearBuild.good_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:01.238768+00:00
-- url     : https://prove2.me/submissions/2af5796e-2be2-46ca-abcf-601fabfa49d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Theorems.Thm_GlobalTheory_ZM_NearBuild_spMap_comp

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.NearBuild
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {R R' : Type} [CommRing R] [CommRing R']
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R)
variable {b Mat κ β v}
namespace GlobalTheory.ZM.NearBuild
theorem _root_.solution (ρ : R →+* R') {K : Type} [Field K] (x : R' →+* K) {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) :
    Good b Mat κ (ρ.comp β) (fun a => ρ (v a)) x t ↔ Good b Mat κ β v (x.comp ρ) t := by
  simp only [Good, spMap_comp, Category.assoc, RingHom.comp_apply]
end GlobalTheory.ZM.NearBuild
