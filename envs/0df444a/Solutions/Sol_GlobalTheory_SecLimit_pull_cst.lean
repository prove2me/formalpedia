-- Prove2me | solution 1 for GlobalTheory.SecLimit.pull_cst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:12:38.246939+00:00
-- url     : https://prove2.me/submissions/ef0a5e9d-fec1-4499-acd2-02975d6a52ac

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueLimit
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.SecLimit
variable {X Y Y' Y'' : Scheme.{0}} (L : LB X) {K K' K₃ : Type} [Fintype K] [Fintype K'] [Fintype K₃]
variable {L}
namespace GlobalTheory.SecLimit
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') {π : Y' ⟶ Y}
    {f : Y ⟶ Spec (CommRingCat.of R)} {f' : Y' ⟶ Spec (CommRingCat.of R')}
    (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) (a : R) : pull L π (cst L f a) = cst L f' (g a) := by
  have e₁ := congrArg (fun Q => Q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  have e₂ := congrArg (fun q => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) w
  funext Z r z J
  exact (gs_pull r π z ⊤ trivial _).symm.trans (congrArg (gs r z ⊤) ((congrArg f'.appTop.hom e₁).trans e₂.symm).symm)
end GlobalTheory.SecLimit
