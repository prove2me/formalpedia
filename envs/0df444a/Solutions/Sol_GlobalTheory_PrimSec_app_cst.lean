-- Prove2me | solution 1 for GlobalTheory.PrimSec.app_cst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:29:52.702177+00:00
-- url     : https://prove2.me/submissions/28a557c9-e37e-47d0-b49f-3307a16cb38f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre
import Theorems.Thm_GlobalTheory_PrimSec_app_rs
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
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
noncomputable section
open GlobalTheory GlobalTheory.PrimSec
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
namespace GlobalTheory.PrimSec
theorem _root_.solution {g : R →+* R'} {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (H : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g))
    (U : X.Opens) (r : R) : (π.app U).hom (AbLaw.cst f U r) = AbLaw.cst f' (π ⁻¹ᵁ U) (g r) := by
  have e₁ := congrArg (fun φ => φ.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) H
  have e₂ := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e₁ e₂
  refine (app_rs π le_top _).trans ?_
  change rs X' le_top (π.appTop.hom _) = rs X' le_top (f'.appTop.hom _)
  rw [e₂, ← e₁]
  rfl
end GlobalTheory.PrimSec
