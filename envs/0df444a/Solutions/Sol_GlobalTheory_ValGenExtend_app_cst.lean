-- Prove2me | solution 1 for GlobalTheory.ValGenExtend.app_cst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:10:32.841211+00:00
-- url     : https://prove2.me/submissions/a2e6cc95-a068-403c-8025-e8508d63d996

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorExtendsFromGenericFibreValuationRing
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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.ValGenExtend
namespace GlobalTheory.ValGenExtend
theorem _root_.solution {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) {X Y : Scheme.{0}}
    {f : X ⟶ Sp O} {j : Y ⟶ X} {g : Y ⟶ Sp K} (h : j ≫ f = g ≫ spMap φ) (U : X.Opens) (a : O) :
    (j.app U).hom (GlobalTheory.AbLaw.cst f U a) = GlobalTheory.AbLaw.cst g (j ⁻¹ᵁ U) (φ a) := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ f.appTop ≫ j.appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop := by
    rw [← Scheme.Hom.comp_appTop, h, Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality_assoc]
  have h2 := congrArg (fun u => u.hom a) h1
  have h3 := congrArg (fun u => u.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)))
    (j.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  exact h3.trans (congrArg (rs Y le_top) h2)
end GlobalTheory.ValGenExtend
