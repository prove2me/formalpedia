-- Prove2me | solution 1 for GlobalTheory.ValGenExtend.isUnit_of_mem_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:56:32.401805+00:00
-- url     : https://prove2.me/submissions/999a75ba-a969-4a97-989b-45239401fde2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorExtendsFromGenericFibreValuationRing
import Theorems.Thm_GlobalTheory_UU_IsWt_inv


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
theorem _root_.solution {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}}
    (f : X ⟶ Sp O) {U : X.Opens} {a : O} {x : X} (hx : x ∈ X.basicOpen (GlobalTheory.AbLaw.cst f U a))
    (hf : f x = IsLocalRing.closedPoint O) : IsUnit a := by
  have h : X.basicOpen (GlobalTheory.AbLaw.cst f U a) =
      U ⊓ X.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) :=
    Scheme.basicOpen_res _ _ _
  have h1 : x ∈ X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) := (h.le hx).2
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at h1
  have h2 : a ∉ (f x).asIdeal := h1
  rw [hf] at h2
  exact not_not.1 h2
end GlobalTheory.ValGenExtend
