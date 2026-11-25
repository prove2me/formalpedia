-- Prove2me | solution 1 for GlobalTheory.CoverGlue.lift_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:56:53.842257+00:00
-- url     : https://prove2.me/submissions/e99a7345-cce6-4f5d-96ba-7f4e5bcb1758

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Theorems.Thm_GlobalTheory_CoverGlue_hom_ext
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverGlue
variable {S : Scheme.{0}} {I : Type} {U : I → S.Opens}
namespace GlobalTheory.CoverGlue
theorem _root_.solution {S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {G : Over S'} {ψ : G.left ⟶ A.left}
    (h : IsPullback ψ G.hom A.hom f) {T : Over S'} {x y : T ⟶ G} (e : x.left ≫ ψ = y.left ≫ ψ) : x = y :=
  Over.OverMorphism.ext (h.hom_ext e ((Over.w x).trans (Over.w y).symm))
end GlobalTheory.CoverGlue
