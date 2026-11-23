-- Prove2me | solution 1 for GlobalTheory.CoverGlue.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:48.00253+00:00
-- url     : https://prove2.me/submissions/764dab2a-dafc-4524-a0c3-b513b2b48150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
    (h : IsPullback ψ G.hom A.hom f) {T : Over S'} (x₀ : Over.mk (T.hom ≫ f) ⟶ A) :
    ∃ x : T ⟶ G, x₀.left = x.left ≫ ψ :=
  ⟨Over.homMk (h.lift x₀.left T.hom (Over.w x₀)) (h.lift_snd _ _ _), (h.lift_fst _ _ _).symm⟩
end GlobalTheory.CoverGlue
