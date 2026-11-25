-- Prove2me | solution 1 for GlobalTheory.HomExt.exists_iso_pullback_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:59.531744+00:00
-- url     : https://prove2.me/submissions/07eb8185-911c-4909-a3ff-9f705cf208b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CompPowEqOneOfPullbackHom
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_torusCoord_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.HomExt
namespace GlobalTheory.HomExt
theorem _root_.solution {X T Z : Scheme.{0}} (p : Z ⟶ T) (f : T ⟶ X) (r : Z ⟶ X)
    (h : p ≫ f = r) (G : Over X) [GrpObj G] :
    ∃ e : (Over.pullback r).obj G ≅ (Over.pullback p).obj ((Over.pullback f).obj G),
      IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst (pullback.snd G.hom f) p ≫ pullback.fst G.hom f =
        pullback.fst G.hom r := by
  subst h
  refine ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.pullCompIso p f G, inferInstance, ?_⟩
  have key := congrArg (fun x => Over.Hom.left x)
    (conjugateEquiv_counit (Over.mapPullbackAdj (p ≫ f))
      ((Over.mapPullbackAdj p).comp (Over.mapPullbackAdj f)) (Over.mapComp p f).symm.hom G)
  have e : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pullCompIso p f G).hom.left =
      ((conjugateEquiv (Over.mapPullbackAdj (p ≫ f))
        ((Over.mapPullbackAdj p).comp (Over.mapPullbackAdj f)) (Over.mapComp p f).symm.hom).app
          G).left := rfl
  rw [e]
  simpa [Adjunction.comp_counit_app] using key
end GlobalTheory.HomExt
