-- Prove2me | solution 1 for GlobalTheory.TorusConst.val_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:34:01.489909+00:00
-- url     : https://prove2.me/submissions/5c166f8c-310b-4a7b-8316-7b75a3bd8ca1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Theorems.Thm_GlobalTheory_TorusConst_spm_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}
namespace GlobalTheory.TorusConst
theorem _root_.solution {R S A : Type} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [CommRing A]
    [Algebra K A] (F : sp K R[X] ⟶ B) (c : R →ₐ[K] S[X]) (x : S[X]) (d : S →ₐ[K] A) (y : A) :
    val (val F c x) d y = val F ((aevalTower d y).comp c) (aevalTower d y x) :=
  spm_val F _ c x
end GlobalTheory.TorusConst
