-- Prove2me | solution 1 for GlobalTheory.RedPts.eq_one_of_pow_of_closedPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:56:31.629693+00:00
-- url     : https://prove2.me/submissions/afedc19b-475c-4526-9736-3177e1d7fc6b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOneOfPowOfClosedPoint
import Theorems.Thm_GlobalTheory_RedPts_toSec_left_fst
import Theorems.Thm_GlobalTheory_RedPts_toSec_injective
import Theorems.Thm_GlobalTheory_GrpTangent_formallyUnramified_mulN
import Theorems.Thm_GlobalTheory_eq_of_isLocalRing_of_unramified
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.RedPts
variable {S : Scheme.{0}}
namespace GlobalTheory.RedPts
theorem _root_.solution (G : Over S) [GrpObj G] [IsCommMonObj G]
    [LocallyOfFiniteType G.hom] {R : Type} [CommRing R] [IsLocalRing R] (p : Sp R ⟶ S) {n : ℕ}
    (hn : IsUnit (n : R)) (x : Over.mk p ⟶ G) (hx : x ^ n = 1) {Z : Over S} (j : Z ⟶ Over.mk p)
    (hj : IsLocalRing.closedPoint R ∈ Set.range (show Z.left ⟶ Sp R from j.left)) (h : j ≫ x = 1) :
    x = 1 := by
  apply toSec_injective G p
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by simpa using hn.map (Scheme.ΓSpecIso (.of R)).inv.hom
  let G' := (Over.pullback p).obj G
  have : LocallyOfFiniteType G'.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom p))
  have := GlobalTheory.GrpTangent.formallyUnramified_mulN G' hn'
  have : LocallyOfFiniteType ((mulN G' n).left ≫ G'.hom) := by rw [Over.w]; infer_instance
  have := locallyOfFiniteType_of_comp (mulN G' n).left G'.hom
  refine Over.OverMorphism.ext (GlobalTheory.eq_of_isLocalRing_of_unramified (R := .of R) (mulN G' n).left
    (a := (toSec G p x).left) (b := (toSec G p 1).left) ?_ (show Z.left ⟶ Sp R from j.left) hj ?_)
  · have e : toSec G p x ≫ mulN G' n = toSec G p 1 ≫ mulN G' n := by
      rw [GlobalTheory.GrpTangent.comp_mulN, GlobalTheory.GrpTangent.comp_mulN, ← map_pow, ← map_pow, hx, one_pow]
    exact congrArg Over.Hom.left e
  · refine pullback.hom_ext ?_ ?_
    · have e : j ≫ x = j ≫ 1 := by rw [h, MonObj.comp_one]
      exact ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·) (toSec_left_fst G p x))).trans
        ((congrArg Over.Hom.left e).trans
          ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·) (toSec_left_fst G p 1))).symm)
    · exact ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·)
        ((Over.w (toSec G p x)).trans (Over.w (toSec G p 1)).symm))).trans (Category.assoc _ _ _).symm
end GlobalTheory.RedPts
