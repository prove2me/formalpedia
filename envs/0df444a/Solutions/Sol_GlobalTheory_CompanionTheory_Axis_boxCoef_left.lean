-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.boxCoef_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:02.069854+00:00
-- url     : https://prove2.me/submissions/59f03999-a4e0-4f92-884e-b9f217c8b8e6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparison
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_boxCoef_tmul_one
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
open CategoryTheory.Limits
variable {R : Type} [CommRing R] {A : Over (Sp R)} {P : Type} [SemilatticeInf P]
namespace GlobalTheory.CompanionTheory.Axis
theorem _root_.solution (S : Sys A.left P) (x : HO1 A.hom) (c : HO1 (A ⊗ A).hom) (h : IsPullO (wOver (fst A A)) x c) :
    (resSys _ (boxSys S)).pull1 c = (boxCoef S).pull1 ((boxL _).pull1 ((resSys _ S).pull1 x)) := by
  have e := congrArg (kL S).pull1 h
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ x
  obtain ⟨g, rfl⟩ := H1.mk_surjective _ c
  refine Eq.trans ?_ (e.symm.trans ?_)
  · rfl
  · refine congrArg (H1.mk _) (Subtype.ext ?_)
    funext T T' φ
    exact (boxCoef_tmul_one S T' _).symm
end GlobalTheory.CompanionTheory.Axis
