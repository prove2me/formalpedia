-- Prove2me | solution 1 for GlobalTheory.SS.IrrSplit.restrictModel_j
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:18:02.322806+00:00
-- url     : https://prove2.me/submissions/eb3bcf38-d9c3-4763-a044-615b55dacc10

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibre

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
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.IrrSplit
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
namespace GlobalTheory.SS.IrrSplit
theorem _root_.solution (M : Model R A) (U : M.Y.left.Opens) [QuasiCompact U.ι]
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) :
    (restrictModel M U hU).j ≫ U.ι = M.j := by
  have h := (isPullback_lift M U hU).isoPullback_hom_fst
  show ((M.e.inv.left ≫ (isPullback_lift M U hU).isoPullback.hom) ≫
    pullback.fst (U.ι ≫ M.Y.hom) (spMap (algebraMap R K))) ≫ U.ι = _
  rw [Category.assoc, Category.assoc, reassoc_of% h, IsOpenImmersion.lift_fac]
  rfl
end GlobalTheory.SS.IrrSplit
