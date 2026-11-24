-- Prove2me | solution 1 for GlobalTheory.SS.GenProj.exists_lift_j
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:16:47.788838+00:00
-- url     : https://prove2.me/submissions/68b4c9ab-8fce-41ab-a00e-81536ace8b11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GenericIsomorphismProductModels

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GenProj
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.GenProj
theorem _root_.solution (M : Model R A) {Z : Scheme.{0}} (a : Z ⟶ M.Y.left) (t : Z ⟶ Sp K)
    (h : a ≫ M.Y.hom = t ≫ spMap (algebraMap R K)) : ∃ d : Z ⟶ A.left, d ≫ M.j = a := by
  refine ⟨pullback.lift a t h ≫ M.e.hom.left, ?_⟩
  have e : M.e.hom.left ≫ M.e.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  unfold Model.j
  rw [Category.assoc, ← Category.assoc M.e.hom.left, e]
  exact (congrArg _ (Category.id_comp _)).trans (pullback.lift_fst _ _ _)
end GlobalTheory.SS.GenProj
