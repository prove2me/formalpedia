-- Prove2me | solution 1 for GlobalTheory.SS.OrdTwist.jac_cross
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:55:43.492772+00:00
-- url     : https://prove2.me/submissions/76b75580-10bf-4d61-95d6-4534eda52721

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AbelianVarietyAutomorphismShiftsJacobianOrder
import Theorems.Thm_GlobalTheory_SS_OrdTwist_det_cross
import Theorems.Thm_GlobalTheory_SS_OrdTwist_rs_jac
import Theorems.Thm_GlobalTheory_SS_OrdTwist_eq_of_locally
import Theorems.Thm_GlobalTheory_SS_OrdTwist_exists_std

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdTwist
variable {K : Type} [Field K] {A : Over (Sp K)} {I : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.SS.OrdTwist
theorem _root_.solution (hA : SmoothOfRelativeDimension (Fintype.card I) A.hom) (D D' : I → VF A)
    (U : A.left.Opens) (t u : I → Γ(A.left, U)) :
    jac D' U t * jac D U u = jac D' U u * jac D U t := by
  refine eq_of_locally _ _ fun x hx => ?_
  obtain ⟨V, e, hxV, hs⟩ := exists_std hA U x hx
  refine ⟨V, e, hxV, ?_⟩
  simp only [map_mul, rs_jac]
  letI := (cstK A V).toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card I) K Γ(A.left, V) := hs
  have := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (Fintype.card I) (R := K) (S := Γ(A.left, V))
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Module.finrank Γ(A.left, V) Ω[Γ(A.left, V)⁄K] = Fintype.card I := by
    rw [Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (Fintype.card I)]
    simp
  exact det_cross ((Module.finBasisOfFinrankEq _ _ this).reindex (Fintype.equivFin I).symm) (fun i => toDer (D i) V) (fun i => toDer (D' i) V) _ _
end GlobalTheory.SS.OrdTwist
