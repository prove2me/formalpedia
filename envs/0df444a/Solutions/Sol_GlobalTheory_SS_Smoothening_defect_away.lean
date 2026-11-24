-- Prove2me | solution 1 for GlobalTheory.SS.Smoothening.defect_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:24:39.296339+00:00
-- url     : https://prove2.me/submissions/2e2e1bce-87a0-4f16-ae98-284c48400605

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterizationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Smoothening
variable {R K B C D : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  [CommRing D] [Algebra R D]
namespace GlobalTheory.SS.Smoothening
theorem _root_.solution (f : B) (a : Localization.Away f →ₐ[R] D) (π : R) (c : ℕ)
    (h : Defect (a.comp (IsScalarTower.toAlgHom R B (Localization.Away f))) π c) : Defect a π c := by
  letI := a.toRingHom.toAlgebra
  letI := (a.comp (IsScalarTower.toAlgHom R B (Localization.Away f))).toRingHom.toAlgebra
  haveI : IsScalarTower B (Localization.Away f) D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro w hw
  let e := kaehlerAway R f D
  apply e.injective
  rw [map_smul, map_zero]
  apply h
  obtain ⟨r, hr⟩ := hw
  refine ⟨r, ?_⟩
  rw [Submonoid.smul_def] at hr ⊢
  rw [← map_smul, hr, map_zero]
end GlobalTheory.SS.Smoothening
