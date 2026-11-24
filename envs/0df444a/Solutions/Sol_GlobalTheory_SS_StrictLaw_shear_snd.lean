-- Prove2me | solution 1 for GlobalTheory.SS.StrictLaw.shear_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:23:19.985417+00:00
-- url     : https://prove2.me/submissions/62d588f0-8527-4eca-bcd9-0dcb25da3999

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeronStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOnPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStrictModelOfBirational

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StrictLaw
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.StrictLaw
theorem _root_.solution [GrpObj A] [IsCommMonObj A] (b : Bool) :
    shear A b ≫ snd A A = coshear A b ≫ fst A A := by
  cases b
  · simp only [coshear, shear, Category.assoc, braiding_hom_fst, lift_snd, MonObj.comp_mul,
      braiding_hom_snd, tensorHom_fst, tensorHom_snd, Category.comp_id]
    rw [mul_comm]; rfl
  · simp only [coshear, shear, Category.assoc, braiding_hom_fst, lift_snd, MonObj.comp_mul,
      braiding_hom_snd]
    rw [mul_comm]
end GlobalTheory.SS.StrictLaw
