-- Prove2me | solution 1 for GlobalTheory.SS.StrictLaw.j_notMem_sp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:23:18.303875+00:00
-- url     : https://prove2.me/submissions/61ccfedc-51d2-4ee2-b53d-d08fe156756d

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
import Theorems.Thm_GlobalTheory_SS_Model_j_hom


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
theorem _root_.solution [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] (M : Model R A)
    (a : A.left) : M.j a ∉ M.sp := by
  intro h
  have h1 : M.Y.hom (M.j a) = spMap (algebraMap R K) (A.hom a) := by
    rw [← Scheme.Hom.comp_apply, M.j_hom, Scheme.Hom.comp_apply]
  have h2 : spMap (algebraMap R K) (A.hom a) = IsLocalRing.closedPoint R := h1.symm.trans h
  have h3 := congrArg PrimeSpectrum.asIdeal h2
  apply IsDiscreteValuationRing.not_a_field R
  refine h3.symm.trans ?_
  show Ideal.comap (algebraMap R K) (PrimeSpectrum.asIdeal (A.hom a)) = ⊥
  rw [@Ideal.eq_bot_of_prime K _ (PrimeSpectrum.asIdeal (R := K) (A.hom a))
    (PrimeSpectrum.isPrime (R := K) (A.hom a))]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)
end GlobalTheory.SS.StrictLaw
