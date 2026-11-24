-- Prove2me | solution 1 for GlobalTheory.SS.StrictLaw.isDominant_j
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:23:16.326328+00:00
-- url     : https://prove2.me/submissions/ec741826-ed50-495d-b1b9-eca27b5e0a60

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
import Theorems.Thm_GlobalTheory_SS_StrictLaw_isPullback_j

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
theorem _root_.solution [IsDomain R] [IsFractionRing R K] (M : Model R A) : IsDominant M.j := by
  have := M.smooth
  have hd : DenseRange (spMap (algebraMap R K)) := by
    show DenseRange (PrimeSpectrum.comap (algebraMap R K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]
    exact bot_le
  refine ⟨(hd.preimage M.Y.hom.isOpenMap).mono ?_⟩
  rintro y ⟨s, hs⟩
  obtain ⟨a, ha, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_j M) y s hs.symm
  exact ⟨a, ha⟩
end GlobalTheory.SS.StrictLaw
