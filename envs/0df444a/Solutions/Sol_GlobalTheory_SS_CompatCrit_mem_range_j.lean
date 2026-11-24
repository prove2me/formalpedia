-- Prove2me | solution 1 for GlobalTheory.SS.CompatCrit.mem_range_j
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:28:33.566023+00:00
-- url     : https://prove2.me/submissions/d26f9bf2-bde1-438b-9f3d-f7e3631c3961

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfSections
import Theorems.Thm_GlobalTheory_SS_CompatCrit_isPullback_j

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.CompatCrit
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}
namespace GlobalTheory.SS.CompatCrit
theorem _root_.solution [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] (M : Model R A)
    (y : M.Y.left) (hy : y ∉ M.sp) : y ∈ Set.range M.j := by
  have h1 : (M.Y.hom y : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (algebraMap R K)) := by
    rw [PrimeSpectrum.localization_comap_range K (nonZeroDivisors R)]
    have hb : (M.Y.hom y : PrimeSpectrum R).asIdeal = ⊥ := by
      by_contra hb
      exact hy (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
        ((M.Y.hom y : PrimeSpectrum R).isPrime.isMaximal hb)))
    show Disjoint _ _
    rw [hb, Set.disjoint_left]
    intro a ha ha'
    exact nonZeroDivisors.ne_zero ha ha'
  obtain ⟨t, ht⟩ := h1
  obtain ⟨a, ha, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_j M) y t ht.symm
  exact ⟨a, ha⟩
end GlobalTheory.SS.CompatCrit
