-- Prove2me | solution 1 for GlobalTheory.SS.exists_places_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:19.547533+00:00
-- url     : https://prove2.me/submissions/62eea608-344a-4e0f-abcf-17fde2643c1c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesOfFgField
import Theorems.Thm_GlobalTheory_SS_isAlgebraic_of_forall_erase
import Theorems.Thm_GlobalTheory_SS_transcendental_erase
import Theorems.Thm_GlobalTheory_T_exists_productFormulaPlaces_function_field


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
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution (k : Type) [Field k] [IsAlgClosed k] (K : Type) [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) :
    ∃ Pl : Places k K, ∀ x : K, (∀ i, x ∈ Pl.O i) → x ∈ Set.range (algebraMap k K) := by
  have : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have : Algebra.EssFiniteType (IntermediateField.adjoin k (s : Set K)) K :=
    Algebra.EssFiniteType.of_comp k _ K
  have hfin : FiniteDimensional (IntermediateField.adjoin k (s : Set K)) K :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  have H : ∀ t : (s : Set K), ∃ Pl : Places (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) K,
      ∀ x : K, (∀ i, x ∈ Pl.O i) →
        IsAlgebraic (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) x := by
    intro t
    have e : IntermediateField.adjoin k (s : Set K) = (IntermediateField.adjoin
        (IntermediateField.adjoin k ((s : Set K) \ {(t : K)})) {(t : K)}).restrictScalars k := by
      rw [IntermediateField.adjoin_adjoin_left, Set.diff_union_of_subset (by simpa using t.2)]
    rw [e] at hsep hfin
    exact GlobalTheory.T.exists_productFormulaPlaces_function_field _ K t (transcendental_erase hs t) hfin hsep
  choose P hP using H
  refine ⟨Places.sigma _ P, fun x hx => ?_⟩
  have hx' : IsAlgebraic k x := isAlgebraic_of_forall_erase hs fun t => hP t x fun i => hx ⟨t, i⟩
  exact minpoly.mem_range_of_degree_eq_one k x
    (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hx'.isIntegral))
end GlobalTheory.SS
