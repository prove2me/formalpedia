-- Prove2me | solution 1 for GlobalTheory.SS.isAlgebraic_of_forall_erase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:27.764907+00:00
-- url     : https://prove2.me/submissions/cfa0afea-26d4-491f-8835-518938fa1f86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesOfFgField

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
theorem _root_.solution {k K : Type} [Field k] [Field K] [Algebra k K] {s : Set K}
    (hs : IsTranscendenceBasis k ((↑) : s → K)) {x : K}
    (h : ∀ t : s, IsAlgebraic (IntermediateField.adjoin k (s \ {(t : K)})) x) : IsAlgebraic k x := by
  have key : x ∈ (AlgebraicIndependent.matroid k K).closure ∅ := by
    have hB := AlgebraicIndependent.matroid_isBase_iff.2 hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · rw [hB.closure_eq]; trivial
    · have := hne.coe_sort
      have e : (⋂ t : s, s \ {(t : K)}) = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun y hy => ?_
        rw [Set.mem_iInter] at hy
        exact (hy ⟨y, (hy this.some).1⟩).2 rfl
      rw [← e, hB.indep.closure_iInter_eq_biInter_closure_of_forall_subset fun _ => Set.diff_subset]
      refine Set.mem_iInter.2 fun t => ?_
      rw [AlgebraicIndependent.matroid_closure_eq]
      exact IntermediateField.isAlgebraic_adjoin_iff.1 (h t)
  rw [AlgebraicIndependent.matroid_closure_eq] at key
  have h2 : IsAlgebraic (IntermediateField.adjoin k (∅ : Set K)) x :=
    IntermediateField.isAlgebraic_adjoin_iff.2 key
  have : Algebra.IsAlgebraic k (IntermediateField.adjoin k (∅ : Set K)) :=
    (IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic k K).2 (by simp)
  exact h2.restrictScalars k
end GlobalTheory.SS
