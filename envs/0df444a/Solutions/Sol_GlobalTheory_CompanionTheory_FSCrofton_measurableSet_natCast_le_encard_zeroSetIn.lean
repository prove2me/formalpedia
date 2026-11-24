-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.measurableSet_natCast_le_encard_zeroSetIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:03:30.467258+00:00
-- url     : https://prove2.me/submissions/162f10ca-392a-4545-9708-346e1bfad30b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCount
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_measurableSet_meets_inter
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_natCast_le_encard_zeroSetIn_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton
open TopologicalSpace
variable {X : Type} [TopologicalSpace X] {d : ℕ} {α : Type} [Fintype α]
namespace GlobalTheory.CompanionTheory.FSCrofton
theorem _root_.solution [T2Space X] [SecondCountableTopology X]
    [LocallyCompactSpace X] {A : Set X} (hA : IsSigmaCompact A) {b : α → X → ℂ}
    (hb : ∀ j, ContinuousOn (b j) A) (N : ℕ) :
    MeasurableSet {C : Fin d → α → ℂ | (N : ℕ∞) ≤ (zeroSetIn A b C).encard} := by
  classical
  haveI : Countable (countableBasis X) := (countable_countableBasis X).to_subtype
  have hEq : {C : Fin d → α → ℂ | (N : ℕ∞) ≤ (zeroSetIn A b C).encard} =
      ⋃ f : Fin N → countableBasis X, ⋃ (_ : ∀ i j, i ≠ j → Disjoint (f i : Set X) (f j)),
        ⋂ i, {C : Fin d → α → ℂ | ∃ z ∈ A ∩ (f i : Set X), ∀ k, ∑ j, C k j * b j z = 0} := by
    ext C
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, exists_prop]
    exact natCast_le_encard_zeroSetIn_iff A b C N
  rw [hEq]
  refine MeasurableSet.iUnion fun f => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun i => ?_
  exact measurableSet_meets_inter hA ((isBasis_countableBasis X).isOpen (f i).2) hb
end GlobalTheory.CompanionTheory.FSCrofton
