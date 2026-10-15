-- Prove2me | solution 1 for OAI.SegmentLenses.refinement_test_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:22:26.290036+00:00
-- url     : https://prove2.me/submissions/ea9cae62-dea6-487e-b4e3-cf94243eae78

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/Basic.lean:L239-L271
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.refinement_test_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic

-- ---- from OAI.Analysis.SegmentLenses.Basic ----
namespace OAI

/-!
# Segment tests, their completion, and coordinate functionals
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

namespace SegmentFamily
variable {V : Type*} [SegmentSystem V]

end SegmentFamily

theorem refinement_test_bound {V ι : Type*} [SegmentSystem V] [Fintype ι]
    (u : V →₀ ℝ) (S A B : ι → Finset V)
    (hd : Pairwise fun i j => Disjoint (S i) (S j))
    (hA : ∀ i, A i ⊆ S i) (hB : ∀ i, B i ⊆ S i)
    (hAB : ∀ i, Disjoint (A i) (B i))
    (hsA : ∀ i, A i = ∅ ∨ SegmentSystem.isSegment (A i))
    (hsB : ∀ i, B i = ∅ ∨ SegmentSystem.isSegment (B i)) :
    ∑ i, ((∑ v ∈ A i, u v) ^ 2 + (∑ v ∈ B i, u v) ^ 2) ≤
      segmentSeminorm V u ^ 2 := by
  classical
  let pieces : ι × Bool → Finset V := fun j => if j.2 then B j.1 else A j.1
  have hp : ∀ j, pieces j = ∅ ∨ SegmentSystem.isSegment (pieces j) := by
    rintro ⟨i, b⟩
    cases b
    · exact hsA i
    · exact hsB i
  have hsub : ∀ j : ι × Bool, pieces j ⊆ S j.1 := by
    rintro ⟨i, b⟩
    cases b
    · exact hA i
    · exact hB i
  have hpd : Pairwise fun i j => Disjoint (pieces i) (pieces j) := by
    rintro ⟨i, b⟩ ⟨j, c⟩ hne
    by_cases hij : i = j
    · subst j
      cases b <;> cases c
      · exact False.elim (hne rfl)
      · exact hAB i
      · exact (hAB i).symm
      · exact False.elim (hne rfl)
    · exact (hd hij).mono (hsub _) (hsub _)
  have h := indexed_test_bound u pieces hp hpd
  simpa [Fintype.sum_prod_type, pieces, Fintype.sum_bool, add_comm] using h

namespace Test
variable {V : Type*}
variable [SegmentSystem V]
end Test

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset

theorem solution {V ι : Type*} [SegmentSystem V] [Fintype ι]
    (u : V →₀ ℝ) (S A B : ι → Finset V)
    (hd : Pairwise fun i j => Disjoint (S i) (S j))
    (hA : ∀ i, A i ⊆ S i) (hB : ∀ i, B i ⊆ S i)
    (hAB : ∀ i, Disjoint (A i) (B i))
    (hsA : ∀ i, A i = ∅ ∨ SegmentSystem.isSegment (A i))
    (hsB : ∀ i, B i = ∅ ∨ SegmentSystem.isSegment (B i)) :
    ∑ i, ((∑ v ∈ A i, u v) ^ 2 + (∑ v ∈ B i, u v) ^ 2) ≤
      segmentSeminorm V u ^ 2 := by
  first
    | exact OAI.SegmentLenses.refinement_test_bound u S A B hd hA hB hAB hsA hsB
    | exact OAI.SegmentLenses.refinement_test_bound
    | (apply OAI.SegmentLenses.refinement_test_bound <;> assumption)
    | (intros; apply OAI.SegmentLenses.refinement_test_bound <;> assumption)
