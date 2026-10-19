-- Prove2me | solution 1 for OAI.MainGap.cornerHer_entries
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:19:10.841615+00:00
-- url     : https://prove2.me/submissions/7a153999-ebd9-4a6c-a574-0237e6d3b94e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/OrthogonalSlots.lean:L125-L152
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.cornerHer_entries. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.OrthogonalSlots ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
open scoped CStarAlgebra
attribute [local instance] OAI.MainGap.orthogonalSlotsPartialOrder
attribute [local instance] OAI.MainGap.orthogonalSlotsStarOrderedRing
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixIsScalarTower
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixSMulCommClass
lemma cornerHer_entries {n : ℕ} (i : Fin n) {h : A}
    {a : CStarMatrix (Fin n) (Fin n) A} (ha : a ∈ Her (entry i i h))
    (j k : Fin n) : a j k ∈ Her h ∧ (j ≠ i ∨ k ≠ i → a j k = 0) := by
  refine closure_minimal (s := Set.range (fun b => entry i i h * b * star (entry i i h)))
    (t := {b | b j k ∈ Her h ∧ (j ≠ i ∨ k ≠ i → b j k = 0)}) ?_ ?_ ha
  · rintro _ ⟨b, rfl⟩
    have heq : entry i i h * b * star (entry i i h) = entry i i (h*b i i*star h) := by
      rw [star_entry]
      exact Matrix.single_mul_mul_single i i i i h (CStarMatrix.ofMatrix.symm b) (star h)
    change (entry i i h * b * star (entry i i h)) j k ∈ Her h ∧
      (j ≠ i ∨ k ≠ i → (entry i i h * b * star (entry i i h)) j k = 0)
    rw [heq, entry_apply]
    split_ifs with heq
    · refine ⟨sandwich_mem_Her h _, ?_⟩
      intro hjk
      rcases hjk with hj | hk
      · exact (hj heq.1.symm).elim
      · exact (hk heq.2.symm).elim
    · exact ⟨(Her h).zero_mem, by simp⟩
  · apply IsClosed.inter
    · exact (isClosed_Her _).preimage (by fun_prop)
    · by_cases hjk : j ≠ i ∨ k ≠ i
      · change IsClosed {b : CStarMatrix (Fin n) (Fin n) A | j ≠ i ∨ k ≠ i → b j k = 0}
        simpa only [hjk, true_implies] using
          (isClosed_eq (show Continuous (fun a : CStarMatrix (Fin n) (Fin n) A => a j k) by fun_prop)
          continuous_const)
      · simp only [hjk, false_implies]
        exact isClosed_univ

namespace RegularTransport
variable {n : ℕ} {h v : A} (i₀ : Fin n)
    (T : RegularTransport (diagonalCorner n h) (entry i₀ i₀ v))

end RegularTransport

namespace OrthogonalSlots
variable {n : ℕ} {h v : A} (S : OrthogonalSlots n h v)

end OrthogonalSlots

section FiniteSum

end FiniteSum
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
open scoped CStarAlgebra
attribute [local instance] OAI.MainGap.orthogonalSlotsPartialOrder
attribute [local instance] OAI.MainGap.orthogonalSlotsStarOrderedRing
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixIsScalarTower
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixSMulCommClass


theorem solution : type_of% @_root_.OAI.MainGap.cornerHer_entries := @_root_.OAI.MainGap.cornerHer_entries
