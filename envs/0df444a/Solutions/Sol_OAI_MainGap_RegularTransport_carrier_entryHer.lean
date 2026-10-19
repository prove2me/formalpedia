-- Prove2me | solution 1 for OAI.MainGap.RegularTransport.carrier_entryHer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:22:38.390763+00:00
-- url     : https://prove2.me/submissions/92f6a258-86b8-4149-82c7-f6ac98692690

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/OrthogonalSlots.lean:L211-L238
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.RegularTransport.carrier_entryHer. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_cornerHer_entries

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
lemma row_zero_of_self_star {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) A) (i : Fin n)
    (hi : (M * star M) i i = 0) (j : Fin n) : M i j = 0 := by
  have hs : ∑ k : Fin n, M i k * star (M i k) = 0 := hi
  have hnonneg : ∀ k ∈ (Finset.univ : Finset (Fin n)), 0 ≤ M i k * star (M i k) :=
    fun k _ => mul_star_self_nonneg _
  have hzero := ((Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hs) j (Finset.mem_univ j)
  apply norm_eq_zero.mp
  have hn : ‖M i j‖ * ‖M i j‖ = 0 := by rw [← CStarRing.norm_self_mul_star, hzero, norm_zero]
  nlinarith [norm_nonneg (M i j)]

lemma col_zero_of_star_self {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) A) (i : Fin n)
    (hi : (star M * M) i i = 0) (j : Fin n) : M j i = 0 := by
  have h := row_zero_of_self_star (star M) i (by simpa only [star_star] using hi) j
  change star (M j i) = 0 at h
  exact star_eq_zero.mp h

namespace RegularTransport
variable {n : ℕ} {h v : A} (i₀ : Fin n)
    (T : RegularTransport (diagonalCorner n h) (entry i₀ i₀ v))

lemma carrier_entryHer (i : Fin n) (k : Her h) :
    T.carrier (entryHer i i₀ k) =
      entry i₀ i₀ ((T.carrier (entryHer i i₀ k)) i₀ i₀) := by
  let M := T.carrier (entryHer i i₀ k)
  have hrow (j : Fin n) (hj : j ≠ i₀) : ∀ l, M j l = 0 := by
    apply row_zero_of_self_star
    have hout := T.outer (entryHer i i₀ k) (entryHer i i₀ k)
    have hm := T.image (entryHer i i₀ k * star (entryHer i i₀ k))
    rw [← hout] at hm
    exact (cornerHer_entries i₀ hm j j).2 (Or.inl hj)
  have hcol (j : Fin n) (hj : j ≠ i₀) : ∀ l, M l j = 0 := by
    apply col_zero_of_star_self
    have hin := T.inner (entryHer i i₀ k) (entryHer i i₀ k)
    simp only [entryHer_val, star_entry, entry_mul] at hin
    have he := congrArg (fun a : CStarMatrix (Fin n) (Fin n) A => a j j) hin
    simpa only [entry_apply, ne_comm.mp hj, false_and, ite_false] using he
  apply CStarMatrix.ext
  intro j l
  change M j l = (entry i₀ i₀ (M i₀ i₀)) j l
  rw [entry_apply]
  by_cases hj : j = i₀
  · subst j
    by_cases hl : l = i₀
    · subst l; simp
    · simp only [true_and, ne_comm.mp hl, ite_false]
      exact hcol l hl i₀
  · simp only [ne_comm.mp hj, false_and, ite_false]
    exact hrow j hj l

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
open OAI OAI.MainGap OAI.MainGap.RegularTransport
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
open scoped CStarAlgebra
attribute [local instance] OAI.MainGap.orthogonalSlotsPartialOrder
attribute [local instance] OAI.MainGap.orthogonalSlotsStarOrderedRing
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixIsScalarTower
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixSMulCommClass


theorem solution : type_of% @_root_.OAI.MainGap.RegularTransport.carrier_entryHer := @_root_.OAI.MainGap.RegularTransport.carrier_entryHer
