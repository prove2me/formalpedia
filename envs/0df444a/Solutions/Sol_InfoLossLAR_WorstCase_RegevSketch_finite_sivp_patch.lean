-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.finite_sivp_patch
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T08:54:19.497479+00:00
-- url     : https://prove2.me/submissions/8e48fd53-c25b-4b86-8ea8-fd3e674f06ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_finite_exact_sivp
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_sivp_dimension_dispatch

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

theorem solution (A : MFamily) (hA : IsMQPT A) (cutoff : ℕ) (gamma : ℕ → ℝ)
    (hgamma : ∀ n,1 ≤ n → 1 ≤ gamma n) :
    ∃ patched : MFamily, IsMQPT patched ∧ ∀ n, 1 ≤ n →
      (cutoff ≤ n → SolvesSIVP A (famN n) (gamma n)) →
        SolvesSIVP patched (famN n) (gamma n) := by
  obtain ⟨E, hE, hexact⟩ := finite_exact_sivp cutoff
  obtain ⟨P, hP, hdispatch⟩ := sivp_dimension_dispatch A E hA hE cutoff
  refine ⟨P, hP, ?_⟩
  intro n hn hlarge
  change SolvesSIVP P n (gamma n)
  intro B hB
  by_cases hsmall : n < cutoff
  · have hsrc := hexact n hn hsmall B hB
    have hmin : 0 ≤ lamN B := by
      apply Real.sInf_nonneg
      rintro r ⟨v, _, _, hbound⟩
      exact (norm_nonneg (v ⟨0, by omega⟩)).trans (hbound ⟨0, by omega⟩)
    have hsrc' : (2 : ℝ) / 3 ≤ outputProb E (encMat encI B) (fun out =>
      ∃ y : Fin n → Fin n → ℤ, encVec (encVec encI) y <+: out ∧
        (∀ i, intVecE (y i) ∈ lattice B) ∧ LinearIndependent ℝ (fun i => intVecE (y i)) ∧
        ∀ i, ‖intVecE (y i)‖ ≤ gamma n * lamN B) := by
      apply hsrc.trans
      unfold outputProb
      apply Finset.sum_le_sum
      intro y _
      split_ifs with h1 h2 h2
      · exact le_rfl
      · obtain ⟨v, hpref, hlat, hlin, hbound⟩ := h1
        have hmul : (1 : ℝ) * lamN B ≤ gamma n * lamN B :=
          mul_le_mul_of_nonneg_right (hgamma n hn) hmin
        exact False.elim (h2 ⟨v, hpref, hlat, hlin, fun i => (hbound i).trans hmul⟩)
      · exact sq_nonneg _
      · exact le_rfl
    apply hsrc'.trans
    have h := hdispatch n B (fun out =>
      ∃ y : Fin n → Fin n → ℤ, encVec (encVec encI) y <+: out ∧
        (∀ i, intVecE (y i) ∈ lattice B) ∧ LinearIndependent ℝ (fun i => intVecE (y i)) ∧
        ∀ i, ‖intVecE (y i)‖ ≤ gamma n * lamN B) (by
          intro s t hs hst
          obtain ⟨v, hv, hl, hi, hb⟩ := hs
          exact ⟨v, hv.trans hst, hl, hi, hb⟩)
    simpa [hsmall] using h
  · have hsrc := hlarge (by omega)
    change SolvesSIVP A n (gamma n) at hsrc
    apply (hsrc B hB).trans
    have h := hdispatch n B (fun out =>
      ∃ y : Fin n → Fin n → ℤ, encVec (encVec encI) y <+: out ∧
        (∀ i, intVecE (y i) ∈ lattice B) ∧ LinearIndependent ℝ (fun i => intVecE (y i)) ∧
        ∀ i, ‖intVecE (y i)‖ ≤ gamma n * lamN B) (by
          intro s t hs hst
          obtain ⟨v, hv, hl, hi, hb⟩ := hs
          exact ⟨v, hv.trans hst, hl, hi, hb⟩)
    simpa [hsmall] using h
