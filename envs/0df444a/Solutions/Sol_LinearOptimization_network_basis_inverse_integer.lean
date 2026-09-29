-- Prove2me | solution 1 for LinearOptimization.network_basis_inverse_integer
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T04:15:17.264521+00:00
-- url     : https://prove2.me/submissions/45a32a02-c832-4fc4-8cf3-ec9f5b74c892

import Definitions.Def_LinearOptimization_NetworkFlowProblem
import Definitions.Def_BasicSolution
import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

private lemma incidence_selected_column_sum {n m k : ℕ}
    (arcs : Fin m → Fin n × Fin n)
    (f : Fin k → Fin n) (hf : Function.Injective f) (j : Fin m)
    (hu : ∃ i, f i = (arcs j).1) (hv : ∃ i, f i = (arcs j).2) :
    ∑ i, LinearOptimization.incidenceMatrix arcs (f i) j = 0 := by
  obtain ⟨iu, hiu⟩ := hu
  obtain ⟨iv, hiv⟩ := hv
  unfold LinearOptimization.incidenceMatrix
  simp only [Matrix.of_apply]
  rw [Finset.sum_sub_distrib]
  have hfirst : (∑ i : Fin k, if (arcs j).1 = f i then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single iu]
    · simp [hiu]
    · intro b _ hbi
      simp only [ite_eq_right_iff]
      intro hb
      exact (hbi (hf (hb.symm.trans hiu.symm))).elim
    · simp
  have hsecond : (∑ i : Fin k, if (arcs j).2 = f i then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single iv]
    · simp [hiv]
    · intro b _ hbi
      simp only [ite_eq_right_iff]
      intro hb
      exact (hbi (hf (hb.symm.trans hiv.symm))).elim
    · simp
  rw [hfirst, hsecond, sub_self]

private lemma incidence_entry_ne_zero_endpoint {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (i : Fin n) (j : Fin m)
    (h : LinearOptimization.incidenceMatrix arcs i j ≠ 0) :
    i = (arcs j).1 ∨ i = (arcs j).2 := by
  unfold LinearOptimization.incidenceMatrix at h
  simp only [Matrix.of_apply] at h
  by_contra hn
  push_neg at hn
  simp [hn.1.symm, hn.2.symm] at h

theorem LinearOptimization.network_incidence_totally_unimodular {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) :
    (incidenceMatrix arcs).IsTotallyUnimodular := by
  intro k
  induction k with
  | zero =>
      intro f g hf hg
      use 1
      simp
  | succ k ih =>
      intro f g hf hg
      let M := (incidenceMatrix arcs).submatrix f g
      by_cases hone : ∃ j i, M i j ≠ 0 ∧ ∀ i' ≠ i, M i' j = 0
      · obtain ⟨j, i, hij, hother⟩ := hone
        rw [Matrix.det_succ_column M j, Fintype.sum_eq_single i]
        · change _ ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
          refine mul_mem (mul_mem (pow_mem ?_ _) ?_) ?_
          · exact ⟨-1, by simp⟩
          · change M i j ∈ Set.range SignType.cast
            simp only [M, Matrix.submatrix_apply]
            unfold incidenceMatrix
            simp only [Matrix.of_apply]
            rcases eq_or_ne (arcs (g j)).1 (f i) with h1 | h1 <;>
              rcases eq_or_ne (arcs (g j)).2 (f i) with h2 | h2 <;>
              simp [h1, h2, SignType.range_eq]
          · have hminor := ih (f ∘ i.succAbove) (g ∘ j.succAbove)
                (hf.comp i.succAbove_right_injective)
                (hg.comp j.succAbove_right_injective)
            simpa [M, Matrix.submatrix_submatrix, Function.comp_def] using hminor
        · intro b hbi
          rw [hother b hbi]
          simp
      · by_cases hzero : ∃ j, ∀ i, M i j = 0
        · obtain ⟨j, hj⟩ := hzero
          use 0
          exact (Matrix.det_eq_zero_of_column_eq_zero j hj).symm
        · have hsum : ∀ j, ∑ i, M i j = 0 := by
            intro j
            have hnonzero : ∃ i, M i j ≠ 0 := by
              exact not_forall.mp ((not_exists.mp hzero) j)
            obtain ⟨i, hi⟩ := hnonzero
            have hiend := incidence_entry_ne_zero_endpoint arcs (f i) (g j) hi
            have hu : ∃ r, f r = (arcs (g j)).1 := by
              rcases hiend with hiu | hiv
              · exact ⟨i, hiu⟩
              · by_contra hmissing
                apply hone
                refine ⟨j, i, hi, ?_⟩
                intro i' hii'
                simp only [M, Matrix.submatrix_apply]
                unfold incidenceMatrix
                simp only [Matrix.of_apply]
                have hsource : (arcs (g j)).1 ≠ f i' := by
                  intro hs
                  exact hmissing ⟨i', hs.symm⟩
                have htarget : (arcs (g j)).2 ≠ f i' := by
                  intro ht
                  exact hii' (hf (ht.symm.trans hiv.symm))
                simp [hsource, htarget]
            have hv : ∃ r, f r = (arcs (g j)).2 := by
              rcases hiend with hiu | hiv
              · by_contra hmissing
                apply hone
                refine ⟨j, i, hi, ?_⟩
                intro i' hii'
                simp only [M, Matrix.submatrix_apply]
                unfold incidenceMatrix
                simp only [Matrix.of_apply]
                have hsource : (arcs (g j)).1 ≠ f i' := by
                  intro hs
                  exact hii' (hf (hs.symm.trans hiu.symm))
                have htarget : (arcs (g j)).2 ≠ f i' := by
                  intro ht
                  exact hmissing ⟨i', ht.symm⟩
                simp [hsource, htarget]
              · exact ⟨i, hiv⟩
            simpa only [M, Matrix.submatrix_apply] using
              incidence_selected_column_sum arcs f hf (g j) hu hv
          use 0
          have hdet := Matrix.det_eq_sum_column_mul_submatrix_succAbove_succAbove_det
            M 0 0 (fun j _ ↦ hsum j)
          change (0 : ℝ) = M.det
          rw [hdet, hsum]
          simp

private lemma totallyUnimodular_inv_apply_integer {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsTotallyUnimodular)
    (hunit : IsUnit A) (i j : Fin n) :
    ∃ z : ℤ, A⁻¹ i j = (z : ℝ) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      have hdetUnit : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hunit
      obtain ⟨s, hs⟩ := hA (n + 1) id id Function.injective_id Function.injective_id
      have hminor := hA n j.succAbove i.succAbove
        j.succAbove_right_injective i.succAbove_right_injective
      obtain ⟨t, ht⟩ := hminor
      simp only [Matrix.submatrix_id_id] at hs
      have hs' : A.det = (s : ℝ) := hs.symm
      have ht' : (A.submatrix j.succAbove i.succAbove).det = (t : ℝ) := ht.symm
      let eps : ℤ := (Int.negOnePow ((j : ℕ) + (i : ℕ)) : ℤ)
      have heps : (eps : ℝ) = (-1 : ℝ) ^ ((j : ℕ) + (i : ℕ)) := by
        exact Int.cast_negOnePow_natCast ℝ ((j : ℕ) + (i : ℕ))
      refine ⟨(s : ℤ) * eps * (t : ℤ), ?_⟩
      simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
        Matrix.adjugate_fin_succ_eq_det_submatrix, hs', ht', Int.cast_mul]
      rw [heps]
      cases s <;>
        simp_all [SignType.zero_eq_zero, SignType.neg_eq_neg_one,
          SignType.pos_eq_one, SignType.coe_zero, SignType.coe_neg_one,
          SignType.coe_one]

theorem solution {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1))
    (B : Fin n ↪ Fin m)
    (hB : LinearOptimization.IsStdBasis
      (LinearOptimization.truncatedIncidence arcs) B) :
    ∀ i j, ∃ z : ℤ,
      (LinearOptimization.basisMatrix
        (LinearOptimization.truncatedIncidence arcs) B)⁻¹ i j = (z : ℝ) := by
  intro i j
  have hTUfull := LinearOptimization.network_incidence_totally_unimodular arcs
  have hTUtrunc :
      (LinearOptimization.truncatedIncidence arcs).IsTotallyUnimodular := by
    exact hTUfull.submatrix Fin.castSucc id
  have hTUbasis :
      (LinearOptimization.basisMatrix
        (LinearOptimization.truncatedIncidence arcs) B).IsTotallyUnimodular := by
    exact hTUtrunc.submatrix id B
  have hunit : IsUnit (LinearOptimization.basisMatrix
      (LinearOptimization.truncatedIncidence arcs) B) := by
    apply Matrix.linearIndependent_cols_iff_isUnit.mp
    exact hB
  exact totallyUnimodular_inv_apply_integer
    (LinearOptimization.basisMatrix
      (LinearOptimization.truncatedIncidence arcs) B) hTUbasis hunit i j
