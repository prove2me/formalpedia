-- Prove2me | solution 1 for LinearOptimization.farkas_inequality_form
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T20:55:31.724156+00:00
-- url     : https://prove2.me/submissions/ea38e14b-1779-4fb9-bd30-f4a090307975

import Theorems.Thm_LinearOptimization_farkas_cone_corollary
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Archimedean

open Matrix

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ)
    (hfeas : ∃ x : Fin n → ℝ, A.mulVec x ≤ b) :
    (∀ x : Fin n → ℝ, A.mulVec x ≤ b → c ⬝ᵥ x ≤ d) ↔
      ∃ p : Fin m → ℝ, 0 ≤ p ∧ Aᵀ.mulVec p = c ∧ p ⬝ᵥ b ≤ d := by
  classical
  have hdual (p : Fin m → ℝ) (x : Fin n → ℝ) :
      p ⬝ᵥ A.mulVec x = Aᵀ.mulVec p ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec]
    congr 1
    funext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  constructor
  · intro hall
    rcases hfeas with ⟨x₀, hx₀⟩
    let row : Fin m → (Fin (n + 1) → ℝ) := fun i ↦
      Fin.lastCases (b i) (fun j ↦ -A i j)
    let extra : Fin (n + 1) → ℝ :=
      Fin.lastCases 1 (fun _ ↦ 0)
    let G : Fin (m + 1) → (Fin (n + 1) → ℝ) :=
      Fin.lastCases extra row
    let v : Fin (n + 1) → ℝ :=
      Fin.lastCases d (fun j ↦ -c j)
    have hhom (y : Fin (n + 1) → ℝ)
        (hy : ∀ i, 0 ≤ y ⬝ᵥ G i) : 0 ≤ y ⬝ᵥ v := by
      let x : Fin n → ℝ := fun j ↦ y j.castSucc
      let t : ℝ := y (Fin.last n)
      have ht : 0 ≤ t := by
        have := hy (Fin.last m)
        simpa [G, extra, t, dotProduct, Fin.sum_univ_castSucc] using this
      have hAx : A.mulVec x ≤ t • b := by
        intro i
        have hi := hy i.castSucc
        simp only [G, Fin.lastCases_castSucc] at hi
        simp [row, x, t, dotProduct, Fin.sum_univ_castSucc,
          Matrix.mulVec] at hi
        simpa [Matrix.mulVec_apply_eq_sum, dotProduct, x, t, Pi.smul_apply, smul_eq_mul,
          mul_comm] using hi
      have hcx : c ⬝ᵥ x ≤ d * t := by
        by_cases htzero : t = 0
        · have hdir : c ⬝ᵥ x ≤ 0 := by
            by_contra hnot
            have hpos : 0 < c ⬝ᵥ x := lt_of_not_ge hnot
            obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((d - c ⬝ᵥ x₀) / (c ⬝ᵥ x))
            let z : Fin n → ℝ := x₀ + (N : ℝ) • x
            have hz : A.mulVec z ≤ b := by
              intro i
              have hxi : A.mulVec x i ≤ 0 := by
                simpa [htzero] using hAx i
              have hx₀i := hx₀ i
              calc
                A.mulVec z i = A.mulVec x₀ i + (N : ℝ) * A.mulVec x i := by
                  simp [z, Matrix.mulVec_add, Matrix.mulVec_smul]
                _ ≤ A.mulVec x₀ i :=
                  add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos
                    (Nat.cast_nonneg N) hxi)
                _ ≤ b i := hx₀i
            have hzbound := hall z hz
            have hscaled : d - c ⬝ᵥ x₀ < (N : ℝ) * (c ⬝ᵥ x) := by
              have := mul_lt_mul_of_pos_right hN hpos
              field_simp at this
              simpa [mul_comm] using this
            simp [z, dotProduct_add, dotProduct_smul] at hzbound
            linarith
          simpa [htzero] using hdir
        · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
          let z : Fin n → ℝ := t⁻¹ • x
          have hz : A.mulVec z ≤ b := by
            intro i
            have hi := hAx i
            have hinv : 0 ≤ t⁻¹ := (inv_pos.mpr htpos).le
            have := mul_le_mul_of_nonneg_left hi hinv
            simpa [z, Matrix.mulVec_smul, htpos.ne'] using this
          have hzbound := hall z hz
          have htne : t ≠ 0 := htpos.ne'
          simp [z, dotProduct_smul] at hzbound
          have := mul_le_mul_of_nonneg_left hzbound ht
          field_simp [htne] at this
          nlinarith
      simpa [v, x, t, dotProduct, Fin.sum_univ_castSucc, mul_comm,
        sub_eq_add_neg] using (sub_nonneg.mpr hcx)
    obtain ⟨lam, hlam, hv⟩ :=
      LinearOptimization.farkas_cone_corollary G v hhom
    let p : Fin m → ℝ := fun i ↦ lam i.castSucc
    refine ⟨p, ?_, ?_, ?_⟩
    · intro i
      exact hlam i.castSucc
    · funext j
      have hj := congrFun hv j.castSucc
      simp [v, G, extra, row, p, Fin.sum_univ_castSucc] at hj
      simpa [Matrix.mulVec, dotProduct, p, mul_comm] using hj.symm
    · have hlast := congrFun hv (Fin.last n)
      have hsnonneg := hlam (Fin.last m)
      simp [v, G, extra, row, p, Fin.sum_univ_castSucc] at hlast
      change (∑ i : Fin m, p i * b i) ≤ d
      linarith
  · rintro ⟨p, hp, hAT, hpb⟩ x hx
    have hdot : p ⬝ᵥ A.mulVec x ≤ p ⬝ᵥ b := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hx i) (hp i)
    rw [hdual, hAT] at hdot
    exact hdot.trans hpb
