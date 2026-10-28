-- Prove2me | solution 1 for NewMinimalStandardModel.seesaw_accommodates_rank_two
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:17:52.102683+00:00
-- url     : https://prove2.me/submissions/82639b29-8115-4d40-b544-becc6c429995

import Mathlib
import Definitions.Def_NewMinimalStandardModel_Defs

open Matrix

namespace S215_9184afda

lemma exists_q_ne (m : Matrix (Fin 3) (Fin 3) ℂ) (hs : mᵀ = m) (h0 : m ≠ 0) :
    ∃ x : Fin 3 → ℂ, x ⬝ᵥ (m *ᵥ x) ≠ 0 := by
  by_contra h
  push Not at h
  apply h0
  have key : ∀ i j, Pi.single i (1:ℂ) ⬝ᵥ (m *ᵥ Pi.single j 1) = m i j := by
    intro i j
    simp [single_dotProduct]
  ext i j
  have h1 := h (Pi.single i 1)
  have h2 := h (Pi.single j 1)
  have h3 := h (Pi.single i 1 + Pi.single j 1)
  have hji : m j i = m i j := by
    have := congrFun (congrFun hs i) j
    simpa using this
  rw [key] at h1 h2
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, key, key, key, key] at h3
  rw [Matrix.zero_apply]
  linear_combination h3 / 2 - h1 / 2 - h2 / 2 - hji / 2

lemma step (m : Matrix (Fin 3) (Fin 3) ℂ) (hs : mᵀ = m) (k : ℕ) (hr : m.rank ≤ k + 1) :
    ∃ w : Fin 3 → ℂ, (m - vecMulVec w w)ᵀ = m - vecMulVec w w ∧
      (m - vecMulVec w w).rank ≤ k := by
  by_cases h0 : m = 0
  · refine ⟨0, ?_, ?_⟩
    · simp [h0]
    · simp [h0, rank_zero]
  obtain ⟨x, hx⟩ := exists_q_ne m hs h0
  set u := m *ᵥ x with hu
  set c := x ⬝ᵥ u with hc
  obtain ⟨s, hs2⟩ := IsAlgClosed.exists_eq_mul_self c⁻¹
  refine ⟨s • u, ?_, ?_⟩
  · simp [transpose_sub, hs]
  set m' := m - vecMulVec (s • u) (s • u) with hm'
  have hsym : ∀ y, u ⬝ᵥ y = x ⬝ᵥ (m *ᵥ y) := by
    intro y
    rw [hu, dotProduct_mulVec, ← vecMul_transpose, hs]
  have hker : LinearMap.ker m.mulVecLin < LinearMap.ker m'.mulVecLin := by
    rw [SetLike.lt_iff_le_and_exists]
    refine ⟨?_, x, ?_, ?_⟩
    · intro y hy
      simp only [LinearMap.mem_ker, mulVecLin_apply] at hy ⊢
      rw [hm', sub_mulVec, hy, vecMulVec_mulVec, smul_dotProduct, hsym, hy]
      simp
    · simp only [LinearMap.mem_ker, mulVecLin_apply]
      rw [hm', sub_mulVec, vecMulVec_mulVec, smul_dotProduct, dotProduct_comm u x, ← hc]
      have hc0 : c ≠ 0 := hx
      have hss : s * s * c = 1 := by rw [← hs2, inv_mul_cancel₀ hc0]
      ext i
      simp
      show u i - s * u i * (s * c) = 0
      linear_combination (-(u i)) * hss
    · simp only [LinearMap.mem_ker, mulVecLin_apply]
      exact fun h => hx (by show x ⬝ᵥ (m *ᵥ x) = 0; rw [h]; simp)
  have hlt := Submodule.finrank_lt_finrank_of_lt hker
  have e1 := LinearMap.finrank_range_add_finrank_ker m.mulVecLin
  have e2 := LinearMap.finrank_range_add_finrank_ker m'.mulVecLin
  unfold Matrix.rank at hr ⊢
  omega

lemma decomp (m : Matrix (Fin 3) (Fin 3) ℂ) (hs : mᵀ = m) (hr : m.rank ≤ 2) :
    ∃ w₁ w₂ : Fin 3 → ℂ, m = vecMulVec w₁ w₁ + vecMulVec w₂ w₂ := by
  obtain ⟨w₁, hs1, hr1⟩ := step m hs 1 hr
  obtain ⟨w₂, -, hr2⟩ := step _ hs1 0 hr1
  have hz : m - vecMulVec w₁ w₁ - vecMulVec w₂ w₂ = 0 := by
    have : Matrix.rank (m - vecMulVec w₁ w₁ - vecMulVec w₂ w₂) = 0 := by omega
    unfold Matrix.rank at this
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at this
    ext i j
    have := congrArg (fun f => f (Pi.single j 1) i) this
    simpa [mulVecLin_apply, mulVec_single_one] using this
  refine ⟨w₁, w₂, ?_⟩
  rw [sub_sub, sub_eq_zero] at hz
  exact hz

end S215_9184afda

open NewMinimalStandardModel in
theorem solution (v : ℝ) (hv : 0 < v) (M : Fin 2 → ℝ)
    (hM : ∀ α, 0 < M α) (m : Matrix (Fin 3) (Fin 3) ℂ) (hsymm : m.transpose = m)
    (hrank : m.rank ≤ 2) :
    ∃ hν : Matrix (Fin 2) (Fin 3) ℂ, seesawMassMatrix v hν M = m := by
  obtain ⟨w₁, w₂, hm⟩ := S215_9184afda.decomp m hsymm hrank
  let c : Fin 2 → ℂ := fun α => Complex.I * (Real.sqrt (M α) : ℂ) * (Real.sqrt 2 : ℂ) / (v : ℂ)
  have key : ∀ α, -(((v : ℂ) / (Real.sqrt 2 : ℂ)) * c α) ^ 2 / (M α : ℂ) = 1 := by
    intro α
    have hv0 : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
    have hM2 : ((Real.sqrt (M α) : ℝ) : ℂ) ^ 2 = M α := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (hM α).le]
    have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
    have hM0 : (M α : ℂ) ≠ 0 := by exact_mod_cast (hM α).ne'
    simp only [c]
    field_simp
    rw [hM2, Complex.I_sq]
    ring
  refine ⟨Matrix.of ![c 0 • w₁, c 1 • w₂], ?_⟩
  rw [hm]
  have k0 := key 0
  have k1 := key 1
  have hM0 : (M 0 : ℂ) ≠ 0 := by exact_mod_cast (hM 0).ne'
  have hM1 : (M 1 : ℂ) ≠ 0 := by exact_mod_cast (hM 1).ne'
  have hinv : (Matrix.diagonal fun α => (M α : ℂ))⁻¹ = Matrix.diagonal fun α => (M α : ℂ)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext α; exact inv_mul_cancel₀ (by exact_mod_cast (hM α).ne')
  ext i j
  simp only [seesawMassMatrix, diracMass, rhNeutrinoMass, hinv, Matrix.neg_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.diagonal_apply,
    Fin.sum_univ_two, Matrix.add_apply, vecMulVec_apply, Matrix.of_apply, smul_eq_mul]
  simp
  linear_combination (w₁ i * w₁ j) * k0 + (w₂ i * w₂ j) * k1

