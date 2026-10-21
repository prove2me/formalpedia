-- Prove2me | solution 1 for MarkovInterference.DQBias.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:33:10.220377+00:00
-- url     : https://prove2.me/submissions/6ef84b93-cc1d-48da-8a95-8315d13cbe38

import Mathlib
import Definitions.Def_MarkovInterference_DQBias_Chain

set_option autoImplicit false
open MarkovInterference.DQBias
open scoped Matrix

section
variable {S : Type} [Fintype S] [DecidableEq S]

lemma pow_mulVec_one (P : Matrix S S ℝ) (hP : IsStochastic P) (k : ℕ) :
    (P ^ k) *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec]
    have : P *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
      ext i; simp [Matrix.mulVec, dotProduct, hP.2 i]
    rw [this, ih]

lemma pow_mulVec_fix (P : Matrix S S ℝ) (v : S → ℝ) (hv : P *ᵥ v = v) (k : ℕ) :
    (P ^ k) *ᵥ v = v := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]

lemma fixed_const (P : Matrix S S ℝ) (hP : IsStochastic P) (k : ℕ)
    (hk : ∀ i j, 0 < (P ^ k) i j) (v : S → ℝ) (hv : P *ᵥ v = v) (i j : S) : v i = v j := by
  have hQ := pow_mulVec_fix P v hv k
  have h1 := pow_mulVec_one P hP k
  have : Nonempty S := ⟨i⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max v
  have hsum : ∑ j, (P ^ k) i0 j * (v i0 - v j) = 0 := by
    have e1 : ∑ j, (P ^ k) i0 j = 1 := by
      have := congrFun h1 i0
      simpa [Matrix.mulVec, dotProduct] using this
    have e2 : ∑ j, (P ^ k) i0 j * v j = v i0 := by
      have := congrFun hQ i0
      simpa [Matrix.mulVec, dotProduct] using this
    calc ∑ j, (P ^ k) i0 j * (v i0 - v j)
        = ∑ j, (v i0 * (P ^ k) i0 j) - ∑ j, (P ^ k) i0 j * v j := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = 0 := by rw [← Finset.mul_sum, e1, e2]; ring
  have hall : ∀ j, v j = v i0 := by
    intro j
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ (P ^ k) i0 j * (v i0 - v j) :=
      fun j _ => mul_nonneg (hk i0 j).le (sub_nonneg.2 (hi0 j))
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum j (Finset.mem_univ j)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hk i0 j).ne'
    · linarith
  rw [hall i, hall j]

lemma ker_trivial (P : Matrix S S ℝ) (rho : S → ℝ) (hP : IsStochastic P) (hp : IsPrimitive P)
    (hrho : IsStationaryDist P rho) (v : S → ℝ)
    (h : (1 - P + onesRho rho) *ᵥ v = 0) : v = 0 := by
  have e : onesRho rho *ᵥ v = (rho ⬝ᵥ v) • (fun _ => (1 : ℝ)) := by
    ext i; simp [onesRho, Matrix.mulVec, Matrix.vecMulVec, dotProduct]
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, e] at h
  have hdot : rho ⬝ᵥ v = 0 := by
    have := congrArg (fun w => rho ⬝ᵥ w) h
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, Matrix.dotProduct_mulVec, hrho.2.2,
      smul_eq_mul, dotProduct_zero] at this
    have hs : rho ⬝ᵥ (fun _ => (1 : ℝ)) = 1 := by simpa [dotProduct] using hrho.2.1
    rw [hs] at this
    linarith
  rw [hdot, zero_smul, add_zero] at h
  have hv : P *ᵥ v = v := by
    have := sub_eq_zero.1 h
    exact this.symm
  obtain ⟨k, hk⟩ := hp
  have hc := fixed_const P hP k hk v hv
  funext i
  have hs : rho ⬝ᵥ v = v i := by
    have : ∀ j, v j = v i := fun j => hc j i
    simp only [dotProduct, this, ← Finset.sum_mul, hrho.2.1, one_mul]
  simp [← hs, hdot]

lemma isUnit_A (P : Matrix S S ℝ) (rho : S → ℝ) (hP : IsStochastic P) (hp : IsPrimitive P)
    (hrho : IsStationaryDist P rho) : IsUnit (1 - P + onesRho rho).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  have : (1 - P + onesRho rho) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.1 (ker_trivial P rho hP hp hrho _ this)

end

theorem solution {S : Type} [Fintype S] [DecidableEq S]
    (P P' : Matrix S S ℝ) (rho rho' : S → ℝ)
    (hP : IsStochastic P) (hP' : IsStochastic P')
    (hp : IsPrimitive P) (hp' : IsPrimitive P')
    (hrho : IsStationaryDist P rho) (hrho' : IsStationaryDist P' rho') :
    rho' = rho + Matrix.vecMul rho' ((P' - P) * groupInv P rho) := by
  set A : Matrix S S ℝ := 1 - P + onesRho rho with hA
  have hU := isUnit_A P rho hP hp hrho
  have hs' : rho' ⬝ᵥ (fun _ => (1 : ℝ)) = 1 := by simpa [dotProduct] using hrho'.2.1
  have hs : rho ⬝ᵥ (fun _ => (1 : ℝ)) = 1 := by simpa [dotProduct] using hrho.2.1
  have hPone : P *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
    ext i; simp [Matrix.mulVec, dotProduct, hP.2 i]
  -- u = rho' (P' - P)
  set u : S → ℝ := Matrix.vecMul rho' (P' - P) with hu
  have hE : ∀ w : S → ℝ, Matrix.vecMul w (onesRho rho) = (w ⬝ᵥ (fun _ => (1 : ℝ))) • rho := by
    intro w; exact Matrix.vecMul_vecMulVec _ _ _
  have h1 : u = Matrix.vecMul rho' A - rho := by
    rw [hu, hA]
    simp only [Matrix.vecMul_sub, Matrix.vecMul_add, Matrix.vecMul_one, hrho'.2.2, hE, hs',
      one_smul]
    abel
  have h2 : Matrix.vecMul rho A = rho := by
    rw [hA, Matrix.vecMul_add, Matrix.vecMul_sub, hrho.2.2, Matrix.vecMul_one, hE, hs]
    simp
  have h3 : u ⬝ᵥ (fun _ => (1 : ℝ)) = 0 := by
    rw [h1]
    have : Matrix.vecMul rho' A ⬝ᵥ (fun _ => (1 : ℝ)) = 1 := by
      rw [← Matrix.dotProduct_mulVec, hA, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hPone]
      have e : onesRho rho *ᵥ (fun _ => (1 : ℝ)) = fun _ => (1 : ℝ) := by
        ext i; simp [onesRho, Matrix.mulVec, Matrix.vecMulVec, dotProduct, hrho.2.1]
      rw [e]; simpa using hs'
    rw [sub_dotProduct, this, hs]; norm_num
  have hinv : Matrix.vecMul rho A⁻¹ = rho := by
    have := congrArg (fun w => Matrix.vecMul w A⁻¹) h2
    simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hU, Matrix.vecMul_one] at this
    exact this.symm
  have hG : groupInv P rho = A⁻¹ - onesRho rho := rfl
  have key : Matrix.vecMul rho' ((P' - P) * groupInv P rho) = rho' - rho := by
    rw [← Matrix.vecMul_vecMul, ← hu, hG, Matrix.vecMul_sub, hE, h3, zero_smul, sub_zero, h1,
      Matrix.sub_vecMul, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hU, Matrix.vecMul_one,
      hinv]
  rw [key]; abel
