-- Prove2me | solution 1 for MayersBC.hjw_steering
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T04:45:31.524571+00:00
-- url     : https://prove2.me/submissions/645f0970-8f69-4b05-9ac6-fc1d08b85d8c

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_FuchsVdGraaf_IsProbDist
import Definitions.Def_MayersBC_mixtureDensity
open QAlgorithms

namespace HJWAux

open Matrix
open scoped ComplexOrder MatrixOrder ComplexConjugate

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section Pinv

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fin (X : Matrix ι ι ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

/-- Moore–Penrose pseudo-inverse of a Hermitian matrix via functional calculus. -/
noncomputable def pinv (P : Matrix ι ι ℂ) : Matrix ι ι ℂ := cfc (fun x : ℝ => x⁻¹) P

lemma pinv_herm (P : Matrix ι ι ℂ) : (pinv P)ᴴ = pinv P :=
  (cfc_predicate (fun x : ℝ => x⁻¹) P : IsSelfAdjoint _)

lemma pinv_mul_mul_pinv {P : Matrix ι ι ℂ} (hP : IsSelfAdjoint P) :
    pinv P * P * pinv P = pinv P := by
  unfold pinv
  conv_lhs => arg 1; arg 2; rw [← cfc_id' ℝ P hP]
  rw [← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
  refine cfc_congr fun x _ => ?_
  by_cases hx : x = 0
  · simp [hx]
  · field_simp

lemma mul_pinv_mul {P : Matrix ι ι ℂ} (hP : IsSelfAdjoint P) :
    P * pinv P * P = P := by
  unfold pinv
  conv_lhs => arg 1; arg 1; rw [← cfc_id' ℝ P hP]
  conv_lhs => arg 2; rw [← cfc_id' ℝ P hP]
  rw [← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
  conv_rhs => rw [← cfc_id' ℝ P hP]
  refine cfc_congr fun x _ => ?_
  by_cases hx : x = 0
  · simp [hx]
  · field_simp

/-- `P P⁺ V = V` for `P = V V†`. -/
lemma range_absorb {W : Type*} [Fintype W] (V : Matrix ι W ℂ) :
    V * Vᴴ * pinv (V * Vᴴ) * V = V := by
  set P := V * Vᴴ with hPdef
  have hP : IsSelfAdjoint P := (Matrix.isHermitian_mul_conjTranspose_self V).isSelfAdjoint
  have hpp := mul_pinv_mul hP
  have hpinvH := pinv_herm P
  have hPH : Pᴴ = P := hP
  have h0 : (P * pinv P * V - V) * (P * pinv P * V - V)ᴴ = 0 := by
    have e1 : (P * pinv P * V) * (P * pinv P * V)ᴴ = P := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hpinvH, hPH]
      calc P * pinv P * V * (Vᴴ * (pinv P * P)) = (P * pinv P * P) * pinv P * P := by
              rw [hPdef]; simp only [Matrix.mul_assoc]
        _ = P := by rw [hpp, hpp]
    have e2 : (P * pinv P * V) * Vᴴ = P := by
      rw [Matrix.mul_assoc, ← hPdef, hpp]
    have e3 : V * (P * pinv P * V)ᴴ = P := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hpinvH, hPH, ← Matrix.mul_assoc,
        ← hPdef, ← Matrix.mul_assoc, hpp]
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, e1, e2, e3,
      ← hPdef]
    abel
  have := Matrix.self_mul_conjTranspose_eq_zero.mp h0
  exact sub_eq_zero.mp this

end Pinv

section Steering

variable {A W ι : Type} [Fintype A] [DecidableEq A] [Fintype W] [Fintype ι] [DecidableEq ι]

/-- Coefficient matrix `C x a = φ(a, x)`. -/
noncomputable def coef (φ : EuclideanSpace ℂ (A × ι)) : Matrix ι A ℂ :=
  Matrix.of fun x a => φ (a, x)

lemma traceLeft_pure (φ : EuclideanSpace ℂ (A × ι)) :
    traceLeft (pureDensity φ) = coef φ * (coef φ)ᴴ := by
  ext x y
  simp [coef, traceLeft, pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma traceLeft_kron_pure (N : Matrix A A ℂ) (φ : EuclideanSpace ℂ (A × ι)) :
    traceLeft (Matrix.kronecker N (1 : Matrix ι ι ℂ) * pureDensity φ) =
      coef φ * Nᵀ * (coef φ)ᴴ := by
  ext x y
  simp only [traceLeft, Matrix.of_apply, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, pureDensity, coef, Matrix.transpose_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [RCLike.star_def]
  ring

/-- `V x w = √p_w ψ_w(x)`. -/
noncomputable def amp (p : W → ℝ) (ψ : W → EuclideanSpace ℂ ι) : Matrix ι W ℂ :=
  Matrix.of fun x w => (Real.sqrt (p w) : ℂ) * ψ w x

lemma amp_mul_amp [DecidableEq W] (p : W → ℝ) (hp : ∀ w, 0 ≤ p w) (ψ : W → EuclideanSpace ℂ ι)
    (w : W) :
    amp p ψ * Matrix.diagonal (fun w' => if w' = w then (1 : ℂ) else 0) * (amp p ψ)ᴴ =
      ((p w : ℝ) : ℂ) • pureDensity (ψ w) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, amp, Matrix.of_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply, pureDensity, smul_eq_mul]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true, mul_one]
  simp only [RCLike.star_def, map_mul, Complex.conj_ofReal]
  have h := Real.mul_self_sqrt (hp w)
  have h' : ((Real.sqrt (p w) : ℂ)) * (Real.sqrt (p w) : ℂ) = (p w : ℂ) := by
    rw [← Complex.ofReal_mul, h]
  linear_combination (ψ w x * (starRingEnd ℂ) (ψ w y)) * h'

lemma amp_mul_amp_conj [DecidableEq W] (p : W → ℝ) (hp : ∀ w, 0 ≤ p w) (ψ : W → EuclideanSpace ℂ ι) :
    amp p ψ * (amp p ψ)ᴴ = MayersBC.mixtureDensity p ψ := by
  have h1 : (1 : Matrix W W ℂ) =
      ∑ w, Matrix.diagonal (fun w' => if w' = w then (1 : ℂ) else 0) := by
    ext a b
    simp only [Matrix.one_apply, Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  rw [show amp p ψ * (amp p ψ)ᴴ = amp p ψ * (1 : Matrix W W ℂ) * (amp p ψ)ᴴ by
    rw [Matrix.mul_one], h1, Matrix.mul_sum, Matrix.sum_mul]
  unfold MayersBC.mixtureDensity
  exact Finset.sum_congr rfl fun w _ => amp_mul_amp p hp ψ w

end Steering

end HJWAux

open scoped Matrix ComplexOrder MatrixOrder

open HJWAux in
theorem solution {A W ι : Type} [Fintype A] [DecidableEq A] [Fintype W] [Fintype ι]
    [DecidableEq ι] (p : W → ℝ) (hp : FuchsVdGraaf.IsProbDist p) (ψ : W → EuclideanSpace ℂ ι)
    (hψ : ∀ w, IsState (ψ w)) (φ : EuclideanSpace ℂ (A × ι))
    (hmarg : traceLeft (pureDensity φ) = MayersBC.mixtureDensity p ψ) :
    ∃ N : W → Matrix A A ℂ, IsPOVM N ∧
      ∀ w, traceLeft (Matrix.kronecker (N w) (1 : Matrix ι ι ℂ) * pureDensity φ) =
        ((p w : ℝ) : ℂ) • pureDensity (ψ w) := by
  classical
  -- a distinguished outcome
  have hW : Nonempty W := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hp.2
    simp at this
  obtain ⟨w0⟩ := hW
  set C := coef φ with hCdef
  set V := amp p ψ with hVdef
  have hCV : C * Cᴴ = V * Vᴴ := by
    rw [hCdef, hVdef, ← traceLeft_pure, hmarg, amp_mul_amp_conj p hp.1]
  set P := C * Cᴴ with hPdef
  have hPsa : IsSelfAdjoint P := (Matrix.isHermitian_mul_conjTranspose_self C).isSelfAdjoint
  -- `K = C† P⁺ V`
  set K : Matrix A W ℂ := Cᴴ * pinv P * V with hK
  have hCK : C * K = V := by
    rw [hK, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hPdef, hCV]
    exact range_absorb V
  set Q : Matrix A A ℂ := Cᴴ * pinv P * C with hQ
  have hKK : K * Kᴴ = Q := by
    rw [hK, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, pinv_herm,
      Matrix.conjTranspose_conjTranspose]
    calc Cᴴ * pinv P * V * (Vᴴ * (pinv P * C)) = Cᴴ * (pinv P * (V * Vᴴ) * pinv P) * C := by
            simp only [Matrix.mul_assoc]
      _ = Q := by rw [← hCV, pinv_mul_mul_pinv hPsa]
  have hQQ : Q * Q = Q := by
    calc Q * Q = Cᴴ * (pinv P * (C * Cᴴ) * pinv P) * C := by
            rw [hQ]; simp only [Matrix.mul_assoc]
      _ = Q := by rw [← hPdef, pinv_mul_mul_pinv hPsa]
  have hQH : Qᴴ = Q := by
    rw [hQ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, pinv_herm,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have h1Q : (1 - Q).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (1 - Q)
    have e : (1 - Q)ᴴ * (1 - Q) = 1 - Q := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQH, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hQQ]
      abel
    rwa [e] at h
  -- the measurement (before transposition)
  let E : W → Matrix W W ℂ := fun w => Matrix.diagonal (fun w' => if w' = w then (1 : ℂ) else 0)
  have hEpsd : ∀ w, (E w).PosSemidef := by
    intro w
    refine Matrix.PosSemidef.diagonal (fun w' => ?_)
    show (0 : ℂ) ≤ if w' = w then 1 else 0
    split_ifs <;> norm_num
  have hEsum : ∑ w, E w = 1 := by
    ext a b
    simp only [E, Matrix.one_apply, Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  let Nt : W → Matrix A A ℂ := fun w => K * E w * Kᴴ + (if w = w0 then 1 - Q else 0)
  refine ⟨fun w => (Nt w)ᵀ, ⟨fun w => ?_, ?_⟩, fun w => ?_⟩
  · -- each element is positive semidefinite
    refine Matrix.PosSemidef.transpose ?_
    refine ((hEpsd w).mul_mul_conjTranspose_same K).add ?_
    split_ifs
    · exact h1Q
    · exact Matrix.PosSemidef.zero
  · -- completeness
    rw [← Matrix.transpose_sum]
    simp only [Nt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, hEsum, Matrix.mul_one, hKK]
    simp
  · -- steering
    rw [traceLeft_kron_pure, Matrix.transpose_transpose]
    show C * (K * E w * Kᴴ + (if w = w0 then 1 - Q else 0)) * Cᴴ = _
    have hcorr : C * (1 - Q) * Cᴴ = 0 := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← hKK]
      have : C * (K * Kᴴ) * Cᴴ = V * Vᴴ := by
        rw [← Matrix.mul_assoc, hCK, Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hCK]
      rw [this, ← hCV, hPdef, sub_self]
    have hmain : C * (K * E w * Kᴴ) * Cᴴ = V * E w * Vᴴ := by
      rw [show C * (K * E w * Kᴴ) * Cᴴ = (C * K) * E w * (C * K)ᴴ by
        rw [Matrix.conjTranspose_mul C K]; simp only [Matrix.mul_assoc]]
      rw [hCK]
    rw [Matrix.mul_add, Matrix.add_mul, hmain]
    split_ifs
    · rw [hcorr, add_zero]
      exact amp_mul_amp p hp.1 ψ w
    · rw [Matrix.mul_zero, Matrix.zero_mul, add_zero]
      exact amp_mul_amp p hp.1 ψ w
