-- Prove2me | solution 1 for GeomQM.MomentumMap.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T11:14:59.790548+00:00
-- url     : https://prove2.me/submissions/d60b3c3f-f04d-4a5d-bcac-711d6637a9e8

import Definitions.Def_GeomQM_MomentumMap_Defs
set_option autoImplicit false


open scoped BigOperators
open Matrix GeomQM.MomentumMap

namespace S06P027

noncomputable def quadDerivC {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (ψ : Fin n → ℂ) : (Fin n → ℂ) →L[ℝ] ℂ :=
  (1 / 2 : ℂ) • (∑ i : Fin n,
    (star (ψ i) • (∑ j : Fin n, A i j • ContinuousLinearMap.proj j) +
      (∑ j : Fin n, A i j * ψ j) •
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj i))))

lemma hasFDerivAt_quadFnC (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (ψ : Fin n → ℂ) : HasFDerivAt (quadFnC A) (quadDerivC A ψ) ψ := by
  unfold quadFnC quadDerivC
  apply HasFDerivAt.const_mul
  change HasFDerivAt
    (fun z : Fin n → ℂ => ∑ i, star (z i) * ∑ j, A i j * z j) _ ψ
  apply HasFDerivAt.fun_sum
  intro i _
  apply HasFDerivAt.mul
  · exact Complex.conjCLE.hasFDerivAt.comp ψ (hasFDerivAt_apply i ψ)
  · apply HasFDerivAt.fun_sum
    intro j _
    exact (hasFDerivAt_apply j ψ).const_mul (A i j)

lemma fderiv_quadFn_apply (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (ψ h : Fin n → ℂ) :
    fderiv ℝ (quadFn A) ψ h =
      ((1 / 2 : ℂ) * ∑ i : Fin n,
        (star (ψ i) * (∑ j : Fin n, A i j * h j) +
          (∑ j : Fin n, A i j * ψ j) * star (h i))).re := by
  have hd := Complex.reCLM.hasFDerivAt.comp ψ (hasFDerivAt_quadFnC n A ψ)
  change HasFDerivAt (quadFn A) _ ψ at hd
  rw [hd.fderiv]
  simp [quadDerivC, smul_eq_mul]

lemma hermitian_column (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (ψ : Fin n → ℂ) (k : Fin n) :
    (∑ i : Fin n, star (ψ i) * A i k) = star ((A *ᵥ ψ) k) := by
  simp only [Matrix.mulVec, dotProduct, star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hA.apply i k]

lemma dq_quad (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (ψ : Fin n → ℂ) (k : Fin n) :
    dq k (quadFn A) ψ = ((A *ᵥ ψ) k).re := by
  classical
  rw [dq, fderiv_quadFn_apply]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, apply_ite star, star_one, star_zero]
  rw [Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hermitian_column n A hA ψ k]
  change ((1 / 2 : ℂ) * (star ((A *ᵥ ψ) k) + (A *ᵥ ψ) k)).re = _
  simp [Complex.mul_re]
  ring

lemma dp_quad (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (ψ : Fin n → ℂ) (k : Fin n) :
    dp k (quadFn A) ψ = ((A *ᵥ ψ) k).im := by
  classical
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  rw [dp, fderiv_quadFn_apply]
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, apply_ite star, star_zero, hI]
  rw [Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, hermitian_column n A hA ψ k]
  change ((1 / 2 : ℂ) * (star ((A *ᵥ ψ) k) * Complex.I +
    ((A *ᵥ ψ) k) * -Complex.I)).re = _
  simp [Complex.mul_re]
  ring

end S06P027

set_option autoImplicit false

namespace S06P027

open Matrix GeomQM.MomentumMap

theorem trace_momentum_mul {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (ψ : Fin n → ℂ) :
    (momentumMap ψ * C).trace = star ψ ⬝ᵥ (C *ᵥ ψ) := by
  rw [momentumMap, vecMulVec_mul, trace_vecMulVec, dotProduct_comm,
    ← dotProduct_mulVec]

theorem linFn_momentumMap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (ψ : Fin n → ℂ) :
    linFn A (momentumMap ψ) = quadFn A ψ := by
  unfold linFn quadFn quadFnC
  rw [trace_momentum_mul]

theorem trace_momentum_mul_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (ψ : Fin n → ℂ) :
    (momentumMap ψ * (A * B)).trace = star (A *ᵥ ψ) ⬝ᵥ (B *ᵥ ψ) := by
  rw [trace_momentum_mul, star_mulVec, hA.eq, ← dotProduct_mulVec,
    mulVec_mulVec]

theorem trace_momentum_mul_mul_rev {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hB : B.IsHermitian) (ψ : Fin n → ℂ) :
    (momentumMap ψ * (B * A)).trace = star (star (A *ᵥ ψ) ⬝ᵥ (B *ᵥ ψ)) := by
  rw [trace_momentum_mul_mul B A hB, star_dotProduct]

theorem alpha_mul_alpha {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    alpha A * alpha B = -(A * B) := by
  simp [alpha, smul_smul]

theorem kks_momentumMap {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (ψ : Fin n → ℂ) :
    kks (momentumMap ψ) A B = (star (A *ᵥ ψ) ⬝ᵥ (B *ᵥ ψ)).im := by
  rw [kks, alpha_mul_alpha, alpha_mul_alpha, mul_sub, mul_neg, mul_neg,
    trace_sub, trace_neg, trace_neg, trace_momentum_mul_mul A B hA,
    trace_momentum_mul_mul_rev A B hB]
  norm_num [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.star_def]
  ring

theorem jordanTensor_momentumMap {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (ψ : Fin n → ℂ) :
    jordanTensor (momentumMap ψ) A B = (star (A *ᵥ ψ) ⬝ᵥ (B *ᵥ ψ)).re := by
  rw [jordanTensor, mul_add, trace_add, trace_momentum_mul_mul A B hA,
    trace_momentum_mul_mul_rev A B hB]
  norm_num [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.star_def]
  ring

end S06P027


open scoped BigOperators
open Matrix GeomQM.MomentumMap

namespace S06P027

lemma im_star_dot {n : ℕ} (u v : Fin n → ℂ) :
    (star u ⬝ᵥ v).im =
      ∑ k, ((u k).re * (v k).im - (u k).im * (v k).re) := by
  simp [dotProduct, Complex.mul_im, sub_eq_add_neg]

lemma re_star_dot {n : ℕ} (u v : Fin n → ℂ) :
    (star u ⬝ᵥ v).re =
      ∑ k, ((u k).re * (v k).re + (u k).im * (v k).im) := by
  simp [dotProduct, Complex.mul_re]

lemma poisson_of_coordinates {n : ℕ}
    (f g : (Fin n → ℂ) → ℝ) (ψ u v : Fin n → ℂ)
    (hfq : ∀ k, dq k f ψ = (u k).re)
    (hfp : ∀ k, dp k f ψ = (u k).im)
    (hgq : ∀ k, dq k g ψ = (v k).re)
    (hgp : ∀ k, dp k g ψ = (v k).im) :
    poisson f g ψ = (star u ⬝ᵥ v).im := by
  simp only [poisson, hfq, hfp, hgq, hgp, im_star_dot]

lemma metric_of_coordinates {n : ℕ}
    (f g : (Fin n → ℂ) → ℝ) (ψ u v : Fin n → ℂ)
    (hfq : ∀ k, dq k f ψ = (u k).re)
    (hfp : ∀ k, dp k f ψ = (u k).im)
    (hgq : ∀ k, dq k g ψ = (v k).re)
    (hgp : ∀ k, dp k g ψ = (v k).im) :
    metricG f g ψ = (star u ⬝ᵥ v).re := by
  simp only [metricG, hfq, hfp, hgq, hgp, re_star_dot]

end S06P027


open Matrix GeomQM.MomentumMap

theorem solution (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (ψ : Fin n → ℂ) :
    linFn A (momentumMap ψ) = quadFn A ψ ∧
    poisson (quadFn A) (quadFn B) ψ = kks (momentumMap ψ) A B ∧
    metricG (quadFn A) (quadFn B) ψ = jordanTensor (momentumMap ψ) A B := by
  refine ⟨S06P027.linFn_momentumMap A ψ, ?_, ?_⟩
  · rw [S06P027.kks_momentumMap A B hA hB ψ]
    exact S06P027.poisson_of_coordinates (quadFn A) (quadFn B) ψ
      (A *ᵥ ψ) (B *ᵥ ψ)
      (S06P027.dq_quad n A hA ψ) (S06P027.dp_quad n A hA ψ)
      (S06P027.dq_quad n B hB ψ) (S06P027.dp_quad n B hB ψ)
  · rw [S06P027.jordanTensor_momentumMap A B hA hB ψ]
    exact S06P027.metric_of_coordinates (quadFn A) (quadFn B) ψ
      (A *ᵥ ψ) (B *ᵥ ψ)
      (S06P027.dq_quad n A hA ψ) (S06P027.dp_quad n A hA ψ)
      (S06P027.dq_quad n B hB ψ) (S06P027.dp_quad n B hB ψ)

#print axioms solution
