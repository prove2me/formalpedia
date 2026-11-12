-- Prove2me | solution 1 for IsingVectorBalancing.Subgaussian.claim_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:25:57.783481+00:00
-- url     : https://prove2.me/submissions/8a21075c-40f9-4200-950a-77c5d950c93b

import Mathlib
import Definitions.Def_IsingVectorBalancing_Subgaussian_Law
import Theorems.Thm_IsingVectorBalancing_Subgaussian_law_well_defined

section
set_option autoImplicit false
namespace IsingVectorBalancing.Subgaussian.Dev.C8
open IsingVectorBalancing.Subgaussian

noncomputable def Zg {n d : ℕ} (v : Fin n → Vec d) (g : Configuration n → ℝ)
    (h : Fin n → ℝ) : ℝ := ∑ σ, g σ * tiltedWeight v h σ

noncomputable def L {n : ℕ} (σ : Configuration n) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin n, spin (σ i) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)

lemma L_apply {n : ℕ} (σ : Configuration n) (x : Fin n → ℝ) :
    L σ x = ∑ i, x i * spin (σ i) := by
  simp [L, mul_comm]

lemma hasFDerivAt_Zg {n d : ℕ} (v : Fin n → Vec d) (g : Configuration n → ℝ)
    (h : Fin n → ℝ) :
    HasFDerivAt (Zg v g)
      (∑ j : Fin n, Zg v (fun σ => g σ * spin (σ j)) h •
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) h := by
  have key : ∀ σ : Configuration n, HasFDerivAt (fun h' : Fin n → ℝ => g σ * tiltedWeight v h' σ)
      ((g σ * tiltedWeight v h σ) • L σ) h := by
    intro σ
    have h1 : HasFDerivAt (fun h' : Fin n → ℝ => ∑ i, h' i * spin (σ i)) (L σ) h := by
      have : (fun h' : Fin n → ℝ => ∑ i, h' i * spin (σ i)) = fun h' => L σ h' := by
        funext h'; rw [L_apply]
      rw [this]; exact (L σ).hasFDerivAt
    have h2 := (h1.exp).mul_const (weight v σ)
    have h3 := h2.const_mul (g σ)
    refine HasFDerivAt.congr_fderiv h3 ?_
    ext x
    simp [tiltedWeight, mul_assoc, mul_comm]
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun σ _ => key σ)
  have : Zg v g = fun h' => ∑ σ, g σ * tiltedWeight v h' σ := rfl
  rw [this]
  refine HasFDerivAt.congr_fderiv hs ?_
  ext x
  simp only [sum_apply, smul_apply, L_apply, Zg,
    smul_eq_mul, ContinuousLinearMap.proj_apply, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ _ => ?_
  ring


lemma partition_eq {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ) :
    partition v h = Zg v (fun _ => 1) h := by
  simp [partition, Zg]

lemma Zg_eq {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ) (hZ : 0 < partition v h)
    (f : Configuration n → ℝ) :
    Zg v f h = expectation v h f * partition v h := by
  unfold expectation probability
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  field_simp

lemma hasFDerivAt_expectation {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ)
    (hZ : 0 < partition v h) (g : Configuration n → ℝ) :
    HasFDerivAt (fun h' => expectation v h' g)
      (∑ j : Fin n, (expectation v h (fun σ => g σ * spin (σ j)) -
          expectation v h g * expectation v h (fun σ => spin (σ j))) •
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) h := by
  have hg := hasFDerivAt_Zg v g h
  have h1 := hasFDerivAt_Zg v (fun _ => 1) h
  have hne : Zg v (fun _ => 1) h ≠ 0 := by rw [← partition_eq]; exact hZ.ne'
  have hinv := (hasDerivAt_inv hne).comp_hasFDerivAt h h1
  have hm := hg.mul hinv
  have hfun : (fun h' => expectation v h' g) = fun x => Zg v g x * (Zg v (fun _ => 1) x)⁻¹ := by
    funext x
    rw [← partition_eq]
    unfold expectation probability Zg
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [hfun]
  refine HasFDerivAt.congr_fderiv hm ?_
  ext x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_sum', Pi.smul_apply, Finset.sum_apply, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.proj_apply, smul_eq_mul, Function.comp, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 := Zg_eq v h hZ g
  have e2 := Zg_eq v h hZ (fun σ => g σ * spin (σ j))
  have e3 := Zg_eq v h hZ (fun σ => 1 * spin (σ j))
  have e4 : (expectation v h fun σ => 1 * spin (σ j)) = expectation v h fun σ => spin (σ j) := by
    simp only [one_mul]
  rw [e4] at e3
  rw [← partition_eq]
  rw [e1, e2, e3]
  field_simp
  ring


lemma hasFDerivAt_log {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ)
    (hZ : 0 < partition v h) :
    HasFDerivAt (logPartition v)
      (∑ i : Fin n, expectation v h (fun σ => spin (σ i)) •
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) h := by
  have hne : Zg v (fun _ => 1) h ≠ 0 := by rw [← partition_eq]; exact hZ.ne'
  have h1 := (hasFDerivAt_Zg v (fun _ => 1) h).log hne
  have hfun : logPartition v = fun x => Real.log (Zg v (fun _ => 1) x) := by
    funext x; simp [logPartition, partition_eq]
  rw [hfun]
  refine HasFDerivAt.congr_fderiv h1 ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e3 := Zg_eq v h hZ (fun σ => 1 * spin (σ j))
  have e4 : (expectation v h fun σ => 1 * spin (σ j)) = expectation v h fun σ => spin (σ j) := by
    simp only [one_mul]
  rw [e4] at e3
  rw [← partition_eq] at hne ⊢
  rw [smul_smul, e3]
  congr 1
  field_simp

end IsingVectorBalancing.Subgaussian.Dev.C8

namespace IsingVectorBalancing.Subgaussian
open IsingVectorBalancing.Subgaussian.Dev.C8 in
theorem chk_claim_8 {n d : ℕ} (v : Fin n → Vec d) (hv : Admissible v)
    (h : Fin n → ℝ) :
    HasFDerivAt (logPartition v)
      (∑ i : Fin n, expectation v h (fun σ => spin (σ i)) •
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) h ∧
    (∀ i : Fin n,
      HasFDerivAt (fun h' : Fin n → ℝ =>
        fderiv ℝ (logPartition v) h' (Pi.single i 1))
        (∑ j : Fin n, spinCovariance v h i j •
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) h) := by
  have hZ : ∀ h, 0 < partition v h := fun h => (law_well_defined v hv h).2.1
  refine ⟨hasFDerivAt_log v h (hZ h), fun i => ?_⟩
  have hfun : (fun h' : Fin n → ℝ => fderiv ℝ (logPartition v) h' (Pi.single i 1))
      = fun h' => expectation v h' (fun σ => spin (σ i)) := by
    funext h'
    rw [(hasFDerivAt_log v h' (hZ h')).fderiv]
    simp [Pi.single_apply]
  rw [hfun]
  exact hasFDerivAt_expectation v h (hZ h) _

end IsingVectorBalancing.Subgaussian
end

theorem solution : type_of% @IsingVectorBalancing.Subgaussian.chk_claim_8 := @IsingVectorBalancing.Subgaussian.chk_claim_8
