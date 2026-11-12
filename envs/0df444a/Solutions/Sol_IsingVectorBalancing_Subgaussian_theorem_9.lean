-- Prove2me | solution 1 for IsingVectorBalancing.Subgaussian.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:25:58.767416+00:00
-- url     : https://prove2.me/submissions/e8779977-c397-40ad-b0e8-b045dbf1122d

import Mathlib
import Definitions.Def_IsingVectorBalancing_Subgaussian_Law
import Theorems.Thm_IsingVectorBalancing_Subgaussian_claim_8
import Theorems.Thm_IsingVectorBalancing_Subgaussian_lemma_7
import Theorems.Thm_IsingVectorBalancing_Subgaussian_law_well_defined

section
set_option autoImplicit false
namespace IsingVectorBalancing.Subgaussian.Dev.T9
open IsingVectorBalancing.Subgaussian

/-- abstract variance identity -/
lemma var_abstract {n : ℕ} (C : Type*) [Fintype C] (p : C → ℝ) (hp : ∑ c, p c = 1)
    (s : Fin n → C → ℝ) (φ : Fin n → ℝ) :
    ∑ c, p c * ((∑ i, φ i * s i c) - ∑ c', p c' * (∑ i, φ i * s i c'))^2 =
      ∑ i, φ i * ∑ j, ((∑ c, p c * (s i c * s j c)) -
        (∑ c, p c * s i c) * (∑ c, p c * s j c)) * φ j := by
  set m : Fin n → ℝ := fun i => ∑ c, p c * s i c with hm
  have h1 : ∀ c, (∑ i, φ i * s i c) - ∑ c', p c' * (∑ i, φ i * s i c')
      = ∑ i, φ i * (s i c - m i) := by
    intro c
    have : ∑ c', p c' * (∑ i, φ i * s i c') = ∑ i, φ i * m i := by
      simp only [hm, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c' _ => by ring
    rw [this]; simp only [mul_sub, Finset.sum_sub_distrib]
  have key : ∀ i j : Fin n, ∑ c, p c * (s i c * s j c) - m i * m j
      = ∑ c, p c * ((s i c - m i) * (s j c - m j)) := by
    intro i j
    have e : ∀ c, p c * ((s i c - m i) * (s j c - m j)) =
        p c * (s i c * s j c) - m j * (p c * s i c) - m i * (p c * s j c) + m i * m j * p c := by
      intro c; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp]
    simp only [hm]
    ring
  have key2 : ∀ i j : Fin n, ((∑ c, p c * (s i c * s j c)) -
        (∑ c, p c * s i c) * (∑ c, p c * s j c)) = ∑ c, p c * ((s i c - m i) * (s j c - m j)) :=
    fun i j => key i j
  rw [Finset.sum_congr rfl (fun i _ => congrArg (fun t => φ i * t)
    (Finset.sum_congr rfl (fun j _ => congrArg (fun t => t * φ j) (key2 i j))))]
  simp only [h1, sq, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring


lemma inner_signedSum {n d : ℕ} (v : Fin n → Vec d) (θ : Vec d) (σ : Configuration n) :
    inner ℝ θ (signedSum v σ) = ∑ i, inner ℝ θ (v i) * spin (σ i) := by
  simp [signedSum, inner_sum, inner_smul_right, mul_comm]

lemma Q_eq_var {n d : ℕ} (v : Fin n → Vec d) (hv : Admissible v) (h : Fin n → ℝ) (θ : Vec d) :
    ∑ i, inner ℝ θ (v i) * ∑ j, spinCovariance v h i j * inner ℝ θ (v j)
      = variance v h (fun σ => inner ℝ θ (signedSum v σ)) := by
  have hp := (law_well_defined v hv h).2.2.2
  have := var_abstract (Configuration n) (probability v h) hp
    (fun i σ => spin (σ i)) (fun i => inner ℝ θ (v i))
  simp only [variance, expectation, inner_signedSum, spinCovariance]
  rw [← this]


lemma fderiv_single {n d : ℕ} (v : Fin n → Vec d) (hv : Admissible v) (h' : Fin n → ℝ)
    (i : Fin n) :
    fderiv ℝ (logPartition v) h' (Pi.single i 1) = expectation v h' (fun σ => spin (σ i)) := by
  rw [(claim_8 v hv h').1.fderiv]
  simp [Pi.single_apply]

lemma main_ineq {n d : ℕ} (v : Fin n → Vec d) (hv : Admissible v) (h : Fin n → ℝ) (θ : Vec d) :
    logPartition v (fun i => h i + inner ℝ θ (v i)) - logPartition v h ≤
      ∑ i, inner ℝ θ (v i) * expectation v h (fun σ => spin (σ i)) + ‖θ‖ ^ 2 / 2 := by
  set φ : Fin n → ℝ := fun i => inner ℝ θ (v i) with hφ
  set γ : ℝ → Fin n → ℝ := fun t i => h i + t * φ i with hγdef
  have hγ : ∀ t, HasDerivAt γ φ t := by
    intro t
    rw [hasDerivAt_pi]
    intro i
    have := ((hasDerivAt_id t).mul_const (φ i)).const_add (h i)
    simpa only [id, one_mul] using this
  set f : ℝ → ℝ := fun t => logPartition v (γ t) with hf
  set D : ℝ → ℝ := fun t => ∑ i, φ i * expectation v (γ t) (fun σ => spin (σ i)) with hD
  have hf' : ∀ t, HasDerivAt f (D t) t := by
    intro t
    have := ((claim_8 v hv (γ t)).1).comp_hasDerivAt t (hγ t)
    refine HasDerivAt.congr_deriv this ?_
    simp [hD, mul_comm]
  set Q : ℝ → ℝ := fun t => ∑ i, φ i * ∑ j, spinCovariance v (γ t) i j * φ j with hQ
  have hD' : ∀ t, HasDerivAt D (Q t) t := by
    intro t
    have hfun : D = fun t => ∑ i, φ i * fderiv ℝ (logPartition v) (γ t) (Pi.single i 1) := by
      funext t; simp only [hD, fderiv_single v hv]
    rw [hfun]
    have hi : ∀ i : Fin n, HasDerivAt
        (fun t => φ i * fderiv ℝ (logPartition v) (γ t) (Pi.single i 1))
        (φ i * ∑ j, spinCovariance v (γ t) i j * φ j) t := by
      intro i
      have := (((claim_8 v hv (γ t)).2 i).comp_hasDerivAt t (hγ t)).const_mul (φ i)
      refine HasDerivAt.congr_deriv this ?_
      simp [mul_comm]
    exact HasDerivAt.fun_sum (fun i _ => hi i)
  have hQle : ∀ t, Q t ≤ ‖θ‖ ^ 2 := by
    intro t
    have := lemma_7 v hv (γ t) θ
    rw [← Q_eq_var v hv (γ t) θ] at this
    exact this
  set g : ℝ → ℝ := fun t => f t - ‖θ‖ ^ 2 * t ^ 2 / 2 with hg
  set g' : ℝ → ℝ := fun t => D t - ‖θ‖ ^ 2 * t with hg'
  have hg1 : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have := (hf' t).sub (((hasDerivAt_pow 2 t).const_mul (‖θ‖ ^ 2)).div_const 2)
    refine HasDerivAt.congr_deriv this ?_
    simp only [hg']; ring
  have hg2 : ∀ t, HasDerivAt g' (Q t - ‖θ‖ ^ 2) t := by
    intro t
    have := (hD' t).sub ((hasDerivAt_id t).const_mul (‖θ‖ ^ 2))
    exact HasDerivAt.congr_deriv this (by simp)
  have hanti : Antitone g' := by
    refine antitone_of_deriv_nonpos (fun t => (hg2 t).differentiableAt) (fun t => ?_)
    rw [(hg2 t).deriv]; linarith [hQle t]
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope g g' (by norm_num : (0:ℝ) < 1)
    (fun t _ => (hg1 t).continuousAt.continuousWithinAt) (fun t _ => hg1 t)
  have h0 : g' c ≤ g' 0 := hanti hc.1.le
  have h1 : g 1 - g 0 ≤ g' 0 := by
    have : g 1 - g 0 = g' c := by rw [hceq]; ring
    linarith
  have e1 : g 1 = logPartition v (fun i => h i + inner ℝ θ (v i)) - ‖θ‖ ^ 2 / 2 := by
    simp [hg, hf, hγdef, hφ]
  have e0 : g 0 = logPartition v h := by
    simp [hg, hf, hγdef]
  have e2 : g' 0 = ∑ i, inner ℝ θ (v i) * expectation v h (fun σ => spin (σ i)) := by
    simp [hg', hD, hγdef]
    rfl
  rw [e1, e0, e2] at h1
  linarith


lemma exp_expect_eq {n d : ℕ} (v : Fin n → Vec d) (hv : Admissible v) (h : Fin n → ℝ) (θ : Vec d) :
    expectation v h (fun σ => Real.exp (inner ℝ θ (signedSum v σ - meanSum v h))) =
      Real.exp (-(∑ i, inner ℝ θ (v i) * expectation v h (fun σ => spin (σ i)))) *
        (partition v (fun i => h i + inner ℝ θ (v i)) / partition v h) := by
  set φ : Fin n → ℝ := fun i => inner ℝ θ (v i) with hφ
  have hmean : inner ℝ θ (meanSum v h) =
      ∑ i, φ i * expectation v h (fun σ => spin (σ i)) := by
    simp only [meanSum, inner_sum, inner_smul_right, inner_signedSum, expectation, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun σ _ => by ring
  have hZ := (law_well_defined v hv h).2.1
  have hshift : ∀ σ, tiltedWeight v h σ * Real.exp (inner ℝ θ (signedSum v σ)) =
      tiltedWeight v (fun i => h i + φ i) σ := by
    intro σ
    simp only [tiltedWeight, inner_signedSum, add_mul, Finset.sum_add_distrib, Real.exp_add]
    ring
  have : ∀ σ, probability v h σ * Real.exp (inner ℝ θ (signedSum v σ - meanSum v h)) =
      Real.exp (-(∑ i, φ i * expectation v h (fun σ => spin (σ i)))) *
        (tiltedWeight v (fun i => h i + φ i) σ / partition v h) := by
    intro σ
    rw [inner_sub_right, hmean, sub_eq_add_neg, Real.exp_add, ← hshift σ]
    unfold probability
    ring
  unfold expectation
  rw [Finset.sum_congr rfl (fun σ _ => this σ), ← Finset.mul_sum, ← Finset.sum_div]
  rfl

end IsingVectorBalancing.Subgaussian.Dev.T9

namespace IsingVectorBalancing.Subgaussian
open IsingVectorBalancing.Subgaussian.Dev.T9 in
theorem chk_theorem_9 {n d : ℕ} (v : Fin n → Vec d) (hv : Admissible v)
    (h : Fin n → ℝ) (θ : Vec d) :
    expectation v h (fun σ => Real.exp (inner ℝ θ (signedSum v σ - meanSum v h))) ≤
      Real.exp (‖θ‖ ^ 2 / 2) := by
  rw [exp_expect_eq v hv h θ]
  have hZ := (law_well_defined v hv h).2.1
  have hZ1 := (law_well_defined v hv (fun i => h i + inner ℝ θ (v i))).2.1
  have hmain := main_ineq v hv h θ
  have hratio : partition v (fun i => h i + inner ℝ θ (v i)) / partition v h =
      Real.exp (logPartition v (fun i => h i + inner ℝ θ (v i)) - logPartition v h) := by
    unfold logPartition
    rw [Real.exp_sub, Real.exp_log hZ1, Real.exp_log hZ]
  rw [hratio, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end IsingVectorBalancing.Subgaussian
end

theorem solution : type_of% @IsingVectorBalancing.Subgaussian.chk_theorem_9 := @IsingVectorBalancing.Subgaussian.chk_theorem_9
