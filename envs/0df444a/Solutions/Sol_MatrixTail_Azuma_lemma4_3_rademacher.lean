-- Prove2me | solution 1 for MatrixTail.Azuma.lemma4_3_rademacher
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:57:31.632217+00:00
-- url     : https://prove2.me/submissions/f7ce251c-572c-42f7-af7e-a45839f35e1d

import Mathlib
import Definitions.Def_MatrixTail_Azuma_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal
open MatrixTail.Azuma

theorem mta_mexp_smul {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (c : ℝ) :
    mexp (c • A) = cfc (fun x : ℝ => Real.exp (c * x)) A := by
  have hA' : IsSelfAdjoint A := hA
  unfold mexp
  rw [← cfc_comp_smul c Real.exp A]
  simp [smul_eq_mul]

theorem mta_cosh_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (θ : ℝ) :
    (1 / 2 : ℝ) • (mexp (θ • A) + mexp ((-θ) • A)) ≤ mexp ((θ ^ 2 / 2) • A ^ 2) := by
  have hA' : IsSelfAdjoint A := hA
  rw [mta_mexp_smul A hA, mta_mexp_smul A hA]
  have c1 : Continuous (fun x : ℝ => Real.exp (θ * x)) := by fun_prop
  have c2 : Continuous (fun x : ℝ => Real.exp (-θ * x)) := by fun_prop
  have e1 : (1 / 2 : ℝ) • (cfc (fun x : ℝ => Real.exp (θ * x)) A + cfc (fun x : ℝ => Real.exp (-θ * x)) A) =
      cfc (fun x : ℝ => 1 / 2 * (Real.exp (θ * x) + Real.exp (-θ * x))) A := by
    rw [cfc_const_mul (1 / 2) (fun x : ℝ => Real.exp (θ * x) + Real.exp (-θ * x)) A
      (c1.add c2).continuousOn,
      cfc_add A (fun x : ℝ => Real.exp (θ * x)) (fun x : ℝ => Real.exp (-θ * x)) c1.continuousOn c2.continuousOn]
  have c3 : Continuous (fun x : ℝ => x ^ 2) := by fun_prop
  have c4 : Continuous (fun x : ℝ => θ ^ 2 / 2 * x ^ 2) := by fun_prop
  have e2 : mexp ((θ ^ 2 / 2) • A ^ 2) = cfc (fun x : ℝ => Real.exp (θ ^ 2 / 2 * x ^ 2)) A := by
    unfold mexp
    have h1 : (θ ^ 2 / 2) • A ^ 2 = cfc (fun x : ℝ => θ ^ 2 / 2 * x ^ 2) A := by
      rw [cfc_const_mul (θ ^ 2 / 2) (fun x : ℝ => x ^ 2) A c3.continuousOn, cfc_pow_id A 2]
    rw [h1, ← cfc_comp Real.exp (fun x : ℝ => θ ^ 2 / 2 * x ^ 2) A hA' Real.continuous_exp.continuousOn c4.continuousOn]
    rfl
  rw [e1, e2]
  refine cfc_mono (fun x _ => ?_) (c1.add c2 |>.const_mul (1/2) |>.continuousOn) (by fun_prop : Continuous (fun x : ℝ => Real.exp (θ ^ 2 / 2 * x ^ 2))).continuousOn
  have := Real.cosh_le_exp_half_sq (θ * x)
  rw [Real.cosh_eq] at this
  have h2 : (θ * x) ^ 2 / 2 = θ ^ 2 / 2 * x ^ 2 := by ring
  rw [h2] at this
  have h3 : -θ * x = -(θ * x) := by ring
  rw [h3]
  linarith

theorem mta_mean_rad {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (ε : Ω → ℝ) (hε : IsRademacher P ε) (θ : ℝ) :
    mean P (fun ω => mexp ((ε ω * θ) • A)) = (1 / 2 : ℝ) • (mexp (θ • A) + mexp ((-θ) • A)) := by
  obtain ⟨hεm, hp1, hp2⟩ := hε
  have hS1 : MeasurableSet {ω | ε ω = 1} := hεm (measurableSet_singleton 1)
  have hS2 : MeasurableSet {ω | ε ω = -1} := hεm (measurableSet_singleton (-1))
  have hdisj : Disjoint {ω | ε ω = 1} {ω | ε ω = -1} := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    rw [h1] at h2; norm_num at h2
  have hae : ∀ᵐ ω ∂P, ω ∈ {ω | ε ω = 1} ∪ {ω | ε ω = -1} := by
    have hU : P ({ω | ε ω = 1} ∪ {ω | ε ω = -1}) = 1 := by
      have h := measureReal_union hdisj hS2 (μ := P)
      rw [hp1, hp2] at h
      have h1 : P.real ({ω | ε ω = 1} ∪ {ω | ε ω = -1}) = 1 := by rw [h]; norm_num
      have := (ENNReal.toReal_eq_one_iff _).mp h1
      exact this
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff (hS1.union hS2)).mpr hU
  ext i j
  have hrhs : ((1 / 2 : ℝ) • (mexp (θ • A) + mexp ((-θ) • A))) i j =
      (1 / 2 : ℝ) • (mexp (θ • A) i j + mexp ((-θ) • A) i j) := by simp
  rw [hrhs]
  unfold mean
  simp only [Matrix.of_apply]
  have hF : (fun ω => mexp ((ε ω * θ) • A) i j) =ᵐ[P]
      fun ω => {ω | ε ω = 1}.indicator (fun _ => mexp (θ • A) i j) ω +
        {ω | ε ω = -1}.indicator (fun _ => mexp ((-θ) • A) i j) ω := by
    filter_upwards [hae] with ω hω
    rcases hω with h | h
    · have h' : ε ω = 1 := h
      have h2 : ω ∉ {ω | ε ω = -1} := by
        intro h3; simp only [Set.mem_setOf_eq] at h3; rw [h'] at h3; norm_num at h3
      rw [Set.indicator_of_mem h, Set.indicator_of_notMem h2, h']
      simp
    · have h' : ε ω = -1 := h
      have h2 : ω ∉ {ω | ε ω = 1} := by
        intro h3; simp only [Set.mem_setOf_eq] at h3; rw [h'] at h3; norm_num at h3
      rw [Set.indicator_of_mem h, Set.indicator_of_notMem h2, h']
      simp
  rw [integral_congr_ae hF, integral_add ((integrable_const _).indicator hS1) ((integrable_const _).indicator hS2),
    integral_indicator_const _ hS1, integral_indicator_const _ hS2, hp1, hp2]
  simp

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (ε : Ω → ℝ) (hε : IsRademacher P ε)
    (θ : ℝ) :
    mean P (fun ω => mexp ((ε ω * θ) • A)) ≤ mexp ((θ ^ 2 / 2) • A ^ 2) := by
  rw [mta_mean_rad P A ε hε θ]
  exact mta_cosh_le A hA θ
