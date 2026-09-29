-- Prove2me | solution 1 for MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/21912cc0-2a7b-5b0a-b3f4-59e70eca5463

import Mathlib
import Theorems.Thm_Complex_exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add
import Theorems.Thm_Real_exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le
import Theorems.Thm_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic
import Theorems.Thm_MeasureTheory_exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le

set_option autoImplicit false

open MeasureTheory Set

namespace K2Asm

lemma abs_fst_le (p : ℝ × ℝ) : |p.1| ≤ ‖p‖ := by
  rw [Prod.norm_def, Real.norm_eq_abs]; exact le_max_left _ _

lemma abs_snd_le (p : ℝ × ℝ) : |p.2| ≤ ‖p‖ := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_right _ _

lemma sq_fst_le (p : ℝ × ℝ) : p.1 ^ 2 ≤ ‖p‖ ^ 2 := by
  calc p.1 ^ 2 = |p.1| ^ 2 := (sq_abs _).symm
    _ ≤ ‖p‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_fst_le p) 2

lemma sq_snd_le (p : ℝ × ℝ) : p.2 ^ 2 ≤ ‖p‖ ^ 2 := by
  calc p.2 ^ 2 = |p.2| ^ 2 := (sq_abs _).symm
    _ ≤ ‖p‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_snd_le p) 2

lemma norm_le_of_abs_le {p : ℝ × ℝ} {a : ℝ} (h1 : |p.1| ≤ a) (h2 : |p.2| ≤ a) : ‖p‖ ≤ a := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact max_le h1 h2

noncomputable def φ (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

lemma φ_contDiff : ContDiff ℝ (⊤ : ℕ∞) φ := by
  unfold φ
  exact Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

lemma φ_of_le_one {t : ℝ} (ht : t ≤ 1) : φ t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma φ_of_two_le {t : ℝ} (ht : 2 ≤ t) : φ t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

noncomputable def ψ (u : ℝ) : ℝ := φ (32 * u ^ 2)

lemma ψ_contDiff : ContDiff ℝ (⊤ : ℕ∞) ψ := by
  unfold ψ; exact φ_contDiff.comp (by fun_prop)

lemma ψ_eq_one {u : ℝ} (hu : |u| ≤ 1 / 6) : ψ u = 1 := by
  unfold ψ; apply φ_of_le_one
  have : u ^ 2 ≤ (1 / 6) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hu 2
  nlinarith

lemma ψ_eq_zero {u : ℝ} (hu : 1 / 4 ≤ |u|) : ψ u = 0 := by
  unfold ψ; apply φ_of_two_le
  have : (1 / 4) ^ 2 ≤ u ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num) hu 2
    rwa [sq_abs] at h
  nlinarith

noncomputable def χt (θ : ℝ) : ℝ := φ (8 * (1 - Real.cos (2 * Real.pi * θ)))

lemma χt_contDiff : ContDiff ℝ (⊤ : ℕ∞) χt := by
  unfold χt; exact φ_contDiff.comp (by fun_prop)

lemma χt_add_one (θ : ℝ) : χt (θ + 1) = χt θ := by
  unfold χt
  have : 2 * Real.pi * (θ + 1) = 2 * Real.pi * θ + 2 * Real.pi := by ring
  rw [this, Real.cos_add_two_pi]

lemma χt_add_int (θ : ℝ) (k : ℤ) : χt (θ + k) = χt θ := by
  unfold χt
  have : 2 * Real.pi * (θ + k) = 2 * Real.pi * θ + k * (2 * Real.pi) := by ring
  rw [this, Real.cos_add_int_mul_two_pi]

lemma χt_eq_one_of_near_int {θ : ℝ} (k : ℤ) (h : |θ - k| ≤ 1 / 16) : χt θ = 1 := by
  have hθ : θ = (θ - k) + k := by ring
  rw [hθ, χt_add_int]
  set u := θ - k with hu
  unfold χt; apply φ_of_le_one
  have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * u)
  have hπ := Real.pi_lt_four
  have hπ0 := Real.pi_pos
  have hu2 : u ^ 2 ≤ (1 / 16) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have : (2 * Real.pi * u) ^ 2 ≤ 1 / 4 := by
    have h1 : (2 * Real.pi) ^ 2 ≤ 64 := by nlinarith
    calc (2 * Real.pi * u) ^ 2 = (2 * Real.pi) ^ 2 * u ^ 2 := by ring
      _ ≤ 64 * (1 / 16) ^ 2 := mul_le_mul h1 hu2 (sq_nonneg _) (by norm_num)
      _ = 1 / 4 := by norm_num
  linarith

lemma χt_eq_zero_of_mem {θ : ℝ} (h1 : 1 / 6 ≤ |θ|) (h2 : |θ| ≤ 1 / 2) : χt θ = 0 := by
  unfold χt; apply φ_of_two_le
  have hcos : Real.cos (2 * Real.pi * θ) ≤ 1 / 2 := by
    have : Real.cos (2 * Real.pi * θ) = Real.cos (2 * Real.pi * |θ|) := by
      rcases abs_choice θ with h | h
      · rw [h]
      · rw [h, mul_neg, Real.cos_neg]
    rw [this, ← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  linarith

noncomputable def Ψ (p : ℝ × ℝ) : ℝ := ψ p.1 * χt p.2

lemma Ψ_contDiff : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
  unfold Ψ
  exact (ψ_contDiff.comp contDiff_fst).mul (χt_contDiff.comp contDiff_snd)

lemma Ψ_add_one (p : ℝ × ℝ) : Ψ (p.1, p.2 + 1) = Ψ p := by
  unfold Ψ; simp only [χt_add_one]

lemma Ψ_eq_one_of_near {p : ℝ × ℝ} (k : ℤ) (h1 : |p.1| < 1 / 16) (h2 : |p.2 - k| < 1 / 16) :
    Ψ p = 1 := by
  unfold Ψ
  rw [ψ_eq_one (by linarith), χt_eq_one_of_near_int k h2.le, mul_one]

noncomputable def W (p : ℝ × ℝ) : ℝ := ψ p.1 * (χt p.2 * ψ p.2)

lemma W_contDiff : ContDiff ℝ (⊤ : ℕ∞) W := by
  unfold W
  exact (ψ_contDiff.comp contDiff_fst).mul
    ((χt_contDiff.comp contDiff_snd).mul (ψ_contDiff.comp contDiff_snd))

lemma W_eq_zero_of_le {p : ℝ × ℝ} (hp : 1 / 4 ≤ ‖p‖) : W p = 0 := by
  unfold W
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, le_max_iff] at hp
  rcases hp with h | h
  · rw [ψ_eq_zero h, zero_mul]
  · rw [ψ_eq_zero h, mul_zero, mul_zero]

lemma W_eq_zero_of_snd {p : ℝ × ℝ} (hp : 1 / 4 ≤ |p.2|) : W p = 0 := by
  unfold W; rw [ψ_eq_zero hp, mul_zero, mul_zero]

lemma W_eq_Ψ {p : ℝ × ℝ} (hp : |p.2| ≤ 1 / 2) : W p = Ψ p := by
  unfold W Ψ
  by_cases h6 : |p.2| ≤ 1 / 6
  · rw [ψ_eq_one h6, mul_one]
  · push Not at h6
    rw [χt_eq_zero_of_mem h6.le hp, zero_mul, mul_zero]

lemma W_hasCompactSupport : HasCompactSupport W := by
  apply HasCompactSupport.intro (K := Metric.closedBall (0 : ℝ × ℝ) 1) (isCompact_closedBall _ _)
  intro p hp
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hp
  exact W_eq_zero_of_le (by linarith)

noncomputable def ψ₂ (p : ℝ × ℝ) : ℝ := φ (8 * p.2 ^ 2)

lemma ψ₂_contDiff : ContDiff ℝ (⊤ : ℕ∞) ψ₂ := by
  unfold ψ₂; exact φ_contDiff.comp (by fun_prop)

lemma ψ₂_eq_one {p : ℝ × ℝ} (hp : ‖p‖ < 1 / 3) : ψ₂ p = 1 := by
  unfold ψ₂; apply φ_of_le_one
  have h := abs_snd_le p
  have : p.2 ^ 2 ≤ (1 / 3) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
  nlinarith

lemma ψ₂_eq_zero {p : ℝ × ℝ} (hp : 1 / 2 ≤ |p.2|) : ψ₂ p = 0 := by
  unfold ψ₂; apply φ_of_two_le
  have : (1 / 2) ^ 2 ≤ p.2 ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num) hp 2
    rwa [sq_abs] at h
  nlinarith

noncomputable def zC (p : ℝ × ℝ) : ℂ := (p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ)

noncomputable def γ (p : ℝ × ℝ) : ℝ :=
  ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖ ^ 2 *
    Real.log ‖(1 : ℂ) - Complex.exp ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ))‖

lemma γ_apply (x θ : ℝ) : γ (x, θ) =
    ‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ ^ 2 *
      Real.log ‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ := rfl

noncomputable def s (p : ℝ × ℝ) : ℝ := 1 / 4 * p.1 ^ 2 + 4 * Real.pi ^ 2 * p.2 ^ 2

noncomputable def L (p : ℝ × ℝ) : ℝ := s p * Real.log (s p)

lemma s_eq (p : ℝ × ℝ) : p.1 ^ 2 / 4 + 4 * Real.pi ^ 2 * p.2 ^ 2 = s p := by
  unfold s; ring

lemma s_nonneg (p : ℝ × ℝ) : 0 ≤ s p := by unfold s; positivity

lemma s_zero : s 0 = 0 := by simp [s]

lemma s_le (p : ℝ × ℝ) : s p ≤ (1 / 4 + 4 * Real.pi ^ 2) * ‖p‖ ^ 2 := by
  unfold s
  have h1 := sq_fst_le p
  have h2 := sq_snd_le p
  have hπ : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  nlinarith

lemma s_contDiff : ContDiff ℝ (⊤ : ℕ∞) s := by
  unfold s; fun_prop

lemma zC_continuous : Continuous zC := by
  unfold zC; fun_prop

lemma exp_zC_add_one (p : ℝ × ℝ) : Complex.exp (zC (p.1, p.2 + 1)) = Complex.exp (zC p) := by
  unfold zC
  have : (((p.1, p.2 + 1) : ℝ × ℝ).1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (((p.1, p.2 + 1) : ℝ × ℝ).2 : ℝ)
      = ((p.1 / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 : ℝ)) + 2 * Real.pi * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_periodic]

lemma γ_eq_zC (p : ℝ × ℝ) : γ p =
    ‖(1 : ℂ) - Complex.exp (zC p)‖ ^ 2 * Real.log ‖(1 : ℂ) - Complex.exp (zC p)‖ := rfl

lemma γ_add_one (p : ℝ × ℝ) : γ (p.1, p.2 + 1) = γ p := by
  rw [γ_eq_zC, γ_eq_zC, exp_zC_add_one]

lemma γ_continuous : Continuous γ := by
  have hn : Continuous fun p : ℝ × ℝ => ‖(1 : ℂ) - Complex.exp (zC p)‖ :=
    (continuous_const.sub (Complex.continuous_exp.comp zC_continuous)).norm
  have h := hn.mul (Real.continuous_mul_log.comp hn)
  have : γ = fun p => ‖(1 : ℂ) - Complex.exp (zC p)‖ *
      (‖(1 : ℂ) - Complex.exp (zC p)‖ * Real.log ‖(1 : ℂ) - Complex.exp (zC p)‖) := by
    funext p; rw [γ_eq_zC]; ring
  rw [this]; exact h

def strip : Set (ℝ × ℝ) := {p : ℝ × ℝ | |p.2| < 1 / 2}

lemma isOpen_strip : IsOpen strip :=
  isOpen_lt (continuous_abs.comp continuous_snd) continuous_const

def regSet : Set (ℝ × ℝ) := {p : ℝ × ℝ | Complex.exp (zC p) ≠ 1}

lemma isOpen_regSet : IsOpen regSet :=
  isOpen_ne_fun (Complex.continuous_exp.comp zC_continuous) continuous_const

theorem structT :
    ∃ a b : ℝ × ℝ → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) a strip ∧ ContDiffOn ℝ (⊤ : ℕ∞) b strip ∧
      (∀ p : ℝ × ℝ, |p.2| < 1 / 2 → 0 < a p) ∧
      (∀ p : ℝ × ℝ, |p.2| < 1 / 2 → γ p = a p * L p + s p * b p) ∧
      (∀ p : ℝ × ℝ, Complex.exp (zC p) = 1 ↔ p.1 = 0 ∧ ∃ k : ℤ, p.2 = k) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) γ regSet := by
  obtain ⟨a, b, ha, hb, hpos, heq, hzero, hsm⟩ :=
    Complex.exists_contDiffOn_norm_one_sub_exp_sq_mul_log_eq_mul_add
  refine ⟨a, b, ha, hb, hpos, fun p hp => ?_, hzero, hsm⟩
  rw [γ, heq p hp, s_eq, L]

noncomputable def aS : ℝ × ℝ → ℝ := structT.choose

noncomputable def bS : ℝ × ℝ → ℝ := structT.choose_spec.choose

lemma aS_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) aS strip := structT.choose_spec.choose_spec.1
lemma bS_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) bS strip := structT.choose_spec.choose_spec.2.1
lemma γ_eq_of_strip {p : ℝ × ℝ} (hp : |p.2| < 1 / 2) : γ p = aS p * L p + s p * bS p :=
  structT.choose_spec.choose_spec.2.2.2.1 p hp
lemma exp_zC_eq_one_iff (p : ℝ × ℝ) : Complex.exp (zC p) = 1 ↔ p.1 = 0 ∧ ∃ k : ℤ, p.2 = k :=
  structT.choose_spec.choose_spec.2.2.2.2.1 p
lemma γ_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) γ regSet := structT.choose_spec.choose_spec.2.2.2.2.2

theorem logGermT : ∃ C : ℝ, 0 ≤ C ∧ ContDiffOn ℝ (⊤ : ℕ∞) L {p : ℝ × ℝ | p ≠ 0} ∧
    ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 →
      ‖p‖ ^ n * ‖iteratedFDeriv ℝ n L p‖ ≤ C * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|) :=
  Real.exists_forall_norm_pow_mul_norm_iteratedFDeriv_mul_log_quadratic_le (1 / 4) (4 * Real.pi ^ 2)
    (by norm_num) (by positivity)

noncomputable def CL : ℝ := logGermT.choose

lemma CL_nonneg : 0 ≤ CL := logGermT.choose_spec.1
lemma L_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) L {p : ℝ × ℝ | p ≠ 0} := logGermT.choose_spec.2.1
lemma L_bound (n : ℕ) (hn : n ≤ 4) (p : ℝ × ℝ) (hp : p ≠ 0) :
    ‖p‖ ^ n * ‖iteratedFDeriv ℝ n L p‖ ≤ CL * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|) :=
  logGermT.choose_spec.2.2 n hn p hp

lemma eq_of_exp_zC_eq_one {p : ℝ × ℝ} (h : Complex.exp (zC p) = 1) :
    p.1 = 0 ∧ ∃ k : ℤ, p.2 = k := (exp_zC_eq_one_iff p).1 h

lemma mem_regSet_of_ne_zero_of_strip {p : ℝ × ℝ} (hp : p ≠ 0) (hs : |p.2| < 1 / 2) :
    p ∈ regSet := by
  intro h
  obtain ⟨h1, k, hk⟩ := eq_of_exp_zC_eq_one h
  have hk0 : (k : ℝ) = 0 := by
    rw [hk] at hs
    have : |(k : ℝ)| < 1 := by linarith
    rw [← Int.cast_abs] at this
    have hk1 : |k| < 1 := by exact_mod_cast this
    have : k = 0 := by
      rcases abs_lt.1 hk1 with ⟨h1, h2⟩
      omega
    simp [this]
  apply hp
  ext
  · exact h1
  · rw [hk, hk0]; rfl

lemma natCast_le_top (i : ℕ) : (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

lemma exists_bound_of_contDiffOn (f : ℝ × ℝ → ℝ) {S K : Set (ℝ × ℝ)} (hS : IsOpen S)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f S) (hK : IsCompact K) (hKS : K ⊆ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ℕ, i ≤ 4 → ∀ q ∈ K, ‖iteratedFDeriv ℝ i f q‖ ≤ C := by
  have hb : ∀ i : ℕ, ∃ C, ∀ q ∈ K, ‖iteratedFDeriv ℝ i f q‖ ≤ C := by
    intro i
    have hc : ContinuousOn (iteratedFDerivWithin ℝ i f S) K :=
      (hf.continuousOn_iteratedFDerivWithin (natCast_le_top i) hS.uniqueDiffOn).mono hKS
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨C, fun q hq => ?_⟩
    rw [← iteratedFDerivWithin_of_isOpen i hS (hKS hq)]
    exact hC q hq
  choose C hC using hb
  refine ⟨∑ k ∈ Finset.range 5, |C k|,
    Finset.sum_nonneg (fun j _ => abs_nonneg (C j)), fun i hi q hq => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ i f q‖ ≤ |C i| := (hC i q hq).trans (le_abs_self _)
  have h2 : |C i| ≤ ∑ j ∈ Finset.range 5, |C j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_range.2 (by omega))
  linarith

lemma exists_bound_of_hasCompactSupport (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ℕ, i ≤ 4 → ∀ q : ℝ × ℝ, ‖iteratedFDeriv ℝ i f q‖ ≤ C := by
  have hb : ∀ i : ℕ, ∃ C, ∀ q : ℝ × ℝ, ‖iteratedFDeriv ℝ i f q‖ ≤ C := by
    intro i
    exact (hfc.iteratedFDeriv i).exists_bound_of_continuous
      (hf.continuous_iteratedFDeriv (natCast_le_top i))
  choose C hC using hb
  refine ⟨∑ k ∈ Finset.range 5, |C k|,
    Finset.sum_nonneg (fun j _ => abs_nonneg (C j)), fun i hi q => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ i f q‖ ≤ |C i| := (hC i q).trans (le_abs_self _)
  have h2 : |C i| ≤ ∑ j ∈ Finset.range 5, |C j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_range.2 (by omega))
  linarith

lemma iteratedFDeriv_add_one (f : ℝ × ℝ → ℝ) (hper : ∀ p : ℝ × ℝ, f (p.1, p.2 + 1) = f p)
    (i : ℕ) (x θ : ℝ) : iteratedFDeriv ℝ i f (x, θ + 1) = iteratedFDeriv ℝ i f (x, θ) := by
  have hfun : (fun z : ℝ × ℝ => f (z + ((0 : ℝ), (1 : ℝ)))) = f := by
    funext z
    have : z + ((0 : ℝ), (1 : ℝ)) = (z.1, z.2 + 1) := by
      ext <;> simp
    rw [this, hper z]
  have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) i ((0 : ℝ), (1 : ℝ)) (x, θ)
  rw [hfun] at h
  have : ((x, θ) : ℝ × ℝ) + ((0 : ℝ), (1 : ℝ)) = (x, θ + 1) := by ext <;> simp
  rw [this] at h
  rw [h]

lemma exists_bound_of_periodic (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : ∀ p : ℝ × ℝ, f (p.1, p.2 + 1) = f p) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ℕ, i ≤ 4 → ∀ q : ℝ × ℝ, |q.1| ≤ R → ‖iteratedFDeriv ℝ i f q‖ ≤ C := by
  set K : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc (0 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_contDiffOn f isOpen_univ hf.contDiffOn hKc (subset_univ _)
  refine ⟨C, hC0, fun i hi q hq => ?_⟩
  have hp : Function.Periodic (fun θ => iteratedFDeriv ℝ i f (q.1, θ)) 1 :=
    fun θ => iteratedFDeriv_add_one f hper i q.1 θ
  obtain ⟨θ', hθ', heq⟩ := hp.exists_mem_Ico₀ one_pos q.2
  have heq' : iteratedFDeriv ℝ i f q = iteratedFDeriv ℝ i f (q.1, θ') := heq
  rw [heq']
  apply hC i hi
  simp only [hK, mem_prod, mem_Icc]
  exact ⟨abs_le.1 hq, hθ'.1, hθ'.2.le⟩

noncomputable def gR (p : ℝ × ℝ) : ℝ := γ p * (1 - Ψ p)

lemma gR_add_one (p : ℝ × ℝ) : gR (p.1, p.2 + 1) = gR p := by
  unfold gR; rw [γ_add_one, Ψ_add_one]

lemma gR_eventuallyEq_zero {p : ℝ × ℝ} (h : Complex.exp (zC p) = 1) :
    gR =ᶠ[nhds p] fun _ => 0 := by
  obtain ⟨h1, k, hk⟩ := eq_of_exp_zC_eq_one h
  have hopen : IsOpen {q : ℝ × ℝ | |q.1| < 1 / 16 ∧ |q.2 - k| < 1 / 16} := by
    apply IsOpen.inter
    · exact isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
    · exact isOpen_lt (continuous_abs.comp (continuous_snd.sub continuous_const)) continuous_const
  have hmem : p ∈ {q : ℝ × ℝ | |q.1| < 1 / 16 ∧ |q.2 - k| < 1 / 16} := by
    simp only [mem_setOf_eq, h1, hk, abs_zero, sub_self]; norm_num
  filter_upwards [hopen.mem_nhds hmem] with q hq
  simp only [gR, Ψ_eq_one_of_near k hq.1 hq.2, sub_self, mul_zero]

lemma gR_contDiff : ContDiff ℝ (⊤ : ℕ∞) gR := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hz : Complex.exp (zC p) = 1
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (gR_eventuallyEq_zero hz)
  · have hγ : ContDiffAt ℝ (⊤ : ℕ∞) γ p := γ_contDiffOn.contDiffAt (isOpen_regSet.mem_nhds hz)
    exact hγ.mul (contDiff_const.sub Ψ_contDiff).contDiffAt

lemma gR_continuous : Continuous gR := gR_contDiff.continuous

noncomputable def G (p : ℝ × ℝ) : ℝ := γ p * ψ₂ p

lemma G_continuous : Continuous G := γ_continuous.mul ψ₂_contDiff.continuous

lemma G_eq_of_lt {q : ℝ × ℝ} (hq : ‖q‖ < 1 / 3) : G q = aS q * L q + s q * bS q := by
  unfold G
  rw [ψ₂_eq_one hq, mul_one]
  exact γ_eq_of_strip (lt_of_le_of_lt (abs_snd_le q) (by linarith))

lemma G_eventuallyEq {p : ℝ × ℝ} (hp : ‖p‖ < 1 / 3) :
    G =ᶠ[nhds p] fun q => aS q * L q + s q * bS q := by
  have hopen : IsOpen {q : ℝ × ℝ | ‖q‖ < 1 / 3} := isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hp] with q hq
  exact G_eq_of_lt hq

lemma G_contDiffOn : ContDiffOn ℝ 4 G {p : ℝ × ℝ | p ≠ 0} := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  by_cases hz : Complex.exp (zC p) = 1
  ·
    obtain ⟨h1, k, hk⟩ := eq_of_exp_zC_eq_one hz
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hp
      ext
      · exact h1
      · rw [hk]; simp
    have hk1 : (1 : ℝ) ≤ |p.2| := by
      rw [hk, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hk0
    have hopen : IsOpen {q : ℝ × ℝ | 1 / 2 < |q.2|} :=
      isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
    have hev : G =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds (show p ∈ {q : ℝ × ℝ | 1 / 2 < |q.2|} by
        simp only [mem_setOf_eq]; linarith)] with q hq
      simp only [G, ψ₂_eq_zero (le_of_lt hq), mul_zero]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  · have hγ : ContDiffAt ℝ (⊤ : ℕ∞) γ p := γ_contDiffOn.contDiffAt (isOpen_regSet.mem_nhds hz)
    exact (hγ.mul ψ₂_contDiff.contDiffAt).of_le (natCast_le_top 4)

noncomputable def gsb (q : ℝ × ℝ) : ℝ := s q * bS q

lemma zero_mem_strip : (0 : ℝ × ℝ) ∈ strip := by
  simp [strip]

lemma closedBall_subset_strip : Metric.closedBall (0 : ℝ × ℝ) (1 / 4) ⊆ strip := by
  intro q hq
  simp only [Metric.mem_closedBall, dist_zero_right] at hq
  show |q.2| < 1 / 2
  linarith [abs_snd_le q]

lemma gsb_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) gsb strip :=
  s_contDiff.contDiffOn.mul bS_contDiffOn

lemma fderiv_gsb_zero : fderiv ℝ gsb 0 = 0 := by
  have hs : DifferentiableAt ℝ s 0 := (s_contDiff.differentiable (by simp)).differentiableAt
  have hb : DifferentiableAt ℝ bS 0 :=
    (bS_contDiffOn.contDiffAt (isOpen_strip.mem_nhds zero_mem_strip)).differentiableAt (by simp)
  have hmin : IsLocalMin s (0 : ℝ × ℝ) :=
    Filter.Eventually.of_forall fun q => by rw [s_zero]; exact s_nonneg q
  have h := fderiv_fun_mul hs hb
  change fderiv ℝ (fun y => s y * bS y) 0 = 0
  rw [h, s_zero, hmin.fderiv_eq_zero, zero_smul, smul_zero, add_zero]

lemma exists_bound_fderiv_gsb : ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ × ℝ, ‖q‖ ≤ 1 / 4 →
    ‖iteratedFDeriv ℝ 1 gsb q‖ ≤ C * ‖q‖ := by
  set K := Metric.closedBall (0 : ℝ × ℝ) (1 / 4) with hK
  have hg1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ gsb) strip :=
    gsb_contDiffOn.fderiv_of_isOpen isOpen_strip (by simp)
  have hdiff : ∀ q ∈ K, DifferentiableAt ℝ (fderiv ℝ gsb) q := fun q hq =>
    (hg1.contDiffAt (isOpen_strip.mem_nhds (closedBall_subset_strip hq))).differentiableAt (by simp)
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ gsb)) K :=
    (hg1.continuousOn_fderiv_of_isOpen isOpen_strip (by simp)).mono closedBall_subset_strip
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ × ℝ) (1 / 4)).exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ gsb)) hcont
  refine ⟨|C|, abs_nonneg _, fun q hq => ?_⟩
  have hqK : q ∈ K := by simpa [hK] using hq
  have h0K : (0 : ℝ × ℝ) ∈ K := by simp [hK]
  have hmvt := (convex_closedBall (0 : ℝ × ℝ) (1 / 4)).norm_image_sub_le_of_norm_fderiv_le
    hdiff (fun x hx => (hC x hx).trans (le_abs_self C)) h0K hqK
  rw [fderiv_gsb_zero, sub_zero, sub_zero] at hmvt
  rw [norm_iteratedFDeriv_one]
  exact hmvt

def pstrip : Set (ℝ × ℝ) := strip ∩ {p : ℝ × ℝ | p ≠ 0}

lemma isOpen_pstrip : IsOpen pstrip := isOpen_strip.inter isOpen_ne

lemma mem_pstrip {p : ℝ × ℝ} (hp : p ≠ 0) (hpr : ‖p‖ ≤ 1 / 4) : p ∈ pstrip :=
  ⟨closedBall_subset_strip (by simpa using hpr), hp⟩

lemma aS_contDiffOn_pstrip : ContDiffOn ℝ 4 aS pstrip :=
  (aS_contDiffOn.mono inter_subset_left).of_le (natCast_le_top 4)

lemma L_contDiffOn_pstrip : ContDiffOn ℝ 4 L pstrip :=
  (L_contDiffOn.mono inter_subset_right).of_le (natCast_le_top 4)

lemma aL_bound (α : ℝ) (hα0 : 0 ≤ α)
    (hα : ∀ i : ℕ, i ≤ 4 → ∀ q : ℝ × ℝ, ‖q‖ ≤ 1 / 4 → ‖iteratedFDeriv ℝ i aS q‖ ≤ α)
    (n : ℕ) (hn : n ≤ 4) (p : ℝ × ℝ) (hp : p ≠ 0) (hpr : ‖p‖ ≤ 1 / 4) :
    ‖p‖ ^ n * ‖iteratedFDeriv ℝ n (fun q => aS q * L q) p‖ ≤
      16 * α * (CL * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|)) := by
  have hpS : p ∈ pstrip := mem_pstrip hp hpr
  have hU : UniqueDiffOn ℝ pstrip := isOpen_pstrip.uniqueDiffOn
  have hL := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (A := ℝ) aS_contDiffOn_pstrip
    L_contDiffOn_pstrip hU hpS (n := n) (by exact_mod_cast hn)
  have hw : ∀ (f : ℝ × ℝ → ℝ) (k : ℕ),
      iteratedFDerivWithin ℝ k f pstrip p = iteratedFDeriv ℝ k f p :=
    fun f k => iteratedFDerivWithin_of_isOpen k isOpen_pstrip hpS
  simp only [hw] at hL
  set t := ‖p‖ with ht_def
  have ht : 0 < t := norm_pos_iff.2 hp
  have ht1 : t ≤ 1 := by linarith
  set Q := CL * t ^ 2 * (1 + |Real.log t|) with hQ
  have hQ0 : 0 ≤ Q := by
    have := CL_nonneg
    positivity
  have hterm : ∀ i ∈ Finset.range (n + 1),
      t ^ n * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i aS p‖ * ‖iteratedFDeriv ℝ (n - i) L p‖) ≤
        (n.choose i : ℝ) * (α * Q) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hsplit : t ^ n = t ^ i * t ^ (n - i) := by
      rw [← pow_add]; congr 1; omega
    have h1 : t ^ i * ‖iteratedFDeriv ℝ i aS p‖ ≤ α := by
      calc t ^ i * ‖iteratedFDeriv ℝ i aS p‖ ≤ 1 * α :=
            mul_le_mul (pow_le_one₀ ht.le ht1) (hα i (hin.trans hn) p hpr) (norm_nonneg _)
              zero_le_one
        _ = α := one_mul α
    have h2 : t ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) L p‖ ≤ Q := L_bound (n - i) (by omega) p hp
    calc t ^ n * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i aS p‖ * ‖iteratedFDeriv ℝ (n - i) L p‖)
        = (n.choose i : ℝ) * ((t ^ i * ‖iteratedFDeriv ℝ i aS p‖) *
            (t ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) L p‖)) := by rw [hsplit]; ring
      _ ≤ (n.choose i : ℝ) * (α * Q) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact mul_le_mul h1 h2 (by positivity) hα0
  calc t ^ n * ‖iteratedFDeriv ℝ n (fun q => aS q * L q) p‖
      ≤ t ^ n * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i aS p‖ *
          ‖iteratedFDeriv ℝ (n - i) L p‖ := mul_le_mul_of_nonneg_left hL (pow_nonneg ht.le n)
    _ = ∑ i ∈ Finset.range (n + 1), t ^ n * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i aS p‖ *
          ‖iteratedFDeriv ℝ (n - i) L p‖) := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (α * Q) := Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * (α * Q) := by rw [Finset.sum_mul]
    _ = (2 : ℝ) ^ n * (α * Q) := by
        congr 1
        have := Nat.sum_range_choose n
        exact_mod_cast this
    _ ≤ (2 : ℝ) ^ 4 * (α * Q) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_right₀ (by norm_num) hn
    _ = 16 * α * (CL * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|)) := by rw [hQ]; ring

lemma sb_bound (β C1 σ : ℝ) (hβ0 : 0 ≤ β) (hC10 : 0 ≤ C1) (hσ0 : 0 ≤ σ)
    (hβ : ∀ q : ℝ × ℝ, ‖q‖ ≤ 1 / 4 → |bS q| ≤ β)
    (hC1 : ∀ q : ℝ × ℝ, ‖q‖ ≤ 1 / 4 → ‖iteratedFDeriv ℝ 1 gsb q‖ ≤ C1 * ‖q‖)
    (hσ : ∀ i : ℕ, i ≤ 4 → ∀ q : ℝ × ℝ, ‖q‖ ≤ 1 / 4 → ‖iteratedFDeriv ℝ i gsb q‖ ≤ σ)
    (n : ℕ) (hn : n ≤ 4) (p : ℝ × ℝ) (hp : p ≠ 0) (hpr : ‖p‖ ≤ 1 / 4) :
    ‖p‖ ^ n * ‖iteratedFDeriv ℝ n gsb p‖ ≤ ((1 / 4 + 4 * Real.pi ^ 2) * β + C1 + σ) * ‖p‖ ^ 2 := by
  set t := ‖p‖ with ht_def
  have ht : 0 < t := norm_pos_iff.2 hp
  have ht1 : t ≤ 1 := by linarith
  have hπ : 0 ≤ 1 / 4 + 4 * Real.pi ^ 2 := by positivity
  have hall : 0 ≤ ((1 / 4 + 4 * Real.pi ^ 2) * β + C1 + σ) := by positivity
  rcases n with _ | _ | n
  ·
    rw [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    have h1 : |gsb p| = s p * |bS p| := by
      rw [gsb, abs_mul, abs_of_nonneg (s_nonneg p)]
    rw [h1]
    calc s p * |bS p| ≤ ((1 / 4 + 4 * Real.pi ^ 2) * t ^ 2) * β :=
          mul_le_mul (s_le p) (hβ p hpr) (abs_nonneg _) (by positivity)
      _ = ((1 / 4 + 4 * Real.pi ^ 2) * β) * t ^ 2 := by ring
      _ ≤ ((1 / 4 + 4 * Real.pi ^ 2) * β + C1 + σ) * t ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          linarith
  ·
    rw [zero_add, pow_one]
    calc t * ‖iteratedFDeriv ℝ 1 gsb p‖ ≤ t * (C1 * t) :=
          mul_le_mul_of_nonneg_left (hC1 p hpr) ht.le
      _ = C1 * t ^ 2 := by ring
      _ ≤ ((1 / 4 + 4 * Real.pi ^ 2) * β + C1 + σ) * t ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          nlinarith
  ·
    have hn2 : 2 ≤ n + 2 := by omega
    have hpow : t ^ (n + 2) ≤ t ^ 2 := pow_le_pow_of_le_one ht.le ht1 hn2
    calc t ^ (n + 2) * ‖iteratedFDeriv ℝ (n + 2) gsb p‖ ≤ t ^ 2 * σ :=
          mul_le_mul hpow (hσ (n + 2) hn p hpr) (norm_nonneg _) (sq_nonneg _)
      _ = σ * t ^ 2 := by ring
      _ ≤ ((1 / 4 + 4 * Real.pi ^ 2) * β + C1 + σ) * t ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          nlinarith

theorem exists_G_bound : ∃ A : ℝ, 0 ≤ A ∧
    ∀ n : ℕ, n ≤ 4 → ∀ p : ℝ × ℝ, p ≠ 0 → ‖p‖ ≤ 1 / 4 →
      ‖p‖ ^ n * ‖iteratedFDeriv ℝ n G p‖ ≤ A * ‖p‖ ^ 2 * (1 + |Real.log ‖p‖|) := by
  have hKc : IsCompact (Metric.closedBall (0 : ℝ × ℝ) (1 / 4)) := isCompact_closedBall _ _
  have hmem : ∀ q : ℝ × ℝ, ‖q‖ ≤ 1 / 4 → q ∈ Metric.closedBall (0 : ℝ × ℝ) (1 / 4) := by
    intro q hq; simpa using hq
  obtain ⟨α, hα0, hα⟩ := exists_bound_of_contDiffOn aS isOpen_strip aS_contDiffOn hKc
    closedBall_subset_strip
  obtain ⟨β, hβ0, hβ⟩ := exists_bound_of_contDiffOn bS isOpen_strip bS_contDiffOn hKc
    closedBall_subset_strip
  obtain ⟨σ, hσ0, hσ⟩ := exists_bound_of_contDiffOn gsb isOpen_strip gsb_contDiffOn hKc
    closedBall_subset_strip
  obtain ⟨C1, hC10, hC1⟩ := exists_bound_fderiv_gsb
  set c2 := (1 / 4 + 4 * Real.pi ^ 2) * β + C1 + σ with hc2
  have hc20 : 0 ≤ c2 := by positivity
  have hCL := CL_nonneg
  refine ⟨16 * α * CL + c2, by positivity, fun n hn p hp hpr => ?_⟩
  set t := ‖p‖ with ht_def
  have ht : 0 < t := norm_pos_iff.2 hp

  have hev := G_eventuallyEq (p := p) (by linarith)
  have hfg : (fun q => aS q * L q + s q * bS q) = (fun q => aS q * L q) + gsb := by
    funext q; rfl
  rw [hfg] at hev
  rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds]

  have hpS : p ∈ pstrip := mem_pstrip hp hpr
  have hf : ContDiffAt ℝ n (fun q => aS q * L q) p :=
    ((aS_contDiffOn_pstrip.mul L_contDiffOn_pstrip).contDiffAt (isOpen_pstrip.mem_nhds hpS)).of_le
      (by exact_mod_cast hn)
  have hg : ContDiffAt ℝ n gsb p :=
    (gsb_contDiffOn.contDiffAt (isOpen_strip.mem_nhds hpS.1)).of_le (natCast_le_top n)
  rw [iteratedFDeriv_add_apply hf hg]
  have h1 := aL_bound α hα0 (fun i hi q hq => hα i hi q (hmem q hq)) n hn p hp hpr
  have h2 := sb_bound β C1 σ hβ0 hC10 hσ0
    (fun q hq => by
      have := hβ 0 (by norm_num) q (hmem q hq)
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this)
    hC1 (fun i hi q hq => hσ i hi q (hmem q hq)) n hn p hp hpr
  have hlog : t ^ 2 ≤ t ^ 2 * (1 + |Real.log t|) := by
    have : (1 : ℝ) ≤ 1 + |Real.log t| := by linarith [abs_nonneg (Real.log t)]
    nlinarith [sq_nonneg t]
  calc t ^ n * ‖iteratedFDeriv ℝ n (fun q => aS q * L q) p + iteratedFDeriv ℝ n gsb p‖
      ≤ t ^ n * (‖iteratedFDeriv ℝ n (fun q => aS q * L q) p‖ + ‖iteratedFDeriv ℝ n gsb p‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg ht.le n)
    _ = t ^ n * ‖iteratedFDeriv ℝ n (fun q => aS q * L q) p‖ +
          t ^ n * ‖iteratedFDeriv ℝ n gsb p‖ := by ring
    _ ≤ 16 * α * (CL * t ^ 2 * (1 + |Real.log t|)) + c2 * t ^ 2 := add_le_add h1 h2
    _ ≤ 16 * α * (CL * t ^ 2 * (1 + |Real.log t|)) + c2 * (t ^ 2 * (1 + |Real.log t|)) := by
        gcongr
    _ = (16 * α * CL + c2) * t ^ 2 * (1 + |Real.log t|) := by ring

lemma leibniz_bound (w : ℝ × ℝ → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (h : ℝ × ℝ → ℂ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (Θ M : ℝ) (hΘ0 : 0 ≤ Θ) (hM0 : 0 ≤ M) (p : ℝ × ℝ)
    (hwb : ∀ i : ℕ, i ≤ 4 → ‖iteratedFDeriv ℝ i w p‖ ≤ Θ)
    (hhb : ∀ i : ℕ, i ≤ 4 → ‖iteratedFDeriv ℝ i h p‖ ≤ M) (n : ℕ) (hn : n ≤ 4) :
    ‖iteratedFDeriv ℝ n (fun q => ((w q : ℝ) : ℂ) * h q) p‖ ≤ 16 * Θ * M := by
  have hw4 : ContDiff ℝ 4 w := hw.of_le (natCast_le_top 4)
  have hwc : ContDiff ℝ 4 (fun q => ((w q : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hw4
  have hh4 : ContDiff ℝ 4 h := hh.of_le (natCast_le_top 4)
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (A := ℂ) hwc hh4 p (n := n) (by exact_mod_cast hn)
  refine hL.trans ?_
  have hiso : ∀ k : ℕ, k ≤ 4 →
      ‖iteratedFDeriv ℝ k (fun q => ((w q : ℝ) : ℂ)) p‖ = ‖iteratedFDeriv ℝ k w p‖ := by
    intro k hk
    exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (hw4.contDiffAt (x := p))
      (i := k) (by exact_mod_cast hk)
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun q => ((w q : ℝ) : ℂ)) p‖ * ‖iteratedFDeriv ℝ (n - i) h p‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Θ * M) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi4 : i ≤ 4 := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hn
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        rw [hiso i hi4]
        exact mul_le_mul (hwb i hi4) (hhb (n - i) (by omega)) (norm_nonneg _) hΘ0
    _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * (Θ * M) := by rw [Finset.sum_mul]
    _ = (2 : ℝ) ^ n * (Θ * M) := by
        congr 1
        have := Nat.sum_range_choose n
        exact_mod_cast this
    _ ≤ (2 : ℝ) ^ 4 * (Θ * M) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_right₀ (by norm_num) hn
    _ = 16 * Θ * M := by ring

section windows

variable (R : ℝ) (h : ℝ × ℝ → ℂ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
  (hsupp : ∀ p : ℝ × ℝ, R < |p.1| → h p = 0)
  (hper : ∀ p : ℝ × ℝ, h (p.1, p.2 + 1) = h p)
  (M : ℝ) (hM : ∀ n : ℕ, n ≤ 6 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n h p‖ ≤ M)

noncomputable def H (h : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := ((W p : ℝ) : ℂ) * h p

noncomputable def FR (h : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := ((gR p : ℝ) : ℂ) * h p

include hM in
lemma M_nonneg : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num) 0)

include hh in
lemma H_contDiff : ContDiff ℝ 4 (H h) :=
  ((Complex.ofRealCLM.contDiff.comp W_contDiff).mul hh).of_le (natCast_le_top 4)

include hh in
lemma H_continuous : Continuous (H h) := (H_contDiff h hh).continuous

lemma H_eq_zero (p : ℝ × ℝ) (hp : 1 / 4 ≤ ‖p‖) : H h p = 0 := by
  simp [H, W_eq_zero_of_le hp]

include hh hM in
lemma H_bound (Θ : ℝ) (hΘ0 : 0 ≤ Θ) (hΘ : ∀ i : ℕ, i ≤ 4 → ∀ q : ℝ × ℝ, ‖iteratedFDeriv ℝ i W q‖ ≤ Θ)
    (n : ℕ) (hn : n ≤ 4) (p : ℝ × ℝ) : ‖iteratedFDeriv ℝ n (H h) p‖ ≤ 16 * Θ * M :=
  leibniz_bound W W_contDiff h hh Θ M hΘ0 (M_nonneg h M hM) p (fun i hi => hΘ i hi p)
    (fun i hi => hM i (by omega) p) n hn

include hh in
lemma FR_contDiff : ContDiff ℝ 4 (FR h) :=
  ((Complex.ofRealCLM.contDiff.comp gR_contDiff).mul hh).of_le (natCast_le_top 4)

include hh in
lemma FR_continuous : Continuous (FR h) := (FR_contDiff h hh).continuous

include hsupp in
lemma FR_eq_zero (p : ℝ × ℝ) (hp : R < |p.1|) : FR h p = 0 := by
  simp [FR, hsupp p hp]

include hper in
lemma FR_add_one (p : ℝ × ℝ) : FR h (p.1, p.2 + 1) = FR h p := by
  simp only [FR]
  rw [hper p]
  have := gR_add_one p
  rw [this]

include hh hsupp hM in
lemma FR_bound (Γ : ℝ) (hΓ0 : 0 ≤ Γ)
    (hΓ : ∀ i : ℕ, i ≤ 4 → ∀ q : ℝ × ℝ, |q.1| ≤ R → ‖iteratedFDeriv ℝ i gR q‖ ≤ Γ)
    (n : ℕ) (hn : n ≤ 4) (p : ℝ × ℝ) : ‖iteratedFDeriv ℝ n (FR h) p‖ ≤ 16 * Γ * M := by
  have hM0 := M_nonneg h M hM
  by_cases hp : R < |p.1|
  · have hopen : IsOpen {q : ℝ × ℝ | R < |q.1|} :=
      isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
    have hev : FR h =ᶠ[nhds p] (fun _ => (0 : ℂ)) := by
      filter_upwards [hopen.mem_nhds hp] with q hq
      exact FR_eq_zero R h hsupp q hq
    rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    positivity
  · push Not at hp
    exact leibniz_bound gR gR_contDiff h hh Γ M hΓ0 hM0 p (fun i hi => hΓ i hi p hp)
      (fun i hi => hM i (by omega) p) n hn

end windows

noncomputable def E (ξ η : ℝ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * p.1 + η * p.2 : ℝ) : ℂ)))

lemma E_continuous (ξ η : ℝ) : Continuous (E ξ η) := by
  unfold E; fun_prop

lemma E_add_one (ξ : ℝ) (m : ℤ) (p : ℝ × ℝ) : E ξ m (p.1, p.2 + 1) = E ξ m p := by
  unfold E
  have : (((ξ * (p.1, p.2 + 1).1 + (m : ℝ) * (p.1, p.2 + 1).2 : ℝ)) : ℂ) =
      ((ξ * p.1 + (m : ℝ) * p.2 : ℝ) : ℂ) + (m : ℂ) := by
    push_cast; ring
  rw [this, mul_add, neg_add, Complex.exp_add]
  have h1 : Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ))) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (-m)
    rw [← this]
    congr 1
    push_cast
    ring
  rw [h1, mul_one]

section slices

variable (R : ℝ) (hR : 0 ≤ R) (h : ℝ × ℝ → ℂ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
  (hsupp : ∀ p : ℝ × ℝ, R < |p.1| → h p = 0)
  (hper : ∀ p : ℝ × ℝ, h (p.1, p.2 + 1) = h p) (ξ : ℝ) (m : ℤ)

noncomputable def fS (h : ℝ × ℝ → ℂ) (ξ : ℝ) (m : ℤ) (p : ℝ × ℝ) : ℂ :=
  E ξ m p * (((γ p * Ψ p : ℝ) : ℂ) * h p)

noncomputable def F2 (h : ℝ × ℝ → ℂ) (ξ : ℝ) (m : ℤ) (p : ℝ × ℝ) : ℂ :=
  E ξ m p * (((G p : ℝ) : ℂ) * H h p)

include hh in
lemma fS_continuous : Continuous (fS h ξ m) := by
  unfold fS
  exact (E_continuous ξ m).mul ((Complex.continuous_ofReal.comp
    (γ_continuous.mul Ψ_contDiff.continuous)).mul hh.continuous)

include hh in
lemma F2_continuous : Continuous (F2 h ξ m) := by
  unfold F2
  exact (E_continuous ξ m).mul ((Complex.continuous_ofReal.comp G_continuous).mul
    (H_continuous h hh))

include hper in
lemma fS_add_one (p : ℝ × ℝ) : fS h ξ m (p.1, p.2 + 1) = fS h ξ m p := by
  unfold fS
  rw [E_add_one, γ_add_one, Ψ_add_one, hper]

lemma F2_eq_zero (p : ℝ × ℝ) (hp : 1 / 4 ≤ ‖p‖) : F2 h ξ m p = 0 := by
  simp [F2, H_eq_zero h p hp]

lemma fS_eq_F2 (p : ℝ × ℝ) (hp : |p.2| ≤ 1 / 2) : fS h ξ m p = F2 h ξ m p := by
  unfold fS F2 H G
  by_cases hq : ‖p‖ < 1 / 3
  · rw [ψ₂_eq_one hq, W_eq_Ψ hp]; push_cast; ring
  · push Not at hq
    have hW : W p = 0 := W_eq_zero_of_le (by linarith)
    have hΨ : Ψ p = 0 := by rw [← W_eq_Ψ hp]; exact hW
    rw [hW, hΨ]; push_cast; ring

include hh in
lemma F2_integrable : Integrable (F2 h ξ m) (volume : Measure (ℝ × ℝ)) := by
  apply (F2_continuous h hh ξ m).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Metric.closedBall (0 : ℝ × ℝ) 1) (isCompact_closedBall _ _)
  intro p hp
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hp
  exact F2_eq_zero h ξ m p (by linarith)

include hper in

lemma sing_slice (x : ℝ) :
    ∫ θ in Ico (0 : ℝ) 1, fS h ξ m (x, θ) = ∫ θ : ℝ, F2 h ξ m (x, θ) := by
  have hperθ : Function.Periodic (fun θ => fS h ξ m (x, θ)) 1 := fun θ =>
    fS_add_one h hper ξ m (x, θ)
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have h1 := hperθ.intervalIntegral_add_eq 0 (-1 / 2)
  have e1 : (0 : ℝ) + 1 = 1 := by norm_num
  have e2 : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [e1, e2] at h1
  rw [h1, intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)]
  have h2 : ∫ θ in Ioc (-1 / 2 : ℝ) (1 / 2), fS h ξ m (x, θ) =
      ∫ θ in Ioc (-1 / 2 : ℝ) (1 / 2), F2 h ξ m (x, θ) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro θ hθ
    apply fS_eq_F2
    simp only [mem_Ioc] at hθ
    show |θ| ≤ 1 / 2
    rw [abs_le]; constructor <;> linarith
  rw [h2]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro θ hθ
  apply F2_eq_zero
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at hθ
  have : 1 / 4 ≤ |θ| := by
    rw [le_abs]
    rcases hθ with hθ | hθ
    · right; linarith
    · left; linarith
  exact this.trans (abs_snd_le (x, θ))

include hh hper in

lemma sing_total :
    ∫ x : ℝ, ∫ θ in Ico (0 : ℝ) 1, fS h ξ m (x, θ) = ∫ p : ℝ × ℝ, F2 h ξ m p := by
  have h1 : (fun x : ℝ => ∫ θ in Ico (0 : ℝ) 1, fS h ξ m (x, θ)) =
      fun x => ∫ θ : ℝ, F2 h ξ m (x, θ) := by
    funext x; exact sing_slice h hper ξ m x
  rw [h1, Measure.volume_eq_prod, integral_prod _ (by
    have := F2_integrable h hh ξ m
    rwa [Measure.volume_eq_prod] at this)]

lemma integrable_slice (f : ℝ × ℝ → ℂ) (hf : Continuous f)
    (hf0 : ∀ p : ℝ × ℝ, R < |p.1| → f p = 0) (hR : 0 ≤ R) :
    Integrable (fun x : ℝ => ∫ θ in Ico (0 : ℝ) 1, f (x, θ)) := by
  have h1 : (fun x : ℝ => ∫ θ in Ico (0 : ℝ) 1, f (x, θ)) = fun x => ∫ θ in (0 : ℝ)..1, f (x, θ) := by
    funext x
    rw [integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]
  rw [h1]
  apply Continuous.integrable_of_hasCompactSupport
  · have hu : Continuous (Function.uncurry fun (x θ : ℝ) => f (x, θ)) :=
      hf.comp (continuous_fst.prodMk continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hu 0 1
  · apply HasCompactSupport.intro (K := Icc (-R) R) isCompact_Icc
    intro x hx
    have hx' : R < |x| := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · exact lt_of_lt_of_le hx (le_abs_self x)
    have : (fun θ => f (x, θ)) = fun _ => 0 := by
      funext θ; exact hf0 (x, θ) hx'
    simp [this]

include hR hh hsupp in
lemma integrable_reg_slice :
    Integrable (fun x : ℝ => ∫ θ in Ico (0 : ℝ) 1, E ξ m (x, θ) * FR h (x, θ)) :=
  integrable_slice R (fun p => E ξ m p * FR h p) ((E_continuous ξ m).mul (FR_continuous h hh))
    (fun p hp => by simp only [FR_eq_zero R h hsupp p hp, mul_zero]) hR

include hR hh hsupp in
lemma integrable_sing_slice :
    Integrable (fun x : ℝ => ∫ θ in Ico (0 : ℝ) 1, fS h ξ m (x, θ)) :=
  integrable_slice R (fS h ξ m) (fS_continuous h hh ξ m)
    (fun p hp => by simp [fS, hsupp p hp]) hR

include hh in

lemma inner_split (x : ℝ) :
    ∫ θ in Ico (0 : ℝ) 1, (E ξ m (x, θ) * FR h (x, θ) + fS h ξ m (x, θ)) =
      (∫ θ in Ico (0 : ℝ) 1, E ξ m (x, θ) * FR h (x, θ)) +
        ∫ θ in Ico (0 : ℝ) 1, fS h ξ m (x, θ) := by
  apply integral_add
  · exact (((E_continuous ξ m).mul (FR_continuous h hh)).comp
      (Continuous.prodMk_right x)).integrableOn_Icc.mono_set Ico_subset_Icc_self
  · exact ((fS_continuous h hh ξ m).comp (Continuous.prodMk_right x)).integrableOn_Icc.mono_set
      Ico_subset_Icc_self

lemma pointwise_split (x θ : ℝ) :
    Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) *
        ((‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ ^ 2 *
            Real.log ‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ : ℝ) : ℂ) *
        h (x, θ) =
      E ξ m (x, θ) * FR h (x, θ) + fS h ξ m (x, θ) := by
  rw [← γ_apply x θ]
  simp only [E, FR, fS, gR]
  push_cast
  ring

end slices

lemma weight_m (b : ℝ) (hb : 0 ≤ b) : (1 + b)⁻¹ ^ 2 ≤ ((1 + b) ^ (3 / 2 : ℝ))⁻¹ := by
  have hu : 1 ≤ 1 + b := by linarith
  have hu0 : 0 < 1 + b := by linarith
  rw [inv_pow]
  apply inv_anti₀ (Real.rpow_pos_of_pos hu0 _)
  calc (1 + b) ^ (3 / 2 : ℝ) ≤ (1 + b) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
    _ = (1 + b) ^ 2 := Real.rpow_two _

lemma weight_ξm (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((1 + a + b) ^ (7 / 2 : ℝ))⁻¹ ≤ (1 + a)⁻¹ ^ 2 * ((1 + b) ^ (3 / 2 : ℝ))⁻¹ := by
  have hv : 0 < 1 + a + b := by linarith
  rw [inv_pow, ← mul_inv]
  apply inv_anti₀ (by positivity)
  have e : (7 / 2 : ℝ) = 2 + 3 / 2 := by norm_num
  rw [e, Real.rpow_add hv, Real.rpow_two]
  apply mul_le_mul
  · exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  · exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  · positivity
  · positivity

theorem main (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (h : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) h → (∀ p : ℝ × ℝ, R < |p.1| → h p = 0) →
        (∀ p : ℝ × ℝ, h (p.1, p.2 + 1) = h p) →
      ∀ M : ℝ, (∀ n : ℕ, n ≤ 6 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n h p‖ ≤ M) →
      ∀ (ξ : ℝ) (m : ℤ),
        ‖∫ x : ℝ, ∫ θ in Set.Ico (0 : ℝ) 1,
            Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) *
              ((‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ ^ 2 *
                  Real.log ‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ : ℝ) : ℂ) *
              h (x, θ)‖ ≤
          K * M * (1 + |ξ|)⁻¹ ^ 2 * ((1 + |(m : ℝ)|) ^ (3 / 2 : ℝ))⁻¹ := by
  obtain ⟨CR, hCR0, hreg⟩ :=
    MeasureTheory.exists_forall_norm_integral_integral_cexp_mul_le_of_contDiff_of_periodic R hR
  obtain ⟨CC, hCC0, hcore⟩ :=
    MeasureTheory.exists_forall_norm_integral_cexp_mul_mul_le_of_norm_iteratedFDeriv_le_mul_log
      (1 / 4) (by norm_num)
  obtain ⟨A, hA0, hA⟩ := exists_G_bound
  obtain ⟨Θ, hΘ0, hΘ⟩ := exists_bound_of_hasCompactSupport W W_contDiff W_hasCompactSupport
  obtain ⟨Γ, hΓ0, hΓ⟩ := exists_bound_of_periodic gR gR_contDiff gR_add_one R
  refine ⟨CR * (16 * Γ) + CC * A * (16 * Θ), by positivity, ?_⟩
  intro h hh hsupp hper M hM ξ m
  have hM0 : 0 ≤ M := M_nonneg h M hM

  have hsplit : (fun x : ℝ => ∫ θ in Set.Ico (0 : ℝ) 1,
      Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) *
        ((‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ ^ 2 *
            Real.log ‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ : ℝ) : ℂ) *
        h (x, θ)) =
      fun x => (∫ θ in Ico (0 : ℝ) 1, E ξ m (x, θ) * FR h (x, θ)) +
        ∫ θ in Ico (0 : ℝ) 1, fS h ξ m (x, θ) := by
    funext x
    rw [← inner_split h hh ξ m x]
    congr 1
    funext θ
    exact pointwise_split h ξ m x θ
  rw [hsplit, integral_add (integrable_reg_slice R hR h hh hsupp ξ m)
    (integrable_sing_slice R hR h hh hsupp ξ m), sing_total h hh hper ξ m]

  have hB : ‖∫ x : ℝ, ∫ θ in Ico (0 : ℝ) 1, E ξ m (x, θ) * FR h (x, θ)‖ ≤
      CR * (16 * Γ * M) * (1 + |ξ|)⁻¹ ^ 2 * (1 + |(m : ℝ)|)⁻¹ ^ 2 :=
    hreg (FR h) (FR_contDiff h hh) (FR_eq_zero R h hsupp) (FR_add_one h hper) (16 * Γ * M)
      (FR_bound R h hh hsupp M hM Γ hΓ0 hΓ) ξ m
  have hC : ‖∫ p : ℝ × ℝ, F2 h ξ m p‖ ≤
      CC * A * (16 * Θ * M) * ((1 + |ξ| + |(m : ℝ)|) ^ (7 / 2 : ℝ))⁻¹ :=
    hcore G (H h) A (16 * Θ * M) hA0 (by positivity) G_contDiffOn hA (H_contDiff h hh)
      (H_eq_zero h) (H_bound h hh M hM Θ hΘ0 hΘ) ξ m
  have hw1 := weight_m |(m : ℝ)| (abs_nonneg _)
  have hw2 := weight_ξm |ξ| |(m : ℝ)| (abs_nonneg _) (abs_nonneg _)
  have ha2 : 0 ≤ (1 + |ξ|)⁻¹ ^ 2 := by positivity
  calc ‖(∫ x : ℝ, ∫ θ in Ico (0 : ℝ) 1, E ξ m (x, θ) * FR h (x, θ)) + ∫ p : ℝ × ℝ, F2 h ξ m p‖
      ≤ ‖∫ x : ℝ, ∫ θ in Ico (0 : ℝ) 1, E ξ m (x, θ) * FR h (x, θ)‖ + ‖∫ p : ℝ × ℝ, F2 h ξ m p‖ :=
        norm_add_le _ _
    _ ≤ CR * (16 * Γ * M) * (1 + |ξ|)⁻¹ ^ 2 * (1 + |(m : ℝ)|)⁻¹ ^ 2 +
          CC * A * (16 * Θ * M) * ((1 + |ξ| + |(m : ℝ)|) ^ (7 / 2 : ℝ))⁻¹ := add_le_add hB hC
    _ ≤ CR * (16 * Γ * M) * (1 + |ξ|)⁻¹ ^ 2 * ((1 + |(m : ℝ)|) ^ (3 / 2 : ℝ))⁻¹ +
          CC * A * (16 * Θ * M) * ((1 + |ξ|)⁻¹ ^ 2 * ((1 + |(m : ℝ)|) ^ (3 / 2 : ℝ))⁻¹) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hw1 (by positivity)
        · exact mul_le_mul_of_nonneg_left hw2 (by positivity)
    _ = (CR * (16 * Γ) + CC * A * (16 * Θ)) * M * (1 + |ξ|)⁻¹ ^ 2 *
          ((1 + |(m : ℝ)|) ^ (3 / 2 : ℝ))⁻¹ := by ring

end K2Asm

open K2Asm in
theorem solution
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (h : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) h → (∀ p : ℝ × ℝ, R < |p.1| → h p = 0) →
        (∀ p : ℝ × ℝ, h (p.1, p.2 + 1) = h p) →
      ∀ M : ℝ, (∀ n : ℕ, n ≤ 6 → ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ n h p‖ ≤ M) →
      ∀ (ξ : ℝ) (m : ℤ),
        ‖∫ x : ℝ, ∫ θ in Set.Ico (0 : ℝ) 1,
            Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x + m * θ : ℝ) : ℂ))) *
              ((‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ ^ 2 *
                  Real.log ‖(1 : ℂ) - Complex.exp ((x / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ : ℝ))‖ : ℝ) : ℂ) *
              h (x, θ)‖ ≤
          K * M * (1 + |ξ|)⁻¹ ^ 2 * ((1 + |(m : ℝ)|) ^ (3 / 2 : ℝ))⁻¹ :=
  main R hR

end S_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le
end P2MW
export P2MW.S_MeasureTheory_exists_forall_norm_integral_integral_cexp_mul_normSq_log_germ_mul_le (solution)
