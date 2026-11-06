-- Prove2me | solution 1 for GuthMaynard.exists_large_values_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:28:19.23998+00:00
-- url     : https://prove2.me/submissions/32ddadcd-52b2-4e1f-b15e-cfdff900a647

import Definitions.Def_GuthMaynard
import Mathlib

section
section
namespace GuthMaynard.S1

open Complex Finset

lemma r_formula (x : ℝ) (hs : Real.sin x ≠ 0) :
    (-(1 / 2 : ℂ) - Complex.I * ((Real.cos x / (2 * Real.sin x) : ℝ) : ℂ)) *
      (Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I) - 1) = 1 := by
  have hexp : Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I) =
      ((Real.cos (2 * x) : ℝ) : ℂ) + ((Real.sin (2 * x) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hexp]
  set ρ : ℝ := Real.cos x / (2 * Real.sin x) with hρ
  set A : ℝ := Real.cos (2 * x)
  set B : ℝ := Real.sin (2 * x)
  have key : (-(1 / 2 : ℂ) - Complex.I * (ρ : ℂ)) * ((A : ℂ) + (B : ℂ) * Complex.I - 1) =
      ((-(A - 1) / 2 + ρ * B : ℝ) : ℂ) + ((-B / 2 - ρ * (A - 1) : ℝ) : ℂ) * Complex.I := by
    push_cast
    have : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (-(ρ : ℂ) * B) * this
  rw [key]
  have hA : A = 1 - 2 * Real.sin x ^ 2 := by
    have h1 := Real.cos_two_mul x
    have h2 := Real.sin_sq_add_cos_sq x
    show Real.cos (2 * x) = _
    nlinarith
  have hB : B = 2 * Real.sin x * Real.cos x := Real.sin_two_mul x
  have h1 : -(A - 1) / 2 + ρ * B = 1 := by
    rw [hA, hB, hρ]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq x]
  have h2 : -B / 2 - ρ * (A - 1) = 0 := by
    rw [hA, hB, hρ]
    field_simp
    ring
  rw [h1, h2]; simp

/-- Kusmin–Landau for a phase with decreasing positive increments at most `π`. -/
lemma kl_sum (φ : ℕ → ℝ) (a H : ℕ) (hH : 1 ≤ H)
    (hpos : ∀ i < H, 0 < φ (a + i + 2) - φ (a + i + 1))
    (hle : ∀ i < H, φ (a + i + 2) - φ (a + i + 1) ≤ Real.pi)
    (hanti : ∀ i, i + 1 < H → φ (a + i + 3) - φ (a + i + 2) ≤ φ (a + i + 2) - φ (a + i + 1)) :
    ‖∑ i ∈ range H, Complex.exp ((φ (a + i + 1) : ℂ) * Complex.I)‖ ≤
      3 * Real.pi / (φ (a + H + 1) - φ (a + H)) := by
  set θ : ℕ → ℝ := fun i => φ (a + i + 2) - φ (a + i + 1) with hθ
  set x : ℕ → ℝ := fun i => θ i / 2 with hx
  have hxpos : ∀ i < H, 0 < x i := fun i hi => by simp only [hx]; linarith [hpos i hi]
  have hxle : ∀ i < H, x i ≤ Real.pi / 2 := fun i hi => by simp only [hx]; linarith [hle i hi]
  have hsin : ∀ i < H, 0 < Real.sin (x i) := fun i hi =>
    Real.sin_pos_of_pos_of_lt_pi (hxpos i hi) (by linarith [hxle i hi, Real.pi_pos])
  have hcos : ∀ i < H, 0 ≤ Real.cos (x i) := fun i hi =>
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hxpos i hi, Real.pi_pos], hxle i hi⟩
  set ρ : ℕ → ℝ := fun i => Real.cos (x i) / (2 * Real.sin (x i)) with hρ
  set r : ℕ → ℂ := fun i => -(1 / 2 : ℂ) - Complex.I * (ρ i : ℂ) with hr
  set A : ℕ → ℂ := fun n => Complex.exp ((φ n : ℂ) * Complex.I) with hA
  -- the summand
  have hterm : ∀ i < H, A (a + i + 1) = r i * (A (a + i + 2) - A (a + i + 1)) := by
    intro i hi
    have h1 : A (a + i + 2) = A (a + i + 1) * Complex.exp (((2 * x i : ℝ) : ℂ) * Complex.I) := by
      simp only [hA]
      rw [← Complex.exp_add]
      congr 1
      have : (2 * x i : ℝ) = φ (a + i + 2) - φ (a + i + 1) := by simp only [hx, hθ]; ring
      rw [this]; push_cast; ring
    have h2 := r_formula (x i) (hsin i hi).ne'
    calc A (a + i + 1) = A (a + i + 1) * 1 := (mul_one _).symm
      _ = A (a + i + 1) * (r i * (Complex.exp (((2 * x i : ℝ) : ℂ) * Complex.I) - 1)) := by
          rw [hr, hρ]; simp only; rw [h2]
      _ = r i * (A (a + i + 2) - A (a + i + 1)) := by rw [h1]; ring
  have hsum : ∑ i ∈ range H, A (a + i + 1) = ∑ i ∈ range H, r i • (A (a + i + 2) - A (a + i + 1)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [smul_eq_mul]; exact hterm i (Finset.mem_range.mp hi)
  have hby := Finset.sum_range_by_parts r (fun i => A (a + i + 2) - A (a + i + 1)) H
  have hG : ∀ k, ∑ i ∈ range k, (A (a + i + 2) - A (a + i + 1)) = A (a + k + 1) - A (a + 1) := by
    intro k
    have := Finset.sum_range_sub (fun i => A (a + i + 1)) k
    simpa [add_assoc, add_comm, add_left_comm] using this
  have hAn : ∀ n, ‖A n‖ = 1 := fun n => by
    simp only [hA]; exact Complex.norm_exp_ofReal_mul_I _
  have hGn : ∀ k, ‖∑ i ∈ range k, (A (a + i + 2) - A (a + i + 1))‖ ≤ 2 := by
    intro k; rw [hG]
    calc _ ≤ ‖A (a + k + 1)‖ + ‖A (a + 1)‖ := norm_sub_le _ _
      _ = 2 := by rw [hAn, hAn]; norm_num
  -- bounds on r
  have hrn : ∀ i < H, ‖r i‖ ≤ 1 / Real.sin (x i) := by
    intro i hi
    have hs := hsin i hi
    have hc := hcos i hi
    have hρ0 : 0 ≤ ρ i := div_nonneg hc (by positivity)
    have : ‖r i‖ ≤ 1 / 2 + ρ i := by
      calc ‖r i‖ ≤ ‖-(1 / 2 : ℂ)‖ + ‖Complex.I * (ρ i : ℂ)‖ := norm_sub_le _ _
        _ = 1 / 2 + ρ i := by
          rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0]; simp
    refine this.trans ?_
    have hcs : Real.cos (x i) ≤ 1 := Real.cos_le_one _
    have hss : Real.sin (x i) ≤ 1 := Real.sin_le_one _
    rw [hρ]; simp only
    rw [div_add_div _ _ (by norm_num) (by positivity), div_le_div_iff₀ (by positivity) hs]
    nlinarith
  have hdiff : ∀ i, i + 1 < H → ‖r (i + 1) - r i‖ = ρ (i + 1) - ρ i ∧ ρ i ≤ ρ (i + 1) := by
    intro i hi
    have hxi : x (i + 1) ≤ x i := by
      simp only [hx, hθ, show a + (i + 1) + 2 = a + i + 3 by omega, show a + (i + 1) + 1 = a + i + 2 by omega]
      linarith [hanti i hi]
    have hsi := hsin i (by omega)
    have hsi' := hsin (i + 1) hi
    have hmono : ρ i ≤ ρ (i + 1) := by
      rw [hρ]; simp only
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hsub : 0 ≤ Real.sin (x i - x (i + 1)) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        linarith [hxle i (by omega), hxpos (i + 1) hi, Real.pi_pos]
      rw [Real.sin_sub] at hsub
      nlinarith
    refine ⟨?_, hmono⟩
    have : r (i + 1) - r i = (Complex.I : ℂ) * (((ρ i - ρ (i + 1) : ℝ)) : ℂ) := by
      simp only [hr]; push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Complex.norm_I, one_mul, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  -- assemble
  have hS : ∑ i ∈ range H, A (a + i + 1) = r (H - 1) * (A (a + H + 1) - A (a + 1)) -
      ∑ i ∈ range (H - 1), (r (i + 1) - r i) * (A (a + (i + 1) + 1) - A (a + 1)) := by
    rw [hsum, hby]
    simp only [smul_eq_mul, hG]
  -- norm of the second part
  have hsec : ‖∑ i ∈ range (H - 1), (r (i + 1) - r i) * (A (a + (i + 1) + 1) - A (a + 1))‖ ≤
      2 * ρ (H - 1) := by
    calc _ ≤ ∑ i ∈ range (H - 1), ‖(r (i + 1) - r i) * (A (a + (i + 1) + 1) - A (a + 1))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ range (H - 1), 2 * (ρ (i + 1) - ρ i) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i + 1 < H := by have := Finset.mem_range.mp hi; omega
          rw [norm_mul, (hdiff i hi').1, mul_comm]
          apply mul_le_mul_of_nonneg_right _ (by linarith [(hdiff i hi').2])
          calc _ ≤ ‖A (a + (i + 1) + 1)‖ + ‖A (a + 1)‖ := norm_sub_le _ _
            _ = 2 := by rw [hAn, hAn]; norm_num
      _ = 2 * (ρ (H - 1) - ρ 0) := by
          rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => ρ i)]
      _ ≤ 2 * ρ (H - 1) := by
          have : 0 ≤ ρ 0 := div_nonneg (hcos 0 (by omega)) (by have := hsin 0 (by omega); positivity)
          linarith
  have hfirst : ‖r (H - 1) * (A (a + H + 1) - A (a + 1))‖ ≤ 2 / Real.sin (x (H - 1)) := by
    rw [norm_mul]
    have h2 : ‖A (a + H + 1) - A (a + 1)‖ ≤ 2 := by
      calc _ ≤ ‖A (a + H + 1)‖ + ‖A (a + 1)‖ := norm_sub_le _ _
        _ = 2 := by rw [hAn, hAn]; norm_num
    calc ‖r (H - 1)‖ * ‖A (a + H + 1) - A (a + 1)‖ ≤ (1 / Real.sin (x (H - 1))) * 2 :=
          mul_le_mul (hrn _ (by omega)) h2 (norm_nonneg _) (by have := hsin (H - 1) (by omega); positivity)
      _ = 2 / Real.sin (x (H - 1)) := by ring
  have hsH := hsin (H - 1) (by omega)
  have hρH : ρ (H - 1) ≤ 1 / (2 * Real.sin (x (H - 1))) := by
    rw [hρ]; simp only
    exact div_le_div_of_nonneg_right (Real.cos_le_one _) (by positivity)
  have hθH : θ (H - 1) = φ (a + H + 1) - φ (a + H) := by
    simp only [hθ]
    have e1 : a + (H - 1) + 2 = a + H + 1 := by omega
    have e2 : a + (H - 1) + 1 = a + H := by omega
    rw [e1, e2]
  have hsinlb : θ (H - 1) / Real.pi ≤ Real.sin (x (H - 1)) := by
    have := Real.mul_le_sin (x := x (H - 1)) (hxpos _ (by omega)).le (hxle _ (by omega))
    simp only [hx] at this ⊢
    have hpi := Real.pi_pos
    calc θ (H - 1) / Real.pi = 2 / Real.pi * (θ (H - 1) / 2) := by field_simp
      _ ≤ _ := this
  have hθpos : 0 < θ (H - 1) := by have := hxpos (H - 1) (by omega); simp only [hx] at this; linarith
  rw [← hθH]
  calc ‖∑ i ∈ range H, A (a + i + 1)‖ ≤ ‖r (H - 1) * (A (a + H + 1) - A (a + 1))‖ +
        ‖∑ i ∈ range (H - 1), (r (i + 1) - r i) * (A (a + (i + 1) + 1) - A (a + 1))‖ := by
        rw [hS]; exact norm_sub_le _ _
    _ ≤ 2 / Real.sin (x (H - 1)) + 2 * ρ (H - 1) := add_le_add hfirst hsec
    _ ≤ 2 / Real.sin (x (H - 1)) + 2 * (1 / (2 * Real.sin (x (H - 1)))) := by linarith
    _ = 3 / Real.sin (x (H - 1)) := by field_simp; ring
    _ ≤ 3 / (θ (H - 1) / Real.pi) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hsinlb
    _ = 3 * Real.pi / θ (H - 1) := by field_simp

end GuthMaynard.S1

end
end

section
section
namespace GuthMaynard.S1

open Complex

/-- `n^{it}` written as an exponential. -/
noncomputable def chi (n : ℕ) (t : ℝ) : ℂ := Complex.exp (((Real.log n : ℝ) : ℂ) * Complex.I * (t : ℂ))

lemma cpow_eq_chi {n : ℕ} (hn : 0 < n) (t : ℝ) : (n : ℂ) ^ ((t : ℂ) * Complex.I) = chi n t := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hnc]
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
  rw [hlog, chi]; congr 1; ring

lemma norm_chi (n : ℕ) (t : ℝ) : ‖chi n t‖ = 1 := by
  rw [chi, show ((Real.log n : ℝ) : ℂ) * Complex.I * (t : ℂ) = ((Real.log n * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma chi_neg (n : ℕ) (t : ℝ) : chi n (-t) = (starRingEnd ℂ) (chi n t) := by
  rw [chi, chi, ← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofReal]
  push_cast; ring

lemma chi_add (n : ℕ) (a b : ℝ) : chi n (a + b) = chi n a * chi n b := by
  rw [chi, chi, chi, ← Complex.exp_add]; congr 1; push_cast; ring

lemma chi_four (n : ℕ) (a b c d : ℝ) :
    chi n (a + b - c - d) = chi n a * chi n b * (starRingEnd ℂ) (chi n c) * (starRingEnd ℂ) (chi n d) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, chi_add, chi_add, chi_add, chi_neg, chi_neg]

/-- the pair correlation `R(n₁/n₂) = ∑_{t ∈ W} (n₁/n₂)^{it}` -/
noncomputable def Pn (W : Finset ℝ) (n₁ n₂ : ℕ) : ℂ :=
  ∑ t ∈ W, chi n₁ t * (starRingEnd ℂ) (chi n₂ t)

lemma sum_swap3 {α β γ : Type*} (A : Finset α) (B : Finset β) (C : Finset γ) (f : α → β → γ → ℂ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c = ∑ b ∈ B, ∑ c ∈ C, ∑ a ∈ A, f a b c := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

lemma sum_swap5 {α β γ δ ε : Type*} (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (E : Finset ε) (f : α → β → γ → δ → ε → ℂ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, ∑ e ∈ E, f a b c d e =
      ∑ d ∈ D, ∑ e ∈ E, ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c d e := by
  have h1 : ∀ a b, ∑ c ∈ C, ∑ d ∈ D, ∑ e ∈ E, f a b c d e = ∑ d ∈ D, ∑ e ∈ E, ∑ c ∈ C, f a b c d e :=
    fun a b => sum_swap3 C D E (f a b)
  simp_rw [h1]
  have h2 : ∀ a, ∑ b ∈ B, ∑ d ∈ D, ∑ e ∈ E, ∑ c ∈ C, f a b c d e =
      ∑ d ∈ D, ∑ e ∈ E, ∑ b ∈ B, ∑ c ∈ C, f a b c d e :=
    fun a => sum_swap3 B D E (fun b d e => ∑ c ∈ C, f a b c d e)
  simp_rw [h2]
  exact sum_swap3 A D E (fun a d e => ∑ b ∈ B, ∑ c ∈ C, f a b c d e)

lemma triple_eq (W : Finset ℝ) (n₁ n₂ : ℕ) (σ' : ℝ) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      (chi n₁ (t₁ + t₂ - t₃ - σ') * (starRingEnd ℂ) (chi n₂ (t₁ + t₂ - t₃ - σ'))) =
    ((starRingEnd ℂ) (chi n₁ σ') * chi n₂ σ') *
      (Pn W n₁ n₂ * Pn W n₁ n₂ * (starRingEnd ℂ) (Pn W n₁ n₂)) := by
  have hterm : ∀ t₁ t₂ t₃ : ℝ, chi n₁ (t₁ + t₂ - t₃ - σ') * (starRingEnd ℂ) (chi n₂ (t₁ + t₂ - t₃ - σ')) =
      ((starRingEnd ℂ) (chi n₁ σ') * chi n₂ σ') *
        ((chi n₁ t₁ * (starRingEnd ℂ) (chi n₂ t₁)) * (chi n₁ t₂ * (starRingEnd ℂ) (chi n₂ t₂)) *
          (starRingEnd ℂ) (chi n₁ t₃ * (starRingEnd ℂ) (chi n₂ t₃))) := by
    intro t₁ t₂ t₃
    rw [chi_four, chi_four]
    simp only [map_mul, Complex.conj_conj]
    ring
  simp_rw [hterm]
  set q : ℝ → ℂ := fun t => chi n₁ t * (starRingEnd ℂ) (chi n₂ t) with hq
  set u : ℂ := (starRingEnd ℂ) (chi n₁ σ') * chi n₂ σ' with hu
  have hP : Pn W n₁ n₂ = ∑ t ∈ W, q t := rfl
  have hcP : (starRingEnd ℂ) (Pn W n₁ n₂) = ∑ t ∈ W, (starRingEnd ℂ) (q t) := by
    rw [hP, map_sum]
  rw [hcP, hP]
  have h3 : ((∑ t ∈ W, q t) * ∑ t ∈ W, q t) * ∑ t ∈ W, (starRingEnd ℂ) (q t) =
      ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W, q x * q y * (starRingEnd ℂ) (q z) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
  rw [h3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]

/-- The triple sum of `|D|²` at shifted points is bounded by the third moment of `R`. -/
lemma triple_sum_le (W : Finset ℝ) (s : Finset ℕ) (c : ℕ → ℂ) (hc : ∀ n ∈ s, ‖c n‖ ≤ 1) (σ' : ℝ) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ‖∑ n ∈ s, c n * chi n (t₁ + t₂ - t₃ - σ')‖ ^ 2 ≤
      ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖Pn W n₁ n₂‖ ^ 3 := by
  have hsq : ∀ y : ℝ, (((‖∑ n ∈ s, c n * chi n y‖ ^ 2 : ℝ)) : ℂ) =
      ∑ n₁ ∈ s, ∑ n₂ ∈ s, c n₁ * (starRingEnd ℂ) (c n₂) * (chi n₁ y * (starRingEnd ℂ) (chi n₂ y)) := by
    intro y
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
    rw [map_mul]; ring
  have hZ : ((∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ‖∑ n ∈ s, c n * chi n (t₁ + t₂ - t₃ - σ')‖ ^ 2 : ℝ) : ℂ) =
      ∑ n₁ ∈ s, ∑ n₂ ∈ s, c n₁ * (starRingEnd ℂ) (c n₂) *
        (((starRingEnd ℂ) (chi n₁ σ') * chi n₂ σ') *
        (Pn W n₁ n₂ * Pn W n₁ n₂ * (starRingEnd ℂ) (Pn W n₁ n₂))) := by
    simp only [Complex.ofReal_sum]
    simp only [hsq]
    rw [sum_swap5]
    refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
    rw [← triple_eq W n₁ n₂ σ']
    simp only [Finset.mul_sum]
  set Z := ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ‖∑ n ∈ s, c n * chi n (t₁ + t₂ - t₃ - σ')‖ ^ 2 with hZdef
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc Z = ‖(Z : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hZ0]
    _ = ‖∑ n₁ ∈ s, ∑ n₂ ∈ s, c n₁ * (starRingEnd ℂ) (c n₂) *
        (((starRingEnd ℂ) (chi n₁ σ') * chi n₂ σ') *
        (Pn W n₁ n₂ * Pn W n₁ n₂ * (starRingEnd ℂ) (Pn W n₁ n₂)))‖ := by rw [hZ]
    _ ≤ ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖c n₁ * (starRingEnd ℂ) (c n₂) *
        (((starRingEnd ℂ) (chi n₁ σ') * chi n₂ σ') *
        (Pn W n₁ n₂ * Pn W n₁ n₂ * (starRingEnd ℂ) (Pn W n₁ n₂)))‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n₁ _ => norm_sum_le _ _)
    _ ≤ ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖Pn W n₁ n₂‖ ^ 3 := by
        refine Finset.sum_le_sum fun n₁ h₁ => Finset.sum_le_sum fun n₂ h₂ => ?_
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj,
          Complex.norm_conj, Complex.norm_conj, norm_chi, norm_chi]
        have a1 := hc n₁ h₁
        have a2 := hc n₂ h₂
        have hP0 := norm_nonneg (Pn W n₁ n₂)
        calc ‖c n₁‖ * ‖c n₂‖ * (1 * 1 * (‖Pn W n₁ n₂‖ * ‖Pn W n₁ n₂‖ * ‖Pn W n₁ n₂‖)) ≤
            1 * 1 * (1 * 1 * (‖Pn W n₁ n₂‖ * ‖Pn W n₁ n₂‖ * ‖Pn W n₁ n₂‖)) := by gcongr
          _ = _ := by ring

lemma sum_swap4 {α β γ δ : Type*} (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (f : α → β → γ → δ → ℂ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d = ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
  have h1 : ∀ a, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d = ∑ c ∈ C, ∑ d ∈ D, ∑ b ∈ B, f a b c d :=
    fun a => sum_swap3 B C D (f a)
  simp_rw [h1]
  exact sum_swap3 A C D (fun a c d => ∑ b ∈ B, f a b c d)

lemma chi_sub (n : ℕ) (a b : ℝ) : chi n (a - b) = chi n a * (starRingEnd ℂ) (chi n b) := by
  rw [sub_eq_add_neg, chi_add, chi_neg]

/-- Second moment of `R` equals the Heath-Brown sum. -/
lemma second_moment_eq (W : Finset ℝ) (s : Finset ℕ) :
    ∑ n₁ ∈ s, ∑ n₂ ∈ s, ‖Pn W n₁ n₂‖ ^ 2 = ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖∑ n ∈ s, chi n (t₁ - t₂)‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  have h1 : ∀ n₁ n₂ : ℕ, ((‖Pn W n₁ n₂‖ : ℝ) : ℂ) ^ 2 =
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, (chi n₁ (t₁ - t₂) * (starRingEnd ℂ) (chi n₂ (t₁ - t₂))) := by
    intro n₁ n₂
    rw [← Complex.mul_conj', Pn, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun t₂ _ => ?_
    rw [chi_sub, chi_sub]
    simp only [map_mul, Complex.conj_conj]
    ring
  have h2 : ∀ t₁ t₂ : ℝ, ((‖∑ n ∈ s, chi n (t₁ - t₂)‖ : ℝ) : ℂ) ^ 2 =
      ∑ n₁ ∈ s, ∑ n₂ ∈ s, (chi n₁ (t₁ - t₂) * (starRingEnd ℂ) (chi n₂ (t₁ - t₂))) := by
    intro t₁ t₂
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  simp_rw [h1, h2]
  exact (sum_swap4 W W s s _).symm

end GuthMaynard.S1

end
end

section
section
namespace GuthMaynard.S1

open Complex Finset

lemma sum_Ioc_eq_range (f : ℕ → ℂ) (a H : ℕ) :
    ∑ n ∈ Finset.Ioc a (a + H), f n = ∑ i ∈ range H, f (a + i + 1) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [show a + (H + 1) = (a + H) + 1 by ring, Finset.sum_Ioc_succ_top (by omega), ih,
      Finset.sum_range_succ]

lemma log_incr_le (m : ℕ) (hm : 1 ≤ m) : Real.log (((m + 1 : ℕ) : ℝ) / m) ≤ 1 / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have := Real.log_le_sub_one_of_pos (show 0 < ((m + 1 : ℕ) : ℝ) / m by positivity)
  have e : ((m + 1 : ℕ) : ℝ) / m - 1 = 1 / m := by push_cast; field_simp; ring
  linarith

lemma log_incr_ge (m : ℕ) (hm : 1 ≤ m) : 1 / ((m : ℝ) + 1) ≤ Real.log (((m + 1 : ℕ) : ℝ) / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have := Real.one_sub_inv_le_log_of_pos (show 0 < ((m + 1 : ℕ) : ℝ) / m by positivity)
  have e : 1 - (((m + 1 : ℕ) : ℝ) / m)⁻¹ = 1 / ((m : ℝ) + 1) := by
    push_cast; field_simp; ring
  linarith

lemma log_incr_anti (m : ℕ) (hm : 1 ≤ m) :
    Real.log (((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤ Real.log (((m + 1 : ℕ) : ℝ) / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ (by positivity) hm0]
  push_cast
  nlinarith

/-- Kusmin–Landau for `∑ n^{iv}` over a block, `v > 0`. -/
lemma far_block_pos (N a H : ℕ) (hN : 1 ≤ N) (haN : N ≤ a) (hH : 1 ≤ H) (haH : a + H ≤ 2 * N)
    (v : ℝ) (hv0 : 0 < v) (hvN : v ≤ N) :
    ‖∑ n ∈ Finset.Ioc a (a + H), chi n v‖ ≤ 30 * N / v := by
  set φ : ℕ → ℝ := fun n => v * Real.log n with hφ
  have hchi : ∀ n, chi n v = Complex.exp ((φ n : ℂ) * Complex.I) := by
    intro n; simp only [chi, hφ]; congr 1; push_cast; ring
  simp_rw [hchi]
  rw [sum_Ioc_eq_range (fun n => Complex.exp ((φ n : ℂ) * Complex.I)) a H]
  have hinc : ∀ m : ℕ, 1 ≤ m → φ (m + 1) - φ m = v * Real.log (((m + 1 : ℕ) : ℝ) / m) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    simp only [hφ]
    rw [Real.log_div (by positivity) hm0.ne']; ring
  have hmN : ∀ i, N ≤ a + i + 1 := fun i => by omega
  have e2 : ∀ i, φ (a + i + 2) - φ (a + i + 1) = v * Real.log (((a + i + 1 + 1 : ℕ) : ℝ) / ((a + i + 1 : ℕ) : ℝ)) := by
    intro i
    have := hinc (a + i + 1) (by omega)
    simpa [add_assoc] using this
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hbig : ∀ i, v / ((a + i + 1 : ℕ) : ℝ) ≤ 1 := by
    intro i
    have : (N : ℝ) ≤ ((a + i + 1 : ℕ) : ℝ) := by exact_mod_cast hmN i
    rw [div_le_one (by linarith)]; linarith
  have hH' : 1 ≤ H := hH
  have key := kl_sum φ a H hH'
    (fun i _ => by
      rw [e2]
      have : 0 < Real.log (((a + i + 1 + 1 : ℕ) : ℝ) / ((a + i + 1 : ℕ) : ℝ)) := by
        apply Real.log_pos
        rw [lt_div_iff₀ (by have := hmN i; positivity)]; push_cast; linarith
      positivity)
    (fun i _ => by
      rw [e2]
      have h1 := log_incr_le (a + i + 1) (by omega)
      have h2 : v * Real.log (((a + i + 1 + 1 : ℕ) : ℝ) / ((a + i + 1 : ℕ) : ℝ)) ≤ v * (1 / ((a + i + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 hv0.le
      have h3 : v * (1 / ((a + i + 1 : ℕ) : ℝ)) ≤ 1 := by rw [mul_one_div]; exact hbig i
      linarith [Real.pi_gt_three])
    (fun i _ => by
      have h3 := e2 (i + 1)
      rw [show a + (i + 1) + 2 = a + i + 3 by ring, show a + (i + 1) + 1 = a + i + 2 by ring] at h3
      rw [h3, e2 i]
      have := log_incr_anti (a + i + 1) (by omega)
      rw [show a + i + 3 = a + i + 1 + 2 by ring, show a + i + 2 = a + i + 1 + 1 by ring]
      exact mul_le_mul_of_nonneg_left this hv0.le)
  refine key.trans ?_
  have hlast : v / ((a + H : ℝ) + 1) ≤ φ (a + H + 1) - φ (a + H) := by
    have := hinc (a + H) (by omega)
    have h2 := log_incr_ge (a + H) (by omega)
    rw [this]
    have h3 : v * (1 / (((a + H : ℕ) : ℝ) + 1)) ≤ v * Real.log (((a + H + 1 : ℕ) : ℝ) / ((a + H : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left h2 hv0.le
    rw [mul_one_div] at h3
    push_cast at h3 ⊢
    exact h3
  have hpos : 0 < v / ((a + H : ℝ) + 1) := by positivity
  have h2N : (a : ℝ) + H ≤ 2 * N := by exact_mod_cast haH
  calc 3 * Real.pi / (φ (a + H + 1) - φ (a + H)) ≤ 3 * Real.pi / (v / ((a + H : ℝ) + 1)) :=
        div_le_div_of_nonneg_left (by positivity) hpos hlast
    _ = 3 * Real.pi * ((a + H : ℝ) + 1) / v := by field_simp
    _ ≤ 30 * N / v := by
        apply div_le_div_of_nonneg_right _ hv0.le
        have : (a : ℝ) + H + 1 ≤ 3 * N := by
          have : (1 : ℝ) ≤ N := by exact_mod_cast hN
          linarith
        nlinarith [Real.pi_lt_d2, Real.pi_pos]

lemma far_block (N a H : ℕ) (hN : 1 ≤ N) (haN : N ≤ a) (hH : 1 ≤ H) (haH : a + H ≤ 2 * N)
    (v : ℝ) (hv0 : v ≠ 0) (hvN : |v| ≤ N) :
    ‖∑ n ∈ Finset.Ioc a (a + H), chi n v‖ ≤ 30 * N / |v| := by
  rcases lt_or_gt_of_ne hv0 with h | h
  · have key := far_block_pos N a H hN haN hH haH (-v) (by linarith)
      (by rw [abs_of_neg h] at hvN; linarith)
    have e : ∑ n ∈ Finset.Ioc a (a + H), chi n v =
        (starRingEnd ℂ) (∑ n ∈ Finset.Ioc a (a + H), chi n (-v)) := by
      rw [map_sum]; refine Finset.sum_congr rfl fun n _ => ?_
      rw [chi_neg, Complex.conj_conj]
    rw [e, Complex.norm_conj, abs_of_neg h]
    exact key
  · rw [abs_of_pos h] at hvN ⊢
    exact far_block_pos N a H hN haN hH haH v h hvN

end GuthMaynard.S1

end
end

section
section
namespace GuthMaynard.S1

open Finset Complex

lemma harm_range_le (n J : ℕ) (hn : n ≤ J) (hJ : 1 ≤ J) :
    ∑ i ∈ range n, 1 / ((i : ℝ) + 1) ≤ 1 + Real.log J := by
  have h1 := harmonic_le_one_add_log n
  have h2 : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ range n, 1 / ((i : ℝ) + 1) := by
    simp [harmonic]
  rw [h2] at h1
  refine h1.trans ?_
  have : Real.log n ≤ Real.log J := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp; exact Real.log_nonneg (by exact_mod_cast hJ)
    · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hn)
  linarith

lemma harm_bound (J j : ℕ) (hj : j < J) :
    ∑ k ∈ (range J).erase j, 1 / |(j : ℝ) - k| ≤ 2 * (1 + Real.log J) := by
  have hJ : 1 ≤ J := by omega
  have hsplit : (range J).erase j = range j ∪ Ico (j + 1) J := by
    ext k; simp only [mem_erase, mem_range, mem_union, mem_Ico]; omega
  have hdisj : Disjoint (range j) (Ico (j + 1) J) := by
    rw [Finset.disjoint_left]; intro k hk hk'; simp only [mem_range, mem_Ico] at hk hk'; omega
  rw [hsplit, Finset.sum_union hdisj]
  have e1 : ∑ k ∈ range j, 1 / |(j : ℝ) - k| = ∑ i ∈ range j, 1 / ((i : ℝ) + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have : (j : ℝ) - ((j - 1 - i : ℕ) : ℝ) = (i : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [this, abs_of_pos (by positivity)]
  have e2 : ∑ k ∈ Ico (j + 1) J, 1 / |(j : ℝ) - k| = ∑ i ∈ range (J - (j + 1)), 1 / ((i : ℝ) + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : (j : ℝ) - ((j + 1 + i : ℕ) : ℝ) = -((i : ℝ) + 1) := by push_cast; ring
    rw [this, abs_neg, abs_of_pos (by positivity)]
  rw [e1, e2]
  have a1 := harm_range_le j J hj.le hJ
  have a2 := harm_range_le (J - (j + 1)) J (by omega) hJ
  linarith

/-- the `k`-th block of integers -/
def blk (N H k : ℕ) : Finset ℕ := Finset.Ioc (N + k * H) (N + k * H + H)

lemma blk_disjoint (N H : ℕ) {k k' : ℕ} (h : k ≠ k') : Disjoint (blk N H k) (blk N H k') := by
  rw [Finset.disjoint_left]
  intro n hn hn'
  simp only [blk, mem_Ioc] at hn hn'
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have : (k + 1) * H ≤ k' * H := Nat.mul_le_mul_right H hlt
    nlinarith
  · have : (k' + 1) * H ≤ k * H := Nat.mul_le_mul_right H hgt
    nlinarith

lemma blk_subset (N H J k : ℕ) (hk : k < J) (hJH : J * H ≤ N) :
    blk N H k ⊆ Finset.Ioc N (2 * N) := by
  intro n hn
  simp only [blk, mem_Ioc] at hn ⊢
  have : (k + 1) * H ≤ J * H := Nat.mul_le_mul_right H hk
  constructor <;> nlinarith [Nat.zero_le (k * H)]

/-- the coefficients -/
noncomputable def bco (N H J Δ : ℕ) (n : ℕ) : ℂ :=
  ∑ k ∈ range J, if n ∈ blk N H k then chi n (-((k * Δ : ℕ) : ℝ)) else 0

lemma norm_bco_le (N H J Δ : ℕ) (n : ℕ) : ‖bco N H J Δ n‖ ≤ 1 := by
  unfold bco
  by_cases h : ∃ k ∈ range J, n ∈ blk N H k
  · obtain ⟨k₀, hk₀, hn₀⟩ := h
    rw [Finset.sum_eq_single_of_mem k₀ hk₀]
    · rw [if_pos hn₀, norm_chi]
    · intro k _ hk
      rw [if_neg]
      intro hn
      exact (Finset.disjoint_left.mp (blk_disjoint N H hk) hn) hn₀
  · push_neg at h
    rw [Finset.sum_eq_zero]
    · simp
    · intro k hk; rw [if_neg (h k hk)]

lemma D_eq (N H J Δ : ℕ) (hJH : J * H ≤ N) (t : ℝ) :
    ∑ n ∈ Finset.Ioc N (2 * N), bco N H J Δ n * chi n t =
      ∑ k ∈ range J, ∑ n ∈ blk N H k, chi n (t - ((k * Δ : ℕ) : ℝ)) := by
  unfold bco
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have : ∀ n ∈ Finset.Ioc N (2 * N), (if n ∈ blk N H k then chi n (-((k * Δ : ℕ) : ℝ)) else 0) * chi n t =
      if n ∈ blk N H k then chi n (t - ((k * Δ : ℕ) : ℝ)) else 0 := by
    intro n _
    split_ifs
    · rw [sub_eq_add_neg, chi_add]; ring
    · simp
  rw [Finset.sum_congr rfl this, ← Finset.sum_filter]
  congr 1
  ext n
  simp only [mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨blk_subset N H J k hk' hJH h, h⟩⟩

lemma chi_mul_conj (n n' : ℕ) (m : ℝ) :
    chi n m * (starRingEnd ℂ) (chi n' m) =
      Complex.exp (((m * (Real.log n - Real.log n') : ℝ) : ℂ) * Complex.I) := by
  rw [chi, chi, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

lemma main_lower (N H L j m : ℕ) (hN : 1 ≤ N) (hH : 1 ≤ H) (hLH : 2 * L * H ≤ N) (hm : m < L) :
    (7 / 8 : ℝ) * H ≤ ‖∑ n ∈ blk N H j, chi n (m : ℝ)‖ := by
  set a := N + j * H with ha
  have hblk : blk N H j = Finset.Ioc a (a + H) := rfl
  have haN : N ≤ a := by omega
  set w : ℂ := (starRingEnd ℂ) (chi (a + 1) (m : ℝ)) with hw
  have hwn : ‖w‖ = 1 := by rw [hw, Complex.norm_conj, norm_chi]
  set S := ∑ n ∈ blk N H j, chi n (m : ℝ) with hS
  have h1 : (S * w).re ≤ ‖S‖ := by
    calc (S * w).re ≤ ‖S * w‖ := Complex.re_le_norm _
      _ = ‖S‖ := by rw [norm_mul, hwn, mul_one]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : ∀ n ∈ blk N H j, (7 / 8 : ℝ) ≤ (chi n (m : ℝ) * w).re := by
    intro n hn
    rw [hblk, Finset.mem_Ioc] at hn
    rw [hw, chi_mul_conj, Complex.exp_ofReal_mul_I_re]
    have hn1 : (a + 1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hn2 : (n : ℝ) ≤ a + H := by exact_mod_cast hn.2
    have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hNa : (N : ℝ) ≤ a := by exact_mod_cast haN
    have hd0 : 0 ≤ Real.log n - Real.log ((a + 1 : ℕ) : ℝ) := by
      have : Real.log ((a + 1 : ℕ) : ℝ) ≤ Real.log n := by
        apply Real.log_le_log (by push_cast; positivity)
        push_cast; exact hn1
      linarith
    have hd1 : Real.log n - Real.log ((a + 1 : ℕ) : ℝ) ≤ H / N := by
      have hnpos : (0 : ℝ) < n := by linarith
      have := Real.log_le_sub_one_of_pos (show 0 < (n : ℝ) / ((a + 1 : ℕ) : ℝ) by
        push_cast; positivity)
      rw [Real.log_div hnpos.ne' (by push_cast; positivity)] at this
      have h3 : (n : ℝ) / ((a + 1 : ℕ) : ℝ) - 1 = ((n : ℝ) - ((a + 1 : ℕ) : ℝ)) / ((a + 1 : ℕ) : ℝ) := by
        field_simp
      have h4 : ((n : ℝ) - ((a + 1 : ℕ) : ℝ)) / ((a + 1 : ℕ) : ℝ) ≤ H / N := by
        rw [div_le_div_iff₀ (by push_cast; positivity) hN0]
        push_cast
        have : (0 : ℝ) ≤ H := by positivity
        nlinarith
      linarith
    set x := (m : ℝ) * (Real.log n - Real.log ((a + 1 : ℕ) : ℝ)) with hx
    have hx0 : 0 ≤ x := by positivity
    have hmL : (m : ℝ) ≤ L := by exact_mod_cast hm.le
    have hLHN : 2 * (L : ℝ) * H ≤ N := by exact_mod_cast hLH
    have hx1 : x ≤ 1 / 2 := by
      calc x ≤ (L : ℝ) * (H / N) := by
            rw [hx]; exact mul_le_mul hmL hd1 hd0 (by positivity)
        _ = (L * H : ℝ) / N := by ring
        _ ≤ 1 / 2 := by rw [div_le_div_iff₀ hN0 (by norm_num)]; nlinarith
    have := Real.one_sub_sq_div_two_le_cos (x := x)
    nlinarith
  have h3 : (S * w).re = ∑ n ∈ blk N H j, (chi n (m : ℝ) * w).re := by
    rw [hS, Finset.sum_mul, Complex.re_sum]
  have h4 : (7 / 8 : ℝ) * H ≤ ∑ n ∈ blk N H j, (chi n (m : ℝ) * w).re := by
    calc (7 / 8 : ℝ) * H = ∑ n ∈ blk N H j, (7 / 8 : ℝ) := by
          rw [Finset.sum_const, hblk, Nat.card_Ioc]; simp; ring
      _ ≤ _ := Finset.sum_le_sum h2
  linarith

lemma interference (N H J L Δ j m : ℕ) (hN : 1 ≤ N) (hH : 1 ≤ H) (hJH : J * H ≤ N)
    (hΔ : 2 * L + 2 ≤ Δ) (hrange : J * Δ + L ≤ N) (hj : j < J) (hm : m < L) :
    ‖∑ k ∈ (range J).erase j, ∑ n ∈ blk N H k,
        chi n (((j * Δ + m : ℕ) : ℝ) - ((k * Δ : ℕ) : ℝ))‖ ≤ 120 * N * (1 + Real.log J) / Δ := by
  have hΔ0 : (0 : ℝ) < Δ := by have : 0 < Δ := by omega
                               exact_mod_cast this
  have hterm : ∀ k ∈ (range J).erase j, ‖∑ n ∈ blk N H k,
      chi n (((j * Δ + m : ℕ) : ℝ) - ((k * Δ : ℕ) : ℝ))‖ ≤ 60 * N / Δ * (1 / |(j : ℝ) - k|) := by
    intro k hk
    have hkJ : k < J := Finset.mem_range.mp (Finset.mem_of_mem_erase hk)
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    have hjk : (1 : ℝ) ≤ |(j : ℝ) - k| := by
      rcases lt_or_gt_of_ne hkj with h | h
      · have hc : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]
        linarith
      · have hc : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]
        linarith
    set v : ℝ := ((j * Δ + m : ℕ) : ℝ) - ((k * Δ : ℕ) : ℝ) with hv
    have hv_eq : v = ((j : ℝ) - k) * Δ + m := by rw [hv]; push_cast; ring
    have hmL : (m : ℝ) ≤ L := by exact_mod_cast hm.le
    have hΔL : 2 * (L : ℝ) + 2 ≤ Δ := by exact_mod_cast hΔ
    have hv_lb : |(j : ℝ) - k| * Δ / 2 ≤ |v| := by
      have h1 : |((j : ℝ) - k) * Δ| = |(j : ℝ) - k| * Δ := by
        rw [abs_mul, abs_of_pos hΔ0]
      have h2 : |((j : ℝ) - k) * Δ| - m ≤ |v| := by
        rw [hv_eq]
        have h5 : |((j : ℝ) - k) * Δ + m| ≥ |((j : ℝ) - k) * Δ| - |(m : ℝ)| := by
          have := abs_add_le (((j : ℝ) - k) * Δ + m) (-(m : ℝ))
          rw [abs_neg] at this
          have e : ((j : ℝ) - k) * Δ + m + -(m : ℝ) = ((j : ℝ) - k) * Δ := by ring
          rw [e] at this
          linarith
        have hmabs : |(m : ℝ)| = m := abs_of_nonneg (Nat.cast_nonneg m)
        rw [hmabs] at h5
        linarith
      nlinarith
    have hv_ub : |v| ≤ N := by
      have hj1 : (j : ℝ) * Δ + m ≤ N := by
        have : j * Δ + m ≤ N := by
          have : j * Δ ≤ J * Δ := Nat.mul_le_mul_right Δ hj.le
          omega
        exact_mod_cast this
      have hk1 : (k : ℝ) * Δ ≤ N := by
        have : k * Δ ≤ N := by
          have : k * Δ ≤ J * Δ := Nat.mul_le_mul_right Δ hkJ.le
          omega
        exact_mod_cast this
      rw [hv_eq, abs_le]
      have hk0 : (0 : ℝ) ≤ k * Δ := by positivity
      have hj0 : (0 : ℝ) ≤ j * Δ := by positivity
      constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hv0 : v ≠ 0 := by
      intro h0; rw [h0, abs_zero] at hv_lb
      have : 0 < |(j : ℝ) - k| * Δ / 2 := by positivity
      linarith
    have hfb := far_block N (N + k * H) H hN (by omega) hH
      (by have : (k + 1) * H ≤ J * H := Nat.mul_le_mul_right H hkJ; nlinarith) v hv0 hv_ub
    have hbl : blk N H k = Finset.Ioc (N + k * H) (N + k * H + H) := rfl
    rw [hbl]
    refine hfb.trans ?_
    have hvpos : 0 < |v| := abs_pos.mpr hv0
    calc 30 * (N : ℝ) / |v| ≤ 30 * N / (|(j : ℝ) - k| * Δ / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hv_lb
      _ = 60 * N / Δ * (1 / |(j : ℝ) - k|) := by
          have : 0 < |(j : ℝ) - k| := by linarith
          field_simp
          norm_num
  calc _ ≤ ∑ k ∈ (range J).erase j, ‖∑ n ∈ blk N H k,
        chi n (((j * Δ + m : ℕ) : ℝ) - ((k * Δ : ℕ) : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ (range J).erase j, 60 * (N : ℝ) / Δ * (1 / |(j : ℝ) - k|) := Finset.sum_le_sum hterm
    _ = 60 * N / Δ * ∑ k ∈ (range J).erase j, 1 / |(j : ℝ) - k| := by rw [Finset.mul_sum]
    _ ≤ 60 * N / Δ * (2 * (1 + Real.log J)) :=
        mul_le_mul_of_nonneg_left (harm_bound J j hj) (by positivity)
    _ = 120 * N * (1 + Real.log J) / Δ := by ring

theorem construct (N H J L Δ : ℕ) (U : ℝ) (hN : 1 ≤ N) (hH : 1 ≤ H) (hJ : 1 ≤ J) (hL : 1 ≤ L)
    (hJH : J * H ≤ N) (hLH : 2 * L * H ≤ N) (hΔ : 2 * L + 2 ≤ Δ) (hrange : J * Δ + L ≤ N)
    (hbig : U + 120 * N * (1 + Real.log J) / Δ < 7 / 8 * H) :
    ∃ (b : ℕ → ℂ) (W : Finset ℝ), (∀ n, ‖b n‖ ≤ 1) ∧
      (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) ∧
      (∀ t ∈ W, t ∈ Set.Icc (0 : ℝ) N ∧
        U < ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) ∧
      W.card = J * L := by
  have hΔ0 : 0 < Δ := by omega
  -- the index set
  let f' : ℕ × ℕ → ℕ := fun p => p.1 * Δ + p.2
  let W : Finset ℝ := (range J ×ˢ range L).image (fun p => ((f' p : ℕ) : ℝ))
  have hinj : Set.InjOn f' ↑(range J ×ˢ range L) := by
    rintro ⟨j, m⟩ hjm ⟨j', m'⟩ hjm' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hjm hjm'
    simp only [f'] at h
    have hmΔ : m < Δ := by omega
    have hmΔ' : m' < Δ := by omega
    have hjj : j = j' := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : (j + 1) * Δ ≤ j' * Δ := Nat.mul_le_mul_right Δ hlt
        nlinarith
      · have : (j' + 1) * Δ ≤ j * Δ := Nat.mul_le_mul_right Δ hgt
        nlinarith
    subst hjj
    have : m = m' := by omega
    rw [this]
  have hinjR : Set.InjOn (fun p : ℕ × ℕ => ((f' p : ℕ) : ℝ)) ↑(range J ×ˢ range L) := by
    intro p hp q hq h
    have h' : ((f' p : ℕ) : ℝ) = ((f' q : ℕ) : ℝ) := h
    exact hinj hp hq (by exact_mod_cast h')
  have hcard : W.card = J * L := by
    rw [Finset.card_image_of_injOn hinjR, Finset.card_product, card_range, card_range]
  refine ⟨bco N H J Δ, W, norm_bco_le N H J Δ, ?_, ?_, hcard⟩
  · intro t ht t' ht' hne
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht'
    have hpq : f' p ≠ f' q := fun h => hne (by rw [h])
    rcases lt_or_gt_of_ne hpq with h | h
    · have : ((f' p : ℕ) : ℝ) + 1 ≤ f' q := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have : ((f' q : ℕ) : ℝ) + 1 ≤ f' p := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  · intro t ht
    obtain ⟨⟨j, m⟩, hjm, rfl⟩ := Finset.mem_image.mp ht
    simp only [Finset.mem_product, Finset.mem_range] at hjm
    obtain ⟨hj, hm⟩ := hjm
    simp only [f']
    refine ⟨⟨by positivity, ?_⟩, ?_⟩
    · have : j * Δ + m ≤ N := by
        have : j * Δ ≤ J * Δ := Nat.mul_le_mul_right Δ hj.le
        omega
      exact_mod_cast this
    · -- the main estimate
      have hcv : ∀ n ∈ Finset.Ioc N (2 * N), (n : ℂ) ^ ((((j * Δ + m : ℕ) : ℝ) : ℂ) * Complex.I) =
          chi n ((j * Δ + m : ℕ) : ℝ) := by
        intro n hn
        exact cpow_eq_chi (by have := (Finset.mem_Ioc.mp hn).1; omega) _
      rw [Finset.sum_congr rfl (fun n hn => by rw [hcv n hn]), D_eq N H J Δ hJH]
      rw [← Finset.add_sum_erase (range J) _ (Finset.mem_range.mpr hj)]
      have e : ((j * Δ + m : ℕ) : ℝ) - ((j * Δ : ℕ) : ℝ) = (m : ℝ) := by push_cast; ring
      simp_rw [e]
      have hmain := main_lower N H L j m hN hH hLH hm
      have hint := interference N H J L Δ j m hN hH hJH hΔ hrange hj hm
      have : ‖∑ n ∈ blk N H j, chi n (m : ℝ) + ∑ k ∈ (range J).erase j, ∑ n ∈ blk N H k,
          chi n (((j * Δ + m : ℕ) : ℝ) - ((k * Δ : ℕ) : ℝ))‖ ≥
          ‖∑ n ∈ blk N H j, chi n (m : ℝ)‖ - ‖∑ k ∈ (range J).erase j, ∑ n ∈ blk N H k,
          chi n (((j * Δ + m : ℕ) : ℝ) - ((k * Δ : ℕ) : ℝ))‖ := by
        have := norm_sub_le (∑ n ∈ blk N H j, chi n (m : ℝ) + ∑ k ∈ (range J).erase j, ∑ n ∈ blk N H k,
          chi n (((j * Δ + m : ℕ) : ℝ) - ((k * Δ : ℕ) : ℝ))) (∑ k ∈ (range J).erase j, ∑ n ∈ blk N H k,
          chi n (((j * Δ + m : ℕ) : ℝ) - ((k * Δ : ℕ) : ℝ)))
        have e2 : ∑ n ∈ blk N H j, chi n (m : ℝ) + ∑ k ∈ (range J).erase j, ∑ n ∈ blk N H k,
          chi n (((j * Δ + m : ℕ) : ℝ) - ((k * Δ : ℕ) : ℝ)) - ∑ k ∈ (range J).erase j, ∑ n ∈ blk N H k,
          chi n (((j * Δ + m : ℕ) : ℝ) - ((k * Δ : ℕ) : ℝ)) = ∑ n ∈ blk N H j, chi n (m : ℝ) := by ring
        rw [e2] at this
        linarith
      linarith
  
end GuthMaynard.S1

end
end

section
section
namespace GuthMaynard

open Finset

lemma asymp (σ : ℝ) (h1 : 1 / 2 < σ) (h2 : σ < 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N ∧ 20 ≤ (N : ℝ) ^ (1 - σ) ∧
      13 * (1 + Real.log N) * (N : ℝ) ^ (1 - σ) + 1 ≤ (N : ℝ) ^ σ := by
  set κ : ℝ := (2 * σ - 1) / 2 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  have hσ1 : 0 < 1 - σ := by linarith
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max 1 (max ((20 : ℝ) ^ (1 / (1 - σ))) ((14 + 13 / κ) ^ (1 / κ))))
  refine ⟨N₀, fun N hN => ?_⟩
  have hNr : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := (le_max_left _ _).trans (hN₀.trans hNr)
  have hN20 : (20 : ℝ) ^ (1 / (1 - σ)) ≤ N :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (hN₀.trans hNr)
  have hNκ : (14 + 13 / κ) ^ (1 / κ) ≤ N :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (hN₀.trans hNr)
  have hN0 : (0 : ℝ) < N := by linarith
  refine ⟨by exact_mod_cast hN1, ?_, ?_⟩
  · calc (20 : ℝ) = ((20 : ℝ) ^ (1 / (1 - σ))) ^ (1 - σ) := by
          rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
      _ ≤ (N : ℝ) ^ (1 - σ) := Real.rpow_le_rpow (by positivity) hN20 hσ1.le
  · have hNκ' : 14 + 13 / κ ≤ (N : ℝ) ^ κ := by
      calc 14 + 13 / κ = ((14 + 13 / κ) ^ (1 / κ)) ^ κ := by
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hκ0.ne', Real.rpow_one]
        _ ≤ (N : ℝ) ^ κ := Real.rpow_le_rpow (by positivity) hNκ hκ0.le
    have hlog : Real.log N ≤ (N : ℝ) ^ κ / κ := Real.log_le_rpow_div hN0.le hκ0
    have hNκ1 : 1 ≤ (N : ℝ) ^ κ := Real.one_le_rpow hN1 hκ0.le
    have h1l : 1 + Real.log N ≤ (N : ℝ) ^ κ * (1 + 1 / κ) := by
      calc 1 + Real.log N ≤ 1 + (N : ℝ) ^ κ / κ := by linarith
        _ ≤ (N : ℝ) ^ κ * 1 + (N : ℝ) ^ κ * (1 / κ) := by
            rw [mul_one, mul_one_div]; linarith
        _ = _ := by ring
    have hexp : (N : ℝ) ^ κ * (N : ℝ) ^ (1 - σ) = (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hN0]; congr 1; rw [hκ]; ring
    have hexp2 : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ κ = (N : ℝ) ^ σ := by
      rw [← Real.rpow_add hN0]; congr 1; rw [hκ]; ring
    have hv : 0 < (N : ℝ) ^ (1 - σ) := by positivity
    have hs : 1 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
    calc 13 * (1 + Real.log N) * (N : ℝ) ^ (1 - σ) + 1
        ≤ 13 * ((N : ℝ) ^ κ * (1 + 1 / κ)) * (N : ℝ) ^ (1 - σ) + 1 := by gcongr
      _ = 13 * (1 + 1 / κ) * (N : ℝ) ^ (1 / 2 : ℝ) + 1 := by rw [← hexp]; ring
      _ ≤ 13 * (1 + 1 / κ) * (N : ℝ) ^ (1 / 2 : ℝ) + (N : ℝ) ^ (1 / 2 : ℝ) := by linarith
      _ = (13 + 13 / κ + 1) * (N : ℝ) ^ (1 / 2 : ℝ) := by ring
      _ ≤ (N : ℝ) ^ κ * (N : ℝ) ^ (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
      _ = (N : ℝ) ^ σ := by rw [mul_comm]; exact hexp2

lemma two_floor_ge (x : ℝ) (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.le_floor (by simpa using hx)
  have h2 := Nat.lt_floor_add_one x
  linarith

theorem chk_exists_large_values_card_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ σ : ℝ, σ ∈ Set.Ioo (1 / 2 : ℝ) 1 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ T : ℝ,
      (N : ℝ) ≤ T →
      ∃ (b : ℕ → ℂ) (W : Finset ℝ), (∀ n, ‖b n‖ ≤ 1) ∧ IsSeparated 1 W ∧
        (∀ t ∈ W, t ∈ Set.Icc 0 T ∧
          (N : ℝ) ^ σ < ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) ∧
        c * (N : ℝ) ^ (2 - 2 * σ) ≤ W.card := by
  refine ⟨1 / 200, by norm_num, ?_⟩
  intro σ hσ
  obtain ⟨hσ1, hσ2⟩ := hσ
  obtain ⟨N₀, hN₀⟩ := asymp σ hσ1 hσ2
  refine ⟨N₀, fun N hN T hNT => ?_⟩
  obtain ⟨hN1, hv20, hasy⟩ := hN₀ N hN
  set Nr : ℝ := (N : ℝ) with hNr
  have hNr1 : (1 : ℝ) ≤ Nr := by
    show (1 : ℝ) ≤ (N : ℝ)
    exact_mod_cast hN1
  have hNr0 : 0 < Nr := by linarith
  set u : ℝ := Nr ^ σ with hu
  set v : ℝ := Nr ^ (1 - σ) with hv
  have huv : u * v = Nr := by
    rw [hu, hv, ← Real.rpow_add hNr0]; simp
  have hu1 : 1 ≤ u := Real.one_le_rpow hNr1 (by linarith)
  have hv0 : 0 < v := by linarith
  have hlogN : 0 ≤ Real.log Nr := Real.log_nonneg hNr1
  set ℓ : ℝ := 1 + Real.log Nr with hℓ
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
  -- parameters
  set H : ℕ := ⌈4 * u⌉₊ with hH
  have hH1 : 4 * u ≤ H := Nat.le_ceil _
  have hH2 : (H : ℝ) < 4 * u + 1 := Nat.ceil_lt_add_one (by linarith)
  have hH5 : (H : ℝ) ≤ 5 * u := by linarith
  have hHpos : (0 : ℝ) < H := by linarith
  have hHn : 1 ≤ H := by
    have : 0 < H := by exact_mod_cast hHpos
    omega
  have hNu : 20 * u ≤ Nr := by
    rw [← huv]
    have := mul_le_mul_of_nonneg_left hv20 (by linarith : (0:ℝ) ≤ u)
    linarith
  set J : ℕ := ⌊Nr / H⌋₊ with hJ
  set L : ℕ := ⌊Nr / (2 * H)⌋₊ with hL
  have hx1 : 4 ≤ Nr / H := by rw [le_div_iff₀ hHpos]; nlinarith
  have hx2 : 2 ≤ Nr / (2 * H) := by rw [le_div_iff₀ (by positivity)]; nlinarith
  have hJle : (J : ℝ) ≤ Nr / H := Nat.floor_le (by positivity)
  have hLle : (L : ℝ) ≤ Nr / (2 * H) := Nat.floor_le (by positivity)
  have hJ1 : 1 ≤ J := by
    have : (1 : ℝ) ≤ J := by
      have := two_floor_ge (Nr / H) (by linarith)
      linarith
    exact_mod_cast this
  have hL1 : 1 ≤ L := by
    have : (1 : ℝ) ≤ L := by
      have := two_floor_ge (Nr / (2 * H)) (by linarith)
      linarith
    exact_mod_cast this
  have hJH : J * H ≤ N := by
    have : (J : ℝ) * H ≤ Nr := by
      calc (J : ℝ) * H ≤ (Nr / H) * H := by gcongr
        _ = Nr := by field_simp
    have h' : ((J * H : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; exact this
    exact_mod_cast h'
  have hLH : 2 * L * H ≤ N := by
    have : 2 * (L : ℝ) * H ≤ Nr := by
      calc 2 * (L : ℝ) * H ≤ 2 * (Nr / (2 * H)) * H := by gcongr
        _ = Nr := by field_simp
    have h' : ((2 * L * H : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; exact this
    exact_mod_cast h'
  have hJv : (J : ℝ) ≤ v / 4 := by
    calc (J : ℝ) ≤ Nr / H := hJle
      _ ≤ Nr / (4 * u) := by
          apply div_le_div_of_nonneg_left hNr0.le (by positivity) hH1
      _ = v / 4 := by rw [← huv]; field_simp
  have hLv : (L : ℝ) ≤ v / 8 := by
    calc (L : ℝ) ≤ Nr / (2 * H) := hLle
      _ ≤ Nr / (2 * (4 * u)) := by
          apply div_le_div_of_nonneg_left hNr0.le (by positivity) (by linarith)
      _ = v / 8 := by rw [← huv]; field_simp; ring
  set Δ : ℕ := ⌈50 * ℓ * v⌉₊ with hΔ
  have hΔ1 : 50 * ℓ * v ≤ Δ := Nat.le_ceil _
  have hΔ2 : (Δ : ℝ) < 50 * ℓ * v + 1 := Nat.ceil_lt_add_one (by positivity)
  have hΔ0 : (0 : ℝ) < Δ := by
    have : 0 < 50 * ℓ * v := by positivity
    linarith
  have hΔ3 : 2 * L + 2 ≤ Δ := by
    have : (2 * L + 2 : ℝ) ≤ Δ := by nlinarith
    exact_mod_cast this
  have hrange : J * Δ + L ≤ N := by
    have : (J : ℝ) * Δ + L ≤ Nr := by
      have h1 : (J : ℝ) * Δ ≤ (v / 4) * (50 * ℓ * v + 1) :=
        mul_le_mul hJv hΔ2.le hΔ0.le (by positivity)
      have h2 : 13 * ℓ * v + 1 ≤ u := by rw [hℓ]; linarith
      have h3 : (13 * ℓ * v + 1) * v ≤ u * v := mul_le_mul_of_nonneg_right h2 hv0.le
      nlinarith
    have h' : ((J * Δ + L : ℕ) : ℝ) ≤ (N : ℝ) := by push_cast; exact this
    exact_mod_cast h'
  have hlogJ : Real.log J ≤ Real.log Nr := by
    apply Real.log_le_log (by exact_mod_cast hJ1)
    exact hJle.trans (by
      rw [div_le_iff₀ hHpos]
      have : (1 : ℝ) ≤ H := by exact_mod_cast hHn
      nlinarith)
  have hbig : u + 120 * Nr * (1 + Real.log J) / Δ < 7 / 8 * H := by
    have h1 : 120 * Nr * (1 + Real.log J) / Δ ≤ 120 * Nr * ℓ / (50 * ℓ * v) := by
      refine div_le_div₀ (by positivity) ?_ (by positivity) hΔ1
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hℓ]; linarith
    have h2 : 120 * Nr * ℓ / (50 * ℓ * v) = 12 / 5 * u := by
      rw [← huv]; field_simp; ring
    have hu0 : 0 < u := by linarith
    nlinarith
  obtain ⟨b, W, hb, hsep, hmem, hcard⟩ := S1.construct N H J L Δ u hN1 hHn hJ1 hL1 hJH hLH hΔ3 hrange hbig
  refine ⟨b, W, hb, hsep, fun t ht => ⟨?_, (hmem t ht).2⟩, ?_⟩
  · have := (hmem t ht).1
    exact ⟨this.1, this.2.trans hNT⟩
  · rw [hcard, Nat.cast_mul]
    have hJ2 : Nr / H / 2 ≤ J := two_floor_ge _ (by linarith)
    have hL2 : Nr / (2 * H) / 2 ≤ L := two_floor_ge _ (by linarith)
    have hpow : Nr ^ (2 - 2 * σ) = v ^ 2 := by
      rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hNr0.le]; congr 1; push_cast; ring
    rw [hpow]
    have hJL : Nr / H / 2 * (Nr / (2 * H) / 2) ≤ (J : ℝ) * L :=
      mul_le_mul hJ2 hL2 (by positivity) (by positivity)
    have hH2' : (H : ℝ) ^ 2 ≤ 25 * u ^ 2 := by
      have := pow_le_pow_left₀ hHpos.le hH5 2
      calc (H : ℝ) ^ 2 ≤ (5 * u) ^ 2 := this
        _ = 25 * u ^ 2 := by ring
    have h3 : 1 / 200 * v ^ 2 ≤ Nr / H / 2 * (Nr / (2 * H) / 2) := by
      have e : Nr / H / 2 * (Nr / (2 * H) / 2) = Nr ^ 2 / (8 * H ^ 2) := by field_simp; ring
      rw [e, le_div_iff₀ (by positivity)]
      have hv2 : Nr ^ 2 = u ^ 2 * v ^ 2 := by rw [← huv]; ring
      rw [hv2]
      calc 1 / 200 * v ^ 2 * (8 * (H : ℝ) ^ 2) ≤ 1 / 200 * v ^ 2 * (8 * (25 * u ^ 2)) := by
            gcongr
        _ = u ^ 2 * v ^ 2 := by ring
    linarith

alias exists_large_values_card_ge_dev := chk_exists_large_values_card_ge

end GuthMaynard

end
end

section
open GuthMaynard

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ σ : ℝ, σ ∈ Set.Ioo (1 / 2 : ℝ) 1 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ T : ℝ, (N : ℝ) ≤ T →
      ∃ (b : ℕ → ℂ) (W : Finset ℝ), (∀ n, ‖b n‖ ≤ 1) ∧ IsSeparated 1 W ∧
        (∀ t ∈ W, t ∈ Set.Icc 0 T ∧
          (N : ℝ) ^ σ < ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) ∧
        c * (N : ℝ) ^ (2 - 2 * σ) ≤ W.card := by
  apply GuthMaynard.exists_large_values_card_ge_dev <;> assumption

end
