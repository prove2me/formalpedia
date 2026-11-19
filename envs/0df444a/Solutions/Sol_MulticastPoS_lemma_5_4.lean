-- Prove2me | solution 1 for MulticastPoS.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:07:23.524543+00:00
-- url     : https://prove2.me/submissions/8ccf7fda-f382-4505-b5b1-046eadd35771

import Mathlib

open MeasureTheory

lemma H_succ (n : ℕ) : (harmonic (n + 1) : ℝ) = harmonic n + 1 / ((n:ℝ) + 1) := by
  rw [harmonic_succ]; push_cast; ring

lemma H_nonneg (n : ℕ) : (0:ℝ) ≤ harmonic n := by
  induction n with
  | zero => simp
  | succ n ih => rw [H_succ]; positivity

lemma H_one_le (n : ℕ) (hn : 1 ≤ n) : (1:ℝ) ≤ harmonic n := by
  induction n, hn using Nat.le_induction with
  | base => simp [harmonic]
  | succ n hn ih =>
    rw [H_succ]; have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    linarith

/-- tangent bound: H n ≤ H k - 1 + n / k -/
lemma H_tangent (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    (harmonic n : ℝ) ≤ (harmonic k - 1) + n / k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  set f : ℕ → ℝ := fun n => (harmonic n : ℝ) - n / k with hf
  suffices f n ≤ f k by
    simp only [hf] at this
    rw [div_self hk0.ne'] at this; linarith
  have hstep : ∀ j, f (j + 1) - f j = 1 / ((j:ℝ) + 1) - 1 / k := by
    intro j; simp only [hf]; rw [H_succ]; push_cast; ring
  have hU : ∀ d j, j + d ≤ k → f j ≤ f (j + d) := by
    intro d; induction d with
    | zero => intro j _; simp
    | succ d ih =>
      intro j hj
      have h1 := ih j (by omega)
      have h2 := hstep (j + d)
      have h3 : 1 / (k:ℝ) ≤ 1 / (((j + d : ℕ) : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : ((j + d + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast (by omega : j + d + 1 ≤ k)
        push_cast at this ⊢; linarith
      rw [← add_assoc]; linarith
  have hD : ∀ d, f (k + d) ≤ f k := by
    intro d; induction d with
    | zero => simp
    | succ d ih =>
      have h2 := hstep (k + d)
      have h3 : 1 / (((k + d : ℕ) : ℝ) + 1) ≤ 1 / (k:ℝ) := by
        apply one_div_le_one_div_of_le hk0
        push_cast; have : (0:ℝ) ≤ d := Nat.cast_nonneg d; linarith
      rw [← add_assoc]; linarith
  rcases le_total n k with h | h
  · have := hU (k - n) n (by omega); rwa [show n + (k - n) = k by omega] at this
  · have := hD (n - k); rwa [show k + (n - k) = n by omega] at this

/-- H(m)/m decreasing: n ≤ m, 1 ≤ n → n * H m ≤ m * H n -/
lemma H_ratio (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) :
    (n:ℝ) * harmonic m ≤ m * harmonic n := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih =>
    rw [H_succ]; push_cast
    have h1 := H_one_le n hn
    have : (n:ℝ) / ((m:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; have : (n:ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have : (n:ℝ) * (1 / ((m:ℝ) + 1)) ≤ harmonic n := by rw [mul_one_div]; linarith
    nlinarith

lemma small_case (k : ℕ) (hk : 1 ≤ k) (hk9 : k ≤ 9) :
    (2:ℝ) * k * harmonic (4 * max 4 (k + 1)) ≤ (4 * max 4 (k + 1) : ℕ) * harmonic k := by
  interval_cases k <;> norm_num

lemma large_case (k : ℕ) (hk : 10 ≤ k) :
    (2:ℝ) * k * harmonic (4 * (k + 1)) ≤ ((4 * (k + 1) : ℕ) : ℝ) * harmonic k := by
  have h1 := harmonic_le_one_add_log (4 * (k + 1))
  have h2 := log_add_one_le_harmonic k
  push_cast at h2
  have hL : Real.log (((4 * (k + 1) : ℕ) : ℝ)) = Real.log 4 + Real.log ((k:ℝ) + 1) := by
    push_cast; rw [Real.log_mul (by norm_num) (by positivity)]
  rw [hL] at h1
  have h11 : 1 + Real.log 4 ≤ Real.log ((k:ℝ) + 1) := by
    have hk' : (11:ℝ) ≤ (k:ℝ) + 1 := by
      have : (10:ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have he : Real.exp (1 + Real.log 4) ≤ 11 := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    calc 1 + Real.log 4 = Real.log (Real.exp (1 + Real.log 4)) := (Real.log_exp _).symm
      _ ≤ Real.log 11 := Real.log_le_log (Real.exp_pos _) he
      _ ≤ _ := Real.log_le_log (by norm_num) hk'
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hLpos : 0 ≤ Real.log ((k:ℝ) + 1) := Real.log_nonneg (by linarith)
  push_cast
  calc (2:ℝ) * k * harmonic (4 * (k + 1)) ≤ 2 * k * (1 + (Real.log 4 + Real.log ((k:ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (4 * ((k:ℝ) + 1)) * Real.log ((k:ℝ) + 1) := by nlinarith
    _ ≤ (4 * ((k:ℝ) + 1)) * harmonic k := mul_le_mul_of_nonneg_left h2 (by positivity)

lemma numeric (k K : ℕ) (hk : 1 ≤ k) (hK : 4 ≤ K) (hkK : k < K) :
    (2:ℝ) * k * harmonic (4 * K) ≤ (4 * K : ℕ) * harmonic k := by
  set N0 := 4 * max 4 (k + 1) with hN0
  have hN0K : N0 ≤ 4 * K := by omega
  have hbase : (2:ℝ) * k * harmonic N0 ≤ (N0 : ℝ) * harmonic k := by
    rcases le_or_gt k 9 with h | h
    · exact small_case k hk h
    · have : N0 = 4 * (k + 1) := by omega
      rw [this]; exact large_case k (by omega)
  have hr := H_ratio N0 (4 * K) (by omega) hN0K
  have hN0pos : (0:ℝ) < N0 := by exact_mod_cast (by omega : 0 < N0)
  have hHk := H_nonneg k
  -- 2k H(4K) * N0 ≤ 2k * 4K * H(N0) ≤ 4K * N0 * H k
  have : (2:ℝ) * k * harmonic (4 * K) * N0 ≤ ((4 * K : ℕ) : ℝ) * harmonic k * N0 := by
    calc (2:ℝ) * k * harmonic (4 * K) * N0 = 2 * k * (N0 * harmonic (4 * K)) := by ring
      _ ≤ 2 * k * (((4 * K : ℕ) : ℝ) * harmonic N0) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = ((4 * K : ℕ) : ℝ) * (2 * k * harmonic N0) := by ring
      _ ≤ ((4 * K : ℕ) : ℝ) * (N0 * harmonic k) := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = _ := by ring
  exact le_of_mul_le_mul_right this hN0pos

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℕ) (hZ : Measurable Z) (k : ℕ) (hk : 1 ≤ k)
    (hEZ : ∫⁻ ω, (Z ω : ENNReal) ∂μ ≤ k) :
    ∫⁻ ω, ENNReal.ofReal (harmonic (Z ω) : ℝ) ∂μ ≤ ENNReal.ofReal (harmonic k : ℝ) ∧
    ∀ K : ℕ, 4 ≤ K → k < K → (∀ ω, Z ω = 0 ∨ 4 * K ≤ Z ω) →
      ∫⁻ ω, ENNReal.ofReal (harmonic (Z ω) : ℝ) ∂μ ≤
        ENNReal.ofReal ((harmonic k : ℝ) / 2) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hZm : Measurable (fun ω => (Z ω : ENNReal)) := (measurable_from_nat (f := fun n : ℕ => (n : ENNReal))).comp hZ
  constructor
  · set c : ℝ := (harmonic k : ℝ) - 1 with hc
    have hc0 : 0 ≤ c := by have := H_one_le k hk; linarith
    have hpt : ∀ ω, ENNReal.ofReal (harmonic (Z ω) : ℝ) ≤
        ENNReal.ofReal c + (Z ω : ENNReal) * (k : ENNReal)⁻¹ := by
      intro ω
      have h := H_tangent k hk (Z ω)
      calc ENNReal.ofReal (harmonic (Z ω) : ℝ) ≤ ENNReal.ofReal (c + (Z ω : ℝ) / k) :=
            ENNReal.ofReal_le_ofReal (by rw [hc]; linarith)
        _ = ENNReal.ofReal c + ENNReal.ofReal ((Z ω : ℝ) / k) :=
            ENNReal.ofReal_add hc0 (by positivity)
        _ = _ := by
            rw [ENNReal.ofReal_div_of_pos hk0, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
              div_eq_mul_inv]
    calc ∫⁻ ω, ENNReal.ofReal (harmonic (Z ω) : ℝ) ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal c + (Z ω : ENNReal) * (k : ENNReal)⁻¹) ∂μ := lintegral_mono hpt
      _ = ENNReal.ofReal c + (∫⁻ ω, (Z ω : ENNReal) ∂μ) * (k : ENNReal)⁻¹ := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_mul_const _ hZm]
      _ ≤ ENNReal.ofReal c + (k : ENNReal) * (k : ENNReal)⁻¹ := by gcongr
      _ = ENNReal.ofReal c + 1 := by
          rw [ENNReal.mul_inv_cancel (by exact_mod_cast (by omega : k ≠ 0)) (ENNReal.natCast_ne_top k)]
      _ = ENNReal.ofReal (harmonic k : ℝ) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add hc0 zero_le_one, hc]; ring_nf
  · intro K hK hkK hsupp
    set N : ℕ := 4 * K with hN
    have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    set c : ℝ := (harmonic N : ℝ) / N with hc
    have hc0 : 0 ≤ c := div_nonneg (H_nonneg N) hNpos.le
    have hpt : ∀ ω, ENNReal.ofReal (harmonic (Z ω) : ℝ) ≤ ENNReal.ofReal c * (Z ω : ENNReal) := by
      intro ω
      rcases hsupp ω with h0 | hge
      · rw [h0]; simp
      · have hr := H_ratio N (Z ω) (by omega) hge
        have hZpos : (0:ℝ) < Z ω := by exact_mod_cast (by omega : 0 < Z ω)
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hc0]
        apply ENNReal.ofReal_le_ofReal
        rw [hc, div_mul_eq_mul_div, le_div_iff₀ hNpos]
        linarith
    have hnum := numeric k K hk hK hkK
    calc ∫⁻ ω, ENNReal.ofReal (harmonic (Z ω) : ℝ) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal c * (Z ω : ENNReal) ∂μ := lintegral_mono hpt
      _ = ENNReal.ofReal c * ∫⁻ ω, (Z ω : ENNReal) ∂μ := lintegral_const_mul _ hZm
      _ ≤ ENNReal.ofReal c * k := by gcongr
      _ = ENNReal.ofReal (c * k) := by rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((harmonic k : ℝ) / 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hc, div_mul_eq_mul_div, div_le_div_iff₀ hNpos (by norm_num)]
          have : ((4 * K : ℕ) : ℝ) = (N : ℝ) := by rw [hN]
          rw [this] at hnum
          linarith
