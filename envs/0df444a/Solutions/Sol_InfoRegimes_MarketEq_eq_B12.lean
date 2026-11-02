-- Prove2me | solution 1 for InfoRegimes.MarketEq.eq_B12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:06:12.446395+00:00
-- url     : https://prove2.me/submissions/06d47d31-6a32-4f8d-ac66-28b64dd02eae

import Mathlib
import Definitions.Def_InfoRegimes_MarketEq_Model

namespace IR41B
open InfoRegimes.MarketEq

lemma trans_nonneg (P : Params) (lam : State P → ℝ) (i j : State P) : 0 ≤ trans P lam i j :=
  ENNReal.toReal_nonneg

lemma trans_sum (P : Params) (lam : State P → ℝ) (i : State P) :
    ∑ j, trans P lam i j = 1 := by
  set c := P.af + P.bf * lam i + P.kf * (grid P i - P.af) with hc
  let A : State P → Set ℝ := fun j => {e : ℝ | projD P (c + e) = j}
  have hnat : Measurable (fun e : ℝ => min P.m ⌈(P.m : ℝ) * max 0 (min 1 (c + e))⌉₊) :=
    measurable_const.min ((measurable_const.mul (measurable_const.max
      (measurable_const.min (measurable_const.add measurable_id)))).nat_ceil)
  have hmeas : ∀ j, MeasurableSet (A j) := by
    intro j
    have : A j = (fun e : ℝ => min P.m ⌈(P.m : ℝ) * max 0 (min 1 (c + e))⌉₊) ⁻¹' {(j : ℕ)} := by
      ext e
      simp only [A, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, projD, Fin.ext_iff]
    rw [this]
    exact hnat (measurableSet_singleton _)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (State P))) A := by
    intro j _ k _ hjk
    rw [Function.onFun, Set.disjoint_left]
    intro e hej hek
    exact hjk (hej.symm.trans hek)
  have hunion : (⋃ j ∈ (Finset.univ : Finset (State P)), A j) = Set.univ := by
    ext e
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left, Set.mem_univ, iff_true]
    exact ⟨projD P (c + e), rfl⟩
  have h1 := MeasureTheory.measure_biUnion_finset (μ := (P.shock : MeasureTheory.Measure ℝ))
    hdisj (fun j _ => hmeas j)
  rw [hunion, MeasureTheory.measure_univ] at h1
  unfold InfoRegimes.MarketEq.trans
  rw [← ENNReal.toReal_sum (fun j _ => MeasureTheory.measure_ne_top _ _)]
  have : (∑ j, (P.shock : MeasureTheory.Measure ℝ) {e : ℝ | projD P
      (P.af + P.bf * lam i + P.kf * (grid P i - P.af) + e) = j}) = 1 := by
    rw [h1]
  rw [this, ENNReal.toReal_one]


lemma quad_max (N γ Q q : ℝ) (hγ : 0 < γ) (hQ : 0 < Q)
    (h : ∀ y, y * N - γ / 2 * y ^ 2 * Q ≤ q * N - γ / 2 * q ^ 2 * Q) : q = N / (γ * Q) := by
  set y := N / (γ * Q) with hy
  have key : q * N - γ / 2 * q ^ 2 * Q = y * N - γ / 2 * y ^ 2 * Q - γ * Q / 2 * (q - y) ^ 2 := by
    rw [hy]; field_simp; ring
  have h1 := h y
  have h2 : γ * Q / 2 * (q - y) ^ 2 ≤ 0 := by linarith
  have h3 : 0 < γ * Q / 2 := by positivity
  have h4 : (q - y) ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (q - y)]) (sq_nonneg _)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
  linarith

/-- Positivity of the two conditional variances, for any coefficients. -/
lemma q_pos (P : Params) (hS : P.Standing) (lam : State P → ℝ) (VB : State P → ℝ)
    (hVB : ∀ i, 0 < VB i) (C : PriceCoeffs P) (i : State P) :
    0 < qID P lam VB C i ∧ qID P lam VB C i ≤ qUD P lam VB C i := by
  obtain ⟨hR, _, _, hσM, hσX, hγ, hφ0, hφ1, hX, hm⟩ := hS
  have hgrid : 0 ≤ grid P i ∧ grid P i ≤ 1 := by
    have hm' : (0 : ℝ) < P.m := by exact_mod_cast hm
    unfold grid
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hm']
    exact_mod_cast Nat.lt_succ_iff.mp i.2
  have hEfVB : 0 < Ef P lam i VB := by
    obtain ⟨k0, _, hk0⟩ := Finset.exists_min_image Finset.univ VB Finset.univ_nonempty
    unfold Ef
    calc 0 < VB k0 := hVB k0
      _ = ∑ l, trans P lam i l * VB k0 := by rw [← Finset.sum_mul, trans_sum, one_mul]
      _ ≤ ∑ l, trans P lam i l * VB l := Finset.sum_le_sum (fun l _ =>
          mul_le_mul_of_nonneg_left (hk0 l (Finset.mem_univ l)) (trans_nonneg P lam i l))
  have hQI : 0 < qID P lam VB C i := by
    unfold qID
    have h1 : 0 ≤ (1 + C.d) ^ 2 * (1 - grid P i) * P.sigM ^ 2 := by
      have : 0 ≤ 1 - grid P i := by linarith [hgrid.2]
      positivity
    linarith
  have hKb : Kgain P C i * C.b i ≤ 1 := by
    unfold Kgain
    have hA : 0 ≤ C.b i ^ 2 * P.phi * grid P i * P.sigM ^ 2 := by
      have := hgrid.1; positivity
    have hB : 0 ≤ C.c i ^ 2 * P.sigX ^ 2 := by positivity
    rw [div_mul_eq_mul_div]
    have e : C.b i * P.phi * grid P i * P.sigM ^ 2 * C.b i =
        C.b i ^ 2 * P.phi * grid P i * P.sigM ^ 2 := by ring
    rw [e]
    exact div_le_one_of_le₀ (by linarith) (by linarith)
  refine ⟨hQI, ?_⟩
  unfold qUD
  have : 0 ≤ (1 + C.d) ^ 2 * (P.phi * grid P i * P.sigM ^ 2 * (1 - Kgain P C i * C.b i)) := by
    have := hgrid.1
    have : 0 ≤ 1 - Kgain P C i * C.b i := by linarith
    positivity
  linarith

/-- The clearing identity at every realization, with the optimal demands substituted. -/
lemma clear_eq (P : Params) (hS : P.Standing) (lam : State P → ℝ) (VB : State P → ℝ)
    (hVB : ∀ i, 0 < VB i) (C : PriceCoeffs P) (hC : Clears P lam VB C) (i : State P)
    (mm θ X D : ℝ) :
    lam i * (((1 + C.d) * (muD P + P.rho * D + θ + mm) + Ef P lam i C.a
        - P.R * (C.a i + C.b i * mm + C.g * θ - C.c i * X + C.d * D)) /
        (P.gam * qID P lam VB C i)) +
      (1 - lam i) * (((1 + C.d) * (muD P + P.rho * D + θ + Kgain P C i *
        ((C.a i + C.b i * mm + C.g * θ - C.c i * X + C.d * D) - C.a i - C.g * θ - C.d * D))
        + Ef P lam i C.a - P.R * (C.a i + C.b i * mm + C.g * θ - C.c i * X + C.d * D)) /
        (P.gam * qUD P lam VB C i)) = P.Xbar + X := by
  have hγ : 0 < P.gam := hS.2.2.2.2.2.1
  obtain ⟨hQI, hQU⟩ := q_pos P hS lam VB hVB C i
  obtain ⟨qI, qU, hI, hU, hclear⟩ := hC i mm θ X D
  have hI' := quad_max _ P.gam _ qI hγ hQI (fun y => isMaxOn_iff.mp hI y (Set.mem_univ y))
  have hU' := quad_max _ P.gam _ qU hγ (lt_of_lt_of_le hQI hQU)
    (fun y => isMaxOn_iff.mp hU y (Set.mem_univ y))
  rw [hI', hU'] at hclear
  exact hclear

lemma coeffs (l γ QI QU k R ρ d g μ a Ea b c K Xb : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hγ : 0 < γ) (hQI : 0 < QI) (hQU : 0 < QU)
    (h : ∀ mm θ X D : ℝ,
      l * ((k * (μ + ρ * D + θ + mm) + Ea - R * (a + b * mm + g * θ - c * X + d * D)) /
        (γ * QI)) +
      (1 - l) * ((k * (μ + ρ * D + θ + K * ((a + b * mm + g * θ - c * X + d * D) - a - g * θ
        - d * D)) + Ea - R * (a + b * mm + g * θ - c * X + d * D)) / (γ * QU)) = Xb + X) :
    k * ρ = R * d ∧ k = R * g ∧ l * (k - R * b) * QU + (1 - l) * (k * K * b - R * b) * QI = 0 ∧
      l * R * c * QU + (1 - l) * (R * c - k * K * c) * QI = γ * QI * QU := by
  have h0 := h 0 0 0 0
  have hD := h 0 0 0 1
  have hθ := h 0 1 0 0
  have hm := h 1 0 0 0
  have hX := h 0 0 1 0
  set u := (γ * QI)⁻¹ with hu
  set v := (γ * QU)⁻¹ with hv
  simp only [div_eq_mul_inv, ← hu, ← hv] at h0 hD hθ hm hX
  have hu0 : 0 < u := by rw [hu]; positivity
  have hv0 : 0 < v := by rw [hv]; positivity
  have huI : u * (γ * QI) = 1 := by rw [hu]; field_simp
  have hvU : v * (γ * QU) = 1 := by rw [hv]; field_simp
  have hW : 0 < l * u + (1 - l) * v := by
    rcases eq_or_lt_of_le hl0 with hl | hl
    · rw [← hl]; simp [hv0]
    · have : 0 ≤ (1 - l) * v := mul_nonneg (by linarith) hv0.le
      have : 0 < l * u := mul_pos hl hu0
      linarith
  have eD : (k * ρ - R * d) * (l * u + (1 - l) * v) = 0 := by linear_combination hD - h0
  have eθ : (k - R * g) * (l * u + (1 - l) * v) = 0 := by linear_combination hθ - h0
  have em : l * (k - R * b) * u + (1 - l) * (k * K * b - R * b) * v = 0 := by
    linear_combination hm - h0
  have eX : l * (R * c) * u + (1 - l) * (R * c - k * K * c) * v = 1 := by
    linear_combination hX - h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (mul_eq_zero.mp eD).resolve_right hW.ne'
    linarith
  · have := (mul_eq_zero.mp eθ).resolve_right hW.ne'
    linarith
  · linear_combination (γ * QI * QU) * em - (l * (k - R * b) * QU) * huI
      - ((1 - l) * (k * K * b - R * b) * QI) * hvU
  · linear_combination (γ * QI * QU) * eX - (l * (R * c) * QU) * huI
      - ((1 - l) * (R * c - k * K * c) * QI) * hvU

end IR41B

open InfoRegimes.MarketEq IR41B in
theorem solution (P : Params) (hS : P.Standing) (lam : State P → ℝ)
    (hlam : ∀ i, lam i ∈ Set.Icc (0 : ℝ) 1) (VB : State P → ℝ) (hVB : ∀ i, 0 < VB i)
    (C : PriceCoeffs P) (hC : Clears P lam VB C) (i : State P) :
    (0 < lam i → C.c i ≠ 0 ∧
        C.b i / C.c i = lam i * (1 + C.d) / (P.gam * qID P lam VB C i)) ∧
      (lam i = 0 → C.c i = P.gam * qUD P lam VB C i / P.R) := by
  have hR : 1 < P.R := hS.1
  have hγ : 0 < P.gam := hS.2.2.2.2.2.1
  obtain ⟨hQI, hQU⟩ := q_pos P hS lam VB hVB C i
  have hQU0 : 0 < qUD P lam VB C i := lt_of_lt_of_le hQI hQU
  obtain ⟨-, -, hm, hX⟩ := coeffs (lam i) P.gam (qID P lam VB C i) (qUD P lam VB C i) (1 + C.d)
    P.R P.rho C.d C.g (muD P) (C.a i) (Ef P lam i C.a) (C.b i) (C.c i) (Kgain P C i) P.Xbar
    (hlam i).1 (hlam i).2 hγ hQI hQU0
    (fun mm θ X D => clear_eq P hS lam VB hVB C hC i mm θ X D)
  set QI := qID P lam VB C i
  set QU := qUD P lam VB C i
  set K := Kgain P C i with hK
  set b := C.b i
  set c := C.c i
  set l := lam i
  set k := 1 + C.d
  -- K = 0 whenever b = 0
  have hK0 : b = 0 → K = 0 := by
    intro hb
    rw [hK]; unfold Kgain
    show b * P.phi * grid P i * P.sigM ^ 2 / _ = 0
    rw [hb]; simp
  have hγQ : 0 < P.gam * QI * QU := by positivity
  constructor
  · intro hl
    have hc : c ≠ 0 := by
      intro hc0
      rw [hc0] at hX
      have : P.gam * QI * QU = 0 := by rw [← hX]; ring
      linarith
    have key : l * k * c * QU = P.gam * QI * b * QU := by
      linear_combination c * hm + b * hX
    have key2 : l * k * c = P.gam * QI * b := by
      have h := mul_right_cancel₀ hQU0.ne' key
      exact h
    refine ⟨hc, ?_⟩
    rw [div_eq_div_iff hc (by positivity)]
    linear_combination -key2
  · intro hl
    rw [hl] at hm hX
    have hb0 : b = 0 := by
      by_contra hb
      have h1 : b * (k * K - P.R) * QI = 0 := by linear_combination hm
      have h2 : k * K - P.R = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' hb
          · exact h'
        · exact absurd h hQI.ne'
      have h3 : P.gam * QI * QU = 0 := by linear_combination -hX - c * QI * h2
      linarith
    have hK' : K = 0 := hK0 hb0
    rw [hK'] at hX
    rw [eq_div_iff (by linarith)]
    have h4 : QI * (c * P.R - P.gam * QU) = 0 := by linear_combination hX
    have := (mul_eq_zero.mp h4).resolve_left hQI.ne'
    linarith
