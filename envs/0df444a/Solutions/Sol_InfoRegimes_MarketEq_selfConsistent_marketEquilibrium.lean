-- Prove2me | solution 1 for InfoRegimes.MarketEq.selfConsistent_marketEquilibrium
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:02:13.254198+00:00
-- url     : https://prove2.me/submissions/c81ab146-6499-4520-8f7b-e9be45b42c71

import Mathlib
import Definitions.Def_InfoRegimes_MarketEq_Model

namespace IR41SC
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

/-- The linear system `R a - E_t a(f_{t+1}) = s` of (B.19) has a solution. -/
lemma exists_a (P : Params) (hR : 1 < P.R) (lam : State P → ℝ) (s : State P → ℝ) :
    ∃ a : State P → ℝ, ∀ i, P.R * a i - Ef P lam i a = s i := by
  let Φ : (State P → ℝ) →ₗ[ℝ] (State P → ℝ) :=
    { toFun := fun a i => P.R * a i - Ef P lam i a
      map_add' := by
        intro a b; funext i
        simp only [Pi.add_apply, Ef, mul_add, Finset.sum_add_distrib]; ring
      map_smul' := by
        intro c a; funext i
        simp only [Pi.smul_apply, smul_eq_mul, Ef, RingHom.id_apply]
        rw [mul_sub, Finset.mul_sum]
        have : ∀ j, trans P lam i j * (c * a j) = c * (trans P lam i j * a j) := fun j => by ring
        simp only [this]
        ring }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have ha' : ∀ i, P.R * a i = Ef P lam i a := by
      intro i
      have := congrFun ha i
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
      linarith
    obtain ⟨j0, _, hj0⟩ := Finset.exists_max_image Finset.univ (fun j => |a j|)
      Finset.univ_nonempty
    have hEf : |Ef P lam j0 a| ≤ |a j0| := by
      unfold Ef
      calc |∑ l, trans P lam j0 l * a l| ≤ ∑ l, |trans P lam j0 l * a l| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ l, trans P lam j0 l * |a j0| := by
            apply Finset.sum_le_sum; intro l _
            rw [abs_mul, abs_of_nonneg (trans_nonneg P lam j0 l)]
            exact mul_le_mul_of_nonneg_left (hj0 l (Finset.mem_univ l)) (trans_nonneg P lam j0 l)
        _ = |a j0| := by rw [← Finset.sum_mul, trans_sum, one_mul]
    have h1 : P.R * |a j0| ≤ |a j0| := by
      have : |P.R * a j0| = P.R * |a j0| := by rw [abs_mul, abs_of_pos (by linarith)]
      rw [← this, ha' j0]; exact hEf
    have h2 : |a j0| ≤ 0 := by nlinarith [abs_nonneg (a j0)]
    funext l
    have := hj0 l (Finset.mem_univ l)
    have : |a l| = 0 := le_antisymm (by linarith) (abs_nonneg _)
    simpa using this
  obtain ⟨a, ha⟩ := (LinearMap.injective_iff_surjective (f := Φ)).mp hinj s
  refine ⟨a, fun i => ?_⟩
  have := congrFun ha i
  simpa [Φ] using this

/-- Basic facts shared by the bounds. -/
lemma basic_facts (k R γ x σ f φ l q E r ℛ qU : ℝ)
    (hk : 0 < k) (hγ : 0 < γ) (hx : 0 < x) (hσ : 0 < σ)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hE : 0 < E)
    (hq : q = k ^ 2 * (1 - f) * σ + E)
    (hℛ : ℛ = r ^ 2 * f * φ * σ / (r ^ 2 * f * φ * σ + x))
    (hqU : qU = q + k ^ 2 * f * φ * σ * (1 - ℛ)) :
    0 < q ∧ 0 ≤ ℛ ∧ ℛ ≤ 1 ∧ q ≤ qU ∧ qU ≤ k ^ 2 * σ + E ∧
      q ≤ l * qU + (1 - l) * q ∧ l * qU + (1 - l) * q ≤ qU ∧
      0 ≤ l * qU + (1 - l) * q * ℛ ∧
      l * qU + (1 - l) * q * ℛ ≤ l * qU + (1 - l) * q ∧
      ℛ * (l * qU + (1 - l) * q) ≤ l * qU + (1 - l) * q * ℛ ∧
      l * qU ≤ l * qU + (1 - l) * q * ℛ := by
  have hq0 : 0 < q := by
    have : 0 ≤ k ^ 2 * (1 - f) * σ := by
      have : 0 ≤ 1 - f := by linarith
      positivity
    rw [hq]; linarith
  have hs0 : 0 ≤ f * φ * σ := by positivity
  have hu0 : 0 ≤ r ^ 2 * f * φ * σ := by positivity
  have hw0 : 0 < r ^ 2 * f * φ * σ + x := by linarith
  have hℛ0 : 0 ≤ ℛ := by rw [hℛ]; positivity
  have hℛ1 : ℛ ≤ 1 := by rw [hℛ, div_le_one hw0]; linarith
  have h1ℛ : 0 ≤ 1 - ℛ := by linarith
  have hK : 0 ≤ k ^ 2 * f * φ * σ := by positivity
  have hqU_ge : q ≤ qU := by
    have : 0 ≤ k ^ 2 * f * φ * σ * (1 - ℛ) := mul_nonneg hK h1ℛ
    rw [hqU]; linarith
  have hqU_le : qU ≤ k ^ 2 * σ + E := by
    have h1 : k ^ 2 * f * φ * σ * (1 - ℛ) ≤ k ^ 2 * f * φ * σ :=
      mul_le_of_le_one_right hK (by linarith)
    have h2 : k ^ 2 * f * φ * σ ≤ k ^ 2 * f * σ := by
      have e : k ^ 2 * f * φ * σ = (k ^ 2 * f * σ) * φ := by ring
      rw [e]; exact mul_le_of_le_one_right (by positivity) hφ1
    have e3 : k ^ 2 * σ + E = k ^ 2 * (1 - f) * σ + E + k ^ 2 * f * σ := by ring
    rw [hqU, hq, e3]; linarith
  have h1l : 0 ≤ 1 - l := by linarith
  have hlq : l * q ≤ l * qU := mul_le_mul_of_nonneg_left hqU_ge hl0
  have hlq2 : (1 - l) * q ≤ (1 - l) * qU := mul_le_mul_of_nonneg_left hqU_ge h1l
  have hBR : (1 - l) * q * ℛ ≤ (1 - l) * q := mul_le_of_le_one_right (mul_nonneg h1l hq0.le) hℛ1
  have hBR0 : 0 ≤ (1 - l) * q * ℛ := mul_nonneg (mul_nonneg h1l hq0.le) hℛ0
  have hlqU : 0 ≤ l * qU := mul_nonneg hl0 (by linarith)
  have hAR : ℛ * (l * qU) ≤ l * qU := mul_le_of_le_one_left hlqU hℛ1
  refine ⟨hq0, hℛ0, hℛ1, hqU_ge, hqU_le, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · have e : ℛ * (l * qU + (1 - l) * q) = ℛ * (l * qU) + (1 - l) * q * ℛ := by ring
    rw [e]; linarith
  · linarith


lemma state_facts (k R γ x σ f φ l q E r ℛ qU b c : ℝ)
    (hk : 0 < k) (hR : 1 < R) (hγ : 0 < γ) (hx : 0 < x) (hσ : 0 < σ)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hE : 0 < E)
    (hq : q = k ^ 2 * (1 - f) * σ + E)
    (hr : r = l * k / (γ * q))
    (hℛ : ℛ = r ^ 2 * f * φ * σ / (r ^ 2 * f * φ * σ + x))
    (hqU : qU = q + k ^ 2 * f * φ * σ * (1 - ℛ))
    (hb : b = k / R * ((l * qU + (1 - l) * q * ℛ) / (l * qU + (1 - l) * q)))
    (hc : c = if 0 < l then b / r else γ * qU / R) :
    0 < q ∧ 0 < qU ∧ 0 < l * qU + (1 - l) * q ∧
      b * φ * f * σ / (b ^ 2 * φ * f * σ + c ^ 2 * x) * b = ℛ ∧
      R * b * (l * qU + (1 - l) * q) = k * (l * qU + (1 - l) * q * ℛ) ∧
      l * R * c * qU + (1 - l) * (R * c - k * (b * φ * f * σ / (b ^ 2 * φ * f * σ + c ^ 2 * x)) * c)
        * q = γ * q * qU := by
  obtain ⟨hq0, hℛ0, hℛ1, hqU_ge, hqU_le, hDq, hDqU, hN0, hND, hNℛ, hNA⟩ :=
    basic_facts k R γ x σ f φ l q E r ℛ qU hk hγ hx hσ hf0 hf1 hφ0 hφ1 hl0 hl1 hE hq hℛ hqU
  have hR0 : 0 < R := by linarith
  have hD0 : 0 < l * qU + (1 - l) * q := lt_of_lt_of_le hq0 hDq
  have hqU0 : 0 < qU := lt_of_lt_of_le hq0 hqU_ge
  have hbD : R * b * (l * qU + (1 - l) * q) = k * (l * qU + (1 - l) * q * ℛ) := by
    rw [hb]; field_simp
  refine ⟨hq0, hqU0, hD0, ?_, hbD, ?_⟩
  · rcases eq_or_lt_of_le hl0 with hl | hl
    · have hr' : r = 0 := by rw [hr, ← hl]; simp
      have hℛ' : ℛ = 0 := by rw [hℛ, hr']; simp
      have hb' : b = 0 := by rw [hb, hℛ', ← hl]; simp
      rw [hb', hℛ']; simp
    · have hc' : c = b / r := by rw [hc]; simp [hl]
      have hr0 : 0 < r := by rw [hr]; positivity
      have hb0 : 0 < b := by
        rw [hb]
        have : 0 < l * qU := mul_pos hl hqU0
        have : 0 < l * qU + (1 - l) * q * ℛ := by linarith
        positivity
      rw [hc', hℛ]
      field_simp
  · rcases eq_or_lt_of_le hl0 with hl | hl
    · have hc' : c = γ * qU / R := by rw [hc, ← hl]; simp
      have hr' : r = 0 := by rw [hr, ← hl]; simp
      have hℛ' : ℛ = 0 := by rw [hℛ, hr']; simp
      have hb' : b = 0 := by rw [hb, hℛ', ← hl]; simp
      rw [hb', hc', ← hl]
      field_simp
      ring
    · have hc' : c = b / r := by rw [hc]; simp [hl]
      have hr0 : 0 < r := by rw [hr]; positivity
      have hb0 : 0 < b := by
        rw [hb]
        have : 0 < l * qU := mul_pos hl hqU0
        have : 0 < l * qU + (1 - l) * q * ℛ := by linarith
        positivity
      have hKb : b * φ * f * σ / (b ^ 2 * φ * f * σ + c ^ 2 * x) * b = ℛ := by
        rw [hc', hℛ]; field_simp
      have hKc : k * (b * φ * f * σ / (b ^ 2 * φ * f * σ + c ^ 2 * x)) * c = k * ℛ / r := by
        rw [← hKb, hc']; field_simp
      have hrq : r * (γ * q) = l * k := by rw [hr]; field_simp
      rw [hKc, hc']
      field_simp
      linear_combination hbD - qU * hrq
lemma quad_isMax (N γ Q : ℝ) (hγ : 0 < γ) (hQ : 0 < Q) :
    IsMaxOn (fun y : ℝ => y * N - γ / 2 * y ^ 2 * Q) Set.univ (N / (γ * Q)) := by
  intro y _
  simp only [Set.mem_setOf_eq]
  have e : N / (γ * Q) * N - γ / 2 * (N / (γ * Q)) ^ 2 * Q - (y * N - γ / 2 * y ^ 2 * Q)
      = γ * Q / 2 * (y - N / (γ * Q)) ^ 2 := by
    field_simp; ring
  have : 0 ≤ γ * Q / 2 * (y - N / (γ * Q)) ^ 2 := by positivity
  linarith

/-- Market clearing as an identity in the coefficients. -/
lemma clear_alg (R γ Xb QI QU l a Ea μ ρ d g b c K ℛ mm θ X D : ℝ)
    (hγ : 0 < γ) (hQI : 0 < QI) (hQU : 0 < QU) (hDen : 0 < l * QU + (1 - l) * QI)
    (hd : (1 + d) * ρ = R * d) (hg : 1 + d = R * g)
    (ha : (1 + d) * μ + Ea - R * a = γ * QI * QU / (l * QU + (1 - l) * QI) * Xb)
    (hb : R * b * (l * QU + (1 - l) * QI) = (1 + d) * (l * QU + (1 - l) * QI * ℛ))
    (hKb : K * b = ℛ)
    (hX : l * R * c * QU + (1 - l) * (R * c - (1 + d) * K * c) * QI = γ * QI * QU) :
    l * (((1 + d) * (μ + ρ * D + θ + mm) + Ea - R * (a + b * mm + g * θ - c * X + d * D)) /
        (γ * QI)) +
      (1 - l) * (((1 + d) * (μ + ρ * D + θ + K * ((a + b * mm + g * θ - c * X + d * D)
          - a - g * θ - d * D)) + Ea - R * (a + b * mm + g * θ - c * X + d * D)) / (γ * QU))
      = Xb + X := by
  set E0 := (1 + d) * μ + Ea - R * a with hE0
  have hNI : (1 + d) * (μ + ρ * D + θ + mm) + Ea - R * (a + b * mm + g * θ - c * X + d * D)
      = E0 + ((1 + d) - R * b) * mm + R * c * X := by
    rw [hE0]; linear_combination D * hd + θ * hg
  have hNU : (1 + d) * (μ + ρ * D + θ + K * ((a + b * mm + g * θ - c * X + d * D)
          - a - g * θ - d * D)) + Ea - R * (a + b * mm + g * θ - c * X + d * D)
      = E0 + ((1 + d) * (K * b) - R * b) * mm + (R * c - (1 + d) * K * c) * X := by
    rw [hE0]; linear_combination D * hd + θ * hg
  rw [hNI, hNU, hKb]
  have hE0' : E0 * (l * QU + (1 - l) * QI) = γ * QI * QU * Xb := by
    rw [ha, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, div_self hDen.ne', mul_one]
  have e : l * ((E0 + (1 + d - R * b) * mm + R * c * X) / (γ * QI)) +
      (1 - l) * ((E0 + ((1 + d) * ℛ - R * b) * mm + (R * c - (1 + d) * K * c) * X) / (γ * QU))
      = (l * (E0 + (1 + d - R * b) * mm + R * c * X) * QU +
        (1 - l) * (E0 + ((1 + d) * ℛ - R * b) * mm + (R * c - (1 + d) * K * c) * X) * QI) /
        (γ * QI * QU) := by
    field_simp
  rw [e, div_eq_iff (by positivity)]
  linear_combination hE0' - mm * hb + X * hX

end IR41SC

open InfoRegimes.MarketEq IR41SC in
theorem solution (P : Params) (hS : P.Standing) (lam : State P → ℝ)
    (hlam : ∀ i, lam i ∈ Set.Icc (0 : ℝ) 1) (VB : State P → ℝ) (hVB : ∀ i, 0 < VB i) :
    (∃ C : PriceCoeffs P, C.b = bRec P lam VB ∧ C.c = cRec P lam VB ∧
        C.d = dConst P ∧ C.g = gConst P ∧ Clears P lam VB C) ∧
      (Tmap P lam VB = VB → MarketEquilibrium P lam) := by
  obtain ⟨hR1, hρ1, hρ2, hσM, hσX, hγ, hφ0, hφ1, hX, hm⟩ := hS
  have hRρ : 0 < P.R - P.rho := by linarith
  have hk : 0 < 1 + dConst P := by
    unfold dConst
    have : 1 + P.rho / (P.R - P.rho) = P.R / (P.R - P.rho) := by field_simp; ring
    rw [this]; exact div_pos (by linarith) hRρ
  have hd : (1 + dConst P) * P.rho = P.R * dConst P := by
    unfold dConst; field_simp; ring
  have hg : 1 + dConst P = P.R * gConst P := by
    unfold dConst gConst; field_simp; ring
  have hσ : 0 < P.sigM ^ 2 := by positivity
  have hx : 0 < P.sigX ^ 2 := by positivity
  have hgrid : ∀ j : State P, 0 ≤ grid P j ∧ grid P j ≤ 1 := by
    intro j
    have hm' : (0 : ℝ) < P.m := by exact_mod_cast hm
    unfold grid
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hm']
    exact_mod_cast Nat.lt_succ_iff.mp j.2
  have hEf : ∀ j, 0 < Ef P lam j VB := by
    intro j
    obtain ⟨k0, _, hk0⟩ := Finset.exists_min_image Finset.univ VB Finset.univ_nonempty
    unfold Ef
    calc 0 < VB k0 := hVB k0
      _ = ∑ l, trans P lam j l * VB k0 := by rw [← Finset.sum_mul, trans_sum, one_mul]
      _ ≤ ∑ l, trans P lam j l * VB l := Finset.sum_le_sum (fun l _ =>
          mul_le_mul_of_nonneg_left (hk0 l (Finset.mem_univ l)) (trans_nonneg P lam j l))
  have facts := fun i : State P =>
    state_facts (1 + dConst P) P.R P.gam (P.sigX ^ 2) (P.sigM ^ 2) (grid P i) P.phi (lam i)
      (qID0 P lam VB i) (Ef P lam i VB) (r0 P lam VB i) (R2rec P lam VB i) (qUD0 P lam VB i)
      (bRec P lam VB i) (cRec P lam VB i) hk hR1 hγ hx hσ (hgrid i).1 (hgrid i).2 hφ0 hφ1
      (hlam i).1 (hlam i).2 (hEf i) rfl rfl rfl rfl rfl rfl
  -- the a(·) curve
  obtain ⟨a, ha⟩ := exists_a P hR1 lam (fun i => (1 + dConst P) * muD P
    - P.gam * qID0 P lam VB i * qUD0 P lam VB i
      / (lam i * qUD0 P lam VB i + (1 - lam i) * qID0 P lam VB i) * P.Xbar)
  let C : PriceCoeffs P := ⟨a, bRec P lam VB, cRec P lam VB, dConst P, gConst P⟩
  have hQI : ∀ i, qID P lam VB C i = qID0 P lam VB i := fun i => rfl
  have hQU : ∀ i, qUD P lam VB C i = qUD0 P lam VB i := by
    intro i
    obtain ⟨-, -, -, hKb, -, -⟩ := facts i
    unfold qUD qUD0
    rw [hQI]
    have hK : Kgain P C i * C.b i = R2rec P lam VB i := hKb
    rw [hK]
    show qID0 P lam VB i + (1 + dConst P) ^ 2 * (P.phi * grid P i * P.sigM ^ 2 * (1 - R2rec P lam VB i))
      = _
    ring
  have hclear : Clears P lam VB C := by
    intro i mm θ X D
    obtain ⟨hq0, hqU0, hDen, hKb, hbD, hXe⟩ := facts i
    refine ⟨((1 + C.d) * (muD P + P.rho * D + θ + mm) + Ef P lam i C.a
        - P.R * price C i mm θ X D) / (P.gam * qID P lam VB C i),
      ((1 + C.d) * (muD P + P.rho * D + θ + Kgain P C i * (price C i mm θ X D - C.a i
        - C.g * θ - C.d * D)) + Ef P lam i C.a - P.R * price C i mm θ X D)
        / (P.gam * qUD P lam VB C i), ?_, ?_, ?_⟩
    · unfold objI
      exact quad_isMax _ _ _ hγ (by rw [hQI]; exact hq0)
    · unfold objU
      exact quad_isMax _ _ _ hγ (by rw [hQU]; exact hqU0)
    · rw [hQI, hQU]
      unfold price
      have ha' : (1 + dConst P) * muD P + Ef P lam i a - P.R * a i =
          P.gam * qID0 P lam VB i * qUD0 P lam VB i
            / (lam i * qUD0 P lam VB i + (1 - lam i) * qID0 P lam VB i) * P.Xbar := by
        have := ha i; linarith
      exact clear_alg P.R P.gam P.Xbar (qID0 P lam VB i) (qUD0 P lam VB i) (lam i) (a i)
        (Ef P lam i a) (muD P) P.rho (dConst P) (gConst P) (bRec P lam VB i) (cRec P lam VB i)
        (Kgain P C i) (R2rec P lam VB i) mm θ X D hγ hq0 hqU0 hDen hd hg ha' hbD hKb hXe
  refine ⟨⟨C, rfl, rfl, rfl, rfl, hclear⟩, ?_⟩
  intro hfix
  refine ⟨VB, C, hVB, hclear, ?_⟩
  intro i
  have := congrFun hfix i
  rw [← this]
  rfl
