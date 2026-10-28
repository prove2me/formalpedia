-- Prove2me | solution 1 for InfoRegimes.MarketEq.eq_B19_B21
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:08:32.248584+00:00
-- url     : https://prove2.me/submissions/6e42e786-b8b3-47e3-a810-3771878a1d2c

import Mathlib
import Definitions.Def_InfoRegimes_MarketEq_Model

open Filter Topology

namespace Aux_IR_B19

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

lemma Ef_affine (P : Params) (lam : State P → ℝ) (i : State P) (p q r : ℝ)
    (h h' : State P → ℝ) :
    Ef P lam i (fun j => p + q * h j + r * h' j) = p + q * Ef P lam i h + r * Ef P lam i h' := by
  unfold Ef
  have hs := trans_sum P lam i
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hs]
  simp only [Finset.mul_sum]
  congr 1
  · congr 1
    · ring
    · apply Finset.sum_congr rfl; intro j _; ring
  · apply Finset.sum_congr rfl; intro j _; ring

lemma iter_affine (P : Params) (lam : State P → ℝ) (p q r : ℝ) (h h' : State P → ℝ) :
    ∀ k i, EfIter P lam k (fun j => p + q * h j + r * h' j) i =
      p + q * EfIter P lam k h i + r * EfIter P lam k h' i := by
  intro k
  induction k with
  | zero => intro i; rfl
  | succ k ih =>
    intro i
    simp only [EfIter]
    have : EfIter P lam k (fun j => p + q * h j + r * h' j) =
        fun j => p + q * EfIter P lam k h j + r * EfIter P lam k h' j := funext ih
    rw [this, Ef_affine]

lemma iter_comm (P : Params) (lam : State P → ℝ) :
    ∀ k (h : State P → ℝ), EfIter P lam k (fun j => Ef P lam j h) = EfIter P lam (k + 1) h := by
  intro k
  induction k with
  | zero => intro h; rfl
  | succ k ih =>
    intro h
    funext i
    simp only [EfIter] at ih ⊢
    rw [ih h]

lemma iter_bound (P : Params) (lam : State P → ℝ) (h : State P → ℝ) (M : ℝ)
    (hM : ∀ j, |h j| ≤ M) : ∀ k i, |EfIter P lam k h i| ≤ M := by
  intro k
  induction k with
  | zero => intro i; exact hM i
  | succ k ih =>
    intro i
    simp only [EfIter]
    unfold Ef
    calc |∑ j, trans P lam i j * EfIter P lam k h j|
        ≤ ∑ j, |trans P lam i j * EfIter P lam k h j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, trans P lam i j * M := by
          apply Finset.sum_le_sum; intro j _
          rw [abs_mul, abs_of_nonneg (trans_nonneg P lam i j)]
          exact mul_le_mul_of_nonneg_left (ih j) (trans_nonneg P lam i j)
      _ = M := by rw [← Finset.sum_mul, trans_sum, one_mul]

lemma iter_nonneg (P : Params) (lam : State P → ℝ) (h : State P → ℝ) (hh : ∀ j, 0 ≤ h j) :
    ∀ k i, 0 ≤ EfIter P lam k h i := by
  intro k
  induction k with
  | zero => intro i; exact hh i
  | succ k ih =>
    intro i
    simp only [EfIter]
    unfold Ef
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (trans_nonneg P lam i j) (ih j))

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

end Aux_IR_B19

open InfoRegimes.MarketEq Aux_IR_B19 in
theorem solution (P : Params) (hS : P.Standing) (lam : State P → ℝ)
    (hlam : ∀ i, lam i ∈ Set.Icc (0 : ℝ) 1) (VB : State P → ℝ) (hVB : ∀ i, 0 < VB i)
    (C : PriceCoeffs P) (hC : Clears P lam VB C) (i : State P) :
    C.a i = 1 / P.R * ((1 + C.d) * muD P
        - P.gam * qID P lam VB C i * qUD P lam VB C i
          / (lam i * qUD P lam VB C i + (1 - lam i) * qID P lam VB C i) * P.Xbar
        + Ef P lam i C.a) ∧
      HasSum
        (fun k : ℕ => (P.R ^ (k + 1))⁻¹ * EfIter P lam k
          (fun j => P.gam * P.Xbar * (qID P lam VB C j * qUD P lam VB C j)
            / (lam j * qUD P lam VB C j + (1 - lam j) * qID P lam VB C j)) i)
        ((1 + C.d) * muD P / (P.R - 1) - C.a i) := by
  obtain ⟨hR, _, _, hσM, hσX, hγ, hφ0, hφ1, hX, hm⟩ := hS
  have hR0 : 0 < P.R := by linarith
  -- positivity facts
  have hgrid : ∀ j : State P, 0 ≤ grid P j ∧ grid P j ≤ 1 := by
    intro j
    have hm' : (0 : ℝ) < P.m := by exact_mod_cast hm
    unfold grid
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hm']
    exact_mod_cast Nat.lt_succ_iff.mp j.2
  have hEfVB : ∀ j, 0 < Ef P lam j VB := by
    intro j
    obtain ⟨k0, _, hk0⟩ := Finset.exists_min_image Finset.univ VB Finset.univ_nonempty
    unfold Ef
    calc 0 < VB k0 := hVB k0
      _ = ∑ l, trans P lam j l * VB k0 := by rw [← Finset.sum_mul, trans_sum, one_mul]
      _ ≤ ∑ l, trans P lam j l * VB l := Finset.sum_le_sum (fun l _ =>
          mul_le_mul_of_nonneg_left (hk0 l (Finset.mem_univ l)) (trans_nonneg P lam j l))
  have hQI : ∀ j, 0 < qID P lam VB C j := by
    intro j
    unfold qID
    have := (hgrid j).2
    have h1 : 0 ≤ (1 + C.d) ^ 2 * (1 - grid P j) * P.sigM ^ 2 := by
      have : 0 ≤ 1 - grid P j := by linarith
      positivity
    linarith [hEfVB j]
  have hKb : ∀ j, Kgain P C j * C.b j ≤ 1 := by
    intro j
    unfold Kgain
    have hA : 0 ≤ C.b j ^ 2 * P.phi * grid P j * P.sigM ^ 2 := by
      have := (hgrid j).1; positivity
    have hB : 0 ≤ C.c j ^ 2 * P.sigX ^ 2 := by positivity
    rw [div_mul_eq_mul_div]
    have e : C.b j * P.phi * grid P j * P.sigM ^ 2 * C.b j = C.b j ^ 2 * P.phi * grid P j * P.sigM ^ 2 := by
      ring
    rw [e]
    exact div_le_one_of_le₀ (by linarith) (by linarith)
  have hQU : ∀ j, qID P lam VB C j ≤ qUD P lam VB C j := by
    intro j
    unfold qUD
    have := hKb j
    have : 0 ≤ (1 + C.d) ^ 2 * (P.phi * grid P j * P.sigM ^ 2 * (1 - Kgain P C j * C.b j)) := by
      have := (hgrid j).1
      have : 0 ≤ 1 - Kgain P C j * C.b j := by linarith
      positivity
    linarith
  have hden : ∀ j, 0 < lam j * qUD P lam VB C j + (1 - lam j) * qID P lam VB C j := by
    intro j
    obtain ⟨hl0, hl1⟩ := hlam j
    nlinarith [hQI j, hQU j]
  -- part 1 for every state
  have part1 : ∀ j, C.a j = 1 / P.R * ((1 + C.d) * muD P
        - P.gam * qID P lam VB C j * qUD P lam VB C j
          / (lam j * qUD P lam VB C j + (1 - lam j) * qID P lam VB C j) * P.Xbar
        + Ef P lam j C.a) := by
    intro j
    obtain ⟨qI, qU, hI, hU, hclear⟩ := hC j 0 0 0 0
    have hp : price C j 0 0 0 0 = C.a j := by unfold price; ring
    rw [hp] at hI hU
    set N := (1 + C.d) * muD P + Ef P lam j C.a - P.R * C.a j with hN
    have hI' : qI = N / (P.gam * qID P lam VB C j) := by
      apply quad_max N P.gam _ qI hγ (hQI j)
      intro y
      have := isMaxOn_iff.mp hI y (Set.mem_univ y)
      unfold objI at this
      rw [hN]
      linarith [this]
    have hU' : qU = N / (P.gam * qUD P lam VB C j) := by
      apply quad_max N P.gam _ qU hγ (lt_of_lt_of_le (hQI j) (hQU j))
      intro y
      have := isMaxOn_iff.mp hU y (Set.mem_univ y)
      unfold objU at this
      simp only [mul_zero, add_zero, sub_self, zero_add, sub_zero] at this
      rw [hN]
      linarith [this]
    rw [hI', hU', add_zero] at hclear
    have hQIp := hQI j
    have hQUp := lt_of_lt_of_le (hQI j) (hQU j)
    have hd := hden j
    have hNval : N = P.gam * qID P lam VB C j * qUD P lam VB C j /
        (lam j * qUD P lam VB C j + (1 - lam j) * qID P lam VB C j) * P.Xbar := by
      have e1 : lam j * (N / (P.gam * qID P lam VB C j)) +
          (1 - lam j) * (N / (P.gam * qUD P lam VB C j)) =
          N * (lam j * qUD P lam VB C j + (1 - lam j) * qID P lam VB C j) /
            (P.gam * qID P lam VB C j * qUD P lam VB C j) := by
        field_simp
      rw [e1, div_eq_iff (by positivity)] at hclear
      rw [div_mul_eq_mul_div, eq_div_iff hd.ne']
      linear_combination hclear
    rw [← hNval, hN]
    field_simp
    ring
  refine ⟨part1 i, ?_⟩
  -- expansion
  set s : State P → ℝ := fun j => P.gam * P.Xbar * (qID P lam VB C j * qUD P lam VB C j)
      / (lam j * qUD P lam VB C j + (1 - lam j) * qID P lam VB C j) with hs
  set c0 := (1 + C.d) * muD P with hc0
  have ha_fun : C.a = fun j => c0 / P.R + (-1 / P.R) * s j + (1 / P.R) * Ef P lam j C.a := by
    funext j
    rw [part1 j, hs, hc0]
    ring
  have hexp : ∀ N, C.a i = ∑ k ∈ Finset.range N, (P.R ^ (k + 1))⁻¹ * (c0 - EfIter P lam k s i)
      + (P.R ^ N)⁻¹ * EfIter P lam N C.a i := by
    intro N
    induction N with
    | zero => simp [EfIter]
    | succ N ih =>
      have hstep : EfIter P lam N C.a i = c0 / P.R + (-1 / P.R) * EfIter P lam N s i +
          (1 / P.R) * EfIter P lam (N + 1) C.a i := by
        conv_lhs => rw [ha_fun]
        rw [iter_affine, iter_comm]
      rw [Finset.sum_range_succ, ih.trans (by rw [hstep])]
      rw [pow_succ]
      field_simp
      ring
  -- convergence
  have hs0 : ∀ j, 0 ≤ s j := by
    intro j
    simp only [hs]
    have := hQI j; have := hQU j; have := hden j
    have : 0 ≤ qUD P lam VB C j := by linarith
    positivity
  have hterm0 : ∀ k, 0 ≤ (P.R ^ (k + 1))⁻¹ * EfIter P lam k s i := fun k =>
    mul_nonneg (by positivity) (iter_nonneg P lam s hs0 k i)
  rw [hasSum_iff_tendsto_nat_of_nonneg hterm0]
  have hpart : ∀ N, ∑ k ∈ Finset.range N, (P.R ^ (k + 1))⁻¹ * EfIter P lam k s i =
      ∑ k ∈ Finset.range N, (P.R ^ (k + 1))⁻¹ * c0 - C.a i + (P.R ^ N)⁻¹ * EfIter P lam N C.a i := by
    intro N
    have := hexp N
    have e : ∑ k ∈ Finset.range N, (P.R ^ (k + 1))⁻¹ * (c0 - EfIter P lam k s i) =
        ∑ k ∈ Finset.range N, (P.R ^ (k + 1))⁻¹ * c0 -
          ∑ k ∈ Finset.range N, (P.R ^ (k + 1))⁻¹ * EfIter P lam k s i := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro k _; ring
    linarith
  simp_rw [hpart]
  -- geometric part
  have hgeo : HasSum (fun k : ℕ => (P.R ^ (k + 1))⁻¹ * c0) (c0 / (P.R - 1)) := by
    have hr0 : 0 ≤ (P.R)⁻¹ := by positivity
    have hr1 : (P.R)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
    have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left ((P.R)⁻¹ * c0)
    have h2 : (fun k : ℕ => (P.R ^ (k + 1))⁻¹ * c0) = fun k => (P.R)⁻¹ * c0 * (P.R)⁻¹ ^ k := by
      funext k; rw [pow_succ, mul_inv, inv_pow]; ring
    have h3 : c0 / (P.R - 1) = (P.R)⁻¹ * c0 * (1 - (P.R)⁻¹)⁻¹ := by
      have : P.R - 1 ≠ 0 := by linarith
      field_simp
    rw [h2, h3]
    exact h
  have hlim1 := hgeo.tendsto_sum_nat
  -- remainder
  set M := ∑ j, |C.a j| with hM
  have hbd := iter_bound P lam C.a M (fun j => Finset.single_le_sum (f := fun j => |C.a j|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ j))
  have hRpow : Tendsto (fun N : ℕ => (P.R ^ N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hR)
  have hlim2 : Tendsto (fun N : ℕ => (P.R ^ N)⁻¹ * EfIter P lam N C.a i) atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ => M * (P.R ^ N)⁻¹) atTop (𝓝 0) := by
      simpa using hRpow.const_mul M
    apply squeeze_zero_norm _ hb
    intro N
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right (hbd N i) (by positivity)
  have := (hlim1.sub_const (C.a i)).add hlim2
  simpa using this
