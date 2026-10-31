-- Prove2me | solution 1 for MinBuying.lemma4_canonical_tightness
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:35:16.964736+00:00
-- url     : https://prove2.me/submissions/4d8c16fc-2b48-437f-b613-ea517c8252cf

import Theorems.Thm_MinBuying_canonical_revenue_bridge
import Theorems.Thm_MinBuying_budget_characterization
import Theorems.Thm_MinBuying_benchmark_characterization
import Theorems.Thm_MinBuying_critical_ratio_characterization
import Theorems.Thm_MinBuying_grid_continuation_approximation

open Set MeasureTheory
open scoped BigOperators
open MinBuying
noncomputable section

private lemma revenue_gap (p D : ℝ) (hp : 0 < p) (hD : 0 < D) :
    p * (1 - p / (p + 1) / D) - 1 =
      p ^ 2 / ((p + 1) * D) * ((1 - (1 / p) ^ 2) * D - 1) := by
  field_simp
  <;> ring

private lemma uniform_prefix_formula (I : CanonicalInstance) (p : ℝ) (k : Fin I.count)
    (hp : 0 < p) (hpP : p ≤ I.terminalCap)
    (hactive : ∀ i, p ≤ I.cap i ↔ i ≤ k) :
    canonicalUniformRevenueAt I p =
      p * (1 - p / (p + 1) /
        (∏ i ∈ Finset.univ.filter (fun i : Fin I.count => i ≤ k), (1 + I.a i / p))) := by
  have ht : triangularReject 1 I.terminalCap p = p / (p + 1) := by
    simp [triangularReject, not_le_of_gt hp, hpP]
  have hi (i : Fin I.count) : triangularReject (I.a i) (I.cap i) p =
      if i ≤ k then (1 + I.a i / p)⁻¹ else 1 := by
    rw [triangularReject, if_neg (not_le_of_gt hp)]
    by_cases hik : i ≤ k
    · rw [if_pos hik, if_pos ((hactive i).mpr hik)]
      field_simp
    · rw [if_neg hik, if_neg (fun h => hik ((hactive i).mp h))]
  unfold canonicalUniformRevenueAt
  rw [ht]
  simp_rw [hi]
  simp only [Finset.prod_ite, Finset.prod_const_one, mul_one, ← Finset.prod_inv_distrib,
    div_eq_mul_inv]

private lemma normalizer_product (r a x : ℝ) (hr : 0 < r) (ha : 0 < a)
    (hrx : r ≤ x) (hx : x < 1) (he : a * (1 - r ^ 2) = r) :
    (1 - x ^ 2) * (1 + a * x) ≤ 1 := by
  have hx0 : 0 ≤ x := hr.le.trans hrx
  have hsq : r ^ 2 ≤ x ^ 2 := by nlinarith
  have hq : a - x - a * x ^ 2 ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq ha.le]
  have hm := mul_nonpos_of_nonneg_of_nonpos hx0 hq
  nlinarith [hm]

private lemma prefix_product_bound (I : CanonicalInstance) (k : Fin I.count) (x : ℝ)
    (hx0 : 0 < x) (hx1 : x < 1) (hkx : 1 / I.cap k ≤ x)
    (hB : (∑ i ∈ Finset.univ.filter (fun i : Fin I.count => i ≤ k), I.a i) ≤
      canonicalBudget (1 / I.cap k)) :
    (1 - x ^ 2) *
      (∏ i ∈ Finset.univ.filter (fun i : Fin I.count => i ≤ k), (1 + I.a i * x)) ≤ 1 := by
  let s := Finset.univ.filter (fun i : Fin I.count => i ≤ k)
  have hkp : 0 < 1 / I.cap k := one_div_pos.mpr (zero_lt_one.trans (I.cap_one_lt k))
  have hk1 : 1 / I.cap k < 1 :=
    (div_lt_one (zero_lt_one.trans (I.cap_one_lt k))).mpr (I.cap_one_lt k)
  have hsum : (∑ i ∈ s, I.a i) ≤ canonicalBudget x := hB.trans
    (budget_characterization.2.2.2.1.monotoneOn ⟨hkp.le, hk1⟩ ⟨hx0.le, hx1⟩ hkx)
  have hprod : (∏ i ∈ s, (1 + I.a i * x)) ≤ Real.exp (x * canonicalBudget x) := by
    calc
      _ ≤ ∏ i ∈ s, Real.exp (I.a i * x) := by
        apply Finset.prod_le_prod
        · intro i hi
          have hai := I.a_pos i
          positivity
        · intro i hi
          simpa [add_comm] using Real.add_one_le_exp (I.a i * x)
      _ = Real.exp (∑ i ∈ s, I.a i * x) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (x * canonicalBudget x) := by
        apply Real.exp_le_exp.mpr
        rw [← Finset.sum_mul]
        nlinarith [mul_le_mul_of_nonneg_left hsum hx0.le]
  have harg : 0 < 1 - x ^ 2 := by nlinarith
  have hAx : x * canonicalBudget x = -Real.log (1 - x ^ 2) := by
    rw [canonicalBudget, if_neg hx0.ne']
    field_simp
  rw [hAx, Real.exp_neg, Real.exp_log harg] at hprod
  have hm := mul_le_mul_of_nonneg_left hprod harg.le
  simpa only [mul_inv_cancel₀ harg.ne'] using hm

private lemma canonical_normalized (I : CanonicalInstance) (hn : 0 < I.count)
    (hfirst : I.a ⟨0, hn⟩ * (1 - (1 / I.cap ⟨0, hn⟩) ^ 2) = 1 / I.cap ⟨0, hn⟩)
    (hB : ∀ k : Fin I.count, 0 < k.val →
      (∑ i ∈ Finset.univ.filter (fun i : Fin I.count => i ≤ k), I.a i) ≤
        canonicalBudget (1 / I.cap k)) :
    CanonicalNormalized I := by
  let z : Fin I.count := ⟨0, hn⟩
  have hsingle : Finset.univ.filter (fun i : Fin I.count => i ≤ z) = {z} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hi
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero hi
    · intro hi
      subst i
      exact le_rfl
  have heq : canonicalUniformRevenueAt I (I.cap z) = 1 := by
    have hp := zero_lt_one.trans (I.cap_one_lt z)
    have hactive : ∀ i, I.cap z ≤ I.cap i ↔ i ≤ z := by
      intro i
      constructor
      · intro h
        by_contra hi
        exact (not_lt_of_ge h) (I.caps_decreasing (lt_of_not_ge hi))
      · intro hi
        exact I.caps_decreasing.antitone hi
    rw [uniform_prefix_formula I (I.cap z) z hp (I.cap_lt_terminal z).le hactive,
      hsingle, Finset.prod_singleton]
    have hD : 0 < 1 + I.a z / I.cap z := by
      have ha := I.a_pos z
      positivity
    have hg : (1 - (1 / I.cap z) ^ 2) * (1 + I.a z / I.cap z) = 1 := by
      have hh := congrArg (fun q => q * (1 / I.cap z)) hfirst
      dsimp only [z]
      dsimp only [z] at hh
      simp only [div_eq_mul_inv, one_mul] at hh ⊢
      nlinarith
    have hh := revenue_gap (I.cap z) (1 + I.a z / I.cap z) hp hD
    rw [hg, sub_self, mul_zero] at hh
    linarith
  refine ⟨?_, I.cap z, (zero_lt_one.trans (I.cap_one_lt z)).le, heq⟩
  intro p hp
  by_cases hp1 : p ≤ 1
  · have hrejn (a v : ℝ) (ha : 0 < a) : 0 ≤ triangularReject a v p := by
      unfold triangularReject
      split_ifs <;> try positivity
    have hQ : 0 ≤ triangularReject 1 I.terminalCap p *
        ∏ i : Fin I.count, triangularReject (I.a i) (I.cap i) p := by
      apply mul_nonneg (hrejn 1 I.terminalCap zero_lt_one)
      exact Finset.prod_nonneg fun i _ => hrejn (I.a i) (I.cap i) (I.a_pos i)
    unfold canonicalUniformRevenueAt
    nlinarith
  have hpp : 1 < p := lt_of_not_ge hp1
  have hp0 : 0 < p := zero_lt_one.trans hpp
  by_cases hP : p ≤ I.terminalCap
  · let s := Finset.univ.filter (fun i : Fin I.count => p ≤ I.cap i)
    by_cases hs : s.Nonempty
    · let k := s.max' hs
      have hk : k ∈ s := Finset.max'_mem s hs
      have hpk : p ≤ I.cap k := (Finset.mem_filter.mp hk).2
      have hactive : ∀ i, p ≤ I.cap i ↔ i ≤ k := by
        intro i
        constructor
        · intro hi
          exact Finset.le_max' s i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
        · intro hi
          exact hpk.trans (I.caps_decreasing.antitone hi)
      rw [uniform_prefix_formula I p k hp0 hP hactive]
      let D := ∏ i ∈ Finset.univ.filter (fun i : Fin I.count => i ≤ k), (1 + I.a i / p)
      have hD : 0 < D := by
        apply Finset.prod_pos
        intro i hi
        have hai := I.a_pos i
        positivity
      have hx0 : 0 < 1 / p := one_div_pos.mpr hp0
      have hx1 : 1 / p < 1 := (div_lt_one hp0).mpr hpp
      have hkx : 1 / I.cap k ≤ 1 / p := one_div_le_one_div_of_le hp0 hpk
      have hg : (1 - (1 / p) ^ 2) * D ≤ 1 := by
        by_cases hk0 : k.val = 0
        · have hkz : k = z := Fin.ext hk0
          dsimp only [D]
          rw [hkz, hsingle, Finset.prod_singleton]
          rw [hkz] at hkx
          simpa only [mul_one_div] using normalizer_product (1 / I.cap z) (I.a z) (1 / p)
            (one_div_pos.mpr (zero_lt_one.trans (I.cap_one_lt z))) (I.a_pos z) hkx hx1 hfirst
        · simpa only [mul_one_div] using
            prefix_product_bound I k (1 / p) hx0 hx1 hkx (hB k (Nat.pos_of_ne_zero hk0))
      have hh := revenue_gap p D hp0 hD
      have hcoeff : 0 ≤ p ^ 2 / ((p + 1) * D) := by positivity
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos hcoeff (sub_nonpos.mpr hg)
      rw [← hh] at hnonpos
      linarith
    · have hrejs (i : Fin I.count) : triangularReject (I.a i) (I.cap i) p = 1 := by
        have hi : ¬ p ≤ I.cap i := by
          intro hi
          exact hs ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
        simp [triangularReject, not_le_of_gt hp0, hi]
      unfold canonicalUniformRevenueAt
      simp_rw [hrejs]
      simp only [Finset.prod_const_one, mul_one]
      rw [triangularReject, if_neg (not_le_of_gt hp0), if_pos hP]
      have he : p * (1 - p / (p + 1)) = p / (p + 1) := by field_simp; ring
      rw [he]
      exact (div_le_one (by positivity : 0 < p + 1)).mpr (by linarith)
  · have hrejs (i : Fin I.count) : triangularReject (I.a i) (I.cap i) p = 1 := by
      have hi : ¬ p ≤ I.cap i := not_le_of_gt ((I.cap_lt_terminal i).trans (lt_of_not_ge hP))
      simp [triangularReject, not_le_of_gt hp0, hi]
    unfold canonicalUniformRevenueAt
    simp_rw [hrejs]
    simp [triangularReject, not_le_of_gt hp0, hP]

private lemma prefix_sum_fin (f : ℕ → ℝ) {m : ℕ} (j : Fin m) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ≤ j), f i.val) =
      ∑ k ∈ Finset.range (j.val + 1), f k := by
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le hi
  · intro i hi k hk he
    exact Fin.ext he
  · intro k hk
    have hkj : k < j.val + 1 := Finset.mem_range.mp hk
    refine ⟨⟨k, by omega⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    omega
  · intro i hi
    rfl

private lemma sum_differences (f : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (f (k + 1) - f k)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

private lemma finRange_vals (m : ℕ) : (List.finRange m).map Fin.val = List.range m := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, Fin.val_cast]

private lemma fold_input_error {α : Type} (l : List α) (a d : α → ℝ)
    (hd : ∀ i ∈ l, 1 ≤ d i) (C D e : ℝ) (he : 0 ≤ e) (hCD : C ≤ D + e) :
    l.foldl (fun c i => (a i + c) / d i) C ≤
      l.foldl (fun c i => (a i + c) / d i) D + e := by
  induction l generalizing C D with
  | nil => simpa using hCD
  | cons i l ih =>
    have hdi : 1 ≤ d i := hd i (by simp)
    have hd0 : 0 < d i := zero_lt_one.trans_le hdi
    have hs : (a i + C) / d i ≤ (a i + D) / d i + e := by
      calc
        _ ≤ (a i + D + e) / d i := div_le_div_of_nonneg_right (by linarith) hd0.le
        _ = (a i + D) / d i + e / d i := by rw [add_div]
        _ ≤ _ := by linarith [div_le_self he hdi]
    simpa only [List.foldl_cons] using
      ih (fun j hj => hd j (by simp [hj])) _ _ hs

private lemma budget_ge_self (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : x ≤ canonicalBudget x := by
  have harg : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hl := Real.log_le_sub_one_of_pos harg
  rw [canonicalBudget, if_neg hx.1.ne']
  apply (le_div_iff₀ hx.1).mpr
  nlinarith

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ I : CanonicalInstance,
      UPRevenue (canonicalLaw I) = 1 ∧
      1 / criticalRatio - ε < DPRevenue (canonicalLaw I) := by
  let t := criticalRatio
  have ht : t ∈ Ioo (0 : ℝ) 1 := critical_ratio_characterization.1
  have hct : continuousBenchmark t = 1 / criticalRatio := by
    apply (eq_div_iff ht.1.ne').mpr
    nlinarith [critical_ratio_characterization.2.1]
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨ρ, hρ, hcont⟩ := Metric.continuousWithinAt_iff.mp
    (benchmark_characterization.2.1 0 (by norm_num)) (ε / 4) hε4
  obtain ⟨δ, hδ0, hδ⟩ := exists_between
    (lt_min ht.1 (lt_min hρ (by norm_num : (0 : ℝ) < 1 / 2)))
  have hδt : δ < t := hδ.trans_le (min_le_left _ _)
  have hδρ : δ < ρ := hδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδhalf : δ < 1 / 2 := hδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ < 1 := hδt.trans ht.2
  have hcδ : continuousBenchmark δ < 1 + ε / 4 := by
    have hc := hcont ⟨hδ0.le, hδ1⟩ (by simpa [Real.dist_eq, abs_of_pos hδ0] using hδρ)
    rw [Real.dist_eq, benchmark_characterization.1] at hc
    linarith [(abs_lt.mp hc).2]
  obtain ⟨m, hm0, hm⟩ := grid_continuation_approximation δ t hδ0.le hδt ht.2 (ε / 4) hε4
  let X : ℕ → ℝ := fun k => δ + (t - δ) * (k : ℝ) / (m : ℝ)
  let a : ℕ → ℝ := fun k => canonicalBudget (X (k + 1)) - canonicalBudget (X k)
  change continuousBenchmark t - ε / 4 <
    (List.range m).foldl (fun C k => (a k + C) / (1 + X (k + 1) * a k))
      (continuousBenchmark δ) at hm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hX0 : X 0 = δ := by simp [X]
  have hXm : X m = t := by dsimp [X]; field_simp; ring
  have hXrange (k : ℕ) (hk : k ≤ m) : X k ∈ Icc δ t := by
    have hkr : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
    have hf0 : 0 ≤ (k : ℝ) / (m : ℝ) := div_nonneg (Nat.cast_nonneg _) hmR.le
    have hf1 : (k : ℝ) / (m : ℝ) ≤ 1 := (div_le_one hmR).mpr hkr
    change δ ≤ δ + (t - δ) * (k : ℝ) / (m : ℝ) ∧
      δ + (t - δ) * (k : ℝ) / (m : ℝ) ≤ t
    rw [mul_div_assoc]
    constructor <;> nlinarith
  have hXmono : StrictMono X := by
    intro i j hij
    dsimp [X]
    have hijR : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    have hdiv := div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hijR (sub_pos.mpr hδt)) hmR
    linarith
  have hapos (k : ℕ) (hk : k < m) : 0 < a k := by
    apply sub_pos.mpr
    exact budget_characterization.2.2.2.1
      ⟨hδ0.le.trans (hXrange k hk.le).1, (hXrange k hk.le).2.trans_lt ht.2⟩
      ⟨hδ0.le.trans (hXrange (k + 1) hk).1, (hXrange (k + 1) hk).2.trans_lt ht.2⟩
      (hXmono (Nat.lt_succ_self k))
  let r := δ / 2
  let a0 := r / (1 - r ^ 2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := by dsimp [r]; linarith
  have hr1 : r < 1 := hrδ.trans hδ1
  have hr2 : 0 < 1 - r ^ 2 := by nlinarith
  have ha0 : 0 < a0 := div_pos hr hr2
  have ha0δ : a0 ≤ δ := by
    apply (div_le_iff₀ hr2).mpr
    have hsq : r ^ 2 ≤ 1 / 4 := by dsimp [r]; nlinarith [hδ0, hδhalf]
    have hmul := mul_le_mul_of_nonneg_left hsq hδ0.le
    dsimp only [r] at *
    nlinarith
  have hAδ : a0 ≤ canonicalBudget δ := ha0δ.trans (budget_ge_self δ ⟨hδ0, hδ1⟩)
  let P := 1 / r + 4 / ε + 1
  have hcap0 : 1 < 1 / r := (one_lt_div hr).mpr hr1
  have hPcap : 1 / r < P := by
    dsimp [P]
    linarith [div_pos (by norm_num : (0 : ℝ) < 4) hε]
  have hP1 : 1 < P := hcap0.trans hPcap
  let I : CanonicalInstance := {
    count := m + 1
    terminalCap := P
    a := Fin.cons a0 (fun i : Fin m => a i.val)
    cap := Fin.cons (1 / r) (fun i : Fin m => 1 / X (i.val + 1))
    terminal_one_lt := hP1
    a_pos := by
      intro i
      refine Fin.cases ha0 (fun j => hapos j.val j.isLt) i
    cap_one_lt := by
      intro i
      refine Fin.cases hcap0 (fun j => ?_) i
      exact (one_lt_div (hδ0.trans_le (hXrange (j.val + 1) j.isLt).1)).mpr
        ((hXrange (j.val + 1) j.isLt).2.trans_lt ht.2)
    cap_lt_terminal := by
      intro i
      refine Fin.cases hPcap (fun j => ?_) i
      exact (one_div_lt_one_div_of_lt hr
        (hrδ.trans_le (hXrange (j.val + 1) j.isLt).1)).trans hPcap
    caps_decreasing := by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases (fun h => (Fin.not_lt_zero _ h).elim) (fun j _ => ?_) j
        exact one_div_lt_one_div_of_lt hr (hrδ.trans_le (hXrange (j.val + 1) j.isLt).1)
      · intro j
        refine Fin.cases (fun h => (Fin.not_lt_zero _ h).elim) (fun j hij => ?_) j
        apply one_div_lt_one_div_of_lt (hδ0.trans_le (hXrange (i.val + 1) i.isLt).1)
        apply hXmono
        have hi : i.val < j.val := Fin.succ_lt_succ_iff.mp hij
        change i.val + 1 < j.val + 1
        exact Nat.succ_lt_succ hi
  }
  have hnorm : CanonicalNormalized I := by
    apply canonical_normalized I (Nat.zero_lt_succ m)
    · change a0 * (1 - (1 / (1 / r)) ^ 2) = 1 / (1 / r)
      simp only [one_div_one_div]
      dsimp [a0]
      field_simp
    · intro k
      refine Fin.cases (fun h => (Nat.not_lt_zero _ h).elim) (fun j hj => ?_) k
      change (∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => i ≤ j.succ),
        Fin.cons a0 (fun i : Fin m => a i.val) i) ≤ canonicalBudget (1 / (1 / X (j.val + 1)))
      simp only [Finset.sum_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.zero_le, if_true, Fin.succ_le_succ_iff, one_div_one_div]
      rw [← Finset.sum_filter, prefix_sum_fin a j]
      have hs := sum_differences (fun k => canonicalBudget (X k)) (j.val + 1)
      change (∑ k ∈ Finset.range (j.val + 1), a k) =
        canonicalBudget (X (j.val + 1)) - canonicalBudget (X 0) at hs
      rw [hs, hX0]
      linarith
  let Cterm := P / (P + 1)
  let Cinit := continuationStep a0 (1 / r) Cterm
  have hPpos : 0 < P := zero_lt_one.trans hP1
  have hCterm0 : 0 ≤ Cterm := by dsimp [Cterm]; positivity
  have hCterm1 : Cterm ≤ 1 := by
    apply (div_le_one (by positivity : 0 < P + 1)).mpr
    linarith
  have hCterm : 1 - ε / 4 < Cterm := by
    have hP4 : 4 / ε < P := by dsimp [P]; linarith [one_div_pos.mpr hr]
    have hPe : 4 < P * ε := (div_lt_iff₀ hε).mp hP4
    have hloss : 1 / (P + 1) < ε / 4 := by
      apply (div_lt_iff₀ (by positivity : 0 < P + 1)).mpr
      nlinarith
    have he : Cterm + 1 / (P + 1) = 1 := by dsimp [Cterm]; field_simp
    linarith
  have hCinit : Cterm ≤ Cinit := by
    change Cterm ≤ (a0 + Cterm) / (1 + a0 / (1 / r))
    simp only [one_div, div_inv_eq_mul]
    apply (le_div_iff₀ (by positivity : 0 < 1 + a0 * r)).mpr
    have hprod : r * Cterm ≤ 1 := by nlinarith [hCterm1]
    nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr hprod)]
  have hstart : continuousBenchmark δ ≤ Cinit + ε / 2 := by linarith
  have hpert := fold_input_error (List.range m) a
    (fun k => 1 + X (k + 1) * a k)
    (by
      intro k hk
      have hk' : k < m := List.mem_range.mp hk
      have hx0 := hδ0.le.trans (hXrange (k + 1) hk').1
      have ha := (hapos k hk').le
      nlinarith)
    (continuousBenchmark δ) Cinit (ε / 2) (by positivity) hstart
  have hcapR : canonicalCapRevenue I =
      (List.range m).foldl (fun C k => (a k + C) / (1 + X (k + 1) * a k)) Cinit := by
    unfold canonicalCapRevenue canonicalContinuation
    rw [List.take_of_length_le (by simp)]
    change (List.finRange (m + 1)).foldl
      (fun (C : ℝ) (i : Fin (m + 1)) => continuationStep (I.a i) (I.cap i) C) Cterm = _
    rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
    simp only [I, Fin.cons_zero, Fin.cons_succ]
    change (List.finRange m).foldl
      (fun C i => continuationStep (a i.val) (1 / X (i.val + 1)) C) Cinit = _
    rw [← finRange_vals m, List.foldl_map]
    congr 1
    funext C i
    simp only [continuationStep, one_div, div_inv_eq_mul]
    ring
  have hcapLower : 1 / criticalRatio - ε < canonicalCapRevenue I := by
    rw [hcapR]
    rw [hct] at hm
    linarith
  have hb := canonical_revenue_bridge I
  have hUP : UPRevenue (canonicalLaw I) = 1 := by
    apply le_antisymm
    · change sSup (uniformValues (canonicalLaw I)) ≤ (1 : ℝ)
      apply csSup_le (show (uniformValues (canonicalLaw I)).Nonempty from
        ⟨uniformRevenue (canonicalLaw I) 0, 0, le_rfl, rfl⟩)
      rintro q ⟨p, hp, rfl⟩
      rw [hb.2.2.2 p hp]
      exact hnorm.1 p hp
    · obtain ⟨p, hp, he⟩ := hnorm.2
      apply le_csSup hb.2.1.2.1
      refine ⟨p, hp, ?_⟩
      rw [hb.2.2.2 p hp, he]
  refine ⟨I, hUP, hcapLower.trans_le ?_⟩
  rw [← hb.2.2.1]
  apply le_csSup hb.2.1.1
  refine ⟨canonicalPrices I, ?_, rfl⟩
  intro i
  refine Fin.cases hPpos.le (fun j => (zero_lt_one.trans (I.cap_one_lt j)).le) i
