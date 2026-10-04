-- Prove2me | solution 1 for IsUltrametricDist.norm_tsum_mul_pow_le_of_hasseDeriv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T09:30:36.041999+00:00
-- url     : https://prove2.me/submissions/a40f7473-2f39-4516-9f9f-7eb4a79882f4

import Mathlib

namespace IsUltrametricDist.SchwarzAux

open Filter Topology

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The Hasse derivative of order `t` at `b` of the series with coefficients `c`. -/
noncomputable def D (t : ℕ) (c : ℕ → K) (b : K) : K :=
  ∑' k : ℕ, (k.choose t : K) * c k * b ^ (k - t)

/-- The tail sums used to divide by `X - a`. -/
noncomputable def quot (c : ℕ → K) (a : K) (j : ℕ) : K :=
  ∑' i : ℕ, c (i + (j + 1)) * a ^ i

lemma summable_of_le {g : ℕ → K} (hg : Tendsto g atTop (𝓝 0)) (f : ℕ → K)
    (hf : ∀ k, ‖f k‖ ≤ ‖g k‖) : Summable f := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  exact squeeze_zero_norm hf (tendsto_zero_iff_norm_tendsto_zero.mp hg)

omit [CompleteSpace K] in
lemma norm_term_le (t k : ℕ) (x b : K) (hb : ‖b‖ ≤ 1) :
    ‖(k.choose t : K) * x * b ^ (k - t)‖ ≤ ‖x‖ := by
  rw [norm_mul, norm_mul, norm_pow]
  have h1 : ‖(k.choose t : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K _
  have h2 : ‖b‖ ^ (k - t) ≤ 1 := pow_le_one₀ (norm_nonneg _) hb
  calc ‖(k.choose t : K)‖ * ‖x‖ * ‖b‖ ^ (k - t) ≤ 1 * ‖x‖ * 1 := by gcongr
    _ = ‖x‖ := by ring

lemma summable_D (t : ℕ) {c : ℕ → K} (hc : Tendsto c atTop (𝓝 0)) {b : K} (hb : ‖b‖ ≤ 1) :
    Summable (fun k : ℕ => (k.choose t : K) * c k * b ^ (k - t)) :=
  summable_of_le hc _ (fun k => norm_term_le t k (c k) b hb)

omit [CompleteSpace K] in
lemma norm_tsum_le' {f : ℕ → K} {M : ℝ} (hM : 0 ≤ M) (h : ∀ k, ‖f k‖ ≤ M) :
    ‖∑' k, f k‖ ≤ M :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hM h

omit [IsUltrametricDist K] [CompleteSpace K] in
lemma D_zero_eq (c : ℕ → K) (b : K) : D 0 c b = ∑' k : ℕ, c k * b ^ k := by
  unfold D
  simp

/-- Division by one linear factor at a zero `a`. -/
lemma exists_div {c : ℕ → K} (hc : Tendsto c atTop (𝓝 0)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ k, ‖c k‖ ≤ M) {a : K} (ha : ‖a‖ ≤ 1) (hfa : ∑' k, c k * a ^ k = 0) :
    ∃ g : ℕ → K, Tendsto g atTop (𝓝 0) ∧ (∀ k, ‖g k‖ ≤ M) ∧ c 0 = -(a * g 0) ∧
      ∀ k, c (k + 1) = g k - a * g (k + 1) := by
  have hterm : ∀ j i : ℕ, ‖c (i + (j + 1)) * a ^ i‖ ≤ ‖c (i + (j + 1))‖ := by
    intro j i
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ha)
  have hshift : ∀ j : ℕ, Tendsto (fun i => c (i + (j + 1))) atTop (𝓝 0) := fun j =>
    (tendsto_add_atTop_iff_nat (j + 1)).mpr hc
  have hsum : ∀ j : ℕ, Summable (fun i : ℕ => c (i + (j + 1)) * a ^ i) := fun j =>
    summable_of_le (hshift j) _ (hterm j)
  have hrel : ∀ j : ℕ, quot c a j = c (j + 1) + a * quot c a (j + 1) := by
    intro j
    unfold quot
    rw [(hsum j).tsum_eq_zero_add, ← tsum_mul_left]
    congr 1
    · simp
    · congr 1
      funext i
      rw [show i + 1 + (j + 1) = i + (j + 1 + 1) by omega, pow_succ]
      ring
  refine ⟨quot c a, ?_, ?_, ?_, ?_⟩
  · rw [Metric.tendsto_atTop] at hc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε / 2) (half_pos hε)
    refine ⟨N, fun j hj => ?_⟩
    rw [dist_zero_right]
    have : ‖quot c a j‖ ≤ ε / 2 := by
      unfold quot
      refine norm_tsum_le' (half_pos hε).le (fun i => (hterm j i).trans ?_)
      have := hN (i + (j + 1)) (by omega)
      rw [dist_zero_right] at this
      exact this.le
    linarith
  · intro k
    unfold quot
    exact norm_tsum_le' hM0 (fun i => (hterm k i).trans (hM _))
  · have hs0 : Summable (fun k : ℕ => c k * a ^ k) :=
      summable_of_le hc _ (fun k => by
        rw [norm_mul, norm_pow]
        exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ha))
    rw [hs0.tsum_eq_zero_add] at hfa
    have : ∑' k : ℕ, c (k + 1) * a ^ (k + 1) = a * quot c a 0 := by
      unfold quot
      rw [← tsum_mul_left]
      congr 1
      funext i
      rw [pow_succ]
      ring_nf
    rw [this] at hfa
    simp only [pow_zero, mul_one] at hfa
    linear_combination hfa
  · intro k
    rw [hrel k]
    ring

/-- Hasse derivatives of a product with `X - a`, first form. -/
lemma D_mul_aux {g c : ℕ → K} (hg : Tendsto g atTop (𝓝 0)) (hc : Tendsto c atTop (𝓝 0))
    {a b : K} (hb : ‖b‖ ≤ 1) (h0 : c 0 = -(a * g 0))
    (hs : ∀ k, c (k + 1) = g k - a * g (k + 1)) (t : ℕ) :
    D t c b = (∑' j : ℕ, ((j + 1).choose t : K) * g j * b ^ (j + 1 - t)) - a * D t g b := by
  have hcs := summable_D t hc hb
  have hgs := summable_D t hg hb
  have hg1 : Tendsto (fun j => g (j + 1)) atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 1).mpr hg
  have hS1 : Summable (fun j : ℕ => ((j + 1).choose t : K) * g j * b ^ (j + 1 - t)) :=
    summable_of_le hg _ (fun j => norm_term_le t (j + 1) (g j) b hb)
  have hS2 : Summable (fun j : ℕ => ((j + 1).choose t : K) * g (j + 1) * b ^ (j + 1 - t)) :=
    summable_of_le hg1 _ (fun j => norm_term_le t (j + 1) (g (j + 1)) b hb)
  unfold D
  rw [hcs.tsum_eq_zero_add, hgs.tsum_eq_zero_add]
  have : ∀ j : ℕ, ((j + 1).choose t : K) * c (j + 1) * b ^ (j + 1 - t) =
      ((j + 1).choose t : K) * g j * b ^ (j + 1 - t) -
        a * (((j + 1).choose t : K) * g (j + 1) * b ^ (j + 1 - t)) := by
    intro j
    rw [hs j]
    ring
  simp only [this]
  rw [hS1.tsum_sub (hS2.mul_left a), tsum_mul_left, h0]
  ring

omit [CompleteSpace K] in
lemma S_zero (g : ℕ → K) (b : K) :
    ∑' j : ℕ, ((j + 1).choose 0 : K) * g j * b ^ (j + 1 - 0) = b * D 0 g b := by
  unfold D
  rw [← tsum_mul_left]
  congr 1
  funext j
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, pow_succ]
  ring

lemma S_succ {g : ℕ → K} (hg : Tendsto g atTop (𝓝 0)) {b : K} (hb : ‖b‖ ≤ 1) (s : ℕ) :
    ∑' j : ℕ, ((j + 1).choose (s + 1) : K) * g j * b ^ (j + 1 - (s + 1)) =
      D s g b + b * D (s + 1) g b := by
  unfold D
  rw [← tsum_mul_left, ← (summable_D s hg hb).tsum_add ((summable_D (s + 1) hg hb).mul_left b)]
  congr 1
  funext j
  rw [Nat.choose_succ_succ, Nat.cast_add, Nat.add_sub_add_right]
  rcases Nat.lt_or_ge j (s + 1) with h | h
  · rw [Nat.choose_eq_zero_of_lt h]
    simp
  · rw [show j - s = (j - (s + 1)) + 1 by omega, pow_succ]
    ring

lemma D_mul_zero {g c : ℕ → K} (hg : Tendsto g atTop (𝓝 0)) (hc : Tendsto c atTop (𝓝 0))
    {a b : K} (hb : ‖b‖ ≤ 1) (h0 : c 0 = -(a * g 0))
    (hs : ∀ k, c (k + 1) = g k - a * g (k + 1)) :
    D 0 c b = (b - a) * D 0 g b := by
  rw [D_mul_aux hg hc hb h0 hs 0, S_zero]
  ring

lemma D_mul_succ {g c : ℕ → K} (hg : Tendsto g atTop (𝓝 0)) (hc : Tendsto c atTop (𝓝 0))
    {a b : K} (hb : ‖b‖ ≤ 1) (h0 : c 0 = -(a * g 0))
    (hs : ∀ k, c (k + 1) = g k - a * g (k + 1)) (s : ℕ) :
    D (s + 1) c b = (b - a) * D (s + 1) g b + D s g b := by
  rw [D_mul_aux hg hc hb h0 hs (s + 1), S_succ hg hb]
  ring

/-- The main induction over a multiset of zeros counted with multiplicity. -/
lemma key [DecidableEq K] {M r : ℝ} (hM0 : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (L : Multiset K) :
    ∀ c : ℕ → K, Tendsto c atTop (𝓝 0) → (∀ k, ‖c k‖ ≤ M) → (∀ a ∈ L, ‖a‖ ≤ r) →
      (∀ b, ∀ t < L.count b, D t c b = 0) →
      ∀ z : K, ‖z‖ ≤ r → ‖∑' k : ℕ, c k * z ^ k‖ ≤ r ^ Multiset.card L * M := by
  classical
  induction L using Multiset.induction_on with
  | empty =>
    intro c _ hM _ _ z hz
    simp only [Multiset.card_zero, pow_zero, one_mul]
    refine norm_tsum_le' hM0 (fun k => ?_)
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (hz.trans hr1))).trans (hM k)
  | cons a L ih =>
    intro c hc hM hL hD z hz
    have ha : ‖a‖ ≤ r := hL a (Multiset.mem_cons_self a L)
    have ha1 : ‖a‖ ≤ 1 := ha.trans hr1
    have hfa : ∑' k, c k * a ^ k = 0 := by
      rw [← D_zero_eq]
      apply hD a 0
      rw [Multiset.count_cons_self]
      omega
    obtain ⟨g, hg, hgM, h0, hs⟩ := exists_div hc hM0 hM ha1 hfa
    have hL' : ∀ a' ∈ L, ‖a'‖ ≤ r := fun a' h => hL a' (Multiset.mem_cons_of_mem h)
    have hD' : ∀ b, ∀ t < L.count b, D t g b = 0 := by
      intro b t ht
      have hbL : b ∈ L := Multiset.count_pos.mp (by omega)
      have hb1 : ‖b‖ ≤ 1 := (hL' b hbL).trans hr1
      by_cases hba : b = a
      · subst hba
        have h1 := hD b (t + 1) (by rw [Multiset.count_cons_self]; omega)
        rw [D_mul_succ hg hc hb1 h0 hs t, sub_self, zero_mul, zero_add] at h1
        exact h1
      · have hne : b - a ≠ 0 := sub_ne_zero.mpr hba
        induction t with
        | zero =>
          have h1 := hD b 0 (by rw [Multiset.count_cons_of_ne hba]; exact ht)
          rw [D_mul_zero hg hc hb1 h0 hs] at h1
          exact (mul_eq_zero.mp h1).resolve_left hne
        | succ s ihs =>
          have h1 := hD b (s + 1) (by rw [Multiset.count_cons_of_ne hba]; exact ht)
          rw [D_mul_succ hg hc hb1 h0 hs s, ihs (by omega), add_zero] at h1
          exact (mul_eq_zero.mp h1).resolve_left hne
    have hgz := ih g hg hgM hL' hD' z hz
    have hz1 : ‖z‖ ≤ 1 := hz.trans hr1
    have hfz : ∑' k, c k * z ^ k = (z - a) * ∑' k, g k * z ^ k := by
      rw [← D_zero_eq, ← D_zero_eq]
      exact D_mul_zero hg hc hz1 h0 hs
    have hza : ‖z - a‖ ≤ r := by
      rw [sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max z (-a)).trans (max_le hz (by rw [norm_neg]; exact ha))
    rw [hfz, norm_mul, Multiset.card_cons, pow_succ]
    calc ‖z - a‖ * ‖∑' k, g k * z ^ k‖ ≤ r * (r ^ Multiset.card L * M) :=
          mul_le_mul hza hgz (norm_nonneg _) hr0
      _ = r ^ Multiset.card L * r * M := by ring

end IsUltrametricDist.SchwarzAux

theorem solution {K : Type*} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K]
    (c : ℕ → K) (hc : Filter.Tendsto c Filter.atTop (nhds 0)) (M : ℝ) (hM : ∀ k, ‖c k‖ ≤ M)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (Z : Finset K) (hZ : ∀ z ∈ Z, ‖z‖ ≤ r) (T : ℕ)
    (hzero : ∀ z ∈ Z, ∀ t < T, ∑' k : ℕ, (k.choose t : K) * c k * z ^ (k - t) = 0)
    (z : K) (hz : ‖z‖ ≤ r) :
    ‖∑' k : ℕ, c k * z ^ k‖ ≤ r ^ (T * Z.card) * M := by
  classical
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hcard : Multiset.card (T • Z.val) = T * Z.card := by
    simp
  rw [← hcard]
  refine IsUltrametricDist.SchwarzAux.key hM0 hr0 hr1 (T • Z.val) c hc hM ?_ ?_ z hz
  · intro a ha
    exact hZ a (Multiset.mem_of_mem_nsmul ha)
  · intro b t ht
    rw [Multiset.count_nsmul] at ht
    have hpos : 0 < Z.val.count b := by
      rcases Nat.eq_zero_or_pos (Z.val.count b) with h | h
      · rw [h, mul_zero] at ht; omega
      · exact h
    have hbZ : b ∈ Z := Multiset.count_pos.mp hpos
    have hle : Z.val.count b ≤ 1 := Multiset.nodup_iff_count_le_one.mp Z.nodup b
    have htT : t < T := by nlinarith
    exact hzero b hbZ t htT
