-- Prove2me | solution 1 for MaxPressure.Throughput.fluid_weak_stability_implies_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:48:57.39362+00:00
-- url     : https://prove2.me/submissions/c556d4b3-838e-46fd-9cd5-6af7bb289173

import Mathlib
import Definitions.Def_MaxPressure_Throughput_Dynamics

open MeasureTheory
open Filter Topology MeasureTheory

namespace MaxPressure.Throughput

lemma g30f_supDist_ev {m : ℕ} (F : ℕ → ℝ → Fin m → ℝ) (G : ℝ → Fin m → ℝ) (t : ℝ)
    (h : Tendsto (fun n => BellWilliams2001.ThresholdPolicy.supDist (F n) G t) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s ∈ Set.Icc 0 t, ∑ i, |F n s i - G s i| < ε := by
  have h2 := (ENNReal.tendsto_nhds_zero.1 h) (ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.2 (by linarith))
  filter_upwards [h2] with n hn s hs
  have h3 : ENNReal.ofReal (∑ i, |F n s i - G s i|) ≤ ENNReal.ofReal (ε / 2) :=
    le_trans (le_iSup₂ (f := fun s (_ : s ∈ Set.Icc 0 t) =>
      ENNReal.ofReal (∑ i, |F n s i - G s i|)) s hs) hn
  have := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h3
  linarith

lemma g30f_supDist_pt {m : ℕ} (F : ℕ → ℝ → Fin m → ℝ) (G : ℝ → Fin m → ℝ) (t : ℝ)
    (h : Tendsto (fun n => BellWilliams2001.ThresholdPolicy.supDist (F n) G t) atTop (𝓝 0))
    {s : ℝ} (hs : s ∈ Set.Icc 0 t) (i : Fin m) :
    Tendsto (fun n => F n s i) atTop (𝓝 (G s i)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (g30f_supDist_ev F G t h hε)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn s hs
  rw [Real.dist_eq]
  have : |F n s i - G s i| ≤ ∑ i, |F n s i - G s i| :=
    Finset.single_le_sum (f := fun i => |F n s i - G s i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
  linarith

/-- asymptotically linear functions applied along a scaled sequence -/
lemma g30f_AL {f : ℝ → ℝ} {c : ℝ}
    (hf : ∀ ε > 0, ∃ C, ∀ x, 0 ≤ x → |f x - c * x| ≤ ε * x + C)
    {x r : ℕ → ℝ} (hx0 : ∀ n, 0 ≤ x n) (hr : ∀ n, 0 < r n) (hrt : Tendsto r atTop atTop)
    {τ : ℝ} (hxt : Tendsto (fun n => x n / r n) atTop (𝓝 τ)) :
    Tendsto (fun n => f (x n) / r n) atTop (𝓝 (c * τ)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hε : 0 < δ / (3 * (|τ| + 1)) := by positivity
  obtain ⟨C, hC⟩ := hf _ hε
  have hCr : Tendsto (fun n => |C| / r n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hrt
  have e1 := (Metric.tendsto_atTop.1 hxt) (min 1 (δ / (3 * (|c| + 1)))) (by positivity)
  have e2 := (Metric.tendsto_atTop.1 hCr) (δ / 3) (by positivity)
  obtain ⟨N1, hN1⟩ := e1
  obtain ⟨N2, hN2⟩ := e2
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have h1 := hN1 n (le_of_max_le_left hn)
  have h2 := hN2 n (le_of_max_le_right hn)
  rw [Real.dist_eq] at h1 h2 ⊢
  have hrn := hr n
  have hxr1 : |x n / r n - τ| < 1 := lt_of_lt_of_le h1 (min_le_left _ _)
  have hxr2 : |x n / r n - τ| < δ / (3 * (|c| + 1)) := lt_of_lt_of_le h1 (min_le_right _ _)
  have hCabs : |C| / r n < δ / 3 := by
    have : 0 ≤ |C| / r n := by positivity
    rw [sub_zero, abs_of_nonneg this] at h2; exact h2
  have hxbound : x n / r n ≤ |τ| + 1 := by
    have := (abs_lt.1 hxr1).2
    linarith [le_abs_self τ]
  have hfx := hC (x n) (hx0 n)
  have key : f (x n) / r n - c * τ = (f (x n) - c * x n) / r n + c * (x n / r n - τ) := by
    field_simp; ring
  rw [key]
  have t1 : |(f (x n) - c * x n) / r n| ≤ δ / (3 * (|τ| + 1)) * (x n / r n) + |C| / r n := by
    rw [abs_div, abs_of_pos hrn, div_le_iff₀ hrn]
    have : δ / (3 * (|τ| + 1)) * (x n / r n) * r n = δ / (3 * (|τ| + 1)) * x n := by
      field_simp
    rw [add_mul, this, div_mul_cancel₀ _ hrn.ne']
    linarith [le_abs_self C]
  have t2 : δ / (3 * (|τ| + 1)) * (x n / r n) ≤ δ / 3 := by
    calc δ / (3 * (|τ| + 1)) * (x n / r n) ≤ δ / (3 * (|τ| + 1)) * (|τ| + 1) :=
          mul_le_mul_of_nonneg_left hxbound hε.le
      _ = δ / 3 := by field_simp
  have t3 : |c * (x n / r n - τ)| ≤ δ / 3 := by
    rw [abs_mul]
    calc |c| * |x n / r n - τ| ≤ (|c| + 1) * (δ / (3 * (|c| + 1))) := by
          apply mul_le_mul (by linarith) hxr2.le (abs_nonneg _) (by positivity)
      _ = δ / 3 := by field_simp
  calc |(f (x n) - c * x n) / r n + c * (x n / r n - τ)|
      ≤ |(f (x n) - c * x n) / r n| + |c * (x n / r n - τ)| := abs_add_le _ _
    _ < δ := by linarith

/-- routing counts are asymptotically linear -/
lemma g30f_phi {φ : ℕ → ℕ} {p : ℝ} (h : Tendsto (fun l : ℕ => (φ l : ℝ) / l) atTop (𝓝 p)) :
    ∀ ε > 0, ∃ C, ∀ x : ℝ, 0 ≤ x → |(φ ⌊x⌋₊ : ℝ) - p * x| ≤ ε * x + C := by
  intro ε hε
  obtain ⟨L0, hL0⟩ := (Metric.tendsto_atTop.1 h) ε hε
  refine ⟨∑ l ∈ Finset.range (L0 + 1), |(φ l : ℝ) - p * l| + |p|, fun x hx => ?_⟩
  set l := ⌊x⌋₊ with hl
  have hl1 : (l : ℝ) ≤ x := Nat.floor_le hx
  have hl2 : x < l + 1 := Nat.lt_floor_add_one x
  have hA : |(φ l : ℝ) - p * l| ≤ ε * l + ∑ l ∈ Finset.range (L0 + 1), |(φ l : ℝ) - p * l| := by
    by_cases hlL : l ≤ L0
    · have : |(φ l : ℝ) - p * l| ≤ ∑ l ∈ Finset.range (L0 + 1), |(φ l : ℝ) - p * l| :=
        Finset.single_le_sum (f := fun l => |(φ l : ℝ) - p * l|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.2 (by omega))
      have : 0 ≤ ε * l := by positivity
      linarith
    · have hd := hL0 l (by omega)
      rw [Real.dist_eq] at hd
      have hlpos : (0 : ℝ) < l := by
        have : 0 < l := by omega
        exact_mod_cast this
      have : |(φ l : ℝ) - p * l| = |(φ l : ℝ) / l - p| * l := by
        rw [← abs_of_pos hlpos, ← abs_mul, abs_of_pos hlpos]
        congr 1; field_simp
      have hsum : 0 ≤ ∑ l ∈ Finset.range (L0 + 1), |(φ l : ℝ) - p * l| :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      rw [this]
      nlinarith
  have hB : |(φ l : ℝ) - p * x| ≤ |(φ l : ℝ) - p * l| + |p| := by
    have : (φ l : ℝ) - p * x = ((φ l : ℝ) - p * l) - p * (x - l) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    have : |p * (x - l)| ≤ |p| := by
      rw [abs_mul]
      have : |x - l| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg p]
    linarith
  have : ε * (l : ℝ) ≤ ε * x := mul_le_mul_of_nonneg_left hl1 hε.le
  linarith

/-- the renewal counting process is asymptotically linear -/
lemma g30f_renewal {S : ℕ → ℝ} {m : ℝ} (hm : 0 < m)
    (hS : Tendsto (fun n : ℕ => S n / n) atTop (𝓝 m)) :
    ∀ ε > 0, ∃ C, ∀ x : ℝ, 0 ≤ x →
      |((BellWilliams2001.ThresholdPolicy.renewalCount S x).toNat : ℝ) - (1 / m) * x| ≤
        ε * x + C := by
  intro ε hε
  -- choose e with 1/(m-e) - 1/m < ε and 1/m - 1/(m+e) < ε
  have hc1 : Tendsto (fun e : ℝ => 1 / (m - e)) (𝓝[>] 0) (𝓝 (1 / m)) := by
    have : ContinuousAt (fun e : ℝ => 1 / (m - e)) 0 := by
      apply ContinuousAt.div continuousAt_const (by fun_prop); simp [hm.ne']
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hc2 : Tendsto (fun e : ℝ => 1 / (m + e)) (𝓝[>] 0) (𝓝 (1 / m)) := by
    have : ContinuousAt (fun e : ℝ => 1 / (m + e)) 0 := by
      apply ContinuousAt.div continuousAt_const (by fun_prop); simp [hm.ne']
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < e ∧ e < m ∧ 1 / (m - e) < 1 / m + ε ∧
      1 / m - ε < 1 / (m + e) := by
    filter_upwards [eventually_mem_nhdsWithin, Ioo_mem_nhdsGT hm,
      hc1.eventually (gt_mem_nhds (by linarith : 1 / m < 1 / m + ε)),
      hc2.eventually (lt_mem_nhds (by linarith : 1 / m - ε < 1 / m))] with e h1 h2 h3 h4
    exact ⟨h1, h2.2, h3, h4⟩
  obtain ⟨e, he0, hem, he1, he2⟩ := hev.exists
  obtain ⟨n0, hn0⟩ := (Metric.tendsto_atTop.1 hS) e he0
  refine ⟨n0 + 1, fun x hx => ?_⟩
  have hmn : ∀ n, n0 ≤ n → 1 ≤ n → (m - e) * n ≤ S n ∧ S n ≤ (m + e) * n := by
    intro n hn h1
    have hd := hn0 n hn
    rw [Real.dist_eq, abs_lt] at hd
    have hnpos : (0 : ℝ) < n := by exact_mod_cast h1
    have e1 : S n = S n / n * n := by field_simp
    constructor <;> nlinarith
  -- upper bound
  set B : ℕ := ⌊(n0 : ℝ) + x / (m - e)⌋₊ with hB
  have hup : BellWilliams2001.ThresholdPolicy.renewalCount S x ≤ (B : ℕ∞) := by
    unfold BellWilliams2001.ThresholdPolicy.renewalCount
    refine iSup₂_le fun n hn => ?_
    rw [Nat.cast_le, hB]
    apply Nat.le_floor
    by_cases h : n0 ≤ n ∧ 1 ≤ n
    · have := (hmn n h.1 h.2).1
      have hme : 0 < m - e := by linarith
      have : (n : ℝ) ≤ x / (m - e) := by
        rw [le_div_iff₀ hme]; linarith
      have : (0 : ℝ) ≤ n0 := by positivity
      linarith
    · have : (n : ℝ) ≤ n0 := by
        rcases not_and_or.1 h with h | h
        · exact_mod_cast (not_le.1 h).le
        · have : n = 0 := by omega
          subst this; simp
      have : 0 ≤ x / (m - e) := div_nonneg hx (by linarith)
      linarith
  have hfin : BellWilliams2001.ThresholdPolicy.renewalCount S x ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top B) hup
  have hup' : ((BellWilliams2001.ThresholdPolicy.renewalCount S x).toNat : ℝ) ≤
      n0 + x / (m - e) := by
    have h1 := ENat.toNat_le_of_le_natCast hup
    have h2 : (B : ℝ) ≤ n0 + x / (m - e) := Nat.floor_le (by
      have : 0 ≤ x / (m - e) := div_nonneg hx (by linarith)
      positivity)
    have : ((BellWilliams2001.ThresholdPolicy.renewalCount S x).toNat : ℝ) ≤ B := by
      exact_mod_cast h1
    linarith
  -- lower bound
  set L : ℕ := ⌊x / (m + e)⌋₊ with hL
  have hlow : ((BellWilliams2001.ThresholdPolicy.renewalCount S x).toNat : ℝ) ≥
      x / (m + e) - 1 - n0 := by
    have hL1 : x / (m + e) < L + 1 := Nat.lt_floor_add_one _
    by_cases h : n0 ≤ L ∧ 1 ≤ L
    · have hSL := (hmn L h.1 h.2).2
      have hLx : (m + e) * L ≤ x := by
        have := Nat.floor_le (div_nonneg hx (by linarith : (0:ℝ) ≤ m + e))
        rw [← hL, le_div_iff₀ (by linarith)] at this
        linarith
      have hle : (L : ℕ∞) ≤ BellWilliams2001.ThresholdPolicy.renewalCount S x := by
        unfold BellWilliams2001.ThresholdPolicy.renewalCount
        exact le_iSup₂ (f := fun (n : ℕ) (_ : S n ≤ x) => (n : ℕ∞)) L (by linarith)
      have := ENat.toNat_le_toNat hle hfin
      simp only [ENat.toNat_coe] at this
      have : (L : ℝ) ≤ (BellWilliams2001.ThresholdPolicy.renewalCount S x).toNat := by
        exact_mod_cast this
      linarith
    · have : (L : ℝ) ≤ n0 := by
        rcases not_and_or.1 h with h | h
        · exact_mod_cast (not_le.1 h).le
        · have : L = 0 := by omega
          rw [this]; simp
      have : (0 : ℝ) ≤ (BellWilliams2001.ThresholdPolicy.renewalCount S x).toNat := by
        positivity
      linarith
  rw [abs_le]
  have hme : 0 < m - e := by linarith
  have hpe : 0 < m + e := by linarith
  have q1 : x / (m - e) ≤ (1 / m + ε) * x := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right he1.le hx
  have q2 : (1 / m - ε) * x ≤ x / (m + e) := by
    rw [div_eq_mul_one_div x, mul_comm x]
    exact mul_le_mul_of_nonneg_right he2.le hx
  constructor <;> nlinarith


lemma g30c_cpt {J : ℕ} (g : ℕ → ℝ → Fin J → ℝ)
    (hlip : ∀ n s u, 0 ≤ s → s ≤ u → ∀ j, 0 ≤ g n u j - g n s j ∧ g n u j - g n s j ≤ u - s)
    (h0 : ∀ n, g n 0 = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Tb : ℝ → Fin J → ℝ, ∀ t, 0 ≤ t → ∀ δ > 0,
      ∀ᶠ n in atTop, ∀ s ∈ Set.Icc 0 t, ∀ j, |g (φ n) s j - Tb s j| < δ := by
  have hbd : ∀ n s, 0 ≤ s → ∀ j, 0 ≤ g n s j ∧ g n s j ≤ s := by
    intro n s hs j
    have := hlip n 0 s le_rfl hs j
    rw [h0 n] at this
    simpa using this
  have hL : ∀ n s u, 0 ≤ s → 0 ≤ u → ∀ j, |g n s j - g n u j| ≤ |s - u| := by
    intro n s u hs hu j
    rcases le_total s u with h | h
    · have := hlip n s u hs h j
      rw [abs_sub_comm, abs_of_nonneg this.1, abs_of_nonpos (by linarith)]
      linarith [this.2]
    · have := hlip n u s hu h j
      rw [abs_of_nonneg this.1, abs_of_nonneg (by linarith)]
      exact this.2
  set G : ℕ → (ℚ → Fin J → ℝ) := fun n q => g n (max (q : ℝ) 0) with hG
  set K : Set (ℚ → Fin J → ℝ) :=
    Set.univ.pi (fun q : ℚ => Metric.closedBall (0 : Fin J → ℝ) (max (q : ℝ) 0)) with hK
  have hKc : IsCompact K := isCompact_univ_pi fun q => isCompact_closedBall _ _
  have hGK : ∀ n, G n ∈ K := by
    intro n q _
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
    intro j
    have := hbd n (max (q : ℝ) 0) (le_max_right _ _) j
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]
    exact this.2
  obtain ⟨Lm, _, φ, hφ, hconv⟩ := hKc.tendsto_subseq hGK
  have hconvq : ∀ q j, Tendsto (fun n => G (φ n) q j) atTop (𝓝 (Lm q j)) := fun q j =>
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hconv q) j
  -- uniform Cauchy property
  have hUC : ∀ t, 0 ≤ t → ∀ δ > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∀ s ∈ Set.Icc 0 t, ∀ j,
      |g (φ n) s j - g (φ m) s j| < δ := by
    intro t ht δ hδ
    set M : ℕ := ⌈4 / δ⌉₊ + 1 with hM
    have hMpos : (0 : ℝ) < M := by positivity
    have hM1 : 1 / (M : ℝ) < δ / 4 := by
      have h1 : 4 / δ ≤ (⌈4 / δ⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (M : ℝ) = ⌈4 / δ⌉₊ + 1 := by rw [hM]; push_cast; ring
      rw [div_lt_iff₀ hMpos]
      have : 4 / δ * δ = 4 := by field_simp
      nlinarith
    set K' : ℕ := ⌊t * M⌋₊ with hK'
    have hev : ∀ᶠ n in atTop, ∀ k ∈ Finset.range (K' + 1), ∀ j,
        |G (φ n) ((k : ℚ) / M) j - Lm ((k : ℚ) / M) j| < δ / 4 := by
      rw [Filter.eventually_all_finset]
      intro k _
      rw [Filter.eventually_all]
      intro j
      have := (Metric.tendsto_atTop.1 (hconvq ((k : ℚ) / M) j)) (δ / 4) (by positivity)
      obtain ⟨N, hN⟩ := this
      exact eventually_atTop.2 ⟨N, fun n hn => by rw [← Real.dist_eq]; exact hN n hn⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun n hn m hm s hs j => ?_⟩
    set k : ℕ := ⌊s * M⌋₊ with hk
    have hkK : k ∈ Finset.range (K' + 1) := by
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right hs.2 hMpos.le)
    have hq : (((k : ℚ) / M : ℚ) : ℝ) = (k : ℝ) / M := by push_cast; ring
    have hq0 : (0 : ℝ) ≤ (k : ℝ) / M := by positivity
    have hsq : |s - (k : ℝ) / M| ≤ 1 / M := by
      have h1 : (k : ℝ) ≤ s * M := Nat.floor_le (by nlinarith [hs.1])
      have h2 : s * M < k + 1 := Nat.lt_floor_add_one _
      have h3 : (k : ℝ) / M ≤ s := by rw [div_le_iff₀ hMpos]; linarith
      have h4 : s ≤ (k : ℝ) / M + 1 / M := by
        rw [← add_div, le_div_iff₀ hMpos]; linarith
      rw [abs_le]
      constructor <;> linarith
    have e1 := hN n hn k hkK j
    have e2 := hN m hm k hkK j
    simp only [hG, hq, max_eq_left hq0] at e1 e2
    have l1 := hL (φ n) s ((k : ℝ) / M) hs.1 hq0 j
    have l2 := hL (φ m) s ((k : ℝ) / M) hs.1 hq0 j
    calc |g (φ n) s j - g (φ m) s j|
        ≤ |g (φ n) s j - g (φ n) (k / M) j| + |g (φ n) (k / M) j - Lm ((k : ℚ) / M) j| +
          |g (φ m) (k / M) j - Lm ((k : ℚ) / M) j| + |g (φ m) s j - g (φ m) (k / M) j| := by
          have t1 := abs_sub_le (g (φ n) s j) (g (φ n) (k / M) j) (g (φ m) s j)
          have t2 := abs_sub_le (g (φ n) (k / M) j) (Lm ((k : ℚ) / M) j) (g (φ m) s j)
          have t3 := abs_sub_le (Lm ((k : ℚ) / M) j) (g (φ m) (k / M) j) (g (φ m) s j)
          have t4 := abs_sub_comm (Lm ((k : ℚ) / M) j) (g (φ m) (k / M) j)
          have t5 := abs_sub_comm (g (φ m) (k / M) j) (g (φ m) s j)
          linarith
      _ < δ := by linarith
  -- pointwise limits
  set Tb : ℝ → Fin J → ℝ := fun s => limUnder atTop (fun n => g (φ n) s) with hTb
  have hTbl : ∀ s, 0 ≤ s → Tendsto (fun n => g (φ n) s) atTop (𝓝 (Tb s)) := by
    intro s hs
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hUC s hs (ε / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_pi_lt_iff hε]
    intro j
    rw [Real.dist_eq]
    have := hN n hn N le_rfl s ⟨hs, le_rfl⟩ j
    linarith
  refine ⟨φ, hφ, Tb, fun t ht δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := hUC t ht (δ / 2) (by positivity)
  refine eventually_atTop.2 ⟨N, fun n hn s hs j => ?_⟩
  have hlim : Tendsto (fun m => |g (φ n) s j - g (φ m) s j|) atTop
      (𝓝 |g (φ n) s j - Tb s j|) :=
    (tendsto_const_nhds.sub (tendsto_pi_nhds.1 (hTbl s hs.1) j)).abs
  have : |g (φ n) s j - Tb s j| ≤ δ / 2 :=
    le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun m hm => (hN n hn m hm s hs j).le⟩)
  linarith


lemma g30u_UAL {σ : Type*} {f : ℝ → ℝ} {c : ℝ}
    (hf : ∀ ε > 0, ∃ C, ∀ x, 0 ≤ x → |f x - c * x| ≤ ε * x + C)
    {X : ℕ → σ → ℝ} {r : ℕ → ℝ} (hX0 : ∀ n s, 0 ≤ X n s) (hr : ∀ n, 0 < r n)
    (hrt : Tendsto r atTop atTop)
    {τ : σ → ℝ} {B : ℝ} (hB : ∀ s, |τ s| ≤ B)
    (hXt : ∀ δ > 0, ∀ᶠ n in atTop, ∀ s, |X n s / r n - τ s| < δ) :
    ∀ δ > 0, ∀ᶠ n in atTop, ∀ s, |f (X n s) / r n - c * τ s| < δ := by
  intro δ hδ
  have hε : 0 < δ / (3 * (|B| + 1)) := by positivity
  obtain ⟨C, hC⟩ := hf _ hε
  have hCr : Tendsto (fun n => |C| / r n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hrt
  have e2 := (Metric.tendsto_atTop.1 hCr) (δ / 3) (by positivity)
  obtain ⟨N2, hN2⟩ := e2
  filter_upwards [hXt (min 1 (δ / (3 * (|c| + 1)))) (by positivity),
    eventually_atTop.2 ⟨N2, fun n hn => hN2 n hn⟩] with n h1 h2 s
  have h1 := h1 s
  rw [Real.dist_eq] at h2
  have hrn := hr n
  have hxr1 : |X n s / r n - τ s| < 1 := lt_of_lt_of_le h1 (min_le_left _ _)
  have hxr2 : |X n s / r n - τ s| < δ / (3 * (|c| + 1)) := lt_of_lt_of_le h1 (min_le_right _ _)
  have hCabs : |C| / r n < δ / 3 := by
    have : 0 ≤ |C| / r n := by positivity
    rw [sub_zero, abs_of_nonneg this] at h2; exact h2
  have hxbound : X n s / r n ≤ |B| + 1 := by
    have := (abs_lt.1 hxr1).2
    linarith [le_abs_self (τ s), hB s, le_abs_self B]
  have hfx := hC (X n s) (hX0 n s)
  have key : f (X n s) / r n - c * τ s =
      (f (X n s) - c * X n s) / r n + c * (X n s / r n - τ s) := by
    field_simp; ring
  rw [key]
  have t1 : |(f (X n s) - c * X n s) / r n| ≤
      δ / (3 * (|B| + 1)) * (X n s / r n) + |C| / r n := by
    rw [abs_div, abs_of_pos hrn, div_le_iff₀ hrn]
    have : δ / (3 * (|B| + 1)) * (X n s / r n) * r n = δ / (3 * (|B| + 1)) * X n s := by
      field_simp
    rw [add_mul, this, div_mul_cancel₀ _ hrn.ne']
    linarith [le_abs_self C]
  have t2 : δ / (3 * (|B| + 1)) * (X n s / r n) ≤ δ / 3 := by
    calc δ / (3 * (|B| + 1)) * (X n s / r n) ≤ δ / (3 * (|B| + 1)) * (|B| + 1) :=
          mul_le_mul_of_nonneg_left hxbound hε.le
      _ = δ / 3 := by field_simp
  have t3 : |c * (X n s / r n - τ s)| ≤ δ / 3 := by
    rw [abs_mul]
    calc |c| * |X n s / r n - τ s| ≤ (|c| + 1) * (δ / (3 * (|c| + 1))) := by
          apply mul_le_mul (by linarith) hxr2.le (abs_nonneg _) (by positivity)
      _ = δ / 3 := by field_simp
  calc |(f (X n s) - c * X n s) / r n + c * (X n s / r n - τ s)|
      ≤ |(f (X n s) - c * X n s) / r n| + |c * (X n s / r n - τ s)| := abs_add_le _ _
    _ < δ := by linarith

lemma g30u_toSup {m : ℕ} (F : ℕ → ℝ → Fin m → ℝ) (G : ℝ → Fin m → ℝ) (t : ℝ)
    (h : ∀ δ > 0, ∀ᶠ n in atTop, ∀ s ∈ Set.Icc 0 t, ∑ i, |F n s i - G s i| < δ) :
    Tendsto (fun n => BellWilliams2001.ThresholdPolicy.supDist (F n) G t) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact Eventually.of_forall fun n => by rw [htop]; exact le_top
  have hpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  filter_upwards [h _ hpos] with n hn
  unfold BellWilliams2001.ThresholdPolicy.supDist
  exact iSup₂_le fun s hs => ENNReal.ofReal_le_of_le_toReal (hn s hs).le

theorem fluid_weak_stability_implies_pathwise_core {I J K : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (Pr : Measure Ω)
    (N : Network I J K) (hN : N.Standing)
    (P : Primitives I J Ω) (hP : P.Valid N Pr)
    (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ)
    (heq : ∀ ω, NetworkEquations N P Z T ω)
    (FM : (ℝ → Fin I → ℝ) → (ℝ → Fin J → ℝ) → Prop)
    (hcorresponding : ∀ ω Zb Tb,
      IsFluidLimit N P Z T ω Zb Tb → FM Zb Tb)
    (hweak : WeaklyStable FM) : PathwiseStable Pr Z := by
  have hgood : ∀ᵐ ω ∂Pr, P.GoodSample N ω := hP.2.2.2.2.2.2.2.2
  filter_upwards [hgood] with ω hω i
  by_contra hne
  rw [Metric.tendsto_nhds] at hne
  push_neg at hne
  obtain ⟨ε, hε, hfreq⟩ := hne
  rw [Filter.frequently_atTop] at hfreq
  choose tq htq hbad using fun n : ℕ => hfreq ((n : ℝ) + 1)
  have hrpos : ∀ n, 0 < tq n := fun n => by
    have := htq n; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hrtop : Tendsto tq atTop atTop :=
    tendsto_atTop_mono htq (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  obtain ⟨hfin, hZe, hZnn, hin, hcap, hmono, hT0⟩ := heq ω
  set g : ℕ → ℝ → Fin J → ℝ := fun n s j => (tq n)⁻¹ * T ω (tq n * s) j with hg
  have hlip : ∀ n s u, 0 ≤ s → s ≤ u → ∀ j,
      0 ≤ g n u j - g n s j ∧ g n u j - g n s j ≤ u - s := by
    intro n s u hs hsu j
    have hr := hrpos n
    have hs' : 0 ≤ tq n * s := mul_nonneg hr.le hs
    have hsu' : tq n * s ≤ tq n * u := mul_le_mul_of_nonneg_left hsu hr.le
    have hm : T ω (tq n * s) ≤ T ω (tq n * u) :=
      hmono (Set.mem_Ici.2 hs') (Set.mem_Ici.2 (hs'.trans hsu')) hsu'
    obtain ⟨k, hk⟩ := hN.2.2.2.2.1 j
    have h1 := hcap _ _ hs' hsu' k
    have h2 : N.A k j * (T ω (tq n * u) j - T ω (tq n * s) j) ≤
        ∑ j, N.A k j * (T ω (tq n * u) j - T ω (tq n * s) j) :=
      Finset.single_le_sum (f := fun j => N.A k j * (T ω (tq n * u) j - T ω (tq n * s) j))
        (fun j' _ => mul_nonneg (by rcases hN.1 k j' with h | h <;> rw [h] <;> norm_num)
          (sub_nonneg.2 (hm j'))) (Finset.mem_univ j)
    rw [hk, one_mul] at h2
    have e : g n u j - g n s j = (tq n)⁻¹ * (T ω (tq n * u) j - T ω (tq n * s) j) := by
      simp only [hg]; ring
    rw [e]
    constructor
    · exact mul_nonneg (inv_nonneg.2 hr.le) (sub_nonneg.2 (hm j))
    · calc (tq n)⁻¹ * (T ω (tq n * u) j - T ω (tq n * s) j)
          ≤ (tq n)⁻¹ * (tq n * u - tq n * s) :=
            mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hr.le)
        _ = u - s := by field_simp
  have h0 : ∀ n, g n 0 = 0 := by
    intro n; funext j; simp [hg, hT0]
  obtain ⟨φ, hφ, Tb, hTb⟩ := g30c_cpt g hlip h0
  set r : ℕ → ℝ := fun n => tq (φ n) with hr
  have hr'pos : ∀ n, 0 < r n := fun n => hrpos (φ n)
  have hr'top : Tendsto r atTop atTop := hrtop.comp hφ.tendsto_atTop
  -- bounds on Tb
  have hTbpt : ∀ s, 0 ≤ s → ∀ j, Tendsto (fun n => g (φ n) s j) atTop (𝓝 (Tb s j)) := by
    intro s hs j
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨M, hM⟩ := eventually_atTop.1 (hTb s hs δ hδ)
    exact ⟨M, fun n hn => by rw [Real.dist_eq]; exact hM n hn s ⟨hs, le_rfl⟩ j⟩
  have hgbd : ∀ n s, 0 ≤ s → ∀ j, 0 ≤ g n s j ∧ g n s j ≤ s := by
    intro n s hs j
    have := hlip n 0 s le_rfl hs j
    rw [h0 n] at this
    simpa using this
  have hTbbd : ∀ s, 0 ≤ s → ∀ j, 0 ≤ Tb s j ∧ Tb s j ≤ s := fun s hs j =>
    ⟨ge_of_tendsto (hTbpt s hs j) (Eventually.of_forall fun n => (hgbd _ s hs j).1),
     le_of_tendsto (hTbpt s hs j) (Eventually.of_forall fun n => (hgbd _ s hs j).2)⟩
  set Zb : ℝ → Fin I → ℝ := fun s i =>
    ∑ i' : Fin (I + 1), ∑ j : Fin J, Tb s j * mu N j * N.B j i' * N.P j i' i.succ -
      ∑ j : Fin J, Tb s j * mu N j * N.B j i.succ with hZb
  have hTnn : ∀ s, 0 ≤ s → ∀ j, 0 ≤ T ω s j := by
    intro s hs j
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs) hs
    rw [hT0] at this
    exact this j
  -- convergence of T
  have hlimT : ∀ t, 0 ≤ t → Tendsto (fun n => BellWilliams2001.ThresholdPolicy.supDist
      (fun s j => (r n)⁻¹ * T ω (r n * s) j) Tb t) atTop (𝓝 0) := by
    intro t ht
    refine g30u_toSup _ _ _ fun δ hδ => ?_
    have hδ' : 0 < δ / (J + 1) := by positivity
    filter_upwards [hTb t ht _ hδ'] with n hn s hs
    calc ∑ j, |(r n)⁻¹ * T ω (r n * s) j - Tb s j| ≤ ∑ _j : Fin J, δ / (J + 1) :=
          Finset.sum_le_sum fun j _ => (hn s hs j).le
      _ = J * (δ / (J + 1)) := by simp
      _ < δ := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  -- convergence of Z
  have hlimZ : ∀ t, 0 ≤ t → Tendsto (fun n => BellWilliams2001.ThresholdPolicy.supDist
      (fun s i => (r n)⁻¹ * Z ω (r n * s) i) Zb t) atTop (𝓝 0) := by
    intro t ht
    refine g30u_toSup _ _ _ fun δ hδ => ?_
    set Kc : ℝ := 1 + ((I : ℝ) + 1) * J + J with hKc
    have hKc0 : 0 < Kc := by positivity
    set δ' : ℝ := δ / ((I + 1) * Kc) with hδ'
    have hδ'0 : 0 < δ' := by positivity
    -- scaled activity times, uniformly on [0, t]
    have hXt : ∀ j, ∀ δ > 0, ∀ᶠ n in atTop, ∀ s : Set.Icc (0 : ℝ) t,
        |T ω (r n * s) j / r n - Tb s j| < δ := by
      intro j δ hδ
      filter_upwards [hTb t ht δ hδ] with n hn s
      rw [div_eq_inv_mul]
      exact hn s s.2 j
    have E1 : ∀ j, ∀ δ > 0, ∀ᶠ n in atTop, ∀ s : Set.Icc (0 : ℝ) t,
        |((completions P j ω (T ω (r n * s) j)).toNat : ℝ) / r n - mu N j * Tb s j| < δ := by
      intro j
      have hm : 0 < N.m j := hN.2.2.2.2.2.2.2.2.1 j
      have hren := g30f_renewal (S := BellWilliams2001.ThresholdPolicy.partialSum
        (fun l => P.eta j l ω)) hm (hω.1 j)
      have := g30u_UAL hren (X := fun n (s : Set.Icc (0 : ℝ) t) => T ω (r n * s) j)
        (fun n s => hTnn _ (mul_nonneg (hr'pos n).le s.2.1) j) hr'pos hr'top
        (τ := fun s => Tb s j) (B := t)
        (fun s => by rw [abs_of_nonneg (hTbbd s s.2.1 j).1]; exact (hTbbd s s.2.1 j).2.trans s.2.2)
        (hXt j)
      simpa [completions, mu] using this
    have E2 : ∀ j (i' : Fin (I + 1)) (i : Fin I), ∀ᶠ n in atTop, ∀ s : Set.Icc (0 : ℝ) t,
        |((P.Phi j i' i.succ ((completions P j ω (T ω (r n * s) j)).toNat *
          (if N.B j i' = 1 then 1 else 0)) ω : ℕ) : ℝ) / r n -
          Tb s j * mu N j * N.B j i' * N.P j i' i.succ| < δ' := by
      intro j i' i
      by_cases hB : N.B j i' = 1
      · simp only [hB, if_true, mul_one]
        have hph := g30f_phi (φ := fun l => P.Phi j i' i.succ l ω) (hω.2 j i' i.succ)
        have := g30u_UAL hph
          (X := fun n (s : Set.Icc (0 : ℝ) t) =>
            ((completions P j ω (T ω (r n * s) j)).toNat : ℝ))
          (fun n s => by positivity) hr'pos hr'top
          (τ := fun s => mu N j * Tb s j) (B := mu N j * t)
          (fun s => by
            have hmu : 0 ≤ mu N j := by
              unfold mu; exact div_nonneg zero_le_one (hN.2.2.2.2.2.2.2.2.1 j).le
            rw [abs_of_nonneg (mul_nonneg hmu (hTbbd s s.2.1 j).1)]
            exact mul_le_mul_of_nonneg_left ((hTbbd s s.2.1 j).2.trans s.2.2) hmu)
          (E1 j) δ' hδ'0
        filter_upwards [this] with n hn s
        have := hn s
        simp only [Nat.floor_natCast] at this
        convert this using 3
        ring
      · have hB0 : N.B j i' = 0 := by
          rcases hN.2.1 j i' with h | h
          · exact h
          · exact absurd h hB
        rw [if_neg hB]
        simp only [mul_zero, hB0, zero_mul, sub_zero]
        have hc : Tendsto (fun n => ((P.Phi j i' i.succ 0 ω : ℕ) : ℝ) / r n) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop hr'top
        obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 hc) δ' hδ'0
        exact eventually_atTop.2 ⟨M, fun n hn s => by
          have := hM n hn; rw [Real.dist_eq, sub_zero] at this; exact this⟩
    have E0 : ∀ i : Fin I, ∀ᶠ n in atTop, |(r n)⁻¹ * Z ω 0 i| < δ' := by
      intro i
      have hc : Tendsto (fun n => (r n)⁻¹ * Z ω 0 i) atTop (𝓝 0) := by
        simpa using (tendsto_inv_atTop_zero.comp hr'top).mul_const (Z ω 0 i)
      obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 hc) δ' hδ'0
      exact eventually_atTop.2 ⟨M, fun n hn => by
        have := hM n hn; rw [Real.dist_eq, sub_zero] at this; exact this⟩
    filter_upwards [Filter.eventually_all.2 fun j => E1 j δ' hδ'0,
      Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun i' =>
        Filter.eventually_all.2 fun i => E2 j i' i,
      Filter.eventually_all.2 E0] with n h1 h2 h3 s hs
    have hper : ∀ i : Fin I, |(r n)⁻¹ * Z ω (r n * s) i - Zb s i| ≤ δ' * Kc := by
      intro i
      have hsn : 0 ≤ r n * s := mul_nonneg (hr'pos n).le hs.1
      rw [hZe (r n * s) hsn i]
      have e : (r n)⁻¹ * (Z ω 0 i +
          ∑ i' : Fin (I + 1), ∑ j : Fin J,
            ((P.Phi j i' i.succ ((completions P j ω (T ω (r n * s) j)).toNat *
              (if N.B j i' = 1 then 1 else 0)) ω : ℕ) : ℝ) -
          ∑ j : Fin J, ((completions P j ω (T ω (r n * s) j)).toNat : ℝ) * N.B j i.succ) -
          Zb s i =
          (r n)⁻¹ * Z ω 0 i +
          ∑ i' : Fin (I + 1), ∑ j : Fin J,
            (((P.Phi j i' i.succ ((completions P j ω (T ω (r n * s) j)).toNat *
              (if N.B j i' = 1 then 1 else 0)) ω : ℕ) : ℝ) / r n -
              Tb s j * mu N j * N.B j i' * N.P j i' i.succ) -
          ∑ j : Fin J, ((((completions P j ω (T ω (r n * s) j)).toNat : ℝ) / r n -
              mu N j * Tb s j) * N.B j i.succ) := by
        simp only [hZb, mul_add, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib,
          div_eq_inv_mul, sub_mul]
        ring_nf
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      have b1 : |∑ i' : Fin (I + 1), ∑ j : Fin J,
            (((P.Phi j i' i.succ ((completions P j ω (T ω (r n * s) j)).toNat *
              (if N.B j i' = 1 then 1 else 0)) ω : ℕ) : ℝ) / r n -
              Tb s j * mu N j * N.B j i' * N.P j i' i.succ)| ≤ ((I : ℝ) + 1) * J * δ' := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i' : Fin (I + 1), |∑ j : Fin J,
              (((P.Phi j i' i.succ ((completions P j ω (T ω (r n * s) j)).toNat *
                (if N.B j i' = 1 then 1 else 0)) ω : ℕ) : ℝ) / r n -
                Tb s j * mu N j * N.B j i' * N.P j i' i.succ)|
            ≤ ∑ _i' : Fin (I + 1), ∑ _j : Fin J, δ' := by
              refine Finset.sum_le_sum fun i' _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
              exact Finset.sum_le_sum fun j _ => (h2 j i' i ⟨s, hs⟩).le
          _ = ((I : ℝ) + 1) * J * δ' := by simp; ring
      have b2 : |∑ j : Fin J, ((((completions P j ω (T ω (r n * s) j)).toNat : ℝ) / r n -
              mu N j * Tb s j) * N.B j i.succ)| ≤ J * δ' := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ j : Fin J, |(((completions P j ω (T ω (r n * s) j)).toNat : ℝ) / r n -
              mu N j * Tb s j) * N.B j i.succ| ≤ ∑ _j : Fin J, δ' := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [abs_mul]
              have hb : |N.B j i.succ| ≤ 1 := by
                rcases hN.2.1 j i.succ with h | h <;> rw [h] <;> norm_num
              have := (h1 j ⟨s, hs⟩).le
              nlinarith [abs_nonneg (((completions P j ω (T ω (r n * s) j)).toNat : ℝ) / r n -
                mu N j * Tb s j), abs_nonneg (N.B j i.succ)]
          _ = J * δ' := by simp
      have b0 := (h3 i).le
      calc _ ≤ |(r n)⁻¹ * Z ω 0 i + ∑ i' : Fin (I + 1), ∑ j : Fin J,
            (((P.Phi j i' i.succ ((completions P j ω (T ω (r n * s) j)).toNat *
              (if N.B j i' = 1 then 1 else 0)) ω : ℕ) : ℝ) / r n -
              Tb s j * mu N j * N.B j i' * N.P j i' i.succ)| +
            |∑ j : Fin J, ((((completions P j ω (T ω (r n * s) j)).toNat : ℝ) / r n -
              mu N j * Tb s j) * N.B j i.succ)| := abs_sub _ _
        _ ≤ |(r n)⁻¹ * Z ω 0 i| + |∑ i' : Fin (I + 1), ∑ j : Fin J,
            (((P.Phi j i' i.succ ((completions P j ω (T ω (r n * s) j)).toNat *
              (if N.B j i' = 1 then 1 else 0)) ω : ℕ) : ℝ) / r n -
              Tb s j * mu N j * N.B j i' * N.P j i' i.succ)| +
            |∑ j : Fin J, ((((completions P j ω (T ω (r n * s) j)).toNat : ℝ) / r n -
              mu N j * Tb s j) * N.B j i.succ)| := by
            gcongr; exact abs_add_le _ _
        _ ≤ δ' * Kc := by rw [hKc]; nlinarith
    calc ∑ i, |(r n)⁻¹ * Z ω (r n * s) i - Zb s i| ≤ ∑ _i : Fin I, δ' * Kc :=
          Finset.sum_le_sum fun i _ => hper i
      _ = I * (δ' * Kc) := by simp
      _ < δ := by
          rw [hδ']
          have : (I : ℝ) * (δ / ((I + 1) * Kc) * Kc) = I * δ / (I + 1) := by
            field_simp
          rw [this, div_lt_iff₀ (by positivity)]
          nlinarith
  have hFL : IsFluidLimit N P Z T ω Zb Tb := ⟨hω, r, hr'pos, hr'top, hlimZ, hlimT⟩
  have hFM := hcorresponding ω Zb Tb hFL
  have hTb0 : ∀ j, Tb 0 j = 0 := fun j =>
    le_antisymm (hTbbd 0 le_rfl j).2 (hTbbd 0 le_rfl j).1
  have hZb0 : Zb 0 = 0 := by
    funext i; simp [hZb, hTb0]
  have hZ1 := congrFun (hweak Zb Tb hFM hZb0 1 zero_le_one) i
  have hpt := g30f_supDist_pt (fun n s i => (r n)⁻¹ * Z ω (r n * s) i) Zb 1
    (hlimZ 1 zero_le_one) ⟨zero_le_one, le_rfl⟩ i
  rw [hZ1] at hpt
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.1 hpt) ε hε
  have h1 := hM M le_rfl
  have h2 := hbad (φ M)
  simp only [mul_one, Pi.zero_apply] at h1
  rw [Real.dist_eq, sub_zero] at h1 h2
  rw [div_eq_inv_mul] at h2
  linarith

end MaxPressure.Throughput

open MaxPressure.Throughput


theorem solution {I J K : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (N : Network I J K) (hN : N.Standing)
    (P : Primitives I J Ω) (hP : P.Valid N Pr)
    (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ)
    (heq : ∀ ω, NetworkEquations N P Z T ω)
    (FM : (ℝ → Fin I → ℝ) → (ℝ → Fin J → ℝ) → Prop)
    (hcorresponding : ∀ ω Zb Tb,
      IsFluidLimit N P Z T ω Zb Tb → FM Zb Tb)
    (hweak : WeaklyStable FM) : PathwiseStable Pr Z := by
  exact fluid_weak_stability_implies_pathwise_core Pr N hN P hP Z T heq FM hcorresponding hweak
