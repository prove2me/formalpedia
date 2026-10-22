-- Prove2me | solution 1 for MaxPressure.Throughput.extended_fluid_limit_equations
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:40:37.938589+00:00
-- url     : https://prove2.me/submissions/797a5f05-0586-450f-a2cc-7a5565f07aa7

import Mathlib
import Definitions.Def_MaxPressure_Throughput_Dynamics

open Filter Topology

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

theorem fluid_limit_equations_core {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (hN : N.Standing) (P : Primitives I J Ω)
    (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ)
    (ω : Ω)
    (heq : NetworkEquations N P Z T ω)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hlim : IsFluidLimit N P Z T ω Zb Tb) :
    IsFluidSolution N Zb Tb ∧ Zb 0 = 0 := by
  obtain ⟨hfin, hZe, hZnn, hin, hcap, hmono, hT0⟩ := heq
  obtain ⟨hgood, r, hrpos, hrtop, hZ, hT⟩ := hlim
  have hZp : ∀ s, 0 ≤ s → ∀ i, Tendsto (fun n => (r n)⁻¹ * Z ω (r n * s) i) atTop
      (𝓝 (Zb s i)) := fun s hs i =>
    g30f_supDist_pt (fun n s i => (r n)⁻¹ * Z ω (r n * s) i) Zb s (hZ s hs) ⟨hs, le_rfl⟩ i
  have hTp : ∀ s, 0 ≤ s → ∀ j, Tendsto (fun n => (r n)⁻¹ * T ω (r n * s) j) atTop
      (𝓝 (Tb s j)) := fun s hs j =>
    g30f_supDist_pt (fun n s j => (r n)⁻¹ * T ω (r n * s) j) Tb s (hT s hs) ⟨hs, le_rfl⟩ j
  have hrinv : Tendsto (fun n => (r n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hrtop
  -- Zb 0 = 0
  have hZb0 : Zb 0 = 0 := by
    funext i
    have h1 := hZp 0 le_rfl i
    simp only [mul_zero] at h1
    have h2 : Tendsto (fun n => (r n)⁻¹ * Z ω 0 i) atTop (𝓝 0) := by
      simpa using hrinv.mul_const (Z ω 0 i)
    exact tendsto_nhds_unique h1 h2
  have hTnn : ∀ s, 0 ≤ s → ∀ j, 0 ≤ T ω s j := by
    intro s hs j
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs) hs
    rw [hT0] at this
    exact this j
  -- completions scale linearly
  have hC : ∀ s, 0 ≤ s → ∀ j, Tendsto (fun n =>
      ((completions P j ω (T ω (r n * s) j)).toNat : ℝ) / r n) atTop
      (𝓝 (mu N j * Tb s j)) := by
    intro s hs j
    have hm : 0 < N.m j := hN.2.2.2.2.2.2.2.2.1 j
    have hren := g30f_renewal (S := BellWilliams2001.ThresholdPolicy.partialSum
      (fun l => P.eta j l ω)) hm (hgood.1 j)
    have := g30f_AL hren (x := fun n => T ω (r n * s) j)
      (fun n => hTnn _ (mul_nonneg (hrpos n).le hs) j) hrpos hrtop
      (τ := Tb s j) (by simpa [div_eq_inv_mul] using hTp s hs j)
    simpa [completions, mu] using this
  have hPhi : ∀ s, 0 ≤ s → ∀ j (i' : Fin (I + 1)) (i : Fin I),
      Tendsto (fun n => ((P.Phi j i' i.succ
        ((completions P j ω (T ω (r n * s) j)).toNat *
          (if N.B j i' = 1 then 1 else 0)) ω : ℕ) : ℝ) / r n) atTop
      (𝓝 (Tb s j * mu N j * N.B j i' * N.P j i' i.succ)) := by
    intro s hs j i' i
    by_cases hB : N.B j i' = 1
    · simp only [hB, if_true, mul_one]
      have hph := g30f_phi (φ := fun l => P.Phi j i' i.succ l ω) (hgood.2 j i' i.succ)
      have := g30f_AL hph
        (x := fun n => ((completions P j ω (T ω (r n * s) j)).toNat : ℝ))
        (fun n => by positivity) hrpos hrtop (hC s hs j)
      simp only [Nat.floor_natCast] at this
      convert this using 2
      ring
    · have hB0 : N.B j i' = 0 := by
        rcases hN.2.1 j i' with h | h
        · exact h
        · exact absurd h hB
      simp only [hB, if_false, mul_zero, hB0]
      simpa [div_eq_inv_mul] using hrinv.mul_const ((P.Phi j i' i.succ 0 ω : ℕ) : ℝ)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hZb0⟩
  · intro s hs i
    have hlimZ := hZp s hs i
    have hR : Tendsto (fun n => (r n)⁻¹ * Z ω 0 i +
        ∑ i' : Fin (I + 1), ∑ j : Fin J,
          ((P.Phi j i' i.succ ((completions P j ω (T ω (r n * s) j)).toNat *
            (if N.B j i' = 1 then 1 else 0)) ω : ℕ) : ℝ) / r n -
        ∑ j : Fin J, ((completions P j ω (T ω (r n * s) j)).toNat : ℝ) / r n *
          N.B j i.succ) atTop
        (𝓝 (Zb 0 i + ∑ i' : Fin (I + 1), ∑ j : Fin J,
          Tb s j * mu N j * N.B j i' * N.P j i' i.succ -
          ∑ j : Fin J, Tb s j * mu N j * N.B j i.succ)) := by
      have hz : Tendsto (fun n => (r n)⁻¹ * Z ω 0 i) atTop (𝓝 (Zb 0 i)) := by
        rw [hZb0]; simpa using hrinv.mul_const (Z ω 0 i)
      refine (hz.add
        (tendsto_finset_sum _ fun i' _ => tendsto_finset_sum _ fun j _ =>
          hPhi s hs j i' i)).sub (tendsto_finset_sum _ fun j _ => ?_)
      have := (hC s hs j).mul_const (N.B j i.succ)
      convert this using 2
      ring
    refine tendsto_nhds_unique hlimZ (hR.congr' (Eventually.of_forall fun n => ?_))
    simp only
    rw [hZe (r n * s) (mul_nonneg (hrpos n).le hs) i]
    simp only [div_eq_inv_mul, mul_add, mul_sub, Finset.mul_sum]
    ring_nf
  · intro s hs i
    exact ge_of_tendsto (hZp s hs i) (Eventually.of_forall fun n =>
      mul_nonneg (inv_nonneg.2 (hrpos n).le) (hZnn _ (mul_nonneg (hrpos n).le hs) i))
  · intro s u hs hsu k hk
    have h1 : Tendsto (fun n => ∑ j, N.A k j * ((r n)⁻¹ * T ω (r n * u) j -
        (r n)⁻¹ * T ω (r n * s) j)) atTop (𝓝 (∑ j, N.A k j * (Tb u j - Tb s j))) :=
      tendsto_finset_sum _ fun j _ =>
        ((hTp u (hs.trans hsu) j).sub (hTp s hs j)).const_mul _
    refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_))
    have := hin (r n * s) (r n * u) (mul_nonneg (hrpos n).le hs)
      (mul_le_mul_of_nonneg_left hsu (hrpos n).le) k hk
    have e : ∑ j, N.A k j * ((r n)⁻¹ * T ω (r n * u) j - (r n)⁻¹ * T ω (r n * s) j) =
        (r n)⁻¹ * ∑ j, N.A k j * (T ω (r n * u) j - T ω (r n * s) j) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    dsimp only
    rw [e, this]
    field_simp [(hrpos n).ne']
  · intro s u hs hsu k
    have h1 : Tendsto (fun n => ∑ j, N.A k j * ((r n)⁻¹ * T ω (r n * u) j -
        (r n)⁻¹ * T ω (r n * s) j)) atTop (𝓝 (∑ j, N.A k j * (Tb u j - Tb s j))) :=
      tendsto_finset_sum _ fun j _ =>
        ((hTp u (hs.trans hsu) j).sub (hTp s hs j)).const_mul _
    refine le_of_tendsto' h1 fun n => ?_
    have := hcap (r n * s) (r n * u) (mul_nonneg (hrpos n).le hs)
      (mul_le_mul_of_nonneg_left hsu (hrpos n).le) k
    have e : ∑ j, N.A k j * ((r n)⁻¹ * T ω (r n * u) j - (r n)⁻¹ * T ω (r n * s) j) =
        (r n)⁻¹ * ∑ j, N.A k j * (T ω (r n * u) j - T ω (r n * s) j) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    have hr := hrpos n
    calc (r n)⁻¹ * ∑ j, N.A k j * (T ω (r n * u) j - T ω (r n * s) j)
        ≤ (r n)⁻¹ * (r n * u - r n * s) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.2 hr.le)
      _ = u - s := by field_simp
  · intro s hs u hu hsu j
    refine le_of_tendsto_of_tendsto' (hTp s hs j) (hTp u hu j) fun n => ?_
    have := hmono (Set.mem_Ici.2 (mul_nonneg (hrpos n).le hs))
      (Set.mem_Ici.2 (mul_nonneg (hrpos n).le hu))
      (mul_le_mul_of_nonneg_left hsu (hrpos n).le)
    exact mul_le_mul_of_nonneg_left (this j) (inv_nonneg.2 (hrpos n).le)
  · funext j
    have h1 := hTp 0 le_rfl j
    simp only [mul_zero, hT0, Pi.zero_apply, mul_zero] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds


lemma g30e_pressure_eq {I J K : ℕ} (N : Network I J K) (v : Fin J → ℝ) (z : Fin I → ℝ) :
    pressure N v z = ∑ j, v j * (∑ i, z i * R N i j) := by
  unfold pressure
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

lemma g30e_pressure_cont_z {I J K : ℕ} (N : Network I J K) (v : Fin J → ℝ) :
    Continuous (fun z => pressure N v z) := by
  simp_rw [g30e_pressure_eq]
  fun_prop

lemma g30e_pressure_smul {I J K : ℕ} (N : Network I J K) (v : Fin J → ℝ) (z : Fin I → ℝ)
    (c : ℝ) : pressure N v (fun i => c * z i) = c * pressure N v z := by
  simp only [g30e_pressure_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

lemma g30e_Zb_cont {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) (hfs : IsFluidSolution N Zb Tb)
    (t : ℝ) (ht : 0 < t) : ContinuousAt Zb t := by
  obtain ⟨hZeq, _, _, hcap, hmono, _⟩ := hfs
  have hlip : ∀ s u, 0 ≤ s → s ≤ u → ∀ j, 0 ≤ Tb u j - Tb s j ∧ Tb u j - Tb s j ≤ u - s := by
    intro s u hs hsu j
    have hm : Tb s ≤ Tb u := hmono (Set.mem_Ici.2 hs) (Set.mem_Ici.2 (hs.trans hsu)) hsu
    refine ⟨sub_nonneg.2 (hm j), ?_⟩
    obtain ⟨k, hk⟩ := hN.2.2.2.2.1 j
    have h1 := hcap s u hs hsu k
    have h2 : N.A k j * (Tb u j - Tb s j) ≤ ∑ j, N.A k j * (Tb u j - Tb s j) :=
      Finset.single_le_sum (f := fun j => N.A k j * (Tb u j - Tb s j))
        (fun j' _ => mul_nonneg (by rcases hN.1 k j' with h | h <;> rw [h] <;> norm_num)
          (sub_nonneg.2 (hm j'))) (Finset.mem_univ j)
    rw [hk, one_mul] at h2
    linarith
  set Tx : ℝ → Fin J → ℝ := fun s => Tb (max s 0) with hTx
  have hTxl : ∀ s u, s ≤ u → ∀ j, |Tx s j - Tx u j| ≤ u - s := by
    intro s u hsu j
    have h := hlip (max s 0) (max u 0) (le_max_right _ _) (max_le_max hsu le_rfl) j
    have : max u 0 - max s 0 ≤ u - s := by
      rcases le_total s 0 with h1 | h1 <;> rcases le_total u 0 with h2 | h2 <;>
        simp [max_eq_left, max_eq_right, *] <;> linarith
    simp only [hTx]
    rw [abs_sub_comm, abs_of_nonneg h.1]
    linarith [h.2]
  have hTxL : LipschitzWith 1 Tx := by
    refine LipschitzWith.of_dist_le_mul fun s u => ?_
    simp only [NNReal.coe_one, one_mul]
    refine (dist_pi_le_iff dist_nonneg).2 fun j => ?_
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total s u with h | h
    · rw [abs_of_nonpos (by linarith : s - u ≤ 0)]; linarith [hTxl s u h j]
    · rw [abs_sub_comm (Tx s j), abs_of_nonneg (by linarith : 0 ≤ s - u)]
      linarith [hTxl u s h j]
  set Zx : ℝ → Fin I → ℝ := fun s i => Zb 0 i - ∑ j, R N i j * Tx s j with hZx
  have hZZ : ∀ s, 0 ≤ s → Zb s = Zx s := by
    intro s hs
    funext i
    simp only [hZx, hTx, max_eq_left hs]
    rw [hZeq s hs i]
    have : ∑ j, R N i j * Tb s j = ∑ j, Tb s j * mu N j * N.B j i.succ -
        ∑ i' : Fin (I + 1), ∑ j : Fin J, Tb s j * mu N j * N.B j i' * N.P j i' i.succ := by
      simp only [R, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i' _ => by ring
    rw [this]; ring
  have hZxc : Continuous Zx := by
    refine continuous_pi fun i => continuous_const.sub
      (continuous_finset_sum _ fun j _ => continuous_const.mul
        ((continuous_apply j).comp hTxL.continuous))
  have hev : Zx =ᶠ[𝓝 t] Zb := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact (hZZ s hs.le).symm
  exact hZxc.continuousAt.congr hev

theorem extended_fluid_limit_equations_core {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (hN : N.Standing) (hEAA : EAA N)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ)
    (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω)
    (heq : NetworkEquations N P Z (activityTime E Ta) ω)
    (hmp : MPProcess N E Z Ta ω)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (Tab : (Fin J → ℝ) → ℝ → ℝ)
    (hlim : IsMPFluidLimit N P E Z Ta ω Zb Tb Tab) :
    IsFluidSolution N Zb Tb ∧
    (∀ t, 0 ≤ t → ∀ j, Tb t j = ∑ a ∈ E, a j * Tab a t) ∧
    (∀ a ∈ E, MonotoneOn (Tab a) (Set.Ici (0 : ℝ))) ∧
    (∀ t, 0 ≤ t → ∑ a ∈ E, Tab a t = t) ∧
    (∀ t, 0 < t → ∀ a ∈ E,
      (∃ a' ∈ E, pressure N a (Zb t) < pressure N a' (Zb t)) →
      HasDerivAt (Tab a) 0 t) := by
  obtain ⟨hgood, r, hrpos, hrtop, hZ, hT, hTa⟩ := hlim
  have hfs := (fluid_limit_equations_core N hN P Z (activityTime E Ta) ω heq Zb Tb
    ⟨hgood, r, hrpos, hrtop, hZ, hT⟩).1
  have hTp : ∀ s, 0 ≤ s → ∀ j, Tendsto (fun n => (r n)⁻¹ * activityTime E Ta ω (r n * s) j)
      atTop (𝓝 (Tb s j)) := fun s hs j =>
    g30f_supDist_pt (fun n s j => (r n)⁻¹ * activityTime E Ta ω (r n * s) j) Tb s (hT s hs)
      ⟨hs, le_rfl⟩ j
  have hTap : ∀ a ∈ E, ∀ s, 0 ≤ s → Tendsto (fun n => (r n)⁻¹ * Ta ω a (r n * s))
      atTop (𝓝 (Tab a s)) := fun a ha s hs =>
    g30f_supDist_pt (fun n s (_ : Fin 1) => (r n)⁻¹ * Ta ω a (r n * s))
      (fun s (_ : Fin 1) => Tab a s) s (hTa a ha s hs) ⟨hs, le_rfl⟩ 0
  refine ⟨hfs, ?_, ?_, ?_, ?_⟩
  · intro t ht j
    refine tendsto_nhds_unique (hTp t ht j) ?_
    refine (tendsto_finset_sum E fun a ha => (hTap a ha t ht).const_mul (a j)).congr'
      (Eventually.of_forall fun n => ?_)
    simp only [activityTime, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  · intro a ha s hs u hu hsu
    refine le_of_tendsto_of_tendsto' (hTap a ha s hs) (hTap a ha u hu) fun n => ?_
    exact mul_le_mul_of_nonneg_left ((hmp.1 a ha).1
      (Set.mem_Ici.2 (mul_nonneg (hrpos n).le hs)) (Set.mem_Ici.2 (mul_nonneg (hrpos n).le hu))
      (mul_le_mul_of_nonneg_left hsu (hrpos n).le)) (inv_nonneg.2 (hrpos n).le)
  · intro t ht
    refine tendsto_nhds_unique (tendsto_finset_sum E fun a ha => hTap a ha t ht) ?_
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
    dsimp only
    rw [← Finset.mul_sum, hmp.2.1 _ (mul_nonneg (hrpos n).le ht)]
    field_simp [(hrpos n).ne']
  · intro t ht a ha ⟨a', ha', hlt⟩
    obtain ⟨as, has, hmax, hcb⟩ := hEAA (Zb t) (hfs.2.1 t ht.le)
    have hasE : as ∈ E := by rw [← Finset.mem_coe, hE]; exact has
    have hlt2 : pressure N a (Zb t) < pressure N as (Zb t) :=
      lt_of_lt_of_le hlt (hmax a' (hE ▸ Finset.mem_coe.2 ha'))
    let Pz : (Fin I → ℝ) → Prop := fun z =>
      (∀ i ∈ constituentBuffers N as, Zb t i / 2 < z i) ∧ pressure N a z < pressure N as z
    have hPz : ∀ᶠ z in 𝓝 (Zb t), Pz z := by
      refine Filter.Eventually.and ?_ ?_
      · rw [Filter.eventually_all]
        intro i
        by_cases hi : i ∈ constituentBuffers N as
        · have h1 : Zb t i / 2 < Zb t i := by linarith [hcb i hi]
          have := ((continuous_apply i).continuousAt (x := Zb t)).eventually
            (lt_mem_nhds h1)
          filter_upwards [this] with z hz _ using hz
        · exact Eventually.of_forall fun z h => absurd h hi
      · have hc : Continuous (fun z => pressure N as z - pressure N a z) :=
          (g30e_pressure_cont_z N as).sub (g30e_pressure_cont_z N a)
        have h1 : (0:ℝ) < pressure N as (Zb t) - pressure N a (Zb t) := by linarith
        have := hc.continuousAt.eventually (lt_mem_nhds h1)
        filter_upwards [this] with z hz
        linarith
    obtain ⟨η, hη, hηP⟩ := Metric.eventually_nhds_iff.1 hPz
    obtain ⟨δ, hδ, hδZ⟩ := Metric.continuousAt_iff.1 (g30e_Zb_cont N hN Zb Tb hfs t ht)
      (η / 2) (by linarith)
    set h0 := min (δ / 2) (t / 2) with hh0
    have hh0pos : 0 < h0 := lt_min (by linarith) (by linarith)
    have hh0d : h0 ≤ δ / 2 := min_le_left _ _
    have hh0t : h0 ≤ t / 2 := min_le_right _ _
    have hconst : ∀ s ∈ Set.Icc (t - h0) (t + h0), Tab a s = Tab a (t - h0) := by
      intro s hs
      have hu := g30f_supDist_ev (fun n s i => (r n)⁻¹ * Z ω (r n * s) i) Zb (t + h0)
        (hZ (t + h0) (by linarith)) (half_pos hη)
      have hbig : ∀ᶠ n in atTop, ∀ i ∈ constituentBuffers N as,
          (J : ℝ) ≤ r n * (Zb t i / 2) := by
        refine Filter.eventually_all.2 fun i => ?_
        by_cases hi : i ∈ constituentBuffers N as
        · have hpos : 0 < Zb t i / 2 := by linarith [hcb i hi]
          filter_upwards [hrtop.eventually_ge_atTop ((J : ℝ) / (Zb t i / 2))] with n hn _
          rw [div_le_iff₀ hpos] at hn
          linarith
        · exact Eventually.of_forall fun n h => absurd h hi
      have hev : ∀ᶠ n in atTop, Ta ω a (r n * s) = Ta ω a (r n * (t - h0)) := by
        filter_upwards [hu, hbig] with n hn hbn
        refine hmp.2.2 a ha (r n * (t - h0)) (r n * s)
          (mul_nonneg (hrpos n).le (by linarith))
          (mul_le_mul_of_nonneg_left hs.1 (hrpos n).le) ?_
        intro τ hτ
        refine ⟨as, hasE, ?_⟩
        set σ := τ / r n with hσ
        have hrσ : r n * σ = τ := by rw [hσ, mul_div_cancel₀ _ (hrpos n).ne']
        have hσ1 : t - h0 ≤ σ := by
          rw [hσ, le_div_iff₀ (hrpos n)]; linarith [hτ.1]
        have hσ2 : σ ≤ s := by
          rw [hσ, div_le_iff₀ (hrpos n)]; linarith [hτ.2]
        have hd1 := hn σ ⟨by linarith, by linarith [hs.2]⟩
        have hd2 : dist (Zb σ) (Zb t) < η / 2 := hδZ (by
          rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.2])
        have hd3 : dist (fun i => (r n)⁻¹ * Z ω (r n * σ) i) (Zb σ) < η / 2 := by
          rw [dist_pi_lt_iff (half_pos hη)]
          intro i
          rw [Real.dist_eq]
          have : |(r n)⁻¹ * Z ω (r n * σ) i - Zb σ i| ≤
              ∑ i, |(r n)⁻¹ * Z ω (r n * σ) i - Zb σ i| :=
            Finset.single_le_sum (f := fun i => |(r n)⁻¹ * Z ω (r n * σ) i - Zb σ i|)
              (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
          linarith
        have hP := hηP (y := fun i => (r n)⁻¹ * Z ω (r n * σ) i)
          (lt_of_le_of_lt (dist_triangle _ _ _) (by linarith))
        have hZeq : Z ω τ = fun i => r n * ((r n)⁻¹ * Z ω (r n * σ) i) := by
          funext i; rw [hrσ, ← mul_assoc, mul_inv_cancel₀ (hrpos n).ne', one_mul]
        rw [hZeq]
        constructor
        · intro i hi
          have h1 := hP.1 i hi
          have h2 := hbn i hi
          have : r n * (Zb t i / 2) ≤ r n * ((r n)⁻¹ * Z ω (r n * σ) i) :=
            mul_le_mul_of_nonneg_left h1.le (hrpos n).le
          linarith
        · rw [g30e_pressure_smul N a (fun i => (r n)⁻¹ * Z ω (r n * σ) i) (r n),
            g30e_pressure_smul N as (fun i => (r n)⁻¹ * Z ω (r n * σ) i) (r n)]
          exact mul_lt_mul_of_pos_left hP.2 (hrpos n)
      refine tendsto_nhds_unique (hTap a ha s (by linarith [hs.1])) ?_
      refine (hTap a ha (t - h0) (by linarith)).congr' ?_
      filter_upwards [hev] with n hn
      rw [hn]
    have hnb : Tab a =ᶠ[𝓝 t] fun _ => Tab a (t - h0) := by
      filter_upwards [Icc_mem_nhds (by linarith : t - h0 < t) (by linarith : t < t + h0)]
        with s hs
      exact hconst s hs
    exact (hasDerivAt_const t (Tab a (t - h0))).congr_of_eventuallyEq hnb

end MaxPressure.Throughput

open MaxPressure.Throughput


theorem solution {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (hN : N.Standing) (hEAA : EAA N)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ)
    (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω)
    (heq : NetworkEquations N P Z (activityTime E Ta) ω)
    (hmp : MPProcess N E Z Ta ω)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (Tab : (Fin J → ℝ) → ℝ → ℝ)
    (hlim : IsMPFluidLimit N P E Z Ta ω Zb Tb Tab) :
    IsFluidSolution N Zb Tb ∧
    (∀ t, 0 ≤ t → ∀ j, Tb t j = ∑ a ∈ E, a j * Tab a t) ∧
    (∀ a ∈ E, MonotoneOn (Tab a) (Set.Ici (0 : ℝ))) ∧
    (∀ t, 0 ≤ t → ∑ a ∈ E, Tab a t = t) ∧
    (∀ t, 0 < t → ∀ a ∈ E,
      (∃ a' ∈ E, pressure N a (Zb t) < pressure N a' (Zb t)) →
      HasDerivAt (Tab a) 0 t) := by
  exact extended_fluid_limit_equations_core N hN hEAA E hE P Z Ta ω heq hmp Zb Tb Tab hlim
