-- Prove2me | solution 1 for MaxPressure.Throughput.fluid_limit_equations
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:37:53.325925+00:00
-- url     : https://prove2.me/submissions/ac2d46f5-6bbe-4fd3-93ca-0637fdc8b5c4

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

end MaxPressure.Throughput

open MaxPressure.Throughput


theorem solution {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (hN : N.Standing) (P : Primitives I J Ω)
    (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ)
    (ω : Ω)
    (heq : NetworkEquations N P Z T ω)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hlim : IsFluidLimit N P Z T ω Zb Tb) :
    IsFluidSolution N Zb Tb ∧ Zb 0 = 0 := by
  exact fluid_limit_equations_core N hN P Z T ω heq Zb Tb hlim
