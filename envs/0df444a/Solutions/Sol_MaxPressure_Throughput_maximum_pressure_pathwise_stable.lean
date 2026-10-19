-- Prove2me | solution 1 for MaxPressure.Throughput.maximum_pressure_pathwise_stable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T21:42:03.826342+00:00
-- url     : https://prove2.me/submissions/4da87314-1e13-4a94-bf22-ced0dbc1c47b

import Mathlib
import Definitions.Def_MaxPressure_Throughput_Dynamics

set_option autoImplicit false

open MeasureTheory Filter Topology

/-- Sublinear growth on `[0, ∞)`. -/
def c565SubLin (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ K : ℝ, ∀ s, 0 ≤ s → |g s| ≤ ε * s + K

lemma c565SubLin_add {f g : ℝ → ℝ} (hf : c565SubLin f) (hg : c565SubLin g) :
    c565SubLin (fun s => f s + g s) := by
  intro ε hε
  obtain ⟨K1, h1⟩ := hf (ε / 2) (by positivity)
  obtain ⟨K2, h2⟩ := hg (ε / 2) (by positivity)
  refine ⟨K1 + K2, fun s hs => ?_⟩
  have e1 := h1 s hs
  have e2 := h2 s hs
  calc |f s + g s| ≤ |f s| + |g s| := abs_add_le _ _
    _ ≤ ε * s + (K1 + K2) := by linarith

lemma c565SubLin_neg {f : ℝ → ℝ} (hf : c565SubLin f) : c565SubLin (fun s => - f s) := by
  intro ε hε
  obtain ⟨K, h⟩ := hf ε hε
  exact ⟨K, fun s hs => by simpa [abs_neg] using h s hs⟩

lemma c565SubLin_sub {f g : ℝ → ℝ} (hf : c565SubLin f) (hg : c565SubLin g) :
    c565SubLin (fun s => f s - g s) := by
  simpa [sub_eq_add_neg] using c565SubLin_add hf (c565SubLin_neg hg)

lemma c565SubLin_const_mul {f : ℝ → ℝ} (c : ℝ) (hf : c565SubLin f) :
    c565SubLin (fun s => c * f s) := by
  intro ε hε
  obtain ⟨K, h⟩ := hf (ε / (|c| + 1)) (by positivity)
  refine ⟨|c| * |K|, fun s hs => ?_⟩
  have e := h s hs
  have hc : 0 ≤ |c| := abs_nonneg c
  have h1 : |c| * (ε / (|c| + 1) * s) ≤ ε * s := by
    have : |c| * (ε / (|c| + 1)) ≤ ε := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have := mul_le_mul_of_nonneg_right this hs
    linarith [mul_assoc |c| (ε / (|c| + 1)) s]
  have h2 : |c| * K ≤ |c| * |K| := mul_le_mul_of_nonneg_left (le_abs_self K) hc
  rw [abs_mul]
  calc |c| * |f s| ≤ |c| * (ε / (|c| + 1) * s + K) := mul_le_mul_of_nonneg_left e hc
    _ = |c| * (ε / (|c| + 1) * s) + |c| * K := by ring
    _ ≤ ε * s + |c| * |K| := by linarith

lemma c565SubLin_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ S, c565SubLin (f i)) :
    c565SubLin (fun s => ∑ i ∈ S, f i s) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro ε hε
    exact ⟨0, fun s hs => by simp; positivity⟩
  | insert a S ha ih =>
    have h1 := hf a (Finset.mem_insert_self a S)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have := c565SubLin_add h1 h2
    simpa [Finset.sum_insert ha] using this

lemma c565SubLin_of_le {f g : ℝ → ℝ} (hg : c565SubLin g)
    (h : ∀ s, 0 ≤ s → |f s| ≤ |g s|) : c565SubLin f := by
  intro ε hε
  obtain ⟨K, hK⟩ := hg ε hε
  exact ⟨K, fun s hs => (h s hs).trans (hK s hs)⟩

lemma c565_lin_approx (f : ℕ → ℝ) (c : ℝ)
    (h : Tendsto (fun l : ℕ => f l / l) atTop (𝓝 c)) :
    ∀ ε > 0, ∃ K, ∀ l : ℕ, |f l - c * l| ≤ ε * l + K := by
  intro ε hε
  obtain ⟨L, hL⟩ := (Metric.tendsto_atTop.1 h) ε hε
  have hK : 0 ≤ ∑ l ∈ Finset.range (L + 1), |f l - c * l| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨∑ l ∈ Finset.range (L + 1), |f l - c * l|, fun l => ?_⟩
  by_cases hl : l ≤ L
  · have h1 : |f l - c * l| ≤ ∑ l ∈ Finset.range (L + 1), |f l - c * l| :=
      Finset.single_le_sum (f := fun l => |f l - c * l|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    have : 0 ≤ ε * (l : ℝ) := by positivity
    linarith
  · have hl' : L < l := not_le.mp hl
    have hl1 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
    have h2 := hL l hl'.le
    rw [Real.dist_eq] at h2
    have e : f l - c * l = (f l / l - c) * l := by field_simp
    rw [e, abs_mul, abs_of_pos hl1]
    nlinarith

open BellWilliams2001.ThresholdPolicy in
lemma c565_renewal (x : ℕ → ℝ) (m : ℝ) (hm : 0 < m)
    (h : Tendsto (fun n : ℕ => partialSum x n / n) atTop (𝓝 m)) :
    ∀ ε > 0, ∃ K, ∀ τ : ℝ, 0 ≤ τ →
      renewalCount (partialSum x) τ ≠ ⊤ ∧
      |((renewalCount (partialSum x) τ).toNat : ℝ) - τ / m| ≤ ε * τ + K := by
  intro ε hε
  set ε' : ℝ := min (m / 2) (ε * m ^ 2 / 4) with hε'
  have hε'pos : 0 < ε' := lt_min (by positivity) (by positivity)
  have hε'1 : ε' ≤ m / 2 := min_le_left _ _
  have hε'2 : ε' ≤ ε * m ^ 2 / 4 := min_le_right _ _
  obtain ⟨K', hK'⟩ := c565_lin_approx (partialSum x) m h ε' hε'pos
  have hS0 : partialSum x 0 = 0 := by simp [partialSum]
  have hK'0 : 0 ≤ K' := by
    have := hK' 0
    simp [hS0] at this
    linarith
  refine ⟨ε * K' / 2 + K' / m + 2, fun τ hτ => ?_⟩
  set U : ℝ := (τ + K') / (m - ε') with hU
  have hmε : 0 < m - ε' := by linarith
  -- every n with S n ≤ τ satisfies n ≤ U
  have hup : ∀ n : ℕ, partialSum x n ≤ τ → (n : ℝ) ≤ U := by
    intro n hn
    have := hK' n
    rw [hU, le_div_iff₀ hmε]
    have h1 := (abs_le.1 this).1
    nlinarith
  have hle : renewalCount (partialSum x) τ ≤ (⌊U⌋₊ : ℕ∞) := by
    unfold renewalCount
    refine iSup₂_le fun n hn => ?_
    exact_mod_cast Nat.le_floor (hup n hn)
  have hfin : renewalCount (partialSum x) τ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle
  refine ⟨hfin, ?_⟩
  set Nn : ℕ := (renewalCount (partialSum x) τ).toNat with hNn
  have hNn_eq : ((Nn : ℕ) : ℕ∞) = renewalCount (partialSum x) τ := ENat.natCast_toNat hfin
  have hge : ∀ n : ℕ, partialSum x n ≤ τ → n ≤ Nn := by
    intro n hn
    have : (n : ℕ∞) ≤ renewalCount (partialSum x) τ := by
      unfold renewalCount
      exact le_iSup₂ (f := fun (n : ℕ) (_ : partialSum x n ≤ τ) => (n : ℕ∞)) n hn
    rw [← hNn_eq] at this
    exact_mod_cast this
  -- upper bound
  have hNU : (Nn : ℝ) ≤ U := by
    have h1 : ((Nn : ℕ) : ℕ∞) ≤ (⌊U⌋₊ : ℕ∞) := by rw [hNn_eq]; exact hle
    have h2 : Nn ≤ ⌊U⌋₊ := by exact_mod_cast h1
    have hU0 : 0 ≤ U := by rw [hU]; exact div_nonneg (by linarith) hmε.le
    calc (Nn : ℝ) ≤ (⌊U⌋₊ : ℝ) := by exact_mod_cast h2
      _ ≤ U := Nat.floor_le hU0
  have hN1 : (m - ε') * Nn ≤ τ + K' := by
    have := hNU
    rw [hU, le_div_iff₀ hmε] at this
    linarith
  have hN0 : (0 : ℝ) ≤ Nn := Nat.cast_nonneg _
  have hmN : m * Nn ≤ 2 * (τ + K') := by nlinarith
  have hεN : ε' * Nn ≤ ε * m * (τ + K') / 2 := by
    have h1 : ε' * Nn ≤ ε * m ^ 2 / 4 * Nn := mul_le_mul_of_nonneg_right hε'2 hN0
    have h2 : ε * m ^ 2 / 4 * Nn = ε * m / 4 * (m * Nn) := by ring
    have h3 : ε * m / 4 * (m * Nn) ≤ ε * m / 4 * (2 * (τ + K')) :=
      mul_le_mul_of_nonneg_left hmN (by positivity)
    nlinarith
  have hupper : m * Nn - τ ≤ ε * m * (τ + K') / 2 + K' := by nlinarith
  -- lower bound
  have hlower : τ - m * Nn ≤ ε * m * (τ + K') / 2 + m + ε' + K' := by
    by_cases hτK : K' ≤ τ
    · set n0 : ℕ := ⌊(τ - K') / (m + ε')⌋₊ with hn0
      have hmε2 : 0 < m + ε' := by linarith
      have hq : 0 ≤ (τ - K') / (m + ε') := div_nonneg (by linarith) hmε2.le
      have hn0le : (m + ε') * n0 ≤ τ - K' := by
        have := Nat.floor_le hq
        rw [← hn0, le_div_iff₀ hmε2] at this
        linarith
      have hn0lt : τ - K' < (m + ε') * (n0 + 1) := by
        have := Nat.lt_floor_add_one ((τ - K') / (m + ε'))
        rw [← hn0, div_lt_iff₀ hmε2] at this
        linarith
      have hSn0 : partialSum x n0 ≤ τ := by
        have := (abs_le.1 (hK' n0)).2
        nlinarith
      have hn0N : (n0 : ℝ) ≤ Nn := by exact_mod_cast hge n0 hSn0
      have : ε' * n0 ≤ ε' * Nn := mul_le_mul_of_nonneg_left hn0N hε'pos.le
      nlinarith
    · have hτK' : τ < K' := lt_of_not_ge hτK
      have : 0 ≤ ε * m * (τ + K') / 2 := by
        have : 0 ≤ τ + K' := by linarith
        positivity
      nlinarith
  have key : |m * Nn - τ| ≤ m * (ε * τ + (ε * K' / 2 + K' / m + 2)) := by
    have e : m * (ε * τ + (ε * K' / 2 + K' / m + 2)) =
        ε * m * τ + ε * m * K' / 2 + K' + 2 * m := by
      field_simp
      ring
    rw [e, abs_le]
    have hτm : 0 ≤ ε * m * τ := by positivity
    have hε'm : ε' ≤ m := by linarith
    constructor <;> nlinarith
  have e2 : (Nn : ℝ) - τ / m = (m * Nn - τ) / m := by field_simp
  rw [e2, abs_div, abs_of_pos hm, div_le_iff₀ hm]
  linarith [key]

open MaxPressure.Throughput in
lemma c565_T_bounds {I J K : ℕ} {Ω : Type*} (N : Network I J K) (hN : N.Standing)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ) (ω : Ω)
    (heq : NetworkEquations N P Z T ω) :
    ∀ s u, 0 ≤ s → s ≤ u → ∀ j, 0 ≤ T ω u j - T ω s j ∧ T ω u j - T ω s j ≤ u - s := by
  obtain ⟨hA01, -, -, -, hAk, -⟩ := hN
  obtain ⟨-, -, -, -, h17, hmono, -⟩ := heq
  intro s u hs hsu j
  have hinc : ∀ j', 0 ≤ T ω u j' - T ω s j' := fun j' =>
    sub_nonneg.mpr (hmono (Set.mem_Ici.mpr hs) (Set.mem_Ici.mpr (hs.trans hsu)) hsu j')
  refine ⟨hinc j, ?_⟩
  obtain ⟨k, hk⟩ := hAk j
  have hnn : ∀ j' ∈ (Finset.univ : Finset (Fin J)),
      0 ≤ N.A k j' * (T ω u j' - T ω s j') := by
    intro j' _
    rcases hA01 k j' with h | h <;> simp [h, hinc j']
  have := Finset.single_le_sum hnn (Finset.mem_univ j)
  simp only [hk, one_mul] at this
  exact this.trans (h17 s u hs hsu k)

open MaxPressure.Throughput in
lemma c565_T_range {I J K : ℕ} {Ω : Type*} (N : Network I J K) (hN : N.Standing)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ) (ω : Ω)
    (heq : NetworkEquations N P Z T ω) :
    ∀ s, 0 ≤ s → ∀ j, 0 ≤ T ω s j ∧ T ω s j ≤ s := by
  intro s hs j
  have h := c565_T_bounds N hN P Z T ω heq 0 s le_rfl hs j
  have h0 : T ω 0 = 0 := heq.2.2.2.2.2.2
  simp only [h0, Pi.zero_apply, sub_zero] at h
  exact h

open MaxPressure.Throughput BellWilliams2001.ThresholdPolicy in
lemma c565_count_sublin {I J K : ℕ} {Ω : Type*} (N : Network I J K) (hN : N.Standing)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ) (ω : Ω)
    (hg : P.GoodSample N ω) (heq : NetworkEquations N P Z T ω) (j : Fin J) :
    c565SubLin (fun s => ((completions P j ω (T ω s j)).toNat : ℝ) - mu N j * T ω s j) := by
  have hm : 0 < N.m j := hN.2.2.2.2.2.2.2.2.1 j
  intro ε hε
  obtain ⟨K, hK⟩ := c565_renewal (fun l => P.eta j l ω) (N.m j) hm (hg.1 j) ε hε
  refine ⟨K, fun s hs => ?_⟩
  obtain ⟨hT0, hTs⟩ := c565_T_range N hN P Z T ω heq s hs j
  have h := (hK (T ω s j) hT0).2
  have e : mu N j * T ω s j = T ω s j / N.m j := by unfold mu; ring
  show |((completions P j ω (T ω s j)).toNat : ℝ) - mu N j * T ω s j| ≤ ε * s + K
  rw [e]
  unfold completions
  have : ε * T ω s j ≤ ε * s := mul_le_mul_of_nonneg_left hTs hε.le
  linarith

open MaxPressure.Throughput BellWilliams2001.ThresholdPolicy in
lemma c565_count_growth {I J K : ℕ} {Ω : Type*} (N : Network I J K) (hN : N.Standing)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ) (ω : Ω)
    (hg : P.GoodSample N ω) (heq : NetworkEquations N P Z T ω) (j : Fin J) :
    ∃ K1, ∀ s, 0 ≤ s → ((completions P j ω (T ω s j)).toNat : ℝ) ≤ (mu N j + 1) * s + K1 := by
  obtain ⟨K, hK⟩ := c565_count_sublin N hN P Z T ω hg heq j 1 one_pos
  refine ⟨K, fun s hs => ?_⟩
  have h := (abs_le.1 (hK s hs)).2
  obtain ⟨hT0, hTs⟩ := c565_T_range N hN P Z T ω heq s hs j
  have hmu : 0 ≤ mu N j := by unfold mu; exact (one_div_pos.2 (hN.2.2.2.2.2.2.2.2.1 j)).le
  have : mu N j * T ω s j ≤ mu N j * s := mul_le_mul_of_nonneg_left hTs hmu
  nlinarith

open MaxPressure.Throughput BellWilliams2001.ThresholdPolicy in
lemma c565_route_sublin {I J K : ℕ} {Ω : Type*} (N : Network I J K) (hN : N.Standing)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ) (ω : Ω)
    (hg : P.GoodSample N ω) (heq : NetworkEquations N P Z T ω)
    (j : Fin J) (i' i'' : Fin (I + 1)) :
    c565SubLin (fun s => (P.Phi j i' i''
        ((completions P j ω (T ω s j)).toNat * (if N.B j i' = 1 then 1 else 0)) ω : ℝ) -
      N.P j i' i'' * N.B j i' * (mu N j * T ω s j)) := by
  set C : ℝ → ℕ := fun s => (completions P j ω (T ω s j)).toNat with hC
  set l : ℝ → ℕ := fun s => C s * (if N.B j i' = 1 then 1 else 0) with hl
  have hlB : ∀ s, (l s : ℝ) = N.B j i' * (C s : ℝ) := by
    intro s
    rcases hN.2.1 j i' with h | h
    · simp [hl, h]
    · simp [hl, h]
  have hlC : ∀ s, (l s : ℝ) ≤ (C s : ℝ) := by
    intro s
    rcases hN.2.1 j i' with h | h
    · simp [hl, h]
    · simp [hl, h]
  -- part A: Phi(l) - P * l
  have hA : c565SubLin (fun s => (P.Phi j i' i'' (l s) ω : ℝ) - N.P j i' i'' * (l s : ℝ)) := by
    obtain ⟨K1, hK1⟩ := c565_count_growth N hN P Z T ω hg heq j
    have hmu : 0 ≤ mu N j := by unfold mu; exact (one_div_pos.2 (hN.2.2.2.2.2.2.2.2.1 j)).le
    intro ε hε
    obtain ⟨K', hK'⟩ := c565_lin_approx (fun l => (P.Phi j i' i'' l ω : ℝ)) (N.P j i' i'')
      (hg.2 j i' i'') (ε / (mu N j + 1)) (by positivity)
    refine ⟨ε / (mu N j + 1) * |K1| + K', fun s hs => ?_⟩
    have h1 := hK' (l s)
    have h2 : (l s : ℝ) ≤ (mu N j + 1) * s + |K1| :=
      (hlC s).trans ((hK1 s hs).trans (by linarith [le_abs_self K1]))
    have h3 : ε / (mu N j + 1) * (l s : ℝ) ≤ ε / (mu N j + 1) * ((mu N j + 1) * s + |K1|) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : ε / (mu N j + 1) * ((mu N j + 1) * s + |K1|) =
        ε * s + ε / (mu N j + 1) * |K1| := by
      field_simp
    linarith
  have hB := c565SubLin_const_mul (N.P j i' i'' * N.B j i')
    (c565_count_sublin N hN P Z T ω hg heq j)
  have hsum := c565SubLin_add hA hB
  refine c565SubLin_of_le hsum (fun s _ => le_of_eq ?_)
  congr 1
  simp only [hl, hC] at hlB ⊢
  rw [hlB s]
  ring

open MaxPressure.Throughput BellWilliams2001.ThresholdPolicy in
lemma c565_decomp {I J K : ℕ} {Ω : Type*} (N : Network I J K) (hN : N.Standing)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ) (ω : Ω)
    (hg : P.GoodSample N ω) (heq : NetworkEquations N P Z T ω) (i : Fin I) :
    c565SubLin (fun s => Z ω s i - Z ω 0 i + (Matrix.mulVec (R N) (T ω s)) i) := by
  have h1 := c565SubLin_sum Finset.univ _ (fun i' _ => c565SubLin_sum Finset.univ _
    (fun j _ => c565_route_sublin N hN P Z T ω hg heq j i' i.succ))
  have h2 := c565SubLin_sum Finset.univ _ (fun j _ =>
    c565SubLin_const_mul (N.B j i.succ) (c565_count_sublin N hN P Z T ω hg heq j))
  refine c565SubLin_of_le (c565SubLin_sub h1 h2) (fun s hs => le_of_eq ?_)
  congr 1
  have hR : (Matrix.mulVec (R N) (T ω s)) i = ∑ j, N.B j i.succ * (mu N j * T ω s j) -
      ∑ i' : Fin (I + 1), ∑ j, N.P j i' i.succ * N.B j i' * (mu N j * T ω s j) := by
    simp only [Matrix.mulVec, dotProduct, R]
    rw [Finset.sum_comm (f := fun (i' : Fin (I + 1)) (j : Fin J) =>
      N.P j i' i.succ * N.B j i' * (mu N j * T ω s j)), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun x _ => by ring
  rw [heq.2.1 s hs i, hR]
  simp only [Finset.sum_sub_distrib, mul_sub]
  rw [show (∑ x, N.B x i.succ * ((completions P x ω (T ω s x)).toNat : ℝ)) =
      ∑ x, ((completions P x ω (T ω s x)).toNat : ℝ) * N.B x i.succ from
      Finset.sum_congr rfl fun x _ => mul_comm _ _]
  ring

open MaxPressure.Throughput Matrix in
/-- The pressure as a linear map in the allocation. -/
noncomputable def c565PressureLin {I J K : ℕ} (N : Network I J K) (z : Fin I → ℝ) :
    (Fin J → ℝ) →ₗ[ℝ] ℝ where
  toFun a := pressure N a z
  map_add' a b := by simp [pressure, Matrix.mulVec_add, dotProduct_add]
  map_smul' c a := by simp [pressure, Matrix.mulVec_smul, dotProduct_smul]

open MaxPressure.Throughput Matrix in
lemma c565_allocSet_isCompact {I J K : ℕ} (N : Network I J K) (hN : N.Standing) :
    IsCompact (allocSet N) := by
  obtain ⟨hA01, -, -, -, hAk, -⟩ := hN
  have hcl : IsClosed (allocSet N) := by
    have h1 : IsClosed {a : Fin J → ℝ | ∀ j, 0 ≤ a j} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
    have h2 : IsClosed {a : Fin J → ℝ | ∀ k, ∑ j, N.A k j * a j ≤ 1} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun k => isClosed_le
        (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j))
        continuous_const
    have h3 : IsClosed {a : Fin J → ℝ | ∀ k, N.inputProc k → ∑ j, N.A k j * a j = 1} := by
      simp only [Set.ofPred_forall]
      refine isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_eq
        (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j))
        continuous_const
    have : allocSet N = {a : Fin J → ℝ | ∀ j, 0 ≤ a j} ∩
        {a : Fin J → ℝ | ∀ k, ∑ j, N.A k j * a j ≤ 1} ∩
        {a : Fin J → ℝ | ∀ k, N.inputProc k → ∑ j, N.A k j * a j = 1} := by
      ext a; simp [allocSet, and_assoc]
    rw [this]; exact (h1.inter h2).inter h3
  refine (isCompact_Icc (a := (0 : Fin J → ℝ)) (b := 1)).of_isClosed_subset hcl ?_
  intro a ha
  obtain ⟨hpos, hle, -⟩ := ha
  refine ⟨fun j => hpos j, fun j => ?_⟩
  obtain ⟨k, hk⟩ := hAk j
  have hnn : ∀ j' ∈ (Finset.univ : Finset (Fin J)), 0 ≤ N.A k j' * a j' := by
    intro j' _
    rcases hA01 k j' with h | h <;> simp [h, hpos j']
  have := Finset.single_le_sum hnn (Finset.mem_univ j)
  simp only [hk, one_mul] at this
  simpa using this.trans (hle k)

open MaxPressure.Throughput Matrix in
lemma c565_max_extreme {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hne : (allocSet N).Nonempty) (z : Fin I → ℝ) :
    ∃ e ∈ extremeAllocs N, ∀ a ∈ allocSet N, pressure N a z ≤ pressure N e z := by
  have hc := c565_allocSet_isCompact N hN
  let l : StrongDual ℝ (Fin J → ℝ) := LinearMap.toContinuousLinearMap (c565PressureLin N z)
  have hl : ∀ a, l a = pressure N a z := fun a => rfl
  have hexp : IsExposed ℝ (allocSet N) (l.toExposed (allocSet N)) :=
    ContinuousLinearMap.toExposed.isExposed
  have hSc : IsCompact (l.toExposed (allocSet N)) := hexp.isCompact hc
  have hSne : (l.toExposed (allocSet N)).Nonempty := by
    obtain ⟨x, hx, hmax⟩ := hc.exists_isMaxOn hne l.continuous.continuousOn
    exact ⟨x, hx, fun y hy => hmax hy⟩
  obtain ⟨e, he⟩ := hSc.extremePoints_nonempty hSne
  refine ⟨e, hexp.isExtreme.extremePoints_subset_extremePoints he, fun a ha => ?_⟩
  have := he.1.2 a ha
  simpa [hl] using this

open MaxPressure.Throughput Matrix in
lemma c565_max_nonneg {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hlp : ∃ x rho, rho ≤ (1 : ℝ) ∧ LPFeasible N x rho)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N)
    (z : Fin I → ℝ) : ∃ a ∈ E, 0 ≤ pressure N a z := by
  obtain ⟨x, rho, hrho, hR, hnon, hin, hx0⟩ := hlp
  have hx : x ∈ allocSet N := by
    refine ⟨hx0, fun k => ?_, hin⟩
    by_cases hk : N.inputProc k
    · rw [hin k hk]
    · exact (hnon k hk).trans hrho
  obtain ⟨e, he, hmax⟩ := c565_max_extreme N hN ⟨x, hx⟩ z
  refine ⟨e, by rw [← Finset.mem_coe, hE]; exact he, ?_⟩
  have h1 := hmax x hx
  have h0 : pressure N x z = 0 := by simp [pressure, hR]
  linarith

open MaxPressure.Throughput Matrix in
/-- A crude bound on the pressure coefficients over `E`. -/
noncomputable def c565D {I J K : ℕ} (N : Network I J K) (E : Finset (Fin J → ℝ)) : ℝ :=
  ∑ a ∈ E, ∑ i, |(R N *ᵥ a) i|

open MaxPressure.Throughput Matrix in
lemma c565D_nonneg {I J K : ℕ} (N : Network I J K) (E : Finset (Fin J → ℝ)) :
    0 ≤ c565D N E :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

open MaxPressure.Throughput Matrix in
lemma c565_p_lip {I J K : ℕ} (N : Network I J K) (E : Finset (Fin J → ℝ))
    (a : Fin J → ℝ) (ha : a ∈ E) (v w : Fin I → ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ i, |v i - w i| ≤ δ) :
    |pressure N a v - pressure N a w| ≤ δ * c565D N E := by
  have e : pressure N a v - pressure N a w = ∑ i, (v i - w i) * (R N *ᵥ a) i := by
    simp only [pressure, dotProduct, ← Finset.sum_sub_distrib, sub_mul]
  rw [e]
  calc |∑ i, (v i - w i) * (R N *ᵥ a) i| ≤ ∑ i, |(v i - w i) * (R N *ᵥ a) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, δ * |(R N *ᵥ a) i| := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hδ i) (abs_nonneg _)
    _ = δ * ∑ i, |(R N *ᵥ a) i| := by rw [Finset.mul_sum]
    _ ≤ δ * c565D N E := mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (f := fun a => ∑ i, |(R N *ᵥ a) i|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) ha) hδ0

open MaxPressure.Throughput Matrix in
lemma c565_trunc {I J K : ℕ} (N : Network I J K) (hEAA : EAA N) (E : Finset (Fin J → ℝ))
    (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ b ∈ E, (∀ i ∈ constituentBuffers N b, L ≤ z i) ∧
      ∀ a ∈ E, pressure N a z ≤ pressure N b z + 2 * L * c565D N E := by
  classical
  set w : Fin I → ℝ := fun i => if L ≤ z i then z i else 0 with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => by
    simp only [hw]; split_ifs
    · exact hz i
    · exact le_rfl
  have hdiff : ∀ i, |z i - w i| ≤ L := fun i => by
    simp only [hw]; split_ifs with h
    · simp; exact hL
    · rw [sub_zero, abs_of_nonneg (hz i)]; exact (not_le.mp h).le
  obtain ⟨b, hb, hbmax, hbpos⟩ := hEAA w hw0
  have hbE : b ∈ E := by rw [← Finset.mem_coe, hE]; exact hb
  refine ⟨b, hbE, fun i hi => ?_, fun a ha => ?_⟩
  · have := hbpos i hi
    simp only [hw] at this
    split_ifs at this with h
    · exact h
    · exact absurd this (lt_irrefl 0)
  · have haE : a ∈ extremeAllocs N := by rw [← hE]; exact ha
    have h1 := hbmax a haE
    have h2 := abs_le.1 (c565_p_lip N E a ha z w L hL hdiff)
    have h3 := abs_le.1 (c565_p_lip N E b hbE z w L hL hdiff)
    linarith

open MaxPressure.Throughput Matrix in
lemma c565_energy_step {I J K : ℕ} (N : Network I J K) (E : Finset (Fin J → ℝ))
    (v w : Fin I → ℝ) (dT : (Fin J → ℝ) → ℝ) (h η : ℝ)
    (hdT0 : ∀ a ∈ E, 0 ≤ dT a) (hsum : ∑ a ∈ E, dT a = h)
    (hnear : ∀ a ∈ E, dT a ≠ 0 → ∀ a' ∈ E, pressure N a' v ≤ pressure N a v + η)
    (hmax : ∃ a0 ∈ E, 0 ≤ pressure N a0 v) :
    ∑ i, w i ^ 2 - ∑ i, v i ^ 2 ≤ 2 * η * h +
      2 * ∑ i, v i * (w i - v i + (R N *ᵥ (∑ a ∈ E, dT a • a)) i) +
      ∑ i, (w i - v i) ^ 2 := by
  obtain ⟨a0, ha0, hp0⟩ := hmax
  have hX : ∑ i, v i * (R N *ᵥ (∑ a ∈ E, dT a • a)) i = ∑ a ∈ E, dT a * pressure N a v := by
    have : ∑ i, v i * (R N *ᵥ (∑ a ∈ E, dT a • a)) i =
        dotProduct v (R N *ᵥ (∑ a ∈ E, dT a • a)) := rfl
    rw [this, Matrix.mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    rfl
  have hneg : -(∑ a ∈ E, dT a * pressure N a v) ≤ η * h := by
    rw [← hsum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun a ha => ?_
    by_cases hd : dT a = 0
    · simp [hd]
    · have h1 := hnear a ha hd a0 ha0
      have h2 := hdT0 a ha
      nlinarith
  have e1 : ∑ i, v i * (w i - v i + (R N *ᵥ (∑ a ∈ E, dT a • a)) i) =
      ∑ i, v i * (w i - v i) + ∑ i, v i * (R N *ᵥ (∑ a ∈ E, dT a • a)) i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, w i ^ 2 - ∑ i, v i ^ 2 = 2 * ∑ i, v i * (w i - v i) + ∑ i, (w i - v i) ^ 2 := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e2, e1, hX]
  linarith

open MaxPressure.Throughput Matrix in
/-- A crude bound on the entries of `R`. -/
noncomputable def c565Cr {I J K : ℕ} (N : Network I J K) : ℝ := ∑ i, ∑ j, |R N i j|

open MaxPressure.Throughput Matrix in
lemma c565Cr_nonneg {I J K : ℕ} (N : Network I J K) : 0 ≤ c565Cr N :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

open MaxPressure.Throughput Matrix in
lemma c565_RT_lip {I J K : ℕ} {Ω : Type*} (N : Network I J K) (hN : N.Standing)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ) (ω : Ω)
    (heq : NetworkEquations N P Z T ω) :
    ∀ s u, 0 ≤ s → s ≤ u → ∀ i,
      |(R N *ᵥ T ω u) i - (R N *ᵥ T ω s) i| ≤ c565Cr N * (u - s) := by
  intro s u hs hsu i
  have hb := c565_T_bounds N hN P Z T ω heq s u hs hsu
  have e : (R N *ᵥ T ω u) i - (R N *ᵥ T ω s) i = ∑ j, R N i j * (T ω u j - T ω s j) := by
    simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, mul_sub]
  rw [e]
  calc |∑ j, R N i j * (T ω u j - T ω s j)| ≤ ∑ j, |R N i j * (T ω u j - T ω s j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |R N i j| * (u - s) := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_nonneg (hb j).1]
        exact mul_le_mul_of_nonneg_left (hb j).2 (abs_nonneg _)
    _ = (∑ j, |R N i j|) * (u - s) := by rw [Finset.sum_mul]
    _ ≤ c565Cr N * (u - s) := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, |R N i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
        (by linarith)

open MaxPressure.Throughput Matrix in
lemma c565_e_unif {I J K : ℕ} {Ω : Type*} (N : Network I J K) (hN : N.Standing)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ) (T : Ω → ℝ → Fin J → ℝ) (ω : Ω)
    (hg : P.GoodSample N ω) (heq : NetworkEquations N P Z T ω) :
    ∀ ε > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ s, 0 ≤ s → ∀ i,
      |Z ω s i - Z ω 0 i + (R N *ᵥ T ω s) i| ≤ ε * s + K := by
  intro ε hε
  choose Kf hK using fun i => c565_decomp N hN P Z T ω hg heq i ε hε
  refine ⟨∑ i, |Kf i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun s hs i => ?_⟩
  have h1 := hK i s hs
  have h2 : Kf i ≤ ∑ i, |Kf i| := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |Kf i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  linarith

open MaxPressure.Throughput Matrix in
lemma c565_step {I J K : ℕ} {Ω : Type*} (N : Network I J K) (hN : N.Standing) (hEAA : EAA N)
    (hlp : ∃ x rho, rho ≤ (1 : ℝ) ∧ LPFeasible N x rho)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ) (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω)
    (heq : NetworkEquations N P Z (activityTime E Ta) ω) (hmp : MPProcess N E Z Ta ω)
    (s u L δ β Bz : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) (hL : 0 ≤ L) (hδ0 : 0 ≤ δ)
    (hδ : ∀ τ ∈ Set.Icc s u, ∀ i, |Z ω τ i - Z ω s i| ≤ δ) (hδL : δ + J ≤ L)
    (hd : ∀ i, |Z ω u i - Z ω s i +
      (R N *ᵥ (activityTime E Ta ω u - activityTime E Ta ω s)) i| ≤ β)
    (hBz : ∀ i, |Z ω s i| ≤ Bz) :
    ∑ i, Z ω u i ^ 2 - ∑ i, Z ω s i ^ 2 ≤
      8 * L * c565D N E * (u - s) + 2 * I * Bz * β + I * δ ^ 2 := by
  classical
  have hD0 : 0 ≤ c565D N E := c565D_nonneg N E
  set dT : (Fin J → ℝ) → ℝ := fun a => Ta ω a u - Ta ω a s with hdT
  have hdT0 : ∀ a ∈ E, 0 ≤ dT a := fun a ha => sub_nonneg.2
    ((hmp.1 a ha).1 (Set.mem_Ici.2 hs) (Set.mem_Ici.2 (hs.trans hsu)) hsu)
  have hsum : ∑ a ∈ E, dT a = u - s := by
    simp only [hdT, Finset.sum_sub_distrib, hmp.2.1 u (hs.trans hsu), hmp.2.1 s hs]
  have hTdiff : activityTime E Ta ω u - activityTime E Ta ω s = ∑ a ∈ E, dT a • a := by
    funext j
    simp only [activityTime, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hdT,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hvz : ∀ i, 0 ≤ Z ω s i := fun i => heq.2.2.1 s hs i
  have hnear : ∀ a ∈ E, dT a ≠ 0 → ∀ a' ∈ E,
      pressure N a' (Z ω s) ≤ pressure N a (Z ω s) + 4 * L * c565D N E := by
    intro a ha hne a' ha'
    by_contra hcon
    have hcon' := not_le.mp hcon
    obtain ⟨b, hbE, hbc, hbmax⟩ := c565_trunc N hEAA E hE (Z ω s) hvz L hL
    have hb1 := hbmax a' ha'
    have hcond : ∀ τ ∈ Set.Icc s u, ∃ a'' ∈ E,
        (∀ i ∈ constituentBuffers N a'', (J : ℝ) ≤ Z ω τ i) ∧
        pressure N a (Z ω τ) < pressure N a'' (Z ω τ) := by
      intro τ hτ
      refine ⟨b, hbE, fun i hi => ?_, ?_⟩
      · have h1 := hbc i hi
        have h2 := abs_le.1 (hδ τ hτ i)
        linarith
      · have hl1 := abs_le.1 (c565_p_lip N E a ha (Z ω τ) (Z ω s) δ hδ0 (fun i => hδ τ hτ i))
        have hl2 := abs_le.1 (c565_p_lip N E b hbE (Z ω τ) (Z ω s) δ hδ0 (fun i => hδ τ hτ i))
        have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
        have : δ * c565D N E ≤ L * c565D N E := mul_le_mul_of_nonneg_right (by linarith) hD0
        linarith
    have := hmp.2.2 a ha s u hs hsu hcond
    exact hne (by simp [hdT, this])
  have hmax := c565_max_nonneg N hN hlp E hE (Z ω s)
  have hen := c565_energy_step N E (Z ω s) (Z ω u) dT (u - s) (4 * L * c565D N E)
    hdT0 hsum hnear hmax
  rw [← hTdiff] at hen
  have hcross : ∑ i, Z ω s i * (Z ω u i - Z ω s i +
      (R N *ᵥ (activityTime E Ta ω u - activityTime E Ta ω s)) i) ≤ I * (Bz * β) := by
    calc _ ≤ ∑ _i : Fin I, Bz * β := Finset.sum_le_sum fun i _ => by
          refine (le_abs_self _).trans ?_
          rw [abs_mul]
          exact mul_le_mul (hBz i) (hd i) (abs_nonneg _) ((abs_nonneg _).trans (hBz i))
      _ = I * (Bz * β) := by simp
  have hsq : ∑ i, (Z ω u i - Z ω s i) ^ 2 ≤ I * δ ^ 2 := by
    calc _ ≤ ∑ _i : Fin I, δ ^ 2 := Finset.sum_le_sum fun i _ => by
          have h := abs_le.1 (hδ u ⟨hsu, le_rfl⟩ i)
          exact sq_le_sq' h.1 h.2
      _ = I * δ ^ 2 := by simp
  nlinarith

open MaxPressure.Throughput Matrix in
lemma c565_grid_step {I J K : ℕ} {Ω : Type*} (N : Network I J K) (hN : N.Standing)
    (hEAA : EAA N) (hlp : ∃ x rho, rho ≤ (1 : ℝ) ∧ LPFeasible N x rho)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ) (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω)
    (heq : NetworkEquations N P Z (activityTime E Ta) ω) (hmp : MPProcess N E Z Ta ω)
    (Z0 θ ε Ke t n s u : ℝ)
    (hKe : ∀ s, 0 ≤ s → ∀ i,
      |Z ω s i - Z ω 0 i + (R N *ᵥ activityTime E Ta ω s) i| ≤ ε * s + Ke)
    (hz0all : ∀ i, |Z ω 0 i| ≤ Z0) (hZ00 : 0 ≤ Z0)
    (hεpos : 0 < ε) (hKe0 : 0 ≤ Ke) (htK : Ke ≤ ε * t) (htZ : Z0 ≤ ε * t)
    (htJ : 3 * (2 * Ke + J) ≤ θ * t) (hε12 : 12 * ε ≤ θ) (hθ1 : θ ≤ 1) (hθ0 : 0 < θ)
    (hnθ1 : 3 * c565Cr N ≤ n * θ) (hnpos : 0 < n) (ht0 : 0 < t)
    (hs0 : 0 ≤ s) (hus : u - s = t / n) (hut : u ≤ t) :
    ∑ i, Z ω u i ^ 2 - ∑ i, Z ω s i ^ 2 ≤
      8 * θ * c565D N E * t ^ 2 / n +
        (8 * I * (c565Cr N + 1) * ε + I * θ ^ 2) * t ^ 2 := by
  have hCr0 : 0 ≤ c565Cr N := c565Cr_nonneg N
  have hI0 : (0 : ℝ) ≤ I := Nat.cast_nonneg I
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hεt : 0 ≤ ε * t := mul_nonneg hεpos.le ht0.le
  have htn : 0 ≤ t / n := div_nonneg ht0.le hnpos.le
  have hCrt : 0 ≤ c565Cr N * (t / n) := mul_nonneg hCr0 htn
  have hεt12 : ε * t * 12 ≤ θ * t := by
    have := mul_le_mul_of_nonneg_right hε12 ht0.le
    linarith
  have hsu : s ≤ u := by linarith
  have hst : s ≤ t := hsu.trans hut
  set Cr := c565Cr N with hCrdef
  set D := c565D N E with hDdef
  have hδ : ∀ τ ∈ Set.Icc s u, ∀ i,
      |Z ω τ i - Z ω s i| ≤ Cr * (t / n) + 2 * (ε * t + Ke) := by
    intro τ hτ i
    have hτ0 : 0 ≤ τ := hs0.trans hτ.1
    have hA := abs_le.1 (hKe τ hτ0 i)
    have hB' := abs_le.1 (hKe s hs0 i)
    have hC := abs_le.1 (c565_RT_lip N hN P Z (activityTime E Ta) ω heq s τ hs0 hτ.1 i)
    have h1 : ε * τ ≤ ε * t := mul_le_mul_of_nonneg_left (hτ.2.trans hut) hεpos.le
    have h2 : ε * s ≤ ε * t := mul_le_mul_of_nonneg_left hst hεpos.le
    have h3 : Cr * (τ - s) ≤ Cr * (t / n) :=
      mul_le_mul_of_nonneg_left (by linarith [hτ.2]) hCr0
    rw [abs_le]; constructor <;> linarith
  have hδ0 : 0 ≤ Cr * (t / n) + 2 * (ε * t + Ke) := by linarith
  have hCrn : Cr * (t / n) * 3 ≤ θ * t := by
    have e : Cr * (t / n) * 3 = 3 * Cr * t / n := by ring
    rw [e, div_le_iff₀ hnpos]
    have := mul_le_mul_of_nonneg_right hnθ1 ht0.le
    linarith
  have hδL : Cr * (t / n) + 2 * (ε * t + Ke) + J ≤ θ * t := by linarith
  have hd : ∀ i, |Z ω u i - Z ω s i +
      (R N *ᵥ (activityTime E Ta ω u - activityTime E Ta ω s)) i| ≤ 2 * (ε * t + Ke) := by
    intro i
    have hA := abs_le.1 (hKe u (hs0.trans hsu) i)
    have hB' := abs_le.1 (hKe s hs0 i)
    have h1 : ε * u ≤ ε * t := mul_le_mul_of_nonneg_left hut hεpos.le
    have h2 : ε * s ≤ ε * t := mul_le_mul_of_nonneg_left hst hεpos.le
    rw [Matrix.mulVec_sub, Pi.sub_apply, abs_le]; constructor <;> linarith
  have hBz : ∀ i, |Z ω s i| ≤ Z0 + Cr * t + ε * t + Ke := by
    intro i
    have hA := abs_le.1 (hKe s hs0 i)
    have hC := abs_le.1 (c565_RT_lip N hN P Z (activityTime E Ta) ω heq 0 s le_rfl hs0 i)
    have hT0 : activityTime E Ta ω 0 = 0 := heq.2.2.2.2.2.2
    rw [hT0, Matrix.mulVec_zero, Pi.zero_apply, sub_zero, sub_zero] at hC
    have hz0' := abs_le.1 (hz0all i)
    have h2 : ε * s ≤ ε * t := mul_le_mul_of_nonneg_left hst hεpos.le
    have h3 : Cr * s ≤ Cr * t := mul_le_mul_of_nonneg_left hst hCr0
    rw [abs_le]; constructor <;> linarith
  have hstp := c565_step N hN hEAA hlp E hE P Z Ta ω heq hmp s u (θ * t) _ _ _ hs0 hsu
    (mul_nonneg hθ0.le ht0.le) hδ0 hδ hδL hd hBz
  have hεt' : ε * t ≤ (1 / 12) * t := mul_le_mul_of_nonneg_right (by linarith) ht0.le
  have hBzle : Z0 + Cr * t + ε * t + Ke ≤ (Cr + 1) * t := by linarith
  have hBz0 : 0 ≤ Z0 + Cr * t + ε * t + Ke := by
    have : 0 ≤ Cr * t := mul_nonneg hCr0 ht0.le
    linarith
  have hβle : 2 * (ε * t + Ke) ≤ 4 * ε * t := by linarith
  have hβ0 : 0 ≤ 2 * (ε * t + Ke) := by linarith
  have hδle : Cr * (t / n) + 2 * (ε * t + Ke) ≤ θ * t := by linarith
  have hp1 : (Z0 + Cr * t + ε * t + Ke) * (2 * (ε * t + Ke)) ≤ ((Cr + 1) * t) * (4 * ε * t) :=
    mul_le_mul hBzle hβle hβ0 (mul_nonneg (by linarith) ht0.le)
  have hp2 : (Cr * (t / n) + 2 * (ε * t + Ke)) ^ 2 ≤ (θ * t) ^ 2 :=
    pow_le_pow_left₀ hδ0 hδle 2
  have hp3 : 8 * (θ * t) * D * (u - s) = 8 * θ * D * t ^ 2 / n := by rw [hus]; ring
  have hp1' := mul_le_mul_of_nonneg_left hp1 (by linarith : (0 : ℝ) ≤ 2 * I)
  have hp2' := mul_le_mul_of_nonneg_left hp2 hI0
  linarith

set_option maxHeartbeats 800000 in
open MaxPressure.Throughput Matrix in
lemma c565_energy_bound {I J K : ℕ} {Ω : Type*} (N : Network I J K) (hN : N.Standing)
    (hEAA : EAA N) (hlp : ∃ x rho, rho ≤ (1 : ℝ) ∧ LPFeasible N x rho)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ) (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω)
    (hg : P.GoodSample N ω)
    (heq : NetworkEquations N P Z (activityTime E Ta) ω) (hmp : MPProcess N E Z Ta ω)
    (γ : ℝ) (hγ : 0 < γ) :
    ∃ t0, ∀ t, t0 ≤ t → ∑ i, Z ω t i ^ 2 ≤ γ * t ^ 2 := by
  set D := c565D N E with hDdef
  set Cr := c565Cr N with hCrdef
  have hD0 : 0 ≤ D := c565D_nonneg N E
  have hCr0 : 0 ≤ Cr := c565Cr_nonneg N
  set Z0 : ℝ := ∑ i, |Z ω 0 i| with hZ0
  have hZ00 : 0 ≤ Z0 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hI0 : (0 : ℝ) ≤ I := Nat.cast_nonneg I
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hIC : 0 ≤ (I : ℝ) * (3 * Cr + 2) := mul_nonneg hI0 (by linarith)
  set c : ℝ := 2 + 8 * D + I * (3 * Cr + 2) with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  set θ : ℝ := min 1 (γ / c) with hθ
  have hθ0 : 0 < θ := lt_min one_pos (div_pos hγ hc0)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθγ : θ * c ≤ γ := by
    have := min_le_right 1 (γ / c)
    rw [le_div_iff₀ hc0] at this
    exact this
  set n : ℕ := ⌈3 * Cr / θ⌉₊ + 1 with hn
  have hceil0 : (0 : ℝ) ≤ (⌈3 * Cr / θ⌉₊ : ℝ) := Nat.cast_nonneg _
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; push_cast; linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hnθ1 : 3 * Cr ≤ n * θ := by
    have h1 : 3 * Cr / θ ≤ ⌈3 * Cr / θ⌉₊ := Nat.le_ceil _
    have h2 : (⌈3 * Cr / θ⌉₊ : ℝ) ≤ n := by rw [hn]; push_cast; linarith
    have h3 : 3 * Cr / θ ≤ n := h1.trans h2
    rwa [div_le_iff₀ hθ0] at h3
  have hnθ2 : n * θ ≤ 3 * Cr + 2 := by
    have h1 : (⌈3 * Cr / θ⌉₊ : ℝ) < 3 * Cr / θ + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (by linarith) hθ0.le)
    have h2 : (n : ℝ) < 3 * Cr / θ + 2 := by rw [hn]; push_cast; linarith
    have h3 : (n : ℝ) * θ < (3 * Cr / θ + 2) * θ := mul_lt_mul_of_pos_right h2 hθ0
    have h4 : (3 * Cr / θ + 2) * θ = 3 * Cr + 2 * θ := by field_simp
    linarith
  have hX0 : 0 ≤ 8 * (n : ℝ) * I * (Cr + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hnpos.le) hI0) (by linarith)
  set M : ℝ := 8 * n * I * (Cr + 1) + 12 with hM
  have hM0 : 0 < M := by rw [hM]; linarith
  set ε : ℝ := θ / M with hε
  have hεpos : 0 < ε := div_pos hθ0 hM0
  have hεM : ε * M = θ := by rw [hε]; field_simp
  have hεM' : ε * M = 8 * n * I * (Cr + 1) * ε + 12 * ε := by rw [hM]; ring
  have hX1 : 0 ≤ 8 * (n : ℝ) * I * (Cr + 1) * ε := mul_nonneg hX0 hεpos.le
  have hε12 : 12 * ε ≤ θ := by linarith
  have hεn : 8 * n * I * (Cr + 1) * ε ≤ θ := by linarith
  obtain ⟨Ke, hKe0, hKe⟩ := c565_e_unif N hN P Z (activityTime E Ta) ω hg heq ε hεpos
  refine ⟨max 1 (max (Ke / ε) (max (Z0 / ε) (3 * (2 * Ke + J) / θ))), fun t ht => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have ht0 : 0 < t := by linarith
  have htK : Ke ≤ ε * t := by
    have : Ke / ε ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
    rw [div_le_iff₀ hεpos] at this; linarith
  have htZ : Z0 ≤ ε * t := by
    have : Z0 / ε ≤ t := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) ht
    rw [div_le_iff₀ hεpos] at this; linarith
  have htJ : 3 * (2 * Ke + J) ≤ θ * t := by
    have : 3 * (2 * Ke + J) / θ ≤ t := le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_right _ _)) (le_max_right _ _)) ht
    rw [div_le_iff₀ hθ0] at this; linarith
  have hεt : 0 ≤ ε * t := mul_nonneg hεpos.le ht0.le
  have htn : 0 ≤ t / n := div_nonneg ht0.le hnpos.le
  have hCrt : 0 ≤ Cr * (t / n) := mul_nonneg hCr0 htn
  have hz0all : ∀ i, |Z ω 0 i| ≤ Z0 := fun i => Finset.single_le_sum (f := fun i => |Z ω 0 i|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  set B : ℝ := 8 * θ * D * t ^ 2 / n + (8 * I * (Cr + 1) * ε + I * θ ^ 2) * t ^ 2 with hB
  set g : ℕ → ℝ := fun k => ∑ i, Z ω ((k : ℝ) * t / n) i ^ 2 with hg'
  have hstep : ∀ k ∈ Finset.range n, g (k + 1) - g k ≤ B := by
    intro k hk
    have hkn : (k : ℝ) + 1 ≤ n := by
      have := Finset.mem_range.1 hk
      exact_mod_cast this
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hs0 : (0 : ℝ) ≤ (k : ℝ) * t / n := div_nonneg (mul_nonneg hk0 ht0.le) hnpos.le
    have hus : ((k : ℝ) + 1) * t / n - (k : ℝ) * t / n = t / n := by ring
    have hut : ((k : ℝ) + 1) * t / n ≤ t := by
      rw [div_le_iff₀ hnpos]
      have := mul_le_mul_of_nonneg_right hkn ht0.le
      linarith
    have hgk1 : g (k + 1) = ∑ i, Z ω (((k : ℝ) + 1) * t / n) i ^ 2 := by
      simp only [hg', Nat.cast_add, Nat.cast_one]
    have hgk : g k = ∑ i, Z ω ((k : ℝ) * t / n) i ^ 2 := rfl
    rw [hgk1, hgk, hB]
    exact c565_grid_step N hN hEAA hlp E hE P Z Ta ω heq hmp Z0 θ ε Ke t n
      _ _ hKe hz0all hZ00 hεpos hKe0 htK htZ htJ hε12 hθ1 hθ0 hnθ1 hnpos ht0 hs0 hus hut
  have htel := Finset.sum_range_sub g n
  have hsumle : ∑ k ∈ Finset.range n, (g (k + 1) - g k) ≤ n * B := by
    calc _ ≤ ∑ _k ∈ Finset.range n, B := Finset.sum_le_sum hstep
      _ = n * B := by simp
  have hgn : g n = ∑ i, Z ω t i ^ 2 := by
    simp only [hg']
    rw [show (n : ℝ) * t / n = t by field_simp]
  have hg0 : g 0 = ∑ i, Z ω 0 i ^ 2 := by simp [hg']
  have hf0 : ∑ i, Z ω 0 i ^ 2 ≤ θ * t ^ 2 := by
    have h1 : ∑ i, Z ω 0 i ^ 2 ≤ Z0 ^ 2 := by
      have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (f := fun i => |Z ω 0 i|) (fun _ _ => abs_nonneg _)
      simpa [sq_abs] using this
    have h2 : Z0 ^ 2 ≤ (ε * t) ^ 2 := pow_le_pow_left₀ hZ00 htZ 2
    have h3 : ε ^ 2 ≤ θ := by
      have hε1 : ε ≤ 1 := by linarith
      have : ε ^ 2 ≤ ε := by rw [sq]; exact mul_le_of_le_one_left hεpos.le hε1
      linarith
    have h4 : (ε * t) ^ 2 ≤ θ * t ^ 2 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right h3 (by positivity)
    linarith
  have hnB : n * B ≤ (8 * D * θ + θ + I * (3 * Cr + 2) * θ) * t ^ 2 := by
    have e : (n : ℝ) * B = 8 * θ * D * t ^ 2 +
        (8 * n * I * (Cr + 1) * ε + I * (n * θ) * θ) * t ^ 2 := by
      rw [hB]; field_simp
    rw [e]
    have h1 : I * (n * θ) * θ ≤ I * (3 * Cr + 2) * θ := by
      have := mul_le_mul_of_nonneg_left hnθ2 hI0
      exact mul_le_mul_of_nonneg_right this hθ0.le
    have ht2 : 0 ≤ t ^ 2 := by positivity
    have h2 : (8 * n * I * (Cr + 1) * ε + I * (n * θ) * θ) * t ^ 2 ≤
        (θ + I * (3 * Cr + 2) * θ) * t ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) ht2
    linarith
  have hfinal : ∑ i, Z ω t i ^ 2 ≤ θ * c * t ^ 2 := by
    have h1 : g n - g 0 ≤ n * B := by rw [← htel]; exact hsumle
    rw [hgn, hg0] at h1
    rw [hc]
    linarith
  calc ∑ i, Z ω t i ^ 2 ≤ θ * c * t ^ 2 := hfinal
    _ ≤ γ * t ^ 2 := mul_le_mul_of_nonneg_right hθγ (by positivity)

open MaxPressure.Throughput Matrix in
lemma c565_tendsto {I J K : ℕ} {Ω : Type*} (N : Network I J K) (hN : N.Standing)
    (hEAA : EAA N) (hlp : ∃ x rho, rho ≤ (1 : ℝ) ∧ LPFeasible N x rho)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ) (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω)
    (hg : P.GoodSample N ω)
    (heq : NetworkEquations N P Z (activityTime E Ta) ω) (hmp : MPProcess N E Z Ta ω)
    (i : Fin I) : Tendsto (fun t : ℝ => Z ω t i / t) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨t0, ht0⟩ := c565_energy_bound N hN hEAA hlp E hE P Z Ta ω hg heq hmp
    ((ε / 2) ^ 2) (by positivity)
  refine ⟨max t0 1, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
  have htpos : 0 < t := by linarith
  have h1 := ht0 t (le_trans (le_max_left _ _) ht)
  have h2 : Z ω t i ^ 2 ≤ ∑ i, Z ω t i ^ 2 := Finset.single_le_sum
    (f := fun i => Z ω t i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h3 : Z ω t i ^ 2 ≤ (ε / 2 * t) ^ 2 := by rw [mul_pow]; linarith
  have hpos : 0 < ε / 2 * t := mul_pos (by positivity) htpos
  have h4 : |Z ω t i| ≤ ε / 2 * t := by
    have := sq_le_sq.1 h3
    rwa [abs_of_pos hpos] at this
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos htpos, div_lt_iff₀ htpos]
  linarith

open MaxPressure.Throughput MeasureTheory Filter Topology in
theorem solution {I J K : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (N : Network I J K) (hN : N.Standing) (hEAA : EAA N)
    (hlp : ∃ x rho, rho ≤ (1 : ℝ) ∧ LPFeasible N x rho)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N)
    (P : Primitives I J Ω) (hP : P.Valid N Pr)
    (Z : Ω → ℝ → Fin I → ℝ)
    (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ)
    (heq : ∀ ω, NetworkEquations N P Z (activityTime E Ta) ω)
    (hmp : ∀ ω, MPProcess N E Z Ta ω) :
    PathwiseStable Pr Z := by
  have hgood : ∀ᵐ ω ∂Pr, P.GoodSample N ω := hP.2.2.2.2.2.2.2.2
  unfold PathwiseStable
  filter_upwards [hgood] with ω hω
  intro i
  exact c565_tendsto N hN hEAA hlp E hE P Z Ta ω hω (heq ω) (hmp ω) i
