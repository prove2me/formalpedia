-- Prove2me | solution 1 for IncProx.Randomized.proposition2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T23:54:36.653851+00:00
-- url     : https://prove2.me/submissions/e24a7611-b5b0-4b2b-86f2-ffce5f162f7c

import Mathlib

open Filter Topology MeasureTheory

namespace IncProx2Aux

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- partial sums `S k = ∑_{j ≤ k} W j`. -/
noncomputable def Sw (W : ℕ → Ω → ℝ) (k : ℕ) (s : Ω) : ℝ := ∑ j ∈ Finset.range (k + 1), W j s

/-- predictable indicator `I k = 1{S k ≤ a}`. -/
noncomputable def Ind (W : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) (s : Ω) : ℝ :=
  if Sw W k s ≤ a then 1 else 0

lemma Ind_nonneg (W : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) (s : Ω) : 0 ≤ Ind W a k s := by
  unfold Ind; split_ifs <;> norm_num

lemma Ind_le_one (W : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) (s : Ω) : Ind W a k s ≤ 1 := by
  unfold Ind; split_ifs <;> norm_num

lemma Sw_mono {W : ℕ → Ω → ℝ} (hW0 : ∀ k s, 0 ≤ W k s) (s : Ω) {j k : ℕ} (h : j ≤ k) :
    Sw W j s ≤ Sw W k s := by
  unfold Sw
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun i _ _ => hW0 i s)

lemma Ind_anti {W : ℕ → Ω → ℝ} (hW0 : ∀ k s, 0 ≤ W k s) (a : ℝ) (s : Ω) {j k : ℕ} (h : j ≤ k) :
    Ind W a k s ≤ Ind W a j s := by
  unfold Ind
  have := Sw_mono hW0 s h
  split_ifs <;> linarith

lemma Ind_mul_W_le {W : ℕ → Ω → ℝ} (hW0 : ∀ k s, 0 ≤ W k s) (a : ℝ) (k : ℕ) (s : Ω) :
    Ind W a k s * W k s ≤ max a 0 := by
  unfold Ind
  split_ifs with h
  · have : W k s ≤ Sw W k s := by
      unfold Sw
      rw [Finset.sum_range_succ]
      have : 0 ≤ ∑ j ∈ Finset.range k, W j s := Finset.sum_nonneg (fun i _ => hW0 i s)
      linarith
    simp only [one_mul]; exact le_trans (le_trans this h) (le_max_left _ _)
  · simp

/-- Telescoping lower bound. -/
lemma tele_lb {W Y : ℕ → Ω → ℝ} (hW0 : ∀ k s, 0 ≤ W k s) (hY0 : ∀ k s, 0 ≤ Y k s) (a : ℝ)
    (s : Ω) : ∀ k, (if k = 0 then 1 else Ind W a (k - 1) s) * Y k s - Y 0 s ≤
      ∑ j ∈ Finset.range k, Ind W a j s * (Y (j + 1) s - Y j s) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    have hJ : Ind W a k s ≤ (if k = 0 then 1 else Ind W a (k - 1) s) := by
      split_ifs with hk
      · exact Ind_le_one _ _ _ _
      · exact Ind_anti hW0 a s (by omega)
    have := hY0 k s
    nlinarith [mul_le_mul_of_nonneg_right hJ this]

lemma sumW_bound {W : ℕ → Ω → ℝ} (hW0 : ∀ k s, 0 ≤ W k s) (a : ℝ) (s : Ω) : ∀ k,
    ∑ j ∈ Finset.range k, Ind W a j s * W j s ≤ max a 0 ∧
      ((if k = 0 then 1 else Ind W a (k - 1) s) = 1 →
        ∑ j ∈ Finset.range k, Ind W a j s * W j s = ∑ j ∈ Finset.range k, W j s) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    by_cases hk : Sw W k s ≤ a
    · have hI : Ind W a k s = 1 := by simp [Ind, hk]
      have hJ : (if k = 0 then 1 else Ind W a (k - 1) s) = 1 := by
        split_ifs with h0
        · rfl
        · have := Ind_anti hW0 a s (show k - 1 ≤ k by omega)
          rw [hI] at this
          have := Ind_le_one W a (k - 1) s
          linarith
      have heq := ih.2 hJ
      rw [heq, hI, one_mul]
      refine ⟨?_, fun _ => rfl⟩
      have : ∑ j ∈ Finset.range k, W j s + W k s = Sw W k s := by
        unfold Sw; rw [Finset.sum_range_succ]
      rw [this]; exact le_trans hk (le_max_left _ _)
    · have hI : Ind W a k s = 0 := by simp [Ind, hk]
      rw [hI, zero_mul, add_zero]
      exact ⟨ih.1, fun h => by norm_num at h⟩


lemma Ind_eq_indicator (W : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) :
    Ind W a k = {s | Sw W k s ≤ a}.indicator 1 := by
  funext s; simp [Ind, Set.indicator]

section Main

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem rs_core (𝓕 : Filtration ℕ m0) (Y Z W : ℕ → Ω → ℝ)
    (hYad : Adapted 𝓕 Y) (hZad : Adapted 𝓕 Z) (hWad : Adapted 𝓕 W)
    (hY0 : ∀ k s, 0 ≤ Y k s) (hZ0 : ∀ k s, 0 ≤ Z k s) (hW0 : ∀ k s, 0 ≤ W k s)
    (hYint : ∀ k, Integrable (Y k) μ)
    (h2 : ∀ k, μ[Y (k + 1) | 𝓕 k] ≤ᵐ[μ] fun s => Y k s - Z k s + W k s) (a : ℝ) :
    ∀ᵐ s ∂μ, (∀ k, Sw W k s ≤ a) →
      (Summable fun k => Z k s) ∧ ∃ L, Tendsto (fun k => Y k s) atTop (𝓝 L) := by
  -- measurability
  have hmeas : ∀ (V : ℕ → Ω → ℝ), Adapted 𝓕 V → ∀ j k, j ≤ k → Measurable[𝓕 k] (V j) :=
    fun V hV j k hjk => (hV j).mono (𝓕.mono hjk) le_rfl
  have hSw : ∀ k, Measurable[𝓕 k] (Sw W k) := by
    intro k
    unfold Sw
    exact Finset.measurable_sum _ (fun j hj => hmeas W hWad j k
      (by simp at hj; omega))
  have hI : ∀ k, Measurable[𝓕 k] (Ind W a k) := by
    intro k
    unfold Ind
    exact Measurable.ite (measurableSet_le (hSw k) measurable_const) measurable_const
      measurable_const
  have hm0 : ∀ (V : ℕ → Ω → ℝ), Adapted 𝓕 V → ∀ k, Measurable (V k) :=
    fun V hV k => (hV k).mono (𝓕.le k) le_rfl
  have hIm0 : ∀ k, Measurable (Ind W a k) := fun k => (hI k).mono (𝓕.le k) le_rfl
  -- integrability
  have hZle : ∀ k, ∀ᵐ s ∂μ, Z k s ≤ Y k s + W k s := by
    intro k
    have hnn : 0 ≤ᵐ[μ] μ[Y (k + 1) | 𝓕 k] :=
      condExp_nonneg (Eventually.of_forall fun s => hY0 (k + 1) s)
    filter_upwards [hnn, h2 k] with s h1 h3
    simp only [Pi.zero_apply] at h1
    linarith
  have hIW : ∀ k, Integrable (fun s => Ind W a k s * W k s) μ := by
    intro k
    refine Integrable.of_bound ((hIm0 k).mul (hm0 W hWad k)).aestronglyMeasurable (max a 0)
      (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Ind_nonneg _ _ _ _) (hW0 k s))]
    exact Ind_mul_W_le hW0 a k s
  have hIZ : ∀ k, Integrable (fun s => Ind W a k s * Z k s) μ := by
    intro k
    refine Integrable.mono' ((hYint k).add (integrable_const (max a 0)))
      ((hIm0 k).mul (hm0 Z hZad k)).aestronglyMeasurable ?_
    filter_upwards [hZle k] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Ind_nonneg _ _ _ _) (hZ0 k s))]
    have h1 := Ind_mul_W_le hW0 a k s
    have h2' := Ind_nonneg W a k s
    have h3 := Ind_le_one W a k s
    have h4 := hY0 k s
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left hs h2']
  have hIY : ∀ k j, Integrable (fun s => Ind W a k s * Y j s) μ := by
    intro k j
    refine Integrable.mono' (hYint j) ((hIm0 k).mul (hm0 Y hYad j)).aestronglyMeasurable
      (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Ind_nonneg _ _ _ _) (hY0 j s))]
    have := Ind_le_one W a k s
    have := hY0 j s
    nlinarith [Ind_nonneg W a k s]
  -- the process
  set D : ℕ → Ω → ℝ := fun j s => Ind W a j s * Y (j + 1) s - Ind W a j s * Y j s +
    Ind W a j s * Z j s - Ind W a j s * W j s with hD
  set M : ℕ → Ω → ℝ := fun k s => ∑ j ∈ Finset.range k, D j s with hM
  have hDint : ∀ j, Integrable (D j) μ := fun j =>
    (((hIY j (j + 1)).sub (hIY j j)).add (hIZ j)).sub (hIW j)
  have hMint : ∀ k, Integrable (M k) μ := fun k =>
    integrable_finsetSum _ (fun j _ => hDint j)
  have hDmeas : ∀ j k, j + 1 ≤ k → Measurable[𝓕 k] (D j) := by
    intro j k hjk
    have hIk : Measurable[𝓕 k] (Ind W a j) := (hI j).mono (𝓕.mono (by omega)) le_rfl
    exact (((hIk.mul (hmeas Y hYad (j + 1) k hjk)).sub (hIk.mul (hmeas Y hYad j k (by omega)))).add
      (hIk.mul (hmeas Z hZad j k (by omega)))).sub (hIk.mul (hmeas W hWad j k (by omega)))
  have hMmeas : ∀ k, Measurable[𝓕 k] (M k) := by
    intro k
    exact Finset.measurable_sum _ (fun j hj => hDmeas j k (by simp at hj; omega))
  have hadM : StronglyAdapted 𝓕 M := fun k => (hMmeas k).stronglyMeasurable
  have hsuper : Supermartingale M 𝓕 μ := by
    refine supermartingale_nat hadM hMint (fun k => ?_)
    have hsplit : M (k + 1) = M k + D k := by
      funext s; simp [hM, Finset.sum_range_succ]
    set G : Ω → ℝ := fun s => Ind W a k s * Y k s - Ind W a k s * Z k s + Ind W a k s * W k s
      with hG
    have hDk : D k = (Ind W a k * Y (k + 1)) - G := by
      funext s; simp only [hD, hG, Pi.sub_apply, Pi.mul_apply]; ring
    have hGint : Integrable G μ := ((hIY k k).sub (hIZ k)).add (hIW k)
    have hGmeas : Measurable[𝓕 k] G :=
      (((hI k).mul (hYad k)).sub ((hI k).mul (hZad k))).add ((hI k).mul (hWad k))
    have hprod : Integrable (Ind W a k * Y (k + 1)) μ := hIY k (k + 1)
    have e1 : μ[M (k + 1) | 𝓕 k] =ᵐ[μ] μ[M k | 𝓕 k] + μ[D k | 𝓕 k] := by
      rw [hsplit]; exact condExp_add (hMint k) (hDint k) _
    have e2 : μ[M k | 𝓕 k] = M k := condExp_of_stronglyMeasurable (𝓕.le k)
      (hMmeas k).stronglyMeasurable (hMint k)
    have e3 : μ[D k | 𝓕 k] =ᵐ[μ] μ[Ind W a k * Y (k + 1) | 𝓕 k] - μ[G | 𝓕 k] := by
      rw [hDk]; exact condExp_sub hprod hGint _
    have e4 : μ[Ind W a k * Y (k + 1) | 𝓕 k] =ᵐ[μ] Ind W a k * μ[Y (k + 1) | 𝓕 k] :=
      condExp_mul_of_stronglyMeasurable_left (hI k).stronglyMeasurable hprod (hYint (k + 1))
    have e5 : μ[G | 𝓕 k] = G := condExp_of_stronglyMeasurable (𝓕.le k)
      hGmeas.stronglyMeasurable hGint
    filter_upwards [e1, e3, e4, h2 k] with s h1 h3 h4 h5
    rw [h1, Pi.add_apply, e2, h3, Pi.sub_apply, h4, e5, Pi.mul_apply]
    simp only [hG]
    have := Ind_nonneg W a k s
    nlinarith [mul_le_mul_of_nonneg_left h5 this]
  -- lower bound
  have hlb : ∀ k s, -Y 0 s - max a 0 ≤ M k s := by
    intro k s
    have hsum : M k s = ∑ j ∈ Finset.range k, Ind W a j s * (Y (j + 1) s - Y j s) +
        ∑ j ∈ Finset.range k, Ind W a j s * Z j s -
        ∑ j ∈ Finset.range k, Ind W a j s * W j s := by
      simp only [hM, hD, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    have t1 := tele_lb hW0 hY0 a s k
    have t2 := (sumW_bound hW0 a s k).1
    have t3 : 0 ≤ ∑ j ∈ Finset.range k, Ind W a j s * Z j s :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (Ind_nonneg _ _ _ _) (hZ0 j s))
    have t4 : 0 ≤ (if k = 0 then 1 else Ind W a (k - 1) s) * Y k s := by
      apply mul_nonneg _ (hY0 k s)
      split_ifs
      · norm_num
      · exact Ind_nonneg _ _ _ _
    linarith
  -- L¹ bound
  set R : ENNReal := ENNReal.ofReal (2 * (∫ s, Y 0 s ∂μ + max a 0)) with hR
  have hbdd : ∀ k, eLpNorm ((-M) k) 1 μ ≤ R := by
    intro k
    show eLpNorm (-(M k)) 1 μ ≤ R
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hMint k).neg]
    apply ENNReal.ofReal_le_ofReal
    have hle : ∀ s, ‖(-M) k s‖ ≤ M k s + 2 * (Y 0 s + max a 0) := by
      intro s
      have := hlb k s
      have := hY0 0 s
      have := le_max_right a 0
      simp only [Pi.neg_apply, norm_neg, Real.norm_eq_abs]
      rcases abs_cases (M k s) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    have hA0 : Integrable (fun s => Y 0 s + max a 0) μ := (hYint 0).add (integrable_const _)
    have hA : Integrable (fun s => 2 * (Y 0 s + max a 0)) μ := hA0.const_mul 2
    have hint2 : Integrable (fun s => M k s + 2 * (Y 0 s + max a 0)) μ := (hMint k).add hA
    have i1 : ∫ s, ‖(-M) k s‖ ∂μ ≤ ∫ s, M k s + 2 * (Y 0 s + max a 0) ∂μ :=
      integral_mono (hMint k).neg.norm hint2 hle
    have i2 : ∫ s, M k s + 2 * (Y 0 s + max a 0) ∂μ =
        ∫ s, M k s ∂μ + 2 * (∫ s, Y 0 s ∂μ + max a 0) := by
      rw [integral_add (hMint k) hA, integral_const_mul,
        integral_add (hYint 0) (integrable_const _)]
      simp
    have i3 : ∫ s, M k s ∂μ ≤ ∫ s, M 0 s ∂μ := by
      have := hsuper.setIntegral_le (Nat.zero_le k) (MeasurableSet.univ)
      simpa using this
    have i4 : ∫ s, M 0 s ∂μ = 0 := by simp [hM]
    simp only [Pi.neg_apply, norm_neg] at i1 ⊢
    linarith
  have hconv := hsuper.neg.exists_ae_tendsto_of_bdd hbdd
  filter_upwards [hconv] with s hs hSa
  obtain ⟨c, hc⟩ := hs
  have hIone : ∀ k, Ind W a k s = 1 := fun k => by simp [Ind, hSa k]
  have hMk : ∀ k, M k s = (Y k s + ∑ j ∈ Finset.range k, Z j s) - Y 0 s -
      ∑ j ∈ Finset.range k, W j s := by
    intro k
    simp only [hM, hD, hIone, one_mul]
    have h1 := Finset.sum_range_sub (fun j => Y j s) k
    have h2 : ∑ x ∈ Finset.range k, Y (x + 1) s - ∑ x ∈ Finset.range k, Y x s = Y k s - Y 0 s := by
      rw [← Finset.sum_sub_distrib]; exact h1
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    linarith
  have hWsum : Summable fun k => W k s := by
    refine summable_of_sum_range_le (c := a) (fun k => hW0 k s) (fun k => ?_)
    have : ∑ i ∈ Finset.range k, W i s ≤ Sw W k s := by
      unfold Sw; rw [Finset.sum_range_succ]; linarith [hW0 k s]
    linarith [hSa k]
  have hWt := hWsum.hasSum.tendsto_sum_nat
  have hP : Tendsto (fun k => Y k s + ∑ j ∈ Finset.range k, Z j s) atTop
      (𝓝 (-c + Y 0 s + ∑' k, W k s)) := by
    have hc' : Tendsto (fun n => M n s) atTop (𝓝 (-c)) := by
      have := hc.neg; simpa using this
    have := ((hc'.add_const (Y 0 s)).add hWt)
    refine this.congr (fun k => ?_)
    rw [hMk k]; ring
  obtain ⟨B, hB⟩ := hP.bddAbove_range
  have hZsum : Summable fun k => Z k s := by
    refine summable_of_sum_range_le (c := B) (fun k => hZ0 k s) (fun k => ?_)
    have := hB ⟨k, rfl⟩
    linarith [hY0 k s]
  have := hP.sub hZsum.hasSum.tendsto_sum_nat
  exact ⟨hZsum, _, this.congr (fun k => by ring)⟩

end Main

end IncProx2Aux

open IncProx2Aux in
theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ m0) (Y Z W : ℕ → Ω → ℝ)
    (hYad : Adapted 𝓕 Y) (hZad : Adapted 𝓕 Z) (hWad : Adapted 𝓕 W)
    (hY0 : ∀ k s, 0 ≤ Y k s) (hZ0 : ∀ k s, 0 ≤ Z k s) (hW0 : ∀ k s, 0 ≤ W k s)
    (hYint : ∀ k, Integrable (Y k) μ)
    (h2 : ∀ k, μ[Y (k + 1) | 𝓕 k] ≤ᵐ[μ] fun s => Y k s - Z k s + W k s)
    (h3 : ∀ᵐ s ∂μ, Summable fun k => W k s) :
    (∀ᵐ s ∂μ, Summable fun k => Z k s) ∧
      ∃ Yinf : Ω → ℝ, Measurable Yinf ∧
        ∀ᵐ s ∂μ, 0 ≤ Yinf s ∧ Tendsto (fun k => Y k s) atTop (𝓝 (Yinf s)) := by
  have hall : ∀ᵐ s ∂μ, ∀ a : ℕ, (∀ k, Sw W k s ≤ (a : ℝ)) →
      (Summable fun k => Z k s) ∧ ∃ L, Tendsto (fun k => Y k s) atTop (𝓝 L) := by
    rw [ae_all_iff]
    intro a
    exact rs_core μ 𝓕 Y Z W hYad hZad hWad hY0 hZ0 hW0 hYint h2 (a : ℝ)
  have hgood : ∀ᵐ s ∂μ, (Summable fun k => Z k s) ∧
      ∃ L, Tendsto (fun k => Y k s) atTop (𝓝 L) := by
    filter_upwards [hall, h3] with s hs hW
    refine hs ⌈∑' k, W k s⌉₊ (fun k => ?_)
    calc Sw W k s ≤ ∑' k, W k s := by
          unfold Sw
          exact hW.sum_le_tsum _ (fun i _ => hW0 i s)
      _ ≤ _ := Nat.le_ceil _
  refine ⟨hgood.mono fun s hs => hs.1, ?_⟩
  have hYm : ∀ k, AEMeasurable (Y k) μ := fun k => ((hYad k).mono (𝓕.le k) le_rfl).aemeasurable
  obtain ⟨Yinf, hYinf, hlim⟩ := measurable_limit_of_tendsto_metrizable_ae hYm
    (hgood.mono fun s hs => hs.2)
  refine ⟨Yinf, hYinf, ?_⟩
  filter_upwards [hlim] with s hs
  exact ⟨ge_of_tendsto' hs (fun k => hY0 k s), hs⟩
