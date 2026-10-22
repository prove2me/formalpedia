-- Prove2me | solution 1 for NatureSLT.Margin.mercer_theorem
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:11:31.845998+00:00
-- url     : https://prove2.me/submissions/b7bba93b-8578-4194-bae2-3c97dc82fe56

import Mathlib
open MeasureTheory Filter Topology

noncomputable def g70slt_S (k : ℕ) : Set (EuclideanSpace ℝ (Fin 1)) :=
  {u | u 0 ∈ Set.Ico ((1/2:ℝ)^(k+1)) ((1/2)^k)}
noncomputable def g70slt_ψ (k : ℕ) : EuclideanSpace ℝ (Fin 1) → ℝ :=
  (g70slt_S k).indicator (fun _ => Real.sqrt (2^(k+1)))
noncomputable def g70slt_a (k : ℕ) : ℝ := (1/4:ℝ)^k
noncomputable def g70slt_K (u v : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  ∑' k, g70slt_a k * g70slt_ψ k u * g70slt_ψ k v

theorem g70slt_meas0 : Measurable (fun u : EuclideanSpace ℝ (Fin 1) => u 0) := by fun_prop

theorem g70slt_vol (B : Set ℝ) (hB : MeasurableSet B) :
    volume {u : EuclideanSpace ℝ (Fin 1) | u 0 ∈ B} = volume B := by
  have hmp := (volume_preserving_funUnique (Fin 1) ℝ).comp (PiLp.volume_preserving_ofLp (Fin 1))
  exact hmp.measure_preimage hB.nullMeasurableSet

theorem g70slt_measS (k : ℕ) : MeasurableSet (g70slt_S k) :=
  g70slt_meas0 measurableSet_Ico

theorem g70slt_disj {u : EuclideanSpace ℝ (Fin 1)} {j k : ℕ} (hj : u ∈ g70slt_S j)
    (hk : u ∈ g70slt_S k) : j = k := by
  simp only [g70slt_S, Set.mem_ofPred_eq, Set.mem_Ico] at hj hk
  rcases lt_trichotomy j k with h | h | h
  · have : (1/2:ℝ)^k ≤ (1/2)^(j+1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    linarith
  · exact h
  · have : (1/2:ℝ)^j ≤ (1/2)^(k+1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    linarith

theorem g70slt_le_one {u : EuclideanSpace ℝ (Fin 1)} {k : ℕ} (hk : u ∈ g70slt_S k) :
    0 ≤ u 0 ∧ u 0 < 1 := by
  simp only [g70slt_S, Set.mem_ofPred_eq, Set.mem_Ico] at hk
  have : (1/2:ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  constructor
  · linarith [show (0:ℝ) ≤ (1/2)^(k+1) by positivity]
  · linarith

theorem g70slt_val (k : ℕ) :
    (1/4:ℝ)^k * Real.sqrt (2^(k+1)) * Real.sqrt (2^(k+1)) = 2 * (1/2:ℝ)^k := by
  have h1 : (1/2:ℝ)^k * 2^k = 1 := by rw [← mul_pow]; norm_num
  have h4 : (1/4:ℝ)^k = (1/2)^k * (1/2)^k := by rw [← mul_pow]; norm_num
  rw [mul_assoc, Real.mul_self_sqrt (by positivity), h4, pow_succ]
  linear_combination (2 * (1/2:ℝ)^k) * h1

open Classical in
theorem g70slt_Tval (k : ℕ) (u v : EuclideanSpace ℝ (Fin 1)) :
    g70slt_a k * g70slt_ψ k u * g70slt_ψ k v =
      if u ∈ g70slt_S k ∧ v ∈ g70slt_S k then 2 * (1/2:ℝ)^k else 0 := by
  by_cases hu : u ∈ g70slt_S k <;> by_cases hv : v ∈ g70slt_S k <;>
    simp only [g70slt_ψ, g70slt_a, Set.indicator_of_mem, Set.indicator_of_notMem, hu, hv,
      and_self, and_false, false_and, if_true, if_false, mul_zero, zero_mul, not_false_eq_true]
  exact g70slt_val k

theorem g70slt_hasSum (u v : EuclideanSpace ℝ (Fin 1)) :
    HasSum (fun k => g70slt_a k * g70slt_ψ k u * g70slt_ψ k v) (g70slt_K u v) := by
  apply Summable.hasSum
  by_cases h : ∃ k0, u ∈ g70slt_S k0
  · obtain ⟨k0, hk0⟩ := h
    refine (hasSum_single k0 (fun k hk => ?_)).summable
    rw [g70slt_Tval, if_neg]
    rintro ⟨hu, _⟩; exact hk (g70slt_disj hu hk0)
  · push Not at h
    have : (fun k => g70slt_a k * g70slt_ψ k u * g70slt_ψ k v) = fun _ => 0 := by
      funext k; rw [g70slt_Tval, if_neg]; rintro ⟨hu, _⟩; exact h k hu
    rw [this]; exact summable_zero

theorem g70slt_Kzero (u v : EuclideanSpace ℝ (Fin 1)) (h : ∀ k, u ∉ g70slt_S k) :
    g70slt_K u v = 0 := by
  have : (fun k => g70slt_a k * g70slt_ψ k u * g70slt_ψ k v) = fun _ => 0 := by
    funext k; rw [g70slt_Tval, if_neg]; rintro ⟨hu, _⟩; exact h k hu
  rw [g70slt_K, this, tsum_zero]

theorem g70slt_tail (u v : EuclideanSpace ℝ (Fin 1)) (N : ℕ) :
    |g70slt_K u v - ∑ k ∈ Finset.range N, g70slt_a k * g70slt_ψ k u * g70slt_ψ k v|
      ≤ 2 * (1/2:ℝ)^N := by
  have hN : (0:ℝ) ≤ 2 * (1/2:ℝ)^N := by positivity
  by_cases h : ∃ k0, u ∈ g70slt_S k0
  · obtain ⟨k0, hk0⟩ := h
    have hz : ∀ k, k ≠ k0 → g70slt_a k * g70slt_ψ k u * g70slt_ψ k v = 0 := by
      intro k hk; rw [g70slt_Tval, if_neg]; rintro ⟨hu, _⟩; exact hk (g70slt_disj hu hk0)
    have hK : g70slt_K u v = g70slt_a k0 * g70slt_ψ k0 u * g70slt_ψ k0 v :=
      ((g70slt_hasSum u v).unique (hasSum_single k0 hz))
    by_cases hlt : k0 < N
    · rw [Finset.sum_eq_single_of_mem k0 (Finset.mem_range.mpr hlt) (fun k _ hk => hz k hk), hK]
      simpa using hN
    · rw [Finset.sum_eq_zero (fun k hk => hz k (by
        intro e; subst e; exact hlt (Finset.mem_range.mp hk))), hK, sub_zero, g70slt_Tval]
      split_ifs
      · rw [abs_of_nonneg (by positivity)]
        have : (1/2:ℝ)^k0 ≤ (1/2)^N :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        linarith
      · simpa using hN
  · push Not at h
    rw [g70slt_Kzero u v h, Finset.sum_eq_zero (fun k _ => by
      rw [g70slt_Tval, if_neg]; rintro ⟨hu, _⟩; exact h k hu)]
    simpa using hN

theorem g70slt_measψ (k : ℕ) : Measurable (g70slt_ψ k) :=
  measurable_const.indicator (g70slt_measS k)

theorem g70slt_measK : Measurable (Function.uncurry g70slt_K) := by
  refine measurable_of_tendsto_metrizable (f := fun N (p : EuclideanSpace ℝ (Fin 1) ×
    EuclideanSpace ℝ (Fin 1)) => ∑ k ∈ Finset.range N, g70slt_a k * g70slt_ψ k p.1 * g70slt_ψ k p.2)
    (fun N => ?_) (tendsto_pi_nhds.mpr fun p => (g70slt_hasSum p.1 p.2).tendsto_sum_nat)
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact (measurable_const.mul ((g70slt_measψ k).comp measurable_fst)).mul
    ((g70slt_measψ k).comp measurable_snd)

theorem solution : ¬ (∀ {d : ℕ} (hd : 0 < d) (U : Set (EuclideanSpace ℝ (Fin d)))
    (hU : MeasurableSet U)
    (hU0 : 0 < volume U) (K : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
    (hsymm : ∀ u ∈ U, ∀ v ∈ U, K u v = K v u)
    (hK : MemLp (Function.uncurry K) 2 ((volume.restrict U).prod (volume.restrict U))),
    (∃ (a : ℕ → ℝ) (ψ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ),
        (∀ k, 0 < a k) ∧ (∀ k, MemLp (ψ k) 2 (volume.restrict U)) ∧
        (∀ j k, ∫ u in U, ψ j u * ψ k u = if j = k then 1 else 0) ∧
        Tendsto (fun N : ℕ => eLpNorm (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
            K p.1 p.2 - ∑ k ∈ Finset.range N, a k * ψ k p.1 * ψ k p.2) 2
              ((volume.restrict U).prod (volume.restrict U))) atTop (𝓝 0)) ↔
      ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, MemLp g 2 (volume.restrict U) →
        ¬ (g =ᵐ[volume.restrict U] 0) →
        0 < ∫ p, K p.1 p.2 * g p.1 * g p.2 ∂((volume.restrict U).prod (volume.restrict U))) := by
  intro H
  set U : Set (EuclideanSpace ℝ (Fin 1)) := {u | u 0 ∈ Set.Ico 0 2} with hUdef
  have hUm : MeasurableSet U := g70slt_meas0 measurableSet_Ico
  have hUv : volume U = ENNReal.ofReal 2 := by
    rw [hUdef, g70slt_vol _ measurableSet_Ico, Real.volume_Ico]; norm_num
  haveI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr (by rw [hUv]; simp)
  set G : Set (EuclideanSpace ℝ (Fin 1)) := {u | u 0 ∈ Set.Ico 1 2} with hGdef
  have hGm : MeasurableSet G := g70slt_meas0 measurableSet_Ico
  set g : EuclideanSpace ℝ (Fin 1) → ℝ := G.indicator (fun _ => 1) with hgdef
  have hKb : ∀ u v, |g70slt_K u v| ≤ 2 := fun u v => by
    simpa using g70slt_tail u v 0
  have hK : MemLp (Function.uncurry g70slt_K) 2
      ((volume.restrict U).prod (volume.restrict U)) :=
    MemLp.of_bound g70slt_measK.aestronglyMeasurable 2
      (Eventually.of_forall fun p => by
        rcases p with ⟨u, v⟩; simpa [Real.norm_eq_abs] using hKb u v)
  have hiff := H (d := 1) one_pos U hUm (by rw [hUv]; simp) g70slt_K
    (fun u _ v _ => by simp only [g70slt_K]; congr 1; funext k; ring) hK
  have hSU : ∀ k, g70slt_S k ⊆ U := fun k u hu => by
    have := g70slt_le_one hu
    simp only [hUdef, Set.mem_ofPred_eq, Set.mem_Ico]; constructor <;> linarith
  have hexp : ∃ (a : ℕ → ℝ) (ψ : ℕ → EuclideanSpace ℝ (Fin 1) → ℝ),
        (∀ k, 0 < a k) ∧ (∀ k, MemLp (ψ k) 2 (volume.restrict U)) ∧
        (∀ j k, ∫ u in U, ψ j u * ψ k u = if j = k then 1 else 0) ∧
        Tendsto (fun N : ℕ => eLpNorm (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) =>
            g70slt_K p.1 p.2 - ∑ k ∈ Finset.range N, a k * ψ k p.1 * ψ k p.2) 2
              ((volume.restrict U).prod (volume.restrict U))) atTop (𝓝 0) := by
    refine ⟨g70slt_a, g70slt_ψ, fun k => by unfold g70slt_a; positivity, fun k => ?_,
      fun j k => ?_, ?_⟩
    · refine MemLp.of_bound (g70slt_measψ k).aestronglyMeasurable (Real.sqrt (2^(k+1)))
        (Eventually.of_forall fun u => ?_)
      by_cases hu : u ∈ g70slt_S k <;> simp [g70slt_ψ, hu, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    · split_ifs with h
      · subst h
        have e : (fun u => g70slt_ψ j u * g70slt_ψ j u) =
            (g70slt_S j).indicator (fun _ => (2:ℝ)^(j+1)) := by
          funext u
          by_cases hu : u ∈ g70slt_S j <;> simp [g70slt_ψ, hu]
        rw [e, integral_indicator_const _ (g70slt_measS j), Measure.real,
          Measure.restrict_apply (g70slt_measS j), Set.inter_eq_left.mpr (hSU j), g70slt_S,
          g70slt_vol _ measurableSet_Ico, Real.volume_Ico,
          ENNReal.toReal_ofReal (by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) j])]
        have h1 : (1/2:ℝ)^(j+1) * 2^(j+1) = 1 := by rw [← mul_pow]; norm_num
        rw [smul_eq_mul]
        have h2 : (1/2:ℝ)^j = 2 * (1/2)^(j+1) := by rw [pow_succ]; ring
        rw [h2]; linear_combination h1
      · have e : (fun u => g70slt_ψ j u * g70slt_ψ k u) = fun _ => 0 := by
          funext u
          by_cases hj : u ∈ g70slt_S j
          · by_cases hk : u ∈ g70slt_S k
            · exact absurd (g70slt_disj hj hk) h
            · simp [g70slt_ψ, hk]
          · simp [g70slt_ψ, hj]
        rw [e, integral_zero]
    · set μ := (volume.restrict U).prod (volume.restrict U)
      have hc : μ Set.univ ^ (2:ENNReal).toReal⁻¹ ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)
      have hb : ∀ N : ℕ, eLpNorm (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) =>
            g70slt_K p.1 p.2 - ∑ k ∈ Finset.range N, g70slt_a k * g70slt_ψ k p.1 * g70slt_ψ k p.2) 2 μ
          ≤ μ Set.univ ^ (2:ENNReal).toReal⁻¹ * ENNReal.ofReal (2 * (1/2:ℝ)^N) := fun N =>
        eLpNorm_le_of_ae_bound (Eventually.of_forall fun p => by
          simpa [Real.norm_eq_abs] using g70slt_tail p.1 p.2 N)
      have hlim : Tendsto (fun N : ℕ => μ Set.univ ^ (2:ENNReal).toReal⁻¹ *
          ENNReal.ofReal (2 * (1/2:ℝ)^N)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun N : ℕ => 2 * (1/2:ℝ)^N) atTop (𝓝 0) := by
          simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
            (by norm_num)).const_mul 2
        have h2 := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal h1) (Or.inr hc)
        simpa using h2
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun _ => bot_le) hb
  have hgL : MemLp g 2 (volume.restrict U) :=
    MemLp.of_bound (measurable_const.indicator hGm).aestronglyMeasurable 1
      (Eventually.of_forall fun u => by by_cases hu : u ∈ G <;> simp [hgdef, hu])
  have hgne : ¬ (g =ᵐ[volume.restrict U] 0) := by
    intro h
    rw [Filter.EventuallyEq, ae_iff] at h
    have e : {a | ¬ g a = (0 : EuclideanSpace ℝ (Fin 1) → ℝ) a} = G := by
      ext u; by_cases hu : u ∈ G <;> simp [hgdef, hu]
    rw [e, Measure.restrict_apply hGm] at h
    have hGU : G ∩ U = G := Set.inter_eq_left.mpr (fun u hu => by
      simp only [hGdef, hUdef, Set.mem_ofPred_eq, Set.mem_Ico] at hu ⊢
      constructor <;> linarith [hu.1, hu.2])
    rw [hGU, hGdef, g70slt_vol _ measurableSet_Ico, Real.volume_Ico] at h
    norm_num at h
  have hpos := hiff.mp hexp g hgL hgne
  have hz : (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) =>
      g70slt_K p.1 p.2 * g p.1 * g p.2) = fun _ => 0 := by
    funext p
    by_cases hp : p.1 ∈ G
    · rw [g70slt_Kzero p.1 p.2 (fun k hk => by
        have := g70slt_le_one hk
        simp only [hGdef, Set.mem_ofPred_eq, Set.mem_Ico] at hp
        linarith [hp.1])]
      simp
    · simp [hgdef, hp]
  rw [hz, integral_zero] at hpos
  exact lt_irrefl _ hpos
