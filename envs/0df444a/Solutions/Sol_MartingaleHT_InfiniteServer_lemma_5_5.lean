-- Prove2me | solution 1 for MartingaleHT.InfiniteServer.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:27:51.607162+00:00
-- url     : https://prove2.me/submissions/7badfd79-db31-49f1-b2bb-fafe36cd8a9c

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ErlangA_Diffusion_SDE
import Definitions.Def_ErlangA_Diffusion_Queue
import Definitions.Def_MartingaleHT_InfiniteServer_Model
import Definitions.Def_MartingaleHT_InfiniteServer_Toolkit
import Theorems.Thm_MartingaleHT_InfiniteServer_lemma_4_1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

open BellWilliams2001.ThresholdPolicy ManyServerQED.Scheduling ErlangA.Diffusion
open MartingaleHT.InfiniteServer

/-- A Skorokhod path is bounded on every compact interval `[0, T]`. -/
lemma mht55_cadlag_bdd (x : ℝ → ℝ) (hx : IsCadlag x) (T : ℝ) :
    ∃ B : ℝ, ∀ s ∈ Set.Icc (0:ℝ) T, |x s| ≤ B := by
  have key := (isCompact_Icc (a := (0:ℝ)) (b := T)).induction_on
    (p := fun s : Set ℝ => ∃ B : ℝ, ∀ y ∈ s, |x y| ≤ B)
    ⟨0, fun y hy => absurd hy (Set.notMem_empty y)⟩
    (fun s t hst ⟨B, hB⟩ => ⟨B, fun y hy => hB y (hst hy)⟩)
    (fun s t ⟨B₁, h₁⟩ ⟨B₂, h₂⟩ => ⟨max B₁ B₂, fun y hy => hy.elim
      (fun h => le_trans (h₁ y h) (le_max_left _ _))
      (fun h => le_trans (h₂ y h) (le_max_right _ _))⟩)
    ?_
  · exact key
  intro y hy
  have hy0 : 0 ≤ y := hy.1
  -- right neighbourhood
  have hR : {s | |x s| ≤ |x y| + 1} ∈ 𝓝[≥] y := by
    have hc := hx.1 y hy0
    have : ∀ᶠ s in 𝓝[≥] y, dist (x s) (x y) < 1 :=
      (Metric.tendsto_nhds.1 hc) 1 one_pos
    filter_upwards [this] with s hs
    rw [Real.dist_eq] at hs
    have := abs_sub_abs_le_abs_sub (x s) (x y)
    show |x s| ≤ |x y| + 1; linarith
  rcases eq_or_lt_of_le hy0 with h0 | hpos
  · subst h0
    refine ⟨{s | |x s| ≤ |x 0| + 1}, ?_, ⟨|x 0| + 1, fun s hs => hs⟩⟩
    exact nhdsWithin_mono _ (fun s hs => hs.1) hR
  · obtain ⟨l, hl⟩ := hx.2 y hpos
    have hL : {s | |x s| ≤ |l| + 1} ∈ 𝓝[<] y := by
      have : ∀ᶠ s in 𝓝[<] y, dist (x s) l < 1 := (Metric.tendsto_nhds.1 hl) 1 one_pos
      filter_upwards [this] with s hs
      rw [Real.dist_eq] at hs
      have := abs_sub_abs_le_abs_sub (x s) l
      show |x s| ≤ |l| + 1; linarith
    refine ⟨{s | |x s| ≤ |x y| + 1} ∪ {s | |x s| ≤ |l| + 1}, ?_, ?_⟩
    · apply mem_nhdsWithin_of_mem_nhds
      rw [← nhdsLT_sup_nhdsGE]
      exact ⟨Filter.mem_of_superset hL Set.subset_union_right,
        Filter.mem_of_superset hR Set.subset_union_left⟩
    · refine ⟨max (|x y| + 1) (|l| + 1), fun s hs => hs.elim
        (fun h => le_trans h (le_max_left _ _)) (fun h => le_trans h (le_max_right _ _))⟩

/-- A path that is right-continuous on `[0, ∞)`, frozen at its value at `0` on `(-∞, 0)`, is
Borel measurable. -/
lemma mht55_cadlag_meas (x : ℝ → ℝ) (hx : IsCadlag x) :
    Measurable (fun t => x (max t 0)) := by
  let f : ℕ → ℝ → ℝ := fun n t => x (max ((⌈((n:ℝ)+1) * t⌉ : ℝ) / ((n:ℝ)+1)) 0)
  have hf : ∀ n, Measurable (f n) := by
    intro n
    have h1 : Measurable (fun t : ℝ => ⌈((n:ℝ)+1) * t⌉) :=
      (measurable_const.mul measurable_id).ceil
    have h2 : Measurable (fun k : ℤ => x (max ((k : ℝ) / ((n:ℝ)+1)) 0)) :=
      measurable_from_top
    exact h2.comp h1
  refine measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.2 fun t => ?_)
  rcases lt_or_ge t 0 with ht | ht
  · have : ∀ n, f n t = x (max t 0) := by
      intro n
      have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
      have hc : ⌈((n:ℝ)+1) * t⌉ ≤ 0 := by
        rw [Int.ceil_le]; push_cast; nlinarith
      have : ((⌈((n:ℝ)+1) * t⌉ : ℤ) : ℝ) / ((n:ℝ)+1) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hc) hn.le
      simp only [f, max_eq_right this, max_eq_right ht.le]
    simp only [this]; exact tendsto_const_nhds
  · set u : ℕ → ℝ := fun n => (⌈((n:ℝ)+1) * t⌉ : ℝ) / ((n:ℝ)+1)
    have hu_ge : ∀ n, t ≤ u n := by
      intro n
      have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
      rw [le_div_iff₀ hn, mul_comm]; exact Int.le_ceil _
    have hu_le : ∀ n, u n ≤ t + 1 / ((n:ℝ)+1) := by
      intro n
      have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
      have := Int.ceil_lt_add_one (((n:ℝ)+1) * t)
      have e : (t + 1 / ((n:ℝ)+1)) * ((n:ℝ)+1) = ((n:ℝ)+1) * t + 1 := by
        field_simp
      rw [div_le_iff₀ hn, e]
      linarith
    have hu : Tendsto u atTop (𝓝[≥] t) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hu_ge⟩
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hu_ge hu_le
      have : Tendsto (fun n : ℕ => t + 1 / ((n:ℝ)+1)) atTop (𝓝 (t + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using this
    have hcont := (hx.1 t ht).tendsto.comp hu
    have : ∀ n, f n t = x (u n) := by
      intro n; simp only [f, u]; rw [max_eq_left (le_trans ht (hu_ge n))]
    simp only [this, max_eq_left ht]
    exact hcont

lemma mht55_intOn (f : ℝ → ℝ) (hf : Measurable f) (T B : ℝ)
    (hB : ∀ s ∈ Set.Icc (0:ℝ) T, |f s| ≤ B) : IntegrableOn f (Set.Icc 0 T) := by
  refine Measure.integrableOn_of_bounded (M := B) (by simp) hf.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall fun s hs => by simpa [Real.norm_eq_abs] using hB s hs

/-- Pathwise Gronwall bound for the integral representation. -/
lemma mht55_path_bound (h : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hLip : ∀ s₁ s₂ : ℝ, |h s₁ - h s₂| ≤ c * |s₁ - s₂|) {k : ℕ}
    (x : ℝ → ℝ) (y : Fin k → ℝ → ℝ) (hx : IsCadlag x) (T : ℝ) (hT : 0 < T)
    (hrep : ∀ t : ℝ, 0 ≤ t → x t = x 0 + ∑ i, y i t + ∫ s in (0 : ℝ)..t, h (x s))
    (c0 : ℝ) (cy : Fin k → ℝ) (hc0 : 0 ≤ c0) (hcy : ∀ i, 0 ≤ cy i) (h0 : |x 0| ≤ c0)
    (hy : ∀ i, ∀ s ∈ Set.Icc (0:ℝ) T, |y i s| ≤ cy i) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      |x t| ≤ (c0 + ∑ i, cy i + |h 0| * T + 1) * Real.exp (c * T) := by
  set F : ℝ → ℝ := fun t => x (max t 0)
  have hFm : Measurable F := mht55_cadlag_meas x hx
  obtain ⟨B, hB⟩ := mht55_cadlag_bdd x hx T
  have hFB : ∀ s ∈ Set.Icc (0:ℝ) T, |F s| ≤ B := by
    intro s hs; simp only [F, max_eq_left hs.1]; exact hB s hs
  have hhc : Continuous h := by
    have : LipschitzWith ⟨c, hc.le⟩ h := LipschitzWith.of_dist_le_mul fun a b => by
      rw [Real.dist_eq, Real.dist_eq]; exact hLip a b
    exact this.continuous
  have hhx : ∀ s, |h s| ≤ |h 0| + c * |s| := by
    intro s
    have := hLip s 0
    simp only [sub_zero] at this
    have := abs_sub_abs_le_abs_sub (h s) (h 0)
    linarith
  set g : ℝ → ℝ := fun s => |F s|
  have hgm : Measurable g := continuous_abs.measurable.comp hFm
  have hgi : IntegrableOn g (Set.Icc 0 T) :=
    mht55_intOn g hgm T B (fun s hs => by simpa [g] using hFB s hs)
  have hhFi : IntegrableOn (fun s => h (F s)) (Set.Icc 0 T) :=
    mht55_intOn _ (hhc.measurable.comp hFm) T (|h 0| + c * B) (fun s hs =>
      le_trans (hhx _) (by nlinarith [hFB s hs]))
  set ε0 := c0 + ∑ i, cy i + |h 0| * T + 1
  have hε0 : 0 < ε0 := by
    have : 0 ≤ ∑ i, cy i := Finset.sum_nonneg fun i _ => hcy i
    positivity
  have hG := MartingaleHT.InfiniteServer.lemma_4_1 g T ε0 c hε0 hc hgm hgi ?_
  · intro t ht
    have := hG t ht
    simp only [g, F, max_eq_left ht.1] at this
    refine le_trans this (mul_le_mul_of_nonneg_left ?_ hε0.le)
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hc.le)
  intro t ht
  refine ⟨abs_nonneg _, ?_⟩
  have ht0 : 0 ≤ t := ht.1
  have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  have hgt : g t = |x t| := by simp [g, F, max_eq_left ht0]
  have hcongr : ∫ s in (0:ℝ)..t, h (x s) = ∫ s in (0:ℝ)..t, h (F s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht0] at hs
    simp [F, max_eq_left hs.1]
  have hII1 : IntervalIntegrable (fun s => |h (F s)|) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]
    exact (hhFi.mono_set hsub).abs
  have hII2 : IntervalIntegrable (fun s => |h 0| + c * g s) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]
    exact (integrableOn_const (by simp)).add ((hgi.mono_set hsub).const_mul c)
  have hIg : IntervalIntegrable g volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]; exact hgi.mono_set hsub
  have hint : |∫ s in (0:ℝ)..t, h (F s)| ≤ |h 0| * t + c * ∫ s in (0:ℝ)..t, g s := by
    calc |∫ s in (0:ℝ)..t, h (F s)| ≤ ∫ s in (0:ℝ)..t, |h (F s)| := by
          have := intervalIntegral.norm_integral_le_integral_norm (f := fun s => h (F s))
            (μ := volume) ht0
          simpa [Real.norm_eq_abs] using this
      _ ≤ ∫ s in (0:ℝ)..t, (|h 0| + c * g s) :=
          intervalIntegral.integral_mono_on ht0 hII1 hII2 fun s _ => hhx _
      _ = |h 0| * t + c * ∫ s in (0:ℝ)..t, g s := by
          rw [intervalIntegral.integral_add intervalIntegrable_const (hIg.const_mul c),
            intervalIntegral.integral_const_mul]
          simp [mul_comm]
  have hsumY : |∑ i, y i t| ≤ ∑ i, cy i := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
    exact hy i t ht
  rw [hgt, hrep t ht0, hcongr]
  have hT' : |h 0| * t ≤ |h 0| * T := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _)
  have h0' : |x 0| ≤ c0 := h0
  have := abs_add_three (x 0) (∑ i, y i t) (∫ s in (0:ℝ)..t, h (F s))
  simp only [ε0]
  linarith

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (h : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hLip : ∀ s₁ s₂ : ℝ, |h s₁ - h s₂| ≤ c * |s₁ - s₂|)
    (X : ℕ → Ω → ℝ → ℝ) (Y : ℕ → Fin k → Ω → ℝ → ℝ)
    (hXcad : ∀ n : ℕ, 1 ≤ n → ∀ ω, IsCadlag (X n ω))
    (hYcad : ∀ n : ℕ, 1 ≤ n → ∀ i ω, IsCadlag (Y n i ω))
    (hXmeas : ∀ n : ℕ, 1 ≤ n → ∀ t, Measurable (fun ω => X n ω t))
    (hYmeas : ∀ n : ℕ, 1 ≤ n → ∀ i t, Measurable (fun ω => Y n i ω t))
    (hrep : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      X n ω t = X n ω 0 + ∑ i, Y n i ω t + ∫ s in (0 : ℝ)..t, h (X n ω s))
    (hX0 : IsSBReal P (fun n ω => X n ω 0))
    (hY : ∀ i, IsSBD P (fun n ω t (_ : Fin 1) => Y n i ω t)) :
    IsSBD P (fun n ω t (_ : Fin 1) => X n ω t) := by
  intro T hT ε hε
  set δ : ℝ := ε / ((k:ℝ) + 1)
  have hδ : 0 < δ := by positivity
  obtain ⟨c0, hc0⟩ := hX0 δ hδ
  have hYc := fun i => hY i T hT δ hδ
  choose cY hcY using hYc
  set ε0 := max c0 0 + ∑ i, max (cY i) 0 + |h 0| * T + 1
  refine ⟨ε0 * Real.exp (c * T), fun n hn => ?_⟩
  set bad : Set Ω := {ω | ¬ ∀ t : ℝ, 0 ≤ t →
      X n ω t = X n ω 0 + ∑ i, Y n i ω t + ∫ s in (0 : ℝ)..t, h (X n ω s)}
  have hbad : P bad = 0 := by
    have := hrep n hn
    rw [ae_iff] at this; exact this
  have hsubset : {ω | ENNReal.ofReal (ε0 * Real.exp (c * T)) <
      supDist (fun t (_ : Fin 1) => X n ω t) 0 T} ⊆
      ({ω | c0 < |X n ω 0|} ∪ ⋃ i, {ω | ENNReal.ofReal (cY i) <
        supDist (fun t (_ : Fin 1) => Y n i ω t) 0 T}) ∪ bad := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists,
      not_lt, not_not, bad] at hcon
    obtain ⟨⟨h0, hYi⟩, hrepω⟩ := hcon
    have hYb : ∀ i, ∀ s ∈ Set.Icc (0:ℝ) T, |Y n i ω s| ≤ max (cY i) 0 := by
      intro i s hs
      have h1 : ENNReal.ofReal (∑ j : Fin 1, |Y n i ω s - (0 : ℝ → Fin 1 → ℝ) s j|)
          ≤ supDist (fun t (_ : Fin 1) => Y n i ω t) 0 T := by
        unfold supDist
        exact le_iSup₂_of_le (f := fun (s : ℝ) (_ : s ∈ Set.Icc 0 T) =>
          ENNReal.ofReal (∑ j : Fin 1, |Y n i ω s - (0 : ℝ → Fin 1 → ℝ) s j|)) s hs le_rfl
      have h2 := le_trans h1 (le_trans (hYi i) (ENNReal.ofReal_le_ofReal (le_max_left _ 0)))
      have h3 := (ENNReal.ofReal_le_ofReal_iff (le_max_right (cY i) 0)).1 h2
      simpa using h3
    have hb := mht55_path_bound h c hc hLip (X n ω) (fun i => Y n i ω) (hXcad n hn ω) T hT
      hrepω (max c0 0) (fun i => max (cY i) 0) (le_max_right _ _) (fun i => le_max_right _ _)
      (le_trans h0 (le_max_left _ _)) hYb
    have hle : supDist (fun t (_ : Fin 1) => X n ω t) 0 T ≤
        ENNReal.ofReal (ε0 * Real.exp (c * T)) := by
      unfold supDist
      refine iSup₂_le fun s hs => ENNReal.ofReal_le_ofReal ?_
      have := hb s hs
      simp only [Finset.univ_unique, Fin.default_eq_zero,
        Finset.sum_singleton, Pi.zero_apply, sub_zero]
      exact this
    exact absurd hω (not_lt.2 hle)
  calc P {ω | ENNReal.ofReal (ε0 * Real.exp (c * T)) <
        supDist (fun t (_ : Fin 1) => X n ω t) 0 T}
      ≤ P (({ω | c0 < |X n ω 0|} ∪ ⋃ i, {ω | ENNReal.ofReal (cY i) <
        supDist (fun t (_ : Fin 1) => Y n i ω t) 0 T}) ∪ bad) := measure_mono hsubset
    _ ≤ P {ω | c0 < |X n ω 0|} + ∑ i, P {ω | ENNReal.ofReal (cY i) <
        supDist (fun t (_ : Fin 1) => Y n i ω t) 0 T} + P bad := by
        exact le_trans (measure_union_le _ _) (add_le_add (le_trans (measure_union_le _ _)
          (add_le_add le_rfl (measure_iUnion_fintype_le _ _))) le_rfl)
    _ ≤ ENNReal.ofReal δ + ∑ _i : Fin k, ENNReal.ofReal δ + 0 := by
        rw [hbad]
        gcongr with i
        · exact hc0 n hn
        · exact hcY i n hn
    _ = ENNReal.ofReal ε := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, add_zero, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add hδ.le (by positivity)]
        congr 1
        simp only [δ]
        field_simp
        ring
