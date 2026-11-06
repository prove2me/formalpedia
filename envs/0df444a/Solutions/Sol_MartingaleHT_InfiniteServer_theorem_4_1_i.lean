-- Prove2me | solution 1 for MartingaleHT.InfiniteServer.theorem_4_1_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:33:32.475712+00:00
-- url     : https://prove2.me/submissions/1a05064b-6c3a-46ae-a6c2-a59c2ad1572c

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
lemma mht41_cadlag_bdd (x : ℝ → ℝ) (hx : IsCadlag x) (T : ℝ) :
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
lemma mht41_cadlag_meas (x : ℝ → ℝ) (hx : IsCadlag x) :
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

lemma mht41_intOn (f : ℝ → ℝ) (hf : Measurable f) (T B : ℝ)
    (hB : ∀ s ∈ Set.Icc (0:ℝ) T, |f s| ≤ B) : IntegrableOn f (Set.Icc 0 T) := by
  refine Measure.integrableOn_of_bounded (M := B) (by simp) hf.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall fun s hs => by simpa [Real.norm_eq_abs] using hB s hs

/-- Frozen path bound: `x(max s 0)` is bounded on every half-line `(-∞, T]`. -/
lemma mht41_frozen_bdd (x : ℝ → ℝ) (hx : IsCadlag x) (T : ℝ) :
    ∃ B : ℝ, ∀ s, s ≤ T → |x (max s 0)| ≤ B := by
  obtain ⟨B, hB⟩ := mht41_cadlag_bdd x hx (max T 0)
  exact ⟨B, fun s hs => hB _ ⟨le_max_right _ _, max_le_max_right 0 hs⟩⟩

lemma mht41_intg (h : ℝ → ℝ) (c : ℝ) (hhc : Continuous h)
    (hhx : ∀ s, |h s| ≤ |h 0| + c * |s|) (hc : 0 ≤ c)
    (F : ℝ → ℝ) (hFm : Measurable F) (hFb : ∀ T, ∃ B : ℝ, ∀ s, s ≤ T → |F s| ≤ B)
    (w : ℝ → ℝ) (a b : ℝ) (hw : ContinuousOn w (Set.uIcc a b)) :
    IntervalIntegrable (fun s => h (F s + w s)) volume a b := by
  rw [intervalIntegrable_iff]
  obtain ⟨Cw, hCw⟩ := isCompact_uIcc.exists_bound_of_continuousOn hw
  obtain ⟨B, hB⟩ := hFb (max a b)
  have hsub : Set.uIoc a b ⊆ Set.uIcc a b := Set.uIoc_subset_uIcc
  show Integrable _ (volume.restrict (Set.uIoc a b))
  rw [← integrableOn_univ]
  refine Measure.integrableOn_of_bounded (M := |h 0| + c * (B + Cw)) ?_ ?_ ?_
  · rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Set.uIoc]; simp
  · exact (hhc.comp_aestronglyMeasurable
      (hFm.aestronglyMeasurable.add (hw.aestronglyMeasurable measurableSet_uIcc))).mono_set hsub
  · rw [Measure.restrict_univ]
    refine ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_
    have hs' := hsub hs
    have h1 : |F s| ≤ B := hB s (Set.mem_uIcc.1 hs' |>.elim (fun h => le_trans h.2 (le_max_right _ _))
      (fun h => le_trans h.2 (le_max_left _ _)))
    have h2 : |w s| ≤ Cw := by simpa [Real.norm_eq_abs] using hCw s hs'
    rw [Real.norm_eq_abs]
    refine le_trans (hhx _) ?_
    have := abs_add_le (F s) (w s)
    nlinarith

noncomputable def mht41_pic (h : ℝ → ℝ) (F : ℝ → ℝ) (b : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => b
  | m + 1 => fun t => b + ∫ s in (0:ℝ)..t, h (F s + mht41_pic h F b m s)

/-- Comparison lemma (Gronwall), used for uniqueness and continuity of the solution map. -/
lemma mht41_cmp (h : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hLip : ∀ s₁ s₂ : ℝ, |h s₁ - h s₂| ≤ c * |s₁ - s₂|)
    (x₁ x₂ : ℝ → ℝ) (h₁ : IsCadlag x₁) (h₂ : IsCadlag x₂) (T ε : ℝ) (hε : 0 < ε)
    (e : ℝ → ℝ) (he : ∀ t ∈ Set.Icc (0:ℝ) T, |e t| ≤ ε)
    (heq : ∀ t ∈ Set.Icc (0:ℝ) T, x₁ t - x₂ t =
      e t + ((∫ s in (0:ℝ)..t, h (x₁ s)) - ∫ s in (0:ℝ)..t, h (x₂ s))) :
    ∀ t ∈ Set.Icc (0:ℝ) T, |x₁ t - x₂ t| ≤ ε * Real.exp (c * T) := by
  have hhc : Continuous h := by
    have : LipschitzWith ⟨c, hc.le⟩ h := LipschitzWith.of_dist_le_mul fun a b => by
      rw [Real.dist_eq, Real.dist_eq]; exact hLip a b
    exact this.continuous
  set F₁ : ℝ → ℝ := fun t => x₁ (max t 0)
  set F₂ : ℝ → ℝ := fun t => x₂ (max t 0)
  have hF₁ : Measurable F₁ := mht41_cadlag_meas x₁ h₁
  have hF₂ : Measurable F₂ := mht41_cadlag_meas x₂ h₂
  obtain ⟨B₁, hB₁⟩ := mht41_cadlag_bdd x₁ h₁ T
  obtain ⟨B₂, hB₂⟩ := mht41_cadlag_bdd x₂ h₂ T
  have hhx : ∀ s, |h s| ≤ |h 0| + c * |s| := by
    intro s
    have := hLip s 0
    simp only [sub_zero] at this
    have := abs_sub_abs_le_abs_sub (h s) (h 0)
    linarith
  set g : ℝ → ℝ := fun s => |F₁ s - F₂ s|
  have hgm : Measurable g := continuous_abs.measurable.comp (hF₁.sub hF₂)
  have hgi : IntegrableOn g (Set.Icc 0 T) := by
    refine mht41_intOn g hgm T (B₁ + B₂) fun s hs => ?_
    simp only [g, F₁, F₂, max_eq_left hs.1, abs_abs]
    have := abs_sub (x₁ s) (x₂ s)
    linarith [hB₁ s hs, hB₂ s hs]
  have hi₁ : IntegrableOn (fun s => h (F₁ s)) (Set.Icc 0 T) :=
    mht41_intOn _ (hhc.measurable.comp hF₁) T (|h 0| + c * B₁) fun s hs => by
      refine le_trans (hhx _) ?_
      have := hB₁ s hs
      simp only [F₁, max_eq_left hs.1]; nlinarith
  have hi₂ : IntegrableOn (fun s => h (F₂ s)) (Set.Icc 0 T) :=
    mht41_intOn _ (hhc.measurable.comp hF₂) T (|h 0| + c * B₂) fun s hs => by
      refine le_trans (hhx _) ?_
      have := hB₂ s hs
      simp only [F₂, max_eq_left hs.1]; nlinarith
  have hG := MartingaleHT.InfiniteServer.lemma_4_1 g T ε c hε hc hgm hgi ?_
  · intro t ht
    have := hG t ht
    simp only [g, F₁, F₂, max_eq_left ht.1] at this
    refine le_trans this (mul_le_mul_of_nonneg_left ?_ hε.le)
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hc.le)
  intro t ht
  refine ⟨abs_nonneg _, ?_⟩
  have ht0 : 0 ≤ t := ht.1
  have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  have hgt : g t = |x₁ t - x₂ t| := by simp [g, F₁, F₂, max_eq_left ht0]
  have hc1 : ∫ s in (0:ℝ)..t, h (x₁ s) = ∫ s in (0:ℝ)..t, h (F₁ s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht0] at hs
    simp [F₁, max_eq_left hs.1]
  have hc2 : ∫ s in (0:ℝ)..t, h (x₂ s) = ∫ s in (0:ℝ)..t, h (F₂ s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht0] at hs
    simp [F₂, max_eq_left hs.1]
  have hI₁ : IntervalIntegrable (fun s => h (F₁ s)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]; exact hi₁.mono_set hsub
  have hI₂ : IntervalIntegrable (fun s => h (F₂ s)) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]; exact hi₂.mono_set hsub
  have hIg : IntervalIntegrable g volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]; exact hgi.mono_set hsub
  have hint : |(∫ s in (0:ℝ)..t, h (F₁ s)) - ∫ s in (0:ℝ)..t, h (F₂ s)|
      ≤ c * ∫ s in (0:ℝ)..t, g s := by
    rw [← intervalIntegral.integral_sub hI₁ hI₂]
    calc |∫ s in (0:ℝ)..t, (h (F₁ s) - h (F₂ s))|
        ≤ ∫ s in (0:ℝ)..t, |h (F₁ s) - h (F₂ s)| := by
          have := intervalIntegral.norm_integral_le_integral_norm
            (f := fun s => h (F₁ s) - h (F₂ s)) (μ := volume) ht0
          simpa [Real.norm_eq_abs] using this
      _ ≤ ∫ s in (0:ℝ)..t, c * g s :=
          intervalIntegral.integral_mono_on ht0 (hI₁.sub hI₂).abs (hIg.const_mul c)
            fun s _ => hLip _ _
      _ = c * ∫ s in (0:ℝ)..t, g s := intervalIntegral.integral_const_mul _ _
  rw [hgt, heq t ht, hc1, hc2]
  have := abs_add_le (e t) ((∫ s in (0:ℝ)..t, h (F₁ s)) - ∫ s in (0:ℝ)..t, h (F₂ s))
  linarith [he t ht]

/-- Existence of a solution in `D`. -/
lemma mht41_exists (h : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hLip : ∀ s₁ s₂ : ℝ, |h s₁ - h s₂| ≤ c * |s₁ - s₂|)
    (y : ℝ → ℝ) (b : ℝ) (hy : IsCadlag y) : ∃ x : ℝ → ℝ, SolvesIntegralRep h b y x := by
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
  set F : ℝ → ℝ := fun t => y (max t 0) with hFdef
  have hFm : Measurable F := mht41_cadlag_meas y hy
  have hFb : ∀ T, ∃ B : ℝ, ∀ s, s ≤ T → |F s| ≤ B := mht41_frozen_bdd y hy
  set p := mht41_pic h F b with hp
  have hp0 : ∀ t, p 0 t = b := fun t => rfl
  have hpS : ∀ m t, p (m+1) t = b + ∫ s in (0:ℝ)..t, h (F s + p m s) := fun m t => rfl
  have hint : ∀ (w : ℝ → ℝ) (a b' : ℝ), ContinuousOn w (Set.uIcc a b') →
      IntervalIntegrable (fun s => h (F s + w s)) volume a b' :=
    fun w a b' hw => mht41_intg h c hhc hhx hc.le F hFm hFb w a b' hw
  have hpc : ∀ m, Continuous (p m) := by
    intro m
    induction m with
    | zero => exact continuous_const
    | succ m ih =>
      have : p (m+1) = fun t => b + ∫ s in (0:ℝ)..t, h (F s + p m s) := rfl
      rw [this]
      exact continuous_const.add (intervalIntegral.continuous_primitive
        (fun a b' => hint (p m) a b' ih.continuousOn) 0)
  -- factorial bound on successive differences
  have hdiff : ∀ T : ℝ, 0 ≤ T → ∃ K : ℝ, 0 ≤ K ∧ ∀ m, ∀ t ∈ Set.Icc (0:ℝ) T,
      |p (m+1) t - p m t| ≤ K * (c * t) ^ m / (m.factorial) := by
    intro T hT
    obtain ⟨K₀, hK₀⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn
      ((hpc 1).sub (hpc 0)).continuousOn
    refine ⟨max K₀ 0, le_max_right _ _, fun m => ?_⟩
    induction m with
    | zero =>
      intro t ht
      have := hK₀ t ht
      simp only [Real.norm_eq_abs, Pi.sub_apply] at this
      simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
      exact le_trans this (le_max_left _ _)
    | succ m ih =>
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have hI1 := hint (p (m+1)) 0 t (hpc _).continuousOn
      have hI2 := hint (p m) 0 t (hpc _).continuousOn
      rw [hpS (m+1) t, hpS m t, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub hI1 hI2]
      have hpoly : IntervalIntegrable (fun s : ℝ => c * (max K₀ 0 * (c * s) ^ m / (m.factorial)))
          volume 0 t := by
        apply Continuous.intervalIntegrable; fun_prop
      calc |∫ s in (0:ℝ)..t, (h (F s + p (m+1) s) - h (F s + p m s))|
          ≤ ∫ s in (0:ℝ)..t, |h (F s + p (m+1) s) - h (F s + p m s)| := by
            have := intervalIntegral.norm_integral_le_integral_norm
              (f := fun s => h (F s + p (m+1) s) - h (F s + p m s)) (μ := volume) ht0
            simpa [Real.norm_eq_abs] using this
        _ ≤ ∫ s in (0:ℝ)..t, c * (max K₀ 0 * (c * s) ^ m / (m.factorial)) := by
            refine intervalIntegral.integral_mono_on ht0 (hI1.sub hI2).abs hpoly fun s hs => ?_
            have h1 := hLip (F s + p (m+1) s) (F s + p m s)
            rw [add_sub_add_left_eq_sub] at h1
            have h2 := ih s ⟨hs.1, le_trans hs.2 ht.2⟩
            exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hc.le)
        _ = max K₀ 0 * (c * t) ^ (m+1) / ((m+1).factorial) := by
            have e : (fun s : ℝ => c * (max K₀ 0 * (c * s) ^ m / (m.factorial))) =
                fun s => (c * max K₀ 0 * c ^ m / (m.factorial)) * s ^ m := by
              funext s; rw [mul_pow]; ring
            rw [e, intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
            push_cast
            have : (m.factorial : ℝ) ≠ 0 := by positivity
            field_simp
            ring
  -- the limit
  set z : ℝ → ℝ := fun t => b + ∑' m, (p (m+1) t - p m t) with hz
  have hconv : ∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn (fun N => p N) z atTop (Set.Icc 0 T) := by
    intro T hT
    obtain ⟨K, hK0, hK⟩ := hdiff T hT
    have hsum : Summable (fun m : ℕ => K * (c * T) ^ m / (m.factorial)) := by
      have := (Real.summable_pow_div_factorial (c * T)).mul_left K
      simpa [mul_div_assoc] using this
    have H := tendstoUniformlyOn_tsum_nat (f := fun m t => p (m+1) t - p m t) hsum
      (s := Set.Icc 0 T) (fun m t ht => by
        rw [Real.norm_eq_abs]
        refine le_trans (hK m t ht) ?_
        gcongr
        · have := ht.1; positivity
        · exact ht.2)
    rw [Metric.tendstoUniformlyOn_iff] at H ⊢
    intro e he
    filter_upwards [H e he] with N hN t ht
    have := hN t ht
    have htel : ∑ n ∈ Finset.range N, (p (n+1) t - p n t) = p N t - b := by
      rw [Finset.sum_range_sub (fun n => p n t), hp0]
    rw [htel] at this
    rw [Real.dist_eq] at this ⊢
    simp only [hz]
    convert this using 2; ring
  have hzc : ContinuousOn z (Set.Ici 0) := by
    intro t ht
    have ht0 : (0:ℝ) ≤ t := ht
    have hco : ContinuousOn z (Set.Icc 0 (t+1)) :=
      (hconv (t+1) (by linarith)).continuousOn
        (Frequently.of_forall fun N => (hpc N).continuousOn)
    have hmem : Set.Icc (0:ℝ) (t+1) ∈ 𝓝[Set.Ici 0] t := by
      rw [← Set.Ici_inter_Iic]
      exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
    exact (hco t ⟨ht0, by linarith⟩).mono_of_mem_nhdsWithin hmem
  -- the equation for z
  have hzeq : ∀ t, 0 ≤ t → z t = b + ∫ s in (0:ℝ)..t, h (F s + z s) := by
    intro t ht
    have hT := hconv t ht
    have h1 : Tendsto (fun N => p (N+1) t) atTop (𝓝 (z t)) :=
      (hT.tendsto_at (Set.right_mem_Icc.2 ht)).comp (tendsto_add_atTop_nat 1)
    have hzI : IntervalIntegrable (fun s => h (F s + z s)) volume 0 t :=
      hint z 0 t (by rw [Set.uIcc_of_le ht]; exact hzc.mono fun s hs => hs.1)
    have h2 : Tendsto (fun N => p (N+1) t) atTop
        (𝓝 (b + ∫ s in (0:ℝ)..t, h (F s + z s))) := by
      simp only [hpS]
      refine tendsto_const_nhds.add ?_
      rw [Metric.tendsto_atTop]
      intro e he
      have hUe := Metric.tendstoUniformlyOn_iff.1 hT (e / (c * t + 1)) (by positivity)
      obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hUe
      refine ⟨N₀, fun N hN => ?_⟩
      have hI := hint (p N) 0 t (hpc N).continuousOn
      rw [Real.dist_eq, ← intervalIntegral.integral_sub hI hzI]
      have hb : ∀ s ∈ Set.uIoc (0:ℝ) t, ‖h (F s + p N s) - h (F s + z s)‖ ≤ c * (e / (c * t + 1)) := by
        intro s hs
        rw [Set.uIoc_of_le ht] at hs
        have h3 := hLip (F s + p N s) (F s + z s)
        rw [add_sub_add_left_eq_sub] at h3
        have h4 := hN₀ N hN s ⟨hs.1.le, hs.2⟩
        rw [Real.dist_eq, abs_sub_comm] at h4
        rw [Real.norm_eq_abs]
        exact le_trans h3 (mul_le_mul_of_nonneg_left h4.le hc.le)
      have := intervalIntegral.norm_integral_le_of_norm_le_const hb
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at this
      refine lt_of_le_of_lt this ?_
      rw [mul_div_assoc', div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    exact tendsto_nhds_unique h1 h2
  refine ⟨fun t => y t + z t, ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    exact (hy.1 t ht).add ((hzc t ht).mono fun s (hs : t ≤ s) => le_trans ht hs)
  · intro t ht
    obtain ⟨l, hl⟩ := hy.2 t ht
    refine ⟨l + z t, hl.add ?_⟩
    have : ContinuousAt z t := hzc.continuousAt (Ici_mem_nhds ht)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  · intro t ht
    show y t + z t = b + y t + ∫ s in (0:ℝ)..t, h (y s + z s)
    rw [hzeq t ht]
    have : ∫ s in (0:ℝ)..t, h (y s + z s) = ∫ s in (0:ℝ)..t, h (F s + z s) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le ht] at hs
      simp [F, max_eq_left hs.1]
    rw [this]; ring

lemma mht41_cont (h : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hLip : ∀ s₁ s₂ : ℝ, |h s₁ - h s₂| ≤ c * |s₁ - s₂|)
    (y : ℝ → ℝ) (b : ℝ) (hy : ContinuousOn y (Set.Ici 0)) (x : ℝ → ℝ)
    (hx : SolvesIntegralRep h b y x) : ContinuousOn x (Set.Ici 0) := by
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
  set F : ℝ → ℝ := fun t => x (max t 0)
  have hFm : Measurable F := mht41_cadlag_meas x hx.1
  have hFb := mht41_frozen_bdd x hx.1
  have hI : ∀ a b', IntervalIntegrable (fun s => h (F s)) volume a b' := by
    intro a b'
    have := mht41_intg h c hhc hhx hc.le F hFm hFb (fun _ => 0) a b' continuousOn_const
    simpa using this
  have hG : Continuous fun t => ∫ s in (0:ℝ)..t, h (F s) :=
    intervalIntegral.continuous_primitive hI 0
  have heq : Set.EqOn x (fun t => b + y t + ∫ s in (0:ℝ)..t, h (F s)) (Set.Ici 0) := by
    intro t (ht : 0 ≤ t)
    rw [hx.2 t ht]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht] at hs
    simp [F, max_eq_left hs.1]
  exact ContinuousOn.congr (f := fun t => b + y t + ∫ s in (0:ℝ)..t, h (F s))
    ((continuousOn_const.add hy).add hG.continuousOn) heq

theorem solution (h : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hLip : ∀ s₁ s₂ : ℝ, |h s₁ - h s₂| ≤ c * |s₁ - s₂|) (h0 : h 0 = 0) :
    (∀ (y : ℝ → ℝ) (b : ℝ), IsCadlag y →
      (∃ x : ℝ → ℝ, SolvesIntegralRep h b y x) ∧
      (∀ x₁ x₂ : ℝ → ℝ, SolvesIntegralRep h b y x₁ → SolvesIntegralRep h b y x₂ →
        ∀ t : ℝ, 0 ≤ t → x₁ t = x₂ t) ∧
      (ContinuousOn y (Set.Ici 0) → ∀ x : ℝ → ℝ, SolvesIntegralRep h b y x →
        ContinuousOn x (Set.Ici 0))) ∧
    ∀ (yn : ℕ → ℝ → ℝ) (bn : ℕ → ℝ) (xn : ℕ → ℝ → ℝ) (y : ℝ → ℝ) (b : ℝ) (x : ℝ → ℝ),
      (∀ n, IsCadlag (yn n)) → IsCadlag y →
      (∀ n, SolvesIntegralRep h (bn n) (yn n) (xn n)) → SolvesIntegralRep h b y x →
      Tendsto bn atTop (𝓝 b) →
      (∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn yn y atTop (Set.Icc 0 T)) →
      ∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn xn x atTop (Set.Icc 0 T) := by
  refine ⟨fun y b hy => ⟨mht41_exists h c hc hLip y b hy, ?_,
    fun hyc x hx => mht41_cont h c hc hLip y b hyc x hx⟩, ?_⟩
  · intro x₁ x₂ h₁ h₂ t ht
    have key : ∀ ε : ℝ, 0 < ε → |x₁ t - x₂ t| ≤ ε * Real.exp (c * t) := by
      intro ε hε
      refine mht41_cmp h c hc hLip x₁ x₂ h₁.1 h₂.1 t ε hε (fun _ => 0)
        (fun _ _ => by simp [hε.le]) (fun s hs => ?_) t ⟨ht, le_rfl⟩
      rw [h₁.2 s hs.1, h₂.2 s hs.1]; ring
    have hle : |x₁ t - x₂ t| ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have := key (ε / Real.exp (c * t)) (by positivity)
      rw [div_mul_cancel₀ _ (Real.exp_pos _).ne'] at this
      linarith
    have := abs_nonneg (x₁ t - x₂ t)
    have : x₁ t - x₂ t = 0 := abs_eq_zero.1 (le_antisymm hle this)
    linarith
  · intro yn bn xn y b x hyn hy hxn hx hb hyconv T hT
    rw [Metric.tendstoUniformlyOn_iff]
    intro e he
    set η := e / (3 * Real.exp (c * T)) with hη
    have hηpos : 0 < η := by positivity
    have hb' : ∀ᶠ n in atTop, |bn n - b| < η := by
      have := (Metric.tendsto_nhds.1 hb) η hηpos
      filter_upwards [this] with n hn
      rwa [Real.dist_eq] at hn
    have hy' := Metric.tendstoUniformlyOn_iff.1 (hyconv T hT) η hηpos
    filter_upwards [hb', hy'] with n hbn hyn' t ht
    have hcm := mht41_cmp h c hc hLip (xn n) x (hxn n).1 hx.1 T (|bn n - b| + η)
      (by positivity) (fun s => (bn n - b) + (yn n s - y s))
      (fun s hs => by
        have := hyn' s hs
        rw [Real.dist_eq, abs_sub_comm] at this
        have := abs_add_le (bn n - b) (yn n s - y s)
        linarith)
      (fun s hs => by rw [(hxn n).2 s hs.1, hx.2 s hs.1]; ring) t ht
    rw [Real.dist_eq, abs_sub_comm]
    refine lt_of_le_of_lt hcm ?_
    have hE := Real.exp_pos (c * T)
    have : (|bn n - b| + η) * Real.exp (c * T) < (2 * η) * Real.exp (c * T) :=
      mul_lt_mul_of_pos_right (by linarith) hE
    have h3 : 2 * η * Real.exp (c * T) = 2 * e / 3 := by
      rw [hη]; field_simp
    linarith
