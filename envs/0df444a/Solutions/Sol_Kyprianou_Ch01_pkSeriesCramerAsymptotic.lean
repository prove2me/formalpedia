-- Prove2me | solution 1 for Kyprianou.Ch01.pkSeriesCramerAsymptotic
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T18:25:39.147494+00:00
-- url     : https://prove2.me/submissions/bfe516d5-45c8-4908-a81e-260e768891dc

import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_QueueingFundamentals_MG1_transforms
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Topology.Order.Monotone

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter QueueingFundamentals.MG1
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false

private lemma integratedTail_eq_withDensity_cr
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (mu : ℝ) (hmu : 0 < mu)
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hetaSupport : eta (Set.Iio (0 : ℝ)) = 0)
    (heta : ∀ x : ℝ, 0 ≤ x → (eta (Set.Iic x)).toReal = integratedTailCDF F mu x) :
    eta = (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun y : ℝ => ENNReal.ofReal ((1 / mu) * (F (Set.Ioi y)).toReal)) := by
  let ν : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun y : ℝ => ENNReal.ofReal ((1 / mu) * (F (Set.Ioi y)).toReal))
  have hν_Iic : ∀ x : ℝ, ν (Set.Iic x) = eta (Set.Iic x) := by
    intro x
    by_cases hx : 0 ≤ x
    · have h1 : ν (Set.Iic x) =
          ∫⁻ y in Set.Ioc (0 : ℝ) x, ENNReal.ofReal ((1 / mu) * (F (Set.Ioi y)).toReal) ∂volume := by
        dsimp only [ν]
        rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
        have hSet : Set.Iic x ∩ Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) x := by
          ext y; simp [Set.mem_Ioc, Set.mem_Iic, Set.mem_Ioi, and_comm]
        rw [hSet]
      have hint_Ioc : IntegrableOn (fun y : ℝ => (1 / mu) * (F (Set.Ioi y)).toReal)
          (Set.Ioc (0 : ℝ) x) := by
        have hanti : Antitone (fun y : ℝ => (F (Set.Ioi y)).toReal) := fun a b hab =>
          ENNReal.toReal_mono (measure_ne_top F _) (measure_mono (Set.Ioi_subset_Ioi hab))
        refine (integrableOn_const (C := 1 / mu) (hs := measure_Ioc_lt_top.ne)).mono'
          ((measurable_const.mul hanti.measurable).aestronglyMeasurable) ?_
        filter_upwards with y
        have h0 : 0 ≤ (F (Set.Ioi y)).toReal := ENNReal.toReal_nonneg
        have hle1 : (F (Set.Ioi y)).toReal ≤ 1 :=
          ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := F) (s := Set.Ioi y))
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) h0)]
        nlinarith [div_pos one_pos hmu]
      have hnonneg : ∀ y : ℝ, 0 ≤ (1 / mu) * (F (Set.Ioi y)).toReal := fun y =>
        mul_nonneg (by positivity) ENNReal.toReal_nonneg
      rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint_Ioc (Filter.Eventually.of_forall hnonneg),
        integral_const_mul]
      change ENNReal.ofReal (integratedTailCDF F mu x) = eta (Set.Iic x)
      rw [← heta x hx, ENNReal.ofReal_toReal (measure_ne_top eta _)]
    · have hlt : x < 0 := lt_of_not_ge hx
      have hν0 : ν (Set.Iic x) = 0 := by
        dsimp only [ν]
        rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
        have hemp : Set.Iic x ∩ Set.Ioi (0 : ℝ) = ∅ := by
          ext y; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
          intro ⟨h1, h2⟩; linarith
        rw [hemp, Measure.restrict_empty, lintegral_zero_measure]
      have heta0 : eta (Set.Iic x) = 0 :=
        measure_mono_null (fun y hy => lt_of_le_of_lt hy hlt) hetaSupport
      rw [hν0, heta0]
  have hν_prob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    have hUnion : (Set.univ : Set ℝ) = ⋃ n : ℕ, Set.Iic (n : ℝ) := by
      ext x; simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_Iic, true_iff]
      exact exists_nat_ge x
    have hMono : Monotone (fun n : ℕ => Set.Iic (n : ℝ)) := fun m n hmn y hy =>
      Set.mem_Iic.mpr (le_trans (Set.mem_Iic.mp hy) (Nat.cast_le.mpr hmn))
    have h1 := tendsto_measure_iUnion_atTop (μ := ν) hMono
    have h2 := tendsto_measure_iUnion_atTop (μ := eta) hMono
    rw [← hUnion] at h1 h2
    have hEq_seq : (⇑ν ∘ fun n : ℕ => Set.Iic (n : ℝ)) = (⇑eta ∘ fun n : ℕ => Set.Iic (n : ℝ)) :=
      funext fun n => hν_Iic n
    rw [hEq_seq] at h1
    rw [tendsto_nhds_unique h1 h2, measure_univ]
  exact (Measure.ext_of_Iic ν eta hν_Iic).symm

private lemma isProbabilityMeasure_convPow_cr (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ k : ℕ, IsProbabilityMeasure (QueueingFundamentals.MG1.convPow μ k)
  | 0 => by dsimp [QueueingFundamentals.MG1.convPow]; infer_instance
  | k + 1 => by
      haveI : IsProbabilityMeasure (QueueingFundamentals.MG1.convPow μ k) :=
        isProbabilityMeasure_convPow_cr μ k
      dsimp [QueueingFundamentals.MG1.convPow]
      infer_instance

private lemma convPow_Iio_zero_cr (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Set.Iio (0 : ℝ)) = 0) :
    ∀ k : ℕ, QueueingFundamentals.MG1.convPow μ k (Set.Iio (0 : ℝ)) = 0
  | 0 => by
      dsimp [QueueingFundamentals.MG1.convPow]
      rw [Measure.dirac_apply' _ measurableSet_Iio]
      simp
  | k + 1 => by
      haveI : IsProbabilityMeasure (QueueingFundamentals.MG1.convPow μ k) :=
        isProbabilityMeasure_convPow_cr μ k
      have hk := convPow_Iio_zero_cr μ hsupp k
      dsimp [QueueingFundamentals.MG1.convPow]
      rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Iio]
      have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Set.Iio (0 : ℝ) ⊆
          (Set.Iio (0 : ℝ) ×ˢ Set.univ) ∪ (Set.univ ×ˢ Set.Iio (0 : ℝ)) := by
        rintro ⟨a, b⟩ hab
        simp only [Set.mem_preimage, Set.mem_Iio] at hab
        by_cases ha : a < 0
        · exact Or.inl ⟨ha, trivial⟩
        · exact Or.inr ⟨trivial, show b < 0 by linarith⟩
      refine le_antisymm ?_ bot_le
      calc ((QueueingFundamentals.MG1.convPow μ k).prod μ) ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Set.Iio 0)
          ≤ ((QueueingFundamentals.MG1.convPow μ k).prod μ)
              ((Set.Iio (0 : ℝ) ×ˢ Set.univ) ∪ (Set.univ ×ˢ Set.Iio (0 : ℝ))) := measure_mono hsub
        _ ≤ ((QueueingFundamentals.MG1.convPow μ k).prod μ) (Set.Iio (0 : ℝ) ×ˢ Set.univ) +
            ((QueueingFundamentals.MG1.convPow μ k).prod μ) (Set.univ ×ˢ Set.Iio (0 : ℝ)) :=
              measure_union_le _ _
        _ = 0 := by simp [Measure.prod_prod, hk, hsupp]

/-- Cantor diagonal extraction for a sequence of equicontinuous `[0, 1]`-valued functions on `ℝ`. -/
private lemma exists_subseq_tendsto_of_equicont_unit
    (u : ℕ → ℝ → ℝ)
    (hBdd : ∀ k t, 0 ≤ u k t ∧ u k t ≤ 1)
    (hEqui : ∀ ε > 0, ∃ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ t1 t2 : ℝ, |t1 - t2| < δ →
      |u k t1 - u k t2| < ε) :
    ∃ (φ : ℕ → ℕ) (g : ℝ → ℝ),
      StrictMono φ ∧
      (∀ t, 0 ≤ g t ∧ g t ≤ 1) ∧
      Continuous g ∧
      (∀ t, Tendsto (fun k => u (φ k) t) atTop (𝓝 (g t))) := by
  classical
  obtain ⟨q, hq_surj⟩ := exists_surjective_nat ℚ
  have hStep : ∀ (n : ℕ) (s : ℕ → ℕ), StrictMono s →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ L ∈ Set.Icc (0 : ℝ) 1,
        Tendsto (fun k => u (s (τ k)) (q n)) atTop (𝓝 L) := by
    intro n s _
    have hmem : ∀ k, u (s k) (q n) ∈ Set.Icc (0 : ℝ) 1 := fun k => hBdd (s k) (q n)
    obtain ⟨L, hL, τ, hτ_mono, hτ_lim⟩ := isCompact_Icc.tendsto_subseq hmem
    exact ⟨τ, hτ_mono, L, hL, hτ_lim⟩
  let stepFn : (n : ℕ) → {s : ℕ → ℕ // StrictMono s} → {s : ℕ → ℕ // StrictMono s} :=
    fun n s =>
      let h := hStep n s.1 s.2
      ⟨s.1 ∘ h.choose, s.2.comp h.choose_spec.1⟩
  let chain : ℕ → {s : ℕ → ℕ // StrictMono s} :=
    Nat.rec (⟨id, strictMono_id⟩) stepFn
  have hChain_lim : ∀ n : ℕ, ∃ L : ℝ,
      Tendsto (fun k => u ((chain (n + 1)).1 k) (q n)) atTop (𝓝 L) := fun n => by
    have h := hStep n (chain n).1 (chain n).2
    obtain ⟨L, _, hlim⟩ := h.choose_spec.2
    exact ⟨L, hlim⟩
  have hSub : ∀ n d : ℕ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ (chain (n + d)).1 = (chain n).1 ∘ ψ := by
    intro n d
    induction d with
    | zero => exact ⟨id, strictMono_id, rfl⟩
    | succ d ih =>
        obtain ⟨ψ, hψ_mono, hψ_eq⟩ := ih
        let h := hStep (n + d) (chain (n + d)).1 (chain (n + d)).2
        refine ⟨ψ ∘ h.choose, hψ_mono.comp h.choose_spec.1, ?_⟩
        ext k
        change (chain (n + d)).1 (h.choose k) = (chain n).1 (ψ (h.choose k))
        exact congrFun hψ_eq (h.choose k)
  let φ : ℕ → ℕ := fun k => (chain (k + 1)).1 k
  have hφ_mono : StrictMono φ := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    dsimp only [φ]
    obtain ⟨ψ, hψ_mono, hψ_eq⟩ := hSub (k + 1) 1
    have h1 : (chain (k + 2)).1 (k + 1) = (chain (k + 1)).1 (ψ (k + 1)) := congrFun hψ_eq (k + 1)
    rw [h1]
    exact (chain (k + 1)).2 (lt_of_lt_of_le (Nat.lt_succ_self k) (hψ_mono.id_le (k + 1)))
  have hConv_rat : ∀ r : ℚ, ∃ L : ℝ, Tendsto (fun k => u (φ k) (r : ℝ)) atTop (𝓝 L) := by
    intro r
    obtain ⟨n, rfl⟩ := hq_surj r
    obtain ⟨L, hL⟩ := hChain_lim n
    refine ⟨L, ?_⟩
    have hTail : ∀ k ≥ n, ∃ m ≥ k, φ k = (chain (n + 1)).1 m := by
      intro k hk
      obtain ⟨ψ, hψ_mono, hψ_eq⟩ := hSub (n + 1) (k - n)
      have hidx : n + 1 + (k - n) = k + 1 := by omega
      rw [hidx] at hψ_eq
      exact ⟨ψ k, hψ_mono.id_le k, congrFun hψ_eq k⟩
    rw [Metric.tendsto_atTop] at hL ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hL ε hε
    refine ⟨max N n, fun k hk => ?_⟩
    obtain ⟨m, hmk, hEq⟩ := hTail k (le_trans (le_max_right _ _) hk)
    rw [hEq]
    exact hN m (le_trans (le_trans (le_max_left _ _) hk) hmk)
  have hCauchy : ∀ t : ℝ, CauchySeq (fun k => u (φ k) t) := by
    intro t
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨δ, hδ, K, hK⟩ := hEqui (ε / 3) (by positivity)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show t - δ < t + δ by linarith)
    have htr : |t - (r : ℝ)| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
    obtain ⟨L, hL⟩ := hConv_rat r
    have hCr := hL.cauchySeq
    rw [Metric.cauchySeq_iff] at hCr
    obtain ⟨N1, hN1⟩ := hCr (ε / 3) (by positivity)
    refine ⟨max K N1, fun m hm n hn => ?_⟩
    have hmK : K ≤ φ m := le_trans (le_max_left _ _) (le_trans hm (hφ_mono.id_le m))
    have hnK : K ≤ φ n := le_trans (le_max_left _ _) (le_trans hn (hφ_mono.id_le n))
    have h1 : |u (φ m) t - u (φ m) (r : ℝ)| < ε / 3 := hK (φ m) hmK t r htr
    have h2 : |u (φ m) (r : ℝ) - u (φ n) (r : ℝ)| < ε / 3 := by
      simpa [Real.dist_eq] using hN1 m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
    have h3 : |u (φ n) (r : ℝ) - u (φ n) t| < ε / 3 := by
      rw [abs_sub_comm]; exact hK (φ n) hnK t r htr
    rw [Real.dist_eq]
    have htri : |u (φ m) t - u (φ n) t| ≤
        |u (φ m) t - u (φ m) (r : ℝ)| + |u (φ m) (r : ℝ) - u (φ n) (r : ℝ)| +
          |u (φ n) (r : ℝ) - u (φ n) t| := by
      calc |u (φ m) t - u (φ n) t|
          = |(u (φ m) t - u (φ m) (r : ℝ)) + ((u (φ m) (r : ℝ) - u (φ n) (r : ℝ)) +
              (u (φ n) (r : ℝ) - u (φ n) t))| := by ring_nf
        _ ≤ |u (φ m) t - u (φ m) (r : ℝ)| + |(u (φ m) (r : ℝ) - u (φ n) (r : ℝ)) +
              (u (φ n) (r : ℝ) - u (φ n) t)| := abs_add_le _ _
        _ ≤ |u (φ m) t - u (φ m) (r : ℝ)| +
              (|u (φ m) (r : ℝ) - u (φ n) (r : ℝ)| + |u (φ n) (r : ℝ) - u (φ n) t|) := by
              gcongr; exact abs_add_le _ _
        _ = _ := by ring
    linarith
  have hConv : ∀ t : ℝ, ∃ L : ℝ, Tendsto (fun k => u (φ k) t) atTop (𝓝 L) := fun t =>
    cauchySeq_tendsto_of_complete (hCauchy t)
  let g : ℝ → ℝ := fun t => (hConv t).choose
  have hg_lim : ∀ t, Tendsto (fun k => u (φ k) t) atTop (𝓝 (g t)) := fun t => (hConv t).choose_spec
  have hg_bdd : ∀ t, 0 ≤ g t ∧ g t ≤ 1 := fun t =>
    ⟨ge_of_tendsto (hg_lim t) (Filter.Eventually.of_forall fun k => (hBdd (φ k) t).1),
     le_of_tendsto (hg_lim t) (Filter.Eventually.of_forall fun k => (hBdd (φ k) t).2)⟩
  have hg_cont : Continuous g := by
    rw [Metric.continuous_iff]
    intro t ε hε
    obtain ⟨δ, hδ, K, hK⟩ := hEqui (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun s hs => ?_⟩
    rw [Real.dist_eq] at hs ⊢
    have hDiff : Tendsto (fun k => |u (φ k) s - u (φ k) t|) atTop (𝓝 |g s - g t|) :=
      ((hg_lim s).sub (hg_lim t)).abs
    have hle : |g s - g t| ≤ ε / 2 :=
      le_of_tendsto hDiff (Filter.eventually_atTop.mpr ⟨K, fun k hk =>
        (hK (φ k) (le_trans hk (hφ_mono.id_le k)) s t hs).le⟩)
    linarith
  exact ⟨φ, g, hφ_mono, hg_bdd, hg_cont, hg_lim⟩

private lemma cramer_step4_unifCont
    (rate : ℝ≥0) (premium nu : ℝ) (hpremium : 0 < premium) (hnu : 0 < nu)
    (barF h Z : ℝ → ℝ)
    (hbarF_anti : Antitone barF) (hbarF_le1 : ∀ y, barF y ≤ 1)
    (hfT_meas : Measurable (fun y : ℝ => if 0 < y then ((rate : ℝ) / premium) * Real.exp (nu * y) * barF y else 0))
    (hfT_nn : ∀ y, 0 ≤ (if 0 < y then ((rate : ℝ) / premium) * Real.exp (nu * y) * barF y else 0))
    (hfT_int : IntegrableOn (fun y : ℝ => if 0 < y then ((rate : ℝ) / premium) * Real.exp (nu * y) * barF y else 0) (Set.Ioi (0 : ℝ)) volume)
    (hTail_tendsto_zero : Tendsto (fun v => ∫ y in Set.Ioi v, (if 0 < y then ((rate : ℝ) / premium) * Real.exp (nu * y) * barF y else 0) ∂volume) atTop (𝓝 0))
    (hGtilde_nn : ∀ v, 0 ≤ ∫ y in Set.Ioi v, (if 0 < y then ((rate : ℝ) / premium) * Real.exp (nu * y) * barF y else 0) ∂volume)
    (hGtilde_anti : Antitone (fun v => ∫ y in Set.Ioi v, (if 0 < y then ((rate : ℝ) / premium) * Real.exp (nu * y) * barF y else 0) ∂volume))
    (hh_unifCont : ∀ ε > 0, ∃ δ > 0, ∀ x1 : ℝ, 0 ≤ x1 → ∀ x2 : ℝ, 0 ≤ x2 → |x1 - x2| < δ → |h x1 - h x2| < ε)
    (hZ_bdd : ∀ x : ℝ, 0 ≤ x → 0 ≤ Z x ∧ Z x ≤ 1)
    (hZ_meas : Measurable Z)
    (hRenew : ∀ x : ℝ, 0 ≤ x → Z x = h x + ∫ y in Set.Ioc (0 : ℝ) x, Z (x - y) * (if 0 < y then ((rate : ℝ) / premium) * Real.exp (nu * y) * barF y else 0) ∂volume) :
    ∀ ε > 0, ∃ δ > 0, ∀ x1 : ℝ, 0 ≤ x1 → ∀ x2 : ℝ, 0 ≤ x2 →
      |x1 - x2| < δ → |Z x1 - Z x2| < ε := by
  let fTilde : ℝ → ℝ := fun y => if 0 < y then ((rate : ℝ) / premium) * Real.exp (nu * y) * barF y else 0
  let Gtilde : ℝ → ℝ := fun v => ∫ y in Set.Ioi v, fTilde y ∂volume
  -- Step 4: L¹ translation continuity of fTilde and uniform continuity of Z on [0, ∞)
  have hL1_shift : ∀ ε > 0, ∃ δ > 0, ∀ d : ℝ, 0 ≤ d → d < δ →
      (∫ v in Set.Ioi (0 : ℝ), |fTilde (v + d) - fTilde v| ∂volume) < ε ∧
      (∫ v in Set.Ioc (0 : ℝ) d, fTilde v ∂volume) < ε := by
    intro ε hε
    -- Part B: ∫_{Ioc 0 d} fTilde → 0 as d ↓ 0 (bounded by (rate/premium)*exp(nu*1)*d for d ≤ 1)
    have hSmall : ∃ δ1 > 0, ∀ d : ℝ, 0 ≤ d → d < δ1 →
        (∫ v in Set.Ioc (0 : ℝ) d, fTilde v ∂volume) < ε := by
      set M1 : ℝ := ((rate : ℝ) / premium) * Real.exp (nu * 1) + 1
      have hM1_pos : 0 < M1 := by positivity
      refine ⟨min (ε / M1) 1, lt_min (div_pos hε hM1_pos) zero_lt_one, fun d hd hlt => ?_⟩
      have hd1 : d < 1 := lt_of_lt_of_le hlt (min_le_right _ _)
      have hbd : (∫ v in Set.Ioc (0 : ℝ) d, fTilde v ∂volume) ≤
          ∫ _v in Set.Ioc (0 : ℝ) d, M1 ∂volume := by
        refine setIntegral_mono_on (hfT_int.mono_set Set.Ioc_subset_Ioi_self)
          (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc fun v hv => ?_
        dsimp only [fTilde]
        rw [if_pos hv.1]
        have hexp : Real.exp (nu * v) ≤ Real.exp (nu * 1) :=
          Real.exp_le_exp.mpr (by nlinarith [hv.2])
        have hpos : 0 ≤ (rate : ℝ) / premium := by positivity
        have h1 : ((rate : ℝ) / premium) * Real.exp (nu * v) * barF v ≤
            ((rate : ℝ) / premium) * Real.exp (nu * 1) :=
          calc ((rate : ℝ) / premium) * Real.exp (nu * v) * barF v
              ≤ ((rate : ℝ) / premium) * Real.exp (nu * v) * 1 :=
                mul_le_mul_of_nonneg_left (hbarF_le1 v) (mul_nonneg hpos (Real.exp_pos _).le)
            _ = ((rate : ℝ) / premium) * Real.exp (nu * v) := mul_one _
            _ ≤ ((rate : ℝ) / premium) * Real.exp (nu * 1) := mul_le_mul_of_nonneg_left hexp hpos
        dsimp only [M1]; linarith
      rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith), sub_zero] at hbd
      have hd_lt : d < ε / M1 := lt_of_lt_of_le hlt (min_le_left _ _)
      have : d * M1 < ε := (lt_div_iff₀ hM1_pos).mp hd_lt
      linarith
    -- Part A: ∫_{Ioi 0} |fTilde (v + d) - fTilde v| < ε for small d ≥ 0
    have hTail_ev := hTail_tendsto_zero.eventually (Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < ε / 4))
    rw [Filter.eventually_atTop] at hTail_ev
    obtain ⟨R0, hR0⟩ := hTail_ev
    set R : ℝ := max R0 1
    have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hTail_R : Gtilde R < ε / 4 := by
      have h1 : dist (Gtilde R) 0 < ε / 4 := hR0 R (le_max_left _ _)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hGtilde_nn R)] at h1
      exact h1
    -- On (0, R], fTilde(v + d) → fTilde(v) a.e. as d ↓ 0 since barF has countably many discontinuities
    have hNull_disc : volume {v : ℝ | ¬ ContinuousAt barF v} = 0 :=
      hbarF_anti.countable_not_continuousAt.measure_zero volume
    have hAE_cont : ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) R)), ContinuousAt fTilde v := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      have hAE : ∀ᵐ v ∂volume, ContinuousAt barF v := by
        rw [ae_iff]; exact hNull_disc
      filter_upwards [hAE] with v hv hmem
      have hv_pos : 0 < v := hmem.1
      have hEq_nhds : fTilde =ᶠ[𝓝 v] fun y => ((rate : ℝ) / premium) * Real.exp (nu * y) * barF y := by
        filter_upwards [Ioi_mem_nhds hv_pos] with y hy
        dsimp only [fTilde]; rw [if_pos (show 0 < y from hy)]
      exact (((continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).continuousAt.mul hv).congr hEq_nhds.symm)
    set C_R : ℝ := 2 * (((rate : ℝ) / premium) * Real.exp (nu * (R + 1)))
    have hDCT_R : Tendsto (fun d : ℝ => ∫ v in Set.Ioc (0 : ℝ) R, |fTilde (v + d) - fTilde v| ∂volume)
        (𝓝[Set.Icc (0 : ℝ) 1] 0) (𝓝 0) := by
      have h := tendsto_integral_filter_of_dominated_convergence
        (μ := volume.restrict (Set.Ioc (0 : ℝ) R))
        (l := 𝓝[Set.Icc (0 : ℝ) 1] 0)
        (F := fun d v => |fTilde (v + d) - fTilde v|)
        (f := fun _ => (0 : ℝ))
        (bound := fun _ => C_R)
        (Filter.Eventually.of_forall fun d =>
          ((hfT_meas.comp (measurable_id.add measurable_const)).sub hfT_meas).abs.aestronglyMeasurable)
        (eventually_nhdsWithin_of_forall fun d hd => by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
          rw [Real.norm_of_nonneg (abs_nonneg _)]
          have hpos : 0 ≤ (rate : ℝ) / premium := by positivity
          have h1 : fTilde (v + d) ≤ ((rate : ℝ) / premium) * Real.exp (nu * (R + 1)) := by
            dsimp only [fTilde]; rw [if_pos (by linarith [hv.1, hd.1])]
            have hexp : Real.exp (nu * (v + d)) ≤ Real.exp (nu * (R + 1)) :=
              Real.exp_le_exp.mpr (by nlinarith [hv.2, hd.2])
            calc ((rate : ℝ) / premium) * Real.exp (nu * (v + d)) * barF (v + d)
                ≤ ((rate : ℝ) / premium) * Real.exp (nu * (v + d)) * 1 :=
                  mul_le_mul_of_nonneg_left (hbarF_le1 _) (mul_nonneg hpos (Real.exp_pos _).le)
              _ = ((rate : ℝ) / premium) * Real.exp (nu * (v + d)) := mul_one _
              _ ≤ ((rate : ℝ) / premium) * Real.exp (nu * (R + 1)) := mul_le_mul_of_nonneg_left hexp hpos
          have h2 : fTilde v ≤ ((rate : ℝ) / premium) * Real.exp (nu * (R + 1)) := by
            dsimp only [fTilde]; rw [if_pos hv.1]
            have hexp : Real.exp (nu * v) ≤ Real.exp (nu * (R + 1)) :=
              Real.exp_le_exp.mpr (by nlinarith [hv.2])
            calc ((rate : ℝ) / premium) * Real.exp (nu * v) * barF v
                ≤ ((rate : ℝ) / premium) * Real.exp (nu * v) * 1 :=
                  mul_le_mul_of_nonneg_left (hbarF_le1 _) (mul_nonneg hpos (Real.exp_pos _).le)
              _ = ((rate : ℝ) / premium) * Real.exp (nu * v) := mul_one _
              _ ≤ ((rate : ℝ) / premium) * Real.exp (nu * (R + 1)) := mul_le_mul_of_nonneg_left hexp hpos
          calc |fTilde (v + d) - fTilde v| ≤ |fTilde (v + d)| + |fTilde v| := abs_sub _ _
            _ = fTilde (v + d) + fTilde v := by rw [abs_of_nonneg (hfT_nn _), abs_of_nonneg (hfT_nn _)]
            _ ≤ C_R := by dsimp only [C_R]; linarith)
        (integrableOn_const (hs := measure_Ioc_lt_top.ne))
        (by
          filter_upwards [hAE_cont] with v hv
          have hadd : Tendsto (fun d : ℝ => v + d) (𝓝[Set.Icc (0 : ℝ) 1] 0) (𝓝 v) := by
            have hcont : Continuous (fun d : ℝ => v + d) := continuous_const.add continuous_id
            have h1 := (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Icc (0 : ℝ) 1))
            simpa using h1
          have hlim := ((hv.tendsto.comp hadd).sub (tendsto_const_nhds (x := fTilde v))).abs
          rwa [sub_self, abs_zero] at hlim)
      simpa using h
    have hEv_R := hDCT_R.eventually (Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < ε / 2))
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hEv_R
    obtain ⟨δ2, hδ2_pos, hδ2⟩ := hEv_R
    obtain ⟨δ1, hδ1_pos, hδ1⟩ := hSmall
    refine ⟨min (min δ1 δ2) 1, lt_min (lt_min hδ1_pos hδ2_pos) zero_lt_one, fun d hd hlt => ?_⟩
    have hd1 : d < δ1 := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_left _ _))
    have hd2 : d < δ2 := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_right _ _))
    have hd_le1 : d ≤ 1 := (lt_of_lt_of_le hlt (min_le_right _ _)).le
    refine ⟨?_, hδ1 d hd hd1⟩
    have hInt_shift : IntegrableOn (fun v => fTilde (v + d)) (Set.Ioi (0 : ℝ)) volume := by
      have hmp : MeasurePreserving (fun v : ℝ => v + d) volume volume := measurePreserving_add_right volume d
      have hpre : (fun v : ℝ => v + d) ⁻¹' Set.Ioi d = Set.Ioi (0 : ℝ) := by
        ext v; simp
      rw [← hpre]
      exact (hmp.integrableOn_comp_preimage (MeasurableEquiv.addRight d).measurableEmbedding).mpr
        (hfT_int.mono_set (Set.Ioi_subset_Ioi hd))
    have hInt_abs : IntegrableOn (fun v => |fTilde (v + d) - fTilde v|) (Set.Ioi (0 : ℝ)) volume :=
      (hInt_shift.sub hfT_int).abs
    have hsplit_set : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) R ∪ Set.Ioi R := by
      ext v; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro hv; by_cases hle : v ≤ R
        · exact Or.inl ⟨hv, hle⟩
        · exact Or.inr (lt_of_not_ge hle)
      · rintro (⟨hv, _⟩ | hgt); exact hv; linarith
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) R) (Set.Ioi R) :=
      Set.disjoint_left.mpr fun v h1 h2 => not_lt_of_ge h1.2 h2
    rw [hsplit_set, setIntegral_union hdisj measurableSet_Ioi
      (hInt_abs.mono_set Set.Ioc_subset_Ioi_self) (hInt_abs.mono_set (Set.Ioi_subset_Ioi hR_pos.le))]
    have hPart1 : (∫ v in Set.Ioc (0 : ℝ) R, |fTilde (v + d) - fTilde v| ∂volume) < ε / 2 := by
      have h1 := hδ2 (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hd]; exact hd2) ⟨hd, hd_le1⟩
      change dist _ 0 < ε / 2 at h1
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at h1
      exact h1
    have hPart2 : (∫ v in Set.Ioi R, |fTilde (v + d) - fTilde v| ∂volume) ≤ 2 * Gtilde R := by
      have h1 : (∫ v in Set.Ioi R, |fTilde (v + d) - fTilde v| ∂volume) ≤
          ∫ v in Set.Ioi R, (fTilde (v + d) + fTilde v) ∂volume := by
        refine setIntegral_mono_on (hInt_abs.mono_set (Set.Ioi_subset_Ioi hR_pos.le))
          ((hInt_shift.mono_set (Set.Ioi_subset_Ioi hR_pos.le)).add (hfT_int.mono_set (Set.Ioi_subset_Ioi hR_pos.le)))
          measurableSet_Ioi fun v _ => ?_
        calc |fTilde (v + d) - fTilde v| ≤ |fTilde (v + d)| + |fTilde v| := abs_sub _ _
          _ = fTilde (v + d) + fTilde v := by rw [abs_of_nonneg (hfT_nn _), abs_of_nonneg (hfT_nn _)]
      rw [integral_add (hInt_shift.mono_set (Set.Ioi_subset_Ioi hR_pos.le))
        (hfT_int.mono_set (Set.Ioi_subset_Ioi hR_pos.le))] at h1
      have h2 : (∫ v in Set.Ioi R, fTilde (v + d) ∂volume) = Gtilde (R + d) := by
        dsimp only [Gtilde]
        have := integral_add_right_eq_self (μ := volume) (fun v => (Set.Ioi (R + d)).indicator fTilde v) d
        have hInd : (fun v => (Set.Ioi (R + d)).indicator fTilde (v + d)) =
            (Set.Ioi R).indicator (fun v => fTilde (v + d)) := by
          ext v; by_cases hv : R < v
          · rw [Set.indicator_of_mem (show v + d ∈ Set.Ioi (R + d) by simp; linarith),
              Set.indicator_of_mem (show v ∈ Set.Ioi R from hv)]
          · rw [Set.indicator_of_notMem (show v + d ∉ Set.Ioi (R + d) by simp; linarith),
              Set.indicator_of_notMem (show v ∉ Set.Ioi R from hv)]
        rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
          ← hInd, this]
      have h3 : Gtilde (R + d) ≤ Gtilde R := hGtilde_anti (by linarith)
      change (∫ v in Set.Ioi R, |fTilde (v + d) - fTilde v| ∂volume) ≤ 2 * Gtilde R
      dsimp only [Gtilde] at h1 h2 h3 ⊢
      linarith
    linarith
  have hZ_unifCont : ∀ ε > 0, ∃ δ > 0, ∀ x1 : ℝ, 0 ≤ x1 → ∀ x2 : ℝ, 0 ≤ x2 →
      |x1 - x2| < δ → |Z x1 - Z x2| < ε := by
    intro ε hε
    obtain ⟨δh, hδh_pos, hδh⟩ := hh_unifCont (ε / 3) (by positivity)
    obtain ⟨δf, hδf_pos, hδf⟩ := hL1_shift (ε / 3) (by positivity)
    refine ⟨min δh δf, lt_min hδh_pos hδf_pos, fun x1 hx1 x2 hx2 hdist => ?_⟩
    have hOrder : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a < min δh δf → |Z b - Z a| < ε := by
      intro a b ha hab hlt
      set d : ℝ := b - a
      have hd_nn : 0 ≤ d := sub_nonneg.mpr hab
      have hd_h : |b - a| < δh := by rw [abs_of_nonneg hd_nn]; exact lt_of_lt_of_le hlt (min_le_left _ _)
      have hd_f : d < δf := lt_of_lt_of_le hlt (min_le_right _ _)
      have hh_diff : |h b - h a| < ε / 3 := hδh b (le_trans ha hab) a ha hd_h
      have ⟨hL1_d, hSmall_d⟩ := hδf d hd_nn hd_f
      -- Change variables u = x - y in the renewal integral
      have hCV : ∀ x : ℝ, 0 ≤ x →
          (∫ y in Set.Ioc (0 : ℝ) x, Z (x - y) * fTilde y ∂volume) =
            ∫ u in Set.Ioc (0 : ℝ) x, Z u * fTilde (x - u) ∂volume := fun x hx => by
        rw [← intervalIntegral.integral_of_le hx, ← intervalIntegral.integral_of_le hx]
        have h := intervalIntegral.integral_comp_sub_left (fun t => Z t * fTilde (x - t)) x (a := 0) (b := x)
        simpa [sub_zero, sub_self, sub_sub_cancel] using h
      rw [hRenew b (le_trans ha hab), hRenew a ha, hCV b (le_trans ha hab), hCV a ha]
      have hInt_b : IntegrableOn (fun u => Z u * fTilde (b - u)) (Set.Ioc (0 : ℝ) b) volume := by
        have hEq_f : IntegrableOn (fun u => fTilde (b - u)) (Set.Ioc (0 : ℝ) b) volume := by
          rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (le_trans ha hab)]
          have h1 : IntervalIntegrable fTilde volume 0 b :=
            (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_trans ha hab)).mpr (hfT_int.mono_set Set.Ioc_subset_Ioi_self)
          simpa [sub_zero, sub_self] using (h1.comp_sub_left b).symm
        refine hEq_f.mono' (hZ_meas.mul (hfT_meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        have hb := hZ_bdd u hu.1.le
        rw [Real.norm_of_nonneg (mul_nonneg hb.1 (hfT_nn _))]
        nlinarith [hfT_nn (b - u)]
      have hInt_a : IntegrableOn (fun u => Z u * fTilde (a - u)) (Set.Ioc (0 : ℝ) a) volume := by
        have hEq_f : IntegrableOn (fun u => fTilde (a - u)) (Set.Ioc (0 : ℝ) a) volume := by
          rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
          have h1 : IntervalIntegrable fTilde volume 0 a :=
            (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mpr (hfT_int.mono_set Set.Ioc_subset_Ioi_self)
          simpa [sub_zero, sub_self] using (h1.comp_sub_left a).symm
        refine hEq_f.mono' (hZ_meas.mul (hfT_meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        have hb := hZ_bdd u hu.1.le
        rw [Real.norm_of_nonneg (mul_nonneg hb.1 (hfT_nn _))]
        nlinarith [hfT_nn (a - u)]
      have hSplit_b : Set.Ioc (0 : ℝ) b = Set.Ioc (0 : ℝ) a ∪ Set.Ioc a b :=
        (Set.Ioc_union_Ioc_eq_Ioc ha hab).symm
      have hDisj_ab : Disjoint (Set.Ioc (0 : ℝ) a) (Set.Ioc a b) :=
        Set.disjoint_left.mpr fun u h1 h2 => not_lt_of_ge h1.2 h2.1
      rw [hSplit_b, setIntegral_union hDisj_ab measurableSet_Ioc
        (hInt_b.mono_set (Set.Ioc_subset_Ioc_right hab))
        (hInt_b.mono_set (Set.Ioc_subset_Ioc_left ha))]
      have hDiff_int : (∫ u in Set.Ioc (0 : ℝ) a, Z u * fTilde (b - u) ∂volume) -
          (∫ u in Set.Ioc (0 : ℝ) a, Z u * fTilde (a - u) ∂volume) =
          ∫ u in Set.Ioc (0 : ℝ) a, Z u * (fTilde (b - u) - fTilde (a - u)) ∂volume := by
        rw [← integral_sub (hInt_b.mono_set (Set.Ioc_subset_Ioc_right hab)) hInt_a]
        congr 1; ext u; ring
      have hBound1 : |∫ u in Set.Ioc (0 : ℝ) a, Z u * (fTilde (b - u) - fTilde (a - u)) ∂volume| ≤
          ∫ v in Set.Ioi (0 : ℝ), |fTilde (v + d) - fTilde v| ∂volume := by
        have h1 : |∫ u in Set.Ioc (0 : ℝ) a, Z u * (fTilde (b - u) - fTilde (a - u)) ∂volume| ≤
            ∫ u in Set.Ioc (0 : ℝ) a, |fTilde (b - u) - fTilde (a - u)| ∂volume := by
          calc |∫ u in Set.Ioc (0 : ℝ) a, Z u * (fTilde (b - u) - fTilde (a - u)) ∂volume|
              ≤ ∫ u in Set.Ioc (0 : ℝ) a, |Z u * (fTilde (b - u) - fTilde (a - u))| ∂volume :=
                abs_integral_le_integral_abs
            _ ≤ ∫ u in Set.Ioc (0 : ℝ) a, |fTilde (b - u) - fTilde (a - u)| ∂volume := by
                have hInt_r : IntegrableOn (fun u => |fTilde (b - u) - fTilde (a - u)|)
                    (Set.Ioc (0 : ℝ) a) volume := by
                  have hfa : IntegrableOn (fun u => fTilde (a - u)) (Set.Ioc (0 : ℝ) a) volume := by
                    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
                    have h1 : IntervalIntegrable fTilde volume 0 a :=
                      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mpr
                        (hfT_int.mono_set Set.Ioc_subset_Ioi_self)
                    simpa [sub_zero, sub_self] using (h1.comp_sub_left a).symm
                  have hfb : IntegrableOn (fun u => fTilde (b - u)) (Set.Ioc (0 : ℝ) a) volume := by
                    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
                    have h1 : IntervalIntegrable fTilde volume (b - a) b :=
                      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
                        (hfT_int.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hd_nn)))
                    simpa [sub_zero, sub_sub_cancel] using (h1.comp_sub_left b).symm
                  exact (hfb.sub hfa).abs
                have hInt_l : IntegrableOn (fun u => |Z u * (fTilde (b - u) - fTilde (a - u))|)
                    (Set.Ioc (0 : ℝ) a) volume :=
                  (((hInt_b.mono_set (Set.Ioc_subset_Ioc_right hab)).sub hInt_a).congr
                    (Filter.Eventually.of_forall fun u => by dsimp; ring)).abs
                refine setIntegral_mono_on hInt_l hInt_r measurableSet_Ioc fun u hu => ?_
                rw [abs_mul, abs_of_nonneg (hZ_bdd u hu.1.le).1]
                exact mul_le_of_le_one_left (abs_nonneg _) (hZ_bdd u hu.1.le).2
        have hCV2 : (∫ u in Set.Ioc (0 : ℝ) a, |fTilde (b - u) - fTilde (a - u)| ∂volume) =
            ∫ v in Set.Ioc (0 : ℝ) a, |fTilde (v + d) - fTilde v| ∂volume := by
          rw [← intervalIntegral.integral_of_le ha, ← intervalIntegral.integral_of_le ha]
          have h := intervalIntegral.integral_comp_sub_left (fun v => |fTilde (v + d) - fTilde v|) a (a := 0) (b := a)
          have hEq_fn : (fun u => |fTilde ((a - u) + d) - fTilde (a - u)|) =
              fun u => |fTilde (b - u) - fTilde (a - u)| := by
            ext u; dsimp only [d]; ring_nf
          rw [hEq_fn] at h
          simpa [sub_zero, sub_self] using h
        have hInt_Ioi : IntegrableOn (fun v => |fTilde (v + d) - fTilde v|) (Set.Ioi (0 : ℝ)) volume := by
          have hInt_s : IntegrableOn (fun v => fTilde (v + d)) (Set.Ioi (0 : ℝ)) volume := by
            have hmp : MeasurePreserving (fun v : ℝ => v + d) volume volume := measurePreserving_add_right volume d
            have hpre : (fun v : ℝ => v + d) ⁻¹' Set.Ioi d = Set.Ioi (0 : ℝ) := by ext v; simp
            rw [← hpre]
            exact (hmp.integrableOn_comp_preimage (MeasurableEquiv.addRight d).measurableEmbedding).mpr
              (hfT_int.mono_set (Set.Ioi_subset_Ioi hd_nn))
          exact (hInt_s.sub hfT_int).abs
        have hMono : (∫ v in Set.Ioc (0 : ℝ) a, |fTilde (v + d) - fTilde v| ∂volume) ≤
            ∫ v in Set.Ioi (0 : ℝ), |fTilde (v + d) - fTilde v| ∂volume :=
          setIntegral_mono_set hInt_Ioi (Filter.Eventually.of_forall fun _ => abs_nonneg _)
            (Filter.Eventually.of_forall Set.Ioc_subset_Ioi_self)
        linarith
      have hBound2 : |∫ u in Set.Ioc a b, Z u * fTilde (b - u) ∂volume| ≤
          ∫ v in Set.Ioc (0 : ℝ) d, fTilde v ∂volume := by
        have h1 : |∫ u in Set.Ioc a b, Z u * fTilde (b - u) ∂volume| ≤
            ∫ u in Set.Ioc a b, fTilde (b - u) ∂volume := by
          have hfb : IntegrableOn (fun u => fTilde (b - u)) (Set.Ioc a b) volume := by
            rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
            have h1 : IntervalIntegrable fTilde volume 0 (b - a) :=
              (intervalIntegrable_iff_integrableOn_Ioc_of_le hd_nn).mpr (hfT_int.mono_set Set.Ioc_subset_Ioi_self)
            simpa [sub_self, sub_sub_cancel] using (h1.comp_sub_left b).symm
          calc |∫ u in Set.Ioc a b, Z u * fTilde (b - u) ∂volume|
              ≤ ∫ u in Set.Ioc a b, |Z u * fTilde (b - u)| ∂volume := abs_integral_le_integral_abs
            _ ≤ ∫ u in Set.Ioc a b, fTilde (b - u) ∂volume := by
                refine setIntegral_mono_on (hInt_b.mono_set (Set.Ioc_subset_Ioc_left ha)).abs hfb
                  measurableSet_Ioc fun u hu => ?_
                have hbu := hZ_bdd u (le_trans ha hu.1.le)
                rw [abs_of_nonneg (mul_nonneg hbu.1 (hfT_nn _))]
                nlinarith [hfT_nn (b - u)]
        have hCV3 : (∫ u in Set.Ioc a b, fTilde (b - u) ∂volume) =
            ∫ v in Set.Ioc (0 : ℝ) d, fTilde v ∂volume := by
          rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hd_nn]
          have h := intervalIntegral.integral_comp_sub_left fTilde b (a := a) (b := b)
          simpa [sub_self, d] using h
        linarith
      have hAlg : (h b + ((∫ u in Set.Ioc (0 : ℝ) a, Z u * fTilde (b - u) ∂volume) +
            ∫ u in Set.Ioc a b, Z u * fTilde (b - u) ∂volume)) -
          (h a + ∫ u in Set.Ioc (0 : ℝ) a, Z u * fTilde (a - u) ∂volume) =
          (h b - h a) + ((∫ u in Set.Ioc (0 : ℝ) a, Z u * (fTilde (b - u) - fTilde (a - u)) ∂volume) +
            ∫ u in Set.Ioc a b, Z u * fTilde (b - u) ∂volume) := by
        linarith [hDiff_int]
      rw [hAlg]
      calc |(h b - h a) + ((∫ u in Set.Ioc (0 : ℝ) a, Z u * (fTilde (b - u) - fTilde (a - u)) ∂volume) +
              ∫ u in Set.Ioc a b, Z u * fTilde (b - u) ∂volume)|
          ≤ |h b - h a| + |(∫ u in Set.Ioc (0 : ℝ) a, Z u * (fTilde (b - u) - fTilde (a - u)) ∂volume) +
              ∫ u in Set.Ioc a b, Z u * fTilde (b - u) ∂volume| := abs_add_le _ _
        _ ≤ |h b - h a| + (|∫ u in Set.Ioc (0 : ℝ) a, Z u * (fTilde (b - u) - fTilde (a - u)) ∂volume| +
              |∫ u in Set.Ioc a b, Z u * fTilde (b - u) ∂volume|) := by
              gcongr; exact abs_add_le _ _
        _ < ε / 3 + (ε / 3 + ε / 3) := by linarith
        _ = ε := by ring
    rcases le_total x1 x2 with hle | hle
    · rw [abs_sub_comm]
      exact hOrder x1 x2 hx1 hle (by rwa [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)] at hdist)
    · exact hOrder x2 x1 hx2 hle (by rwa [abs_of_nonneg (sub_nonneg.mpr hle)] at hdist)
  exact hZ_unifCont

private lemma cramer_step78_limit
    (rate : ℝ≥0) (hrateR : (0 : ℝ) < (rate : ℝ))
    (mu premium nu : ℝ) (hpremium : 0 < premium) (hnu : 0 < nu)
    (hnet : (rate : ℝ) * mu < premium)
    (weightedTail : ℝ≥0∞)
    (fTilde h Z : ℝ → ℝ)
    (hfT_meas : Measurable fTilde) (hfT_nn : ∀ y, 0 ≤ fTilde y)
    (hfT_int : IntegrableOn fTilde (Set.Ioi (0 : ℝ)) volume)
    (hfT_integral : (∫ y in Set.Ioi (0 : ℝ), fTilde y ∂volume) = 1)
    (hh_nn : ∀ x, 0 ≤ h x)
    (hGtilde_nn : ∀ v, 0 ≤ ∫ y in Set.Ioi v, fTilde y ∂volume)
    (hGtilde_le1 : ∀ v, 0 ≤ v → (∫ y in Set.Ioi v, fTilde y ∂volume) ≤ 1)
    (hGtilde_anti : Antitone (fun v => ∫ y in Set.Ioi v, fTilde y ∂volume))
    (hh_tendsto_zero : Tendsto h atTop (𝓝 0))
    (hh_int_val : IntegrableOn h (Set.Ioi (0 : ℝ)) volume ∧
      (∫ x in Set.Ioi (0 : ℝ), h x ∂volume) = (premium - (rate : ℝ) * mu) / (premium * nu))
    (hZ_bdd : ∀ x : ℝ, 0 ≤ x → 0 ≤ Z x ∧ Z x ≤ 1)
    (hZ_meas : Measurable Z)
    (hRenew : ∀ x : ℝ, 0 ≤ x → Z x = h x + ∫ y in Set.Ioc (0 : ℝ) x, Z (x - y) * fTilde y ∂volume)
    (hZ_unifCont : ∀ ε > 0, ∃ δ > 0, ∀ x1 : ℝ, 0 ≤ x1 → ∀ x2 : ℝ, 0 ≤ x2 → |x1 - x2| < δ → |Z x1 - Z x2| < ε)
    (hFubini : ∀ T : ℝ, 0 ≤ T → (∫ t in Set.Ioc (0 : ℝ) T, h t ∂volume) = ∫ v in Set.Ioc (0 : ℝ) T, Z (T - v) * (∫ y in Set.Ioi v, fTilde y ∂volume) ∂volume)
    (hGtilde_lintegral : (∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (∫ y in Set.Ioi v, fTilde y ∂volume) ∂volume) =
      ENNReal.ofReal ((rate : ℝ) / premium) * weightedTail)
    (hPos_window : ∃ a : ℝ, 0 < a ∧ ∀ y ∈ Set.Ioo (0 : ℝ) a, (rate : ℝ) / (2 * premium) ≤ fTilde y) :
    Tendsto Z atTop
      (𝓝 (if weightedTail = ⊤ then 0 else
        (((rate : ℝ) * nu / (premium - (rate : ℝ) * mu)) * weightedTail.toReal)⁻¹)) := by
  let Gtilde : ℝ → ℝ := fun v => ∫ y in Set.Ioi v, fTilde y ∂volume
  -- Step 7: Key subsequential-limit lemma forcing any extremal limit c to equal the target L
  set L_target : ℝ := if weightedTail = ⊤ then 0 else
    (((rate : ℝ) * nu / (premium - (rate : ℝ) * mu)) * weightedTail.toReal)⁻¹
  have hwt_pos : 0 < weightedTail := by
    obtain ⟨a, ha_pos, ha⟩ := hPos_window
    have hG_pos : 0 < ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (Gtilde v) ∂volume := by
      have hGt_pos : ∀ v ∈ Set.Ioo (0 : ℝ) (a / 2), (a / 2) * ((rate : ℝ) / (2 * premium)) ≤ Gtilde v := by
        intro v hv
        dsimp only [Gtilde]
        have hsub : Set.Ioo v a ⊆ Set.Ioi v := fun y hy => hy.1
        have h1 : (∫ y in Set.Ioo v a, ((rate : ℝ) / (2 * premium)) ∂volume) ≤
            ∫ y in Set.Ioo v a, fTilde y ∂volume :=
          setIntegral_mono_on (integrableOn_const (hs := measure_Ioo_lt_top.ne))
            (hfT_int.mono_set (Set.Ioo_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hv.1.le)))
            measurableSet_Ioo fun y hy => ha y ⟨lt_trans hv.1 hy.1, hy.2⟩
        have h2 : (∫ y in Set.Ioo v a, fTilde y ∂volume) ≤ ∫ y in Set.Ioi v, fTilde y ∂volume :=
          setIntegral_mono_set (hfT_int.mono_set (Set.Ioi_subset_Ioi hv.1.le))
            (Filter.Eventually.of_forall hfT_nn) (Filter.Eventually.of_forall hsub)
        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
          ENNReal.toReal_ofReal (by linarith [hv.2])] at h1
        have hlen : a / 2 ≤ a - v := by linarith [hv.2]
        nlinarith [div_pos hrateR (mul_pos two_pos hpremium)]
      set c1 : ℝ := (a / 2) * ((rate : ℝ) / (2 * premium))
      have hc1_pos : 0 < c1 := by positivity
      calc (0 : ℝ≥0∞) < ENNReal.ofReal c1 * volume (Set.Ioo (0 : ℝ) (a / 2)) := by
            rw [Real.volume_Ioo, sub_zero]
            exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hc1_pos).ne' (ENNReal.ofReal_pos.mpr (by positivity)).ne'
        _ = ∫⁻ _v in Set.Ioo (0 : ℝ) (a / 2), ENNReal.ofReal c1 ∂volume := by simp
        _ ≤ ∫⁻ v in Set.Ioo (0 : ℝ) (a / 2), ENNReal.ofReal (Gtilde v) ∂volume :=
            setLIntegral_mono' measurableSet_Ioo fun v hv => ENNReal.ofReal_le_ofReal (hGt_pos v hv)
        _ ≤ ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (Gtilde v) ∂volume :=
            lintegral_mono_set Set.Ioo_subset_Ioi_self
    rw [hGtilde_lintegral] at hG_pos
    by_contra h0
    have hwt0 : weightedTail = 0 := le_antisymm (le_of_not_gt h0) (bot_le)
    rw [hwt0, mul_zero] at hG_pos
    exact lt_irrefl _ hG_pos
  have hExtremal_eq : ∀ (x : ℕ → ℝ) (c : ℝ),
      Tendsto x atTop atTop →
      Tendsto (fun k => Z (x k)) atTop (𝓝 c) →
      ((∀ t : ℝ, ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ L, Tendsto (fun k => Z (x (φ k) + t)) atTop (𝓝 L) → L ≤ c) ∨
       (∀ t : ℝ, ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ L, Tendsto (fun k => Z (x (φ k) + t)) atTop (𝓝 L) → c ≤ L)) →
      c = L_target := by
    intro x c hx_top hx_lim hExt
    let u : ℕ → ℝ → ℝ := fun k t => Z (max 0 (x k + t))
    have hu_bdd : ∀ k t, 0 ≤ u k t ∧ u k t ≤ 1 := fun k t => hZ_bdd _ (le_max_left _ _)
    have hu_equi : ∀ ε > 0, ∃ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ t1 t2 : ℝ, |t1 - t2| < δ →
        |u k t1 - u k t2| < ε := by
      intro ε hε
      obtain ⟨δ, hδ_pos, hδ⟩ := hZ_unifCont ε hε
      refine ⟨δ, hδ_pos, 0, fun k _ t1 t2 hlt => ?_⟩
      refine hδ _ (le_max_left _ _) _ (le_max_left _ _) ?_
      have hmax : |max (0 : ℝ) (x k + t1) - max 0 (x k + t2)| ≤ |(x k + t1) - (x k + t2)| := by
        rw [max_comm 0 (x k + t1), max_comm 0 (x k + t2)]
        exact abs_max_sub_max_le_abs _ _ _
      have hsub : (x k + t1) - (x k + t2) = t1 - t2 := by ring
      rw [hsub] at hmax
      exact lt_of_le_of_lt hmax hlt
    obtain ⟨φ, g, hφ_mono, hg_bdd, hg_cont, hg_lim⟩ := exists_subseq_tendsto_of_equicont_unit u hu_bdd hu_equi
    have hxφ_top : Tendsto (fun k => x (φ k)) atTop atTop := hx_top.comp hφ_mono.tendsto_atTop
    have hg_shift_lim : ∀ t : ℝ, Tendsto (fun k => Z (x (φ k) + t)) atTop (𝓝 (g t)) := fun t => by
      have hEv := hxφ_top.eventually (Filter.eventually_ge_atTop (-t))
      refine (hg_lim t).congr' ?_
      filter_upwards [hEv] with k hk
      dsimp only [u]
      rw [max_eq_right (by linarith)]
    have hg0 : g 0 = c := by
      have h1 : Tendsto (fun k => Z (x (φ k) + 0)) atTop (𝓝 (g 0)) := hg_shift_lim 0
      have h2 : Tendsto (fun k => Z (x (φ k))) atTop (𝓝 c) := hx_lim.comp hφ_mono.tendsto_atTop
      simp only [add_zero] at h1
      exact tendsto_nhds_unique h1 h2
    -- g satisfies the homogeneous renewal equation g(t) = ∫_{Ioi 0} g(t - y) fTilde(y) dy
    have hg_conv : ∀ t : ℝ, g t = ∫ y in Set.Ioi (0 : ℝ), g (t - y) * fTilde y ∂volume := by
      intro t
      have hLHS := hg_shift_lim t
      have hEv_pos := hxφ_top.eventually (Filter.eventually_ge_atTop (-t))
      have hh_lim : Tendsto (fun k => h (x (φ k) + t)) atTop (𝓝 0) :=
        hh_tendsto_zero.comp (tendsto_atTop_add_const_right atTop t hxφ_top)
      have hInt_lim : Tendsto (fun k => ∫ y in Set.Ioi (0 : ℝ),
          (if y ≤ x (φ k) + t then Z (x (φ k) + t - y) * fTilde y else 0) ∂volume)
          atTop (𝓝 (∫ y in Set.Ioi (0 : ℝ), g (t - y) * fTilde y ∂volume)) := by
        refine tendsto_integral_of_dominated_convergence fTilde ?_ hfT_int ?_ ?_
        · intro k
          exact (Measurable.ite (measurableSet_le measurable_id measurable_const)
            ((hZ_meas.comp (measurable_const.sub measurable_id)).mul hfT_meas)
            measurable_const).aestronglyMeasurable
        · intro k
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with y _
          split_ifs with hle
          · have hb := hZ_bdd _ (sub_nonneg.mpr hle)
            rw [Real.norm_of_nonneg (mul_nonneg hb.1 (hfT_nn y))]
            nlinarith [hfT_nn y]
          · simp [hfT_nn y]
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y _
          have hEv_y := hxφ_top.eventually (Filter.eventually_ge_atTop (y - t))
          have hLim_y : Tendsto (fun k => Z (x (φ k) + (t - y)) * fTilde y) atTop (𝓝 (g (t - y) * fTilde y)) :=
            (hg_shift_lim (t - y)).mul_const (fTilde y)
          refine hLim_y.congr' ?_
          filter_upwards [hEv_y] with k hk
          rw [if_pos (by linarith), show x (φ k) + t - y = x (φ k) + (t - y) by ring]
      have hRHS : Tendsto (fun k => h (x (φ k) + t) + ∫ y in Set.Ioi (0 : ℝ),
          (if y ≤ x (φ k) + t then Z (x (φ k) + t - y) * fTilde y else 0) ∂volume)
          atTop (𝓝 (0 + ∫ y in Set.Ioi (0 : ℝ), g (t - y) * fTilde y ∂volume)) := hh_lim.add hInt_lim
      rw [zero_add] at hRHS
      have hEv_eq : ∀ᶠ k in atTop, Z (x (φ k) + t) =
          h (x (φ k) + t) + ∫ y in Set.Ioi (0 : ℝ),
            (if y ≤ x (φ k) + t then Z (x (φ k) + t - y) * fTilde y else 0) ∂volume := by
        filter_upwards [hEv_pos] with k hk
        rw [hRenew (x (φ k) + t) (by linarith)]
        congr 1
        have hInd : (fun y => if y ≤ x (φ k) + t then Z (x (φ k) + t - y) * fTilde y else 0) =
            (Set.Iic (x (φ k) + t)).indicator (fun y => Z (x (φ k) + t - y) * fTilde y) := by
          ext y; by_cases hle : y ≤ x (φ k) + t <;> simp [hle]
        rw [hInd, setIntegral_indicator measurableSet_Iic]
        rfl
      exact tendsto_nhds_unique (hLHS.congr' hEv_eq) hRHS
    -- Because fTilde ≥ c0 > 0 on (0, a) and g is continuous with extremal value c at 0, g(t) = c for all t ≤ 0!
    obtain ⟨a, ha_pos, ha⟩ := hPos_window
    have hg_const_neg : ∀ t : ℝ, t ≤ 0 → g t = c := by
      have hStep_const : ∀ s : ℝ, g s = c →
          ((∀ r, g r ≤ c) ∨ (∀ r, c ≤ g r)) →
          ∀ y ∈ Set.Icc (0 : ℝ) a, g (s - y) = c := by
        intro s hgs hSign y hy
        -- If g(s - y) ≠ c on (0, a), by continuity there is an open subinterval where |c - g(s - ·)| > 0
        have hInt_diff : (∫ r in Set.Ioi (0 : ℝ), (c - g (s - r)) * fTilde r ∂volume) = 0 := by
          have hInt_g : IntegrableOn (fun r => g (s - r) * fTilde r) (Set.Ioi (0 : ℝ)) volume := by
            refine hfT_int.mono' ((hg_cont.measurable.comp (measurable_const.sub measurable_id)).mul hfT_meas).aestronglyMeasurable ?_
            refine Filter.Eventually.of_forall fun r => ?_
            rw [Real.norm_of_nonneg (mul_nonneg (hg_bdd _).1 (hfT_nn r))]
            nlinarith [(hg_bdd (s - r)).2, hfT_nn r]
          have hEq : (fun r => (c - g (s - r)) * fTilde r) = fun r => c * fTilde r - g (s - r) * fTilde r := by
            ext r; ring
          rw [hEq, integral_sub (hfT_int.const_mul c) hInt_g, integral_const_mul, hfT_integral, mul_one,
            ← hg_conv s, hgs, sub_self]
        -- Continuous function q(r) := |c - g(s - r)| is nonnegative; if q(y) > 0 for some y ∈ [0, a],
        -- then q > 0 on some subinterval Ioo u v ⊆ Ioo 0 a, contradicting ∫ (c - g(s - r)) fTilde r = 0
        by_contra hne
        have hq_cont : Continuous (fun r => |c - g (s - r)|) :=
          (continuous_const.sub (hg_cont.comp (continuous_const.sub continuous_id))).abs
        have hpos_y : 0 < |c - g (s - y)| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
        have hEv_y := hq_cont.continuousAt.eventually (lt_mem_nhds (by linarith : |c - g (s - y)| / 2 < |c - g (s - y)|))
        rw [Metric.eventually_nhds_iff] at hEv_y
        obtain ⟨δ, hδ_pos, hδ⟩ := hEv_y
        -- Pick a nondegenerate open interval (u, v) ⊆ (0, a) ∩ (y - δ, y + δ)
        set u0 : ℝ := max 0 (y - δ / 2)
        set v0 : ℝ := min a (y + δ / 2)
        have huv : u0 < v0 := by
          dsimp only [u0, v0]
          exact max_lt (lt_min ha_pos (by linarith [hy.1, hδ_pos]))
            (lt_min (by linarith [hy.2, hδ_pos]) (by linarith [hδ_pos]))
        have hSub : Set.Ioo u0 v0 ⊆ Set.Ioi (0 : ℝ) := fun r hr => lt_of_le_of_lt (le_max_left _ _) hr.1
        have hSub_a : ∀ r ∈ Set.Ioo u0 v0, r ∈ Set.Ioo (0 : ℝ) a := fun r hr =>
          ⟨lt_of_le_of_lt (le_max_left _ _) hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩
        have hPos_on : ∀ r ∈ Set.Ioo u0 v0,
            (|c - g (s - y)| / 2) * ((rate : ℝ) / (2 * premium)) ≤ |c - g (s - r)| * fTilde r := fun r hr => by
          have hr_dist : dist r y < δ := by
            rw [Real.dist_eq, abs_lt]
            have h1 : y - δ / 2 < r := lt_of_le_of_lt (le_max_right _ _) hr.1
            have h2 : r < y + δ / 2 := lt_of_lt_of_le hr.2 (min_le_right _ _)
            exact ⟨by linarith, by linarith⟩
          have hq_ge : |c - g (s - y)| / 2 ≤ |c - g (s - r)| := (hδ hr_dist).le
          have hf_ge : (rate : ℝ) / (2 * premium) ≤ fTilde r := ha r (hSub_a r hr)
          exact mul_le_mul hq_ge hf_ge (by positivity) (abs_nonneg _)
        have hInt_abs_zero : (∫ r in Set.Ioi (0 : ℝ), |c - g (s - r)| * fTilde r ∂volume) = 0 := by
          rcases hSign with hLe | hGe
          · have hEq : ∀ r, |c - g (s - r)| * fTilde r = (c - g (s - r)) * fTilde r := fun r => by
              rw [abs_of_nonneg (sub_nonneg.mpr (hLe _))]
            simp_rw [hEq]; exact hInt_diff
          · have hEq : ∀ r, |c - g (s - r)| * fTilde r = -((c - g (s - r)) * fTilde r) := fun r => by
              rw [abs_of_nonpos (sub_nonpos.mpr (hGe _))]; ring
            simp_rw [hEq, integral_neg, hInt_diff, neg_zero]
        have hInt_abs : IntegrableOn (fun r => |c - g (s - r)| * fTilde r) (Set.Ioi (0 : ℝ)) volume := by
          refine (hfT_int.const_mul (|c| + 1)).mono'
            (((continuous_const.sub (hg_cont.comp (continuous_const.sub continuous_id))).abs.measurable).mul
              hfT_meas).aestronglyMeasurable (Filter.Eventually.of_forall fun r => ?_)
          rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hfT_nn r))]
          have h1 : |c - g (s - r)| ≤ |c| + 1 := by
            calc |c - g (s - r)| ≤ |c| + |g (s - r)| := abs_sub _ _
              _ = |c| + g (s - r) := by rw [abs_of_nonneg (hg_bdd _).1]
              _ ≤ |c| + 1 := by linarith [(hg_bdd (s - r)).2]
          exact mul_le_mul_of_nonneg_right h1 (hfT_nn r)
        have hPos_int : 0 < ∫ r in Set.Ioi (0 : ℝ), |c - g (s - r)| * fTilde r ∂volume := by
          set c2 : ℝ := (|c - g (s - y)| / 2) * ((rate : ℝ) / (2 * premium))
          have hc2_pos : 0 < c2 := by positivity
          have h1 : (v0 - u0) * c2 ≤ ∫ r in Set.Ioo u0 v0, |c - g (s - r)| * fTilde r ∂volume := by
            have hle := setIntegral_mono_on (integrableOn_const (C := c2) (hs := measure_Ioo_lt_top.ne))
              (hInt_abs.mono_set hSub) measurableSet_Ioo hPos_on
            rwa [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
              ENNReal.toReal_ofReal (sub_nonneg.mpr huv.le)] at hle
          have h2 : (∫ r in Set.Ioo u0 v0, |c - g (s - r)| * fTilde r ∂volume) ≤
              ∫ r in Set.Ioi (0 : ℝ), |c - g (s - r)| * fTilde r ∂volume :=
            setIntegral_mono_set hInt_abs (Filter.Eventually.of_forall fun _ => mul_nonneg (abs_nonneg _) (hfT_nn _))
              (Filter.Eventually.of_forall hSub)
          have h3 : 0 < (v0 - u0) * c2 := mul_pos (sub_pos.mpr huv) hc2_pos
          linarith
        linarith
      have hSign : (∀ r, g r ≤ c) ∨ (∀ r, c ≤ g r) := by
        rcases hExt with hLe | hGe
        · exact Or.inl fun r => hLe r φ hφ_mono (g r) (hg_shift_lim r)
        · exact Or.inr fun r => hGe r φ hφ_mono (g r) (hg_shift_lim r)
      have hInd_k : ∀ n : ℕ, ∀ t ∈ Set.Icc (-(n : ℝ) * a) 0, g t = c := by
        intro n
        induction n with
        | zero =>
            intro t ht; simp at ht
            rw [ht, hg0]
        | succ n ih =>
            intro t ht
            by_cases h1 : -(n : ℝ) * a ≤ t
            · exact ih t ⟨h1, ht.2⟩
            · have hgn : g (-(n : ℝ) * a) = c := ih (-(n : ℝ) * a) ⟨le_rfl, by nlinarith⟩
              have hy_mem : (-(n : ℝ) * a) - t ∈ Set.Icc (0 : ℝ) a := by
                have ht_ge : -(((n + 1 : ℕ) : ℝ)) * a ≤ t := ht.1
                push_cast at ht_ge
                exact ⟨by linarith, by linarith⟩
              have hres := hStep_const (-(n : ℝ) * a) hgn hSign ((-(n : ℝ) * a) - t) hy_mem
              simpa [sub_sub_cancel] using hres
      intro t ht
      obtain ⟨n, hn⟩ := exists_nat_ge (-t / a)
      have hle : -(n : ℝ) * a ≤ t := by
        have h1 : -t ≤ (n : ℝ) * a := (div_le_iff₀ ha_pos).mp hn
        linarith
      exact hInd_k n t ⟨hle, ht⟩
    -- Plug T = x (φ k) into hFubini!
    have hFub_lim : Tendsto (fun k => ∫ t in Set.Ioc (0 : ℝ) (x (φ k)), h t ∂volume)
        atTop (𝓝 ((premium - (rate : ℝ) * mu) / (premium * nu))) := by
      have h1 := tendsto_integral_filter_of_dominated_convergence
        (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (F := fun k t => if t ≤ x (φ k) then h t else 0)
        (f := h)
        (bound := h)
        (Filter.Eventually.of_forall fun k => by
          have hInd : (fun t => if t ≤ x (φ k) then h t else 0) = (Set.Iic (x (φ k))).indicator h := by
            ext t; by_cases hle : t ≤ x (φ k) <;> simp [hle]
          rw [hInd]
          exact hh_int_val.1.aestronglyMeasurable.indicator measurableSet_Iic)
        (Filter.Eventually.of_forall fun k => Filter.Eventually.of_forall fun t => by
          split_ifs
          · rw [Real.norm_of_nonneg (hh_nn t)]
          · simp [hh_nn t])
        hh_int_val.1
        (Filter.Eventually.of_forall fun t => by
          have hEv := hxφ_top.eventually (Filter.eventually_ge_atTop t)
          rw [Filter.eventually_atTop] at hEv
          obtain ⟨K, hK⟩ := hEv
          exact tendsto_atTop_of_eventually_const (i₀ := K) fun k hk => by rw [if_pos (hK k hk)])
      rw [hh_int_val.2] at h1
      refine h1.congr' ?_
      filter_upwards [hxφ_top.eventually (Filter.eventually_ge_atTop (0 : ℝ))] with k hk
      have hInd : (fun t => if t ≤ x (φ k) then h t else 0) = (Set.Iic (x (φ k))).indicator h := by
        ext t; by_cases hle : t ≤ x (φ k) <;> simp [hle]
      rw [hInd, setIntegral_indicator measurableSet_Iic]
      rfl
    have hEv_pos0 := hxφ_top.eventually (Filter.eventually_ge_atTop (0 : ℝ))
    have hFub_eq : ∀ᶠ k in atTop,
        (∫ t in Set.Ioc (0 : ℝ) (x (φ k)), h t ∂volume) =
          ∫ v in Set.Ioi (0 : ℝ), (if v ≤ x (φ k) then Z (x (φ k) - v) * Gtilde v else 0) ∂volume := by
      filter_upwards [hEv_pos0] with k hk
      rw [hFubini (x (φ k)) hk]
      have hInd : (fun v => if v ≤ x (φ k) then Z (x (φ k) - v) * Gtilde v else 0) =
          (Set.Iic (x (φ k))).indicator (fun v => Z (x (φ k) - v) * Gtilde v) := by
        ext v; by_cases hle : v ≤ x (φ k) <;> simp [hle]
      rw [hInd, setIntegral_indicator measurableSet_Iic]
      rfl
    -- Case split on weightedTail = ⊤
    by_cases hwt_top : weightedTail = ⊤
    · dsimp only [L_target]; rw [if_pos hwt_top]
      -- Fatou's lemma forces c = 0
      have hc_nn : 0 ≤ c := by rw [← hg0]; exact (hg_bdd 0).1
      by_contra hc_ne
      have hc_pos : 0 < c := lt_of_le_of_ne hc_nn (Ne.symm hc_ne)
      have hFatou : (∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (c * Gtilde v) ∂volume) ≤
          liminf (fun k => ∫⁻ v in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (if v ≤ x (φ k) then Z (x (φ k) - v) * Gtilde v else 0) ∂volume) atTop := by
        have hLim_pt : ∀ v ∈ Set.Ioi (0 : ℝ),
            Tendsto (fun k => ENNReal.ofReal (if v ≤ x (φ k) then Z (x (φ k) - v) * Gtilde v else 0))
              atTop (𝓝 (ENNReal.ofReal (c * Gtilde v))) := fun v hv => by
          have hEv_v := hxφ_top.eventually (Filter.eventually_ge_atTop v)
          have hLim_v : Tendsto (fun k => Z (x (φ k) + (-v)) * Gtilde v) atTop (𝓝 (g (-v) * Gtilde v)) :=
            (hg_shift_lim (-v)).mul_const (Gtilde v)
          rw [hg_const_neg (-v) (by linarith [show (0 : ℝ) < v from hv])] at hLim_v
          refine (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hLim_v).congr' ?_
          filter_upwards [hEv_v] with k hk
          dsimp only [Function.comp_apply]
          rw [if_pos hk, sub_eq_add_neg]
        have hEq_liminf : ∀ v ∈ Set.Ioi (0 : ℝ),
            ENNReal.ofReal (c * Gtilde v) =
              liminf (fun k => ENNReal.ofReal (if v ≤ x (φ k) then Z (x (φ k) - v) * Gtilde v else 0)) atTop :=
          fun v hv => (hLim_pt v hv).liminf_eq.symm
        rw [setLIntegral_congr_fun measurableSet_Ioi hEq_liminf]
        exact lintegral_liminf_le fun k =>
          ENNReal.measurable_ofReal.comp
            (Measurable.ite (measurableSet_le measurable_id measurable_const)
              ((hZ_meas.comp (measurable_const.sub measurable_id)).mul hGtilde_anti.measurable)
              measurable_const)
      have hLHS_top : (∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (c * Gtilde v) ∂volume) = ⊤ := by
        have hEq : ∀ v, ENNReal.ofReal (c * Gtilde v) = ENNReal.ofReal c * ENNReal.ofReal (Gtilde v) :=
          fun v => ENNReal.ofReal_mul hc_pos.le
        simp_rw [hEq]
        have hG_meas : Measurable (fun v => ENNReal.ofReal (Gtilde v)) :=
          ENNReal.measurable_ofReal.comp hGtilde_anti.measurable
        rw [lintegral_const_mul (ENNReal.ofReal c) hG_meas,
          hGtilde_lintegral, hwt_top,
          ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne',
          ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc_pos).ne']
      have hRHS_lim : Tendsto (fun k => ∫⁻ v in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (if v ≤ x (φ k) then Z (x (φ k) - v) * Gtilde v else 0) ∂volume)
          atTop (𝓝 (ENNReal.ofReal ((premium - (rate : ℝ) * mu) / (premium * nu)))) := by
        have h1 := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hFub_lim
        refine h1.congr' ?_
        filter_upwards [hEv_pos0, hFub_eq] with k hk hEqk
        dsimp only [Function.comp_apply]
        rw [hEqk]
        have hInt_k : IntegrableOn (fun v => if v ≤ x (φ k) then Z (x (φ k) - v) * Gtilde v else 0)
            (Set.Ioi (0 : ℝ)) volume := by
          have hInd : (fun v => if v ≤ x (φ k) then Z (x (φ k) - v) * Gtilde v else 0) =
              (Set.Iic (x (φ k))).indicator (fun v => Z (x (φ k) - v) * Gtilde v) := by
            ext v; by_cases hle : v ≤ x (φ k) <;> simp [hle]
          rw [hInd, integrableOn_indicator_iff measurableSet_Iic]
          have hSet : Set.Ioi (0 : ℝ) ∩ Set.Iic (x (φ k)) = Set.Ioc (0 : ℝ) (x (φ k)) := rfl
          rw [Set.inter_comm, hSet]
          refine (integrableOn_const (C := (1 : ℝ)) (hs := measure_Ioc_lt_top.ne)).mono'
            ((hZ_meas.comp (measurable_const.sub measurable_id)).mul hGtilde_anti.measurable).aestronglyMeasurable ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
          have hb1 := hZ_bdd (x (φ k) - v) (sub_nonneg.mpr hv.2)
          have hb2 := hGtilde_le1 v hv.1.le
          rw [Real.norm_of_nonneg (mul_nonneg hb1.1 (hGtilde_nn v))]
          exact le_trans (mul_le_of_le_one_left (hGtilde_nn v) hb1.2) hb2
        exact ofReal_integral_eq_lintegral_ofReal hInt_k (Filter.Eventually.of_forall fun v => by
          dsimp only
          split_ifs with hle
          · exact mul_nonneg (hZ_bdd _ (sub_nonneg.mpr hle)).1 (hGtilde_nn v)
          · exact le_rfl)
      rw [hLHS_top, hRHS_lim.liminf_eq] at hFatou
      exact absurd (top_le_iff.mp hFatou) ENNReal.ofReal_ne_top
    · dsimp only [L_target]; rw [if_neg hwt_top]
      -- Finite weightedTail: Gtilde ∈ L¹(Ioi 0) with integral (rate/premium) * weightedTail.toReal
      have hGtilde_int : IntegrableOn Gtilde (Set.Ioi (0 : ℝ)) volume := by
        refine ⟨hGtilde_anti.measurable.aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        have hEq : (∫⁻ v in Set.Ioi (0 : ℝ), ‖Gtilde v‖ₑ ∂volume) =
            ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (Gtilde v) ∂volume := by
          refine lintegral_congr fun v => ?_
          rw [← ofReal_norm, Real.norm_of_nonneg (hGtilde_nn v)]
        rw [hEq, hGtilde_lintegral]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hwt_top)
      have hGtilde_val : (∫ v in Set.Ioi (0 : ℝ), Gtilde v ∂volume) =
          ((rate : ℝ) / premium) * weightedTail.toReal := by
        have hof := ofReal_integral_eq_lintegral_ofReal hGtilde_int (Filter.Eventually.of_forall hGtilde_nn)
        rw [hGtilde_lintegral] at hof
        have h := congrArg ENNReal.toReal hof
        rw [ENNReal.toReal_ofReal (integral_nonneg hGtilde_nn),
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
        exact h
      have hRHS_dct : Tendsto (fun k => ∫ v in Set.Ioi (0 : ℝ),
            (if v ≤ x (φ k) then Z (x (φ k) - v) * Gtilde v else 0) ∂volume)
          atTop (𝓝 (∫ v in Set.Ioi (0 : ℝ), c * Gtilde v ∂volume)) := by
        refine tendsto_integral_of_dominated_convergence Gtilde ?_ hGtilde_int ?_ ?_
        · intro k
          exact (Measurable.ite (measurableSet_le measurable_id measurable_const)
            ((hZ_meas.comp (measurable_const.sub measurable_id)).mul hGtilde_anti.measurable)
            measurable_const).aestronglyMeasurable
        · intro k
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
          split_ifs with hle
          · have hb := hZ_bdd _ (sub_nonneg.mpr hle)
            rw [Real.norm_of_nonneg (mul_nonneg hb.1 (hGtilde_nn v))]
            nlinarith [hGtilde_nn v]
          · rw [norm_zero]; exact hGtilde_nn v
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
          have hEv_v := hxφ_top.eventually (Filter.eventually_ge_atTop v)
          have hLim_v : Tendsto (fun k => Z (x (φ k) + (-v)) * Gtilde v) atTop (𝓝 (g (-v) * Gtilde v)) :=
            (hg_shift_lim (-v)).mul_const (Gtilde v)
          rw [hg_const_neg (-v) (by linarith [show (0 : ℝ) < v from hv])] at hLim_v
          refine hLim_v.congr' ?_
          filter_upwards [hEv_v] with k hk
          rw [if_pos hk, sub_eq_add_neg]
      rw [integral_const_mul, hGtilde_val] at hRHS_dct
      have hEq_lim : (premium - (rate : ℝ) * mu) / (premium * nu) =
          c * (((rate : ℝ) / premium) * weightedTail.toReal) :=
        tendsto_nhds_unique (hFub_lim.congr' hFub_eq) hRHS_dct
      have hwt_toR_pos : 0 < weightedTail.toReal := ENNReal.toReal_pos hwt_pos.ne' hwt_top
      have hnet_pos : 0 < premium - (rate : ℝ) * mu := by linarith
      have hden_ne : ((rate : ℝ) / premium) * weightedTail.toReal ≠ 0 := by positivity
      calc c = ((premium - (rate : ℝ) * mu) / (premium * nu)) /
              (((rate : ℝ) / premium) * weightedTail.toReal) := by
            rw [hEq_lim, mul_div_cancel_right₀ _ hden_ne]
        _ = (((rate : ℝ) * nu / (premium - (rate : ℝ) * mu)) * weightedTail.toReal)⁻¹ := by
            field_simp [hpremium.ne', hnu.ne', hrateR.ne', hnet_pos.ne', hwt_toR_pos.ne']
  -- Step 8: Apply hExtremal_eq to M = limsup Z atTop and m = liminf Z atTop
  have hBdd_above : IsBoundedUnder (· ≤ ·) atTop Z :=
    ⟨1, Filter.eventually_map.mpr (Filter.eventually_atTop.mpr ⟨0, fun x hx => (hZ_bdd x hx).2⟩)⟩
  have hBdd_below : IsBoundedUnder (· ≥ ·) atTop Z :=
    ⟨0, Filter.eventually_map.mpr (Filter.eventually_atTop.mpr ⟨0, fun x hx => (hZ_bdd x hx).1⟩)⟩
  set M : ℝ := limsup Z atTop
  set m : ℝ := liminf Z atTop
  have hM_eq : M = L_target := by
    -- Extract a sequence x_k → ∞ with Z (x_k) → M
    have hEx : ∀ k : ℕ, ∃ x : ℝ, (k : ℝ) ≤ x ∧ M - 1 / ((k : ℝ) + 1) < Z x := by
      intro k
      have hlt : M - 1 / ((k : ℝ) + 1) < limsup Z atTop := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      have hFreq := frequently_lt_of_lt_limsup (f := atTop) (u := Z) hBdd_below.isCoboundedUnder_le hlt
      rw [Filter.frequently_atTop] at hFreq
      exact hFreq (k : ℝ)
    choose x hx_ge hx_gt using hEx
    have hx_top : Tendsto x atTop atTop :=
      tendsto_atTop_mono hx_ge tendsto_natCast_atTop_atTop
    have hx_bdd_up : IsBoundedUnder (· ≤ ·) atTop (fun k => Z (x k)) :=
      ⟨1, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun k =>
        (hZ_bdd (x k) (le_trans (Nat.cast_nonneg k) (hx_ge k))).2)⟩
    have hx_bdd_lo : IsBoundedUnder (· ≥ ·) atTop (fun k => Z (x k)) :=
      ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun k =>
        (hZ_bdd (x k) (le_trans (Nat.cast_nonneg k) (hx_ge k))).1)⟩
    have hx_lim : Tendsto (fun k => Z (x k)) atTop (𝓝 M) := by
      refine tendsto_of_le_liminf_of_limsup_le ?_ ?_ hx_bdd_up hx_bdd_lo
      · have h1 : Tendsto (fun k : ℕ => M - 1 / ((k : ℝ) + 1)) atTop (𝓝 M) := by
          simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        rw [← h1.liminf_eq]
        exact liminf_le_liminf (Filter.Eventually.of_forall fun k => (hx_gt k).le)
          h1.isBoundedUnder_ge hx_bdd_up.isCoboundedUnder_ge
      · refine le_of_forall_pos_le_add fun ε hε => ?_
        have hEv := eventually_lt_of_limsup_lt (show limsup Z atTop < M + ε by linarith) hBdd_above
        exact limsup_le_of_le hx_bdd_lo.isCoboundedUnder_le ((hx_top.eventually hEv).mono fun k hk => hk.le)
    refine hExtremal_eq x M hx_top hx_lim (Or.inl fun t φ hφ_mono L hL => ?_)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hEv := eventually_lt_of_limsup_lt (show limsup Z atTop < M + ε by linarith) hBdd_above
    have hEv_k := (tendsto_atTop_add_const_right atTop t (hx_top.comp hφ_mono.tendsto_atTop)).eventually hEv
    exact le_of_tendsto hL (hEv_k.mono fun _ hk => hk.le)
  have hm_eq : m = L_target := by
    have hEx : ∀ k : ℕ, ∃ x : ℝ, (k : ℝ) ≤ x ∧ Z x < m + 1 / ((k : ℝ) + 1) := by
      intro k
      have hlt : liminf Z atTop < m + 1 / ((k : ℝ) + 1) := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      have hFreq := frequently_lt_of_liminf_lt (f := atTop) (u := Z) hBdd_above.isCoboundedUnder_ge hlt
      rw [Filter.frequently_atTop] at hFreq
      exact hFreq (k : ℝ)
    choose x hx_ge hx_lt using hEx
    have hx_top : Tendsto x atTop atTop :=
      tendsto_atTop_mono hx_ge tendsto_natCast_atTop_atTop
    have hx_bdd_up : IsBoundedUnder (· ≤ ·) atTop (fun k => Z (x k)) :=
      ⟨1, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun k =>
        (hZ_bdd (x k) (le_trans (Nat.cast_nonneg k) (hx_ge k))).2)⟩
    have hx_bdd_lo : IsBoundedUnder (· ≥ ·) atTop (fun k => Z (x k)) :=
      ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun k =>
        (hZ_bdd (x k) (le_trans (Nat.cast_nonneg k) (hx_ge k))).1)⟩
    have hx_lim : Tendsto (fun k => Z (x k)) atTop (𝓝 m) := by
      refine tendsto_of_le_liminf_of_limsup_le ?_ ?_ hx_bdd_up hx_bdd_lo
      · refine le_of_forall_pos_le_add fun ε hε => ?_
        have hEv := eventually_lt_of_lt_liminf (show m - ε < liminf Z atTop by linarith) hBdd_below
        have hle := le_liminf_of_le hx_bdd_up.isCoboundedUnder_ge ((hx_top.eventually hEv).mono fun k hk => hk.le)
        linarith
      · have h1 : Tendsto (fun k : ℕ => m + 1 / ((k : ℝ) + 1)) atTop (𝓝 m) := by
          simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        rw [← h1.limsup_eq]
        exact limsup_le_limsup (Filter.Eventually.of_forall fun k => (hx_lt k).le)
          hx_bdd_lo.isCoboundedUnder_le h1.isBoundedUnder_le
    refine hExtremal_eq x m hx_top hx_lim (Or.inr fun t φ hφ_mono L hL => ?_)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hEv := eventually_lt_of_lt_liminf (show m - ε < liminf Z atTop by linarith) hBdd_below
    have hEv_k := (tendsto_atTop_add_const_right atTop t (hx_top.comp hφ_mono.tendsto_atTop)).eventually hEv
    have hle : m - ε ≤ L := ge_of_tendsto hL (hEv_k.mono fun _ hk => hk.le)
    linarith
  exact tendsto_of_le_liminf_of_limsup_le (by rw [← hm_eq]) (by rw [← hM_eq]) hBdd_above hBdd_below

private lemma cramer_step5_fubini
    (fTilde h Z : ℝ → ℝ)
    (hfT_meas : Measurable fTilde) (hfT_nn : ∀ y, 0 ≤ fTilde y)
    (hfT_lintegral : (∫⁻ y in Set.Ioi (0 : ℝ), ENNReal.ofReal (fTilde y) ∂volume) = 1)
    (hfT_int : IntegrableOn fTilde (Set.Ioi (0 : ℝ)) volume)
    (hfT_integral : (∫ y in Set.Ioi (0 : ℝ), fTilde y ∂volume) = 1)
    (hGtilde_nn : ∀ v, 0 ≤ ∫ y in Set.Ioi v, fTilde y ∂volume)
    (hGtilde_le1 : ∀ v, 0 ≤ v → (∫ y in Set.Ioi v, fTilde y ∂volume) ≤ 1)
    (hGtilde_anti : Antitone (fun v => ∫ y in Set.Ioi v, fTilde y ∂volume))
    (hh_int_val_1 : IntegrableOn h (Set.Ioi (0 : ℝ)) volume)
    (hZ_bdd : ∀ x : ℝ, 0 ≤ x → 0 ≤ Z x ∧ Z x ≤ 1)
    (hZ_meas : Measurable Z)
    (hRenew : ∀ x : ℝ, 0 ≤ x → Z x = h x + ∫ y in Set.Ioc (0 : ℝ) x, Z (x - y) * fTilde y ∂volume) :
    ∀ T : ℝ, 0 ≤ T →
      (∫ t in Set.Ioc (0 : ℝ) T, h t ∂volume) =
        ∫ v in Set.Ioc (0 : ℝ) T, Z (T - v) * (∫ y in Set.Ioi v, fTilde y ∂volume) ∂volume := by
  let Gtilde : ℝ → ℝ := fun v => ∫ y in Set.Ioi v, fTilde y ∂volume
  -- Step 5: Exact Fubini identity ∫_{Ioc 0 T} h(t) dt = ∫_{Ioc 0 T} Z(T - v) * Gtilde(v) dv
  have hFubini : ∀ T : ℝ, 0 ≤ T →
      (∫ t in Set.Ioc (0 : ℝ) T, h t ∂volume) =
        ∫ v in Set.Ioc (0 : ℝ) T, Z (T - v) * Gtilde v ∂volume := by
    intro T hT
    have hZ_intT : IntegrableOn Z (Set.Ioc (0 : ℝ) T) volume := by
      refine (integrableOn_const (C := (1 : ℝ)) (hs := measure_Ioc_lt_top.ne)).mono'
        hZ_meas.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_of_nonneg (hZ_bdd t ht.1.le).1]; exact (hZ_bdd t ht.1.le).2
    have hH_intT : IntegrableOn h (Set.Ioc (0 : ℝ) T) volume :=
      hh_int_val_1.mono_set Set.Ioc_subset_Ioi_self
    -- Fubini on (Ioc 0 T) × (Ioi 0) for K(t, y) = 1_{y ≤ t} Z(t - y) fTilde(y)
    let K : ℝ × ℝ → ℝ := fun p => if p.2 ≤ p.1 then Z (p.1 - p.2) * fTilde p.2 else 0
    have hK_meas : Measurable K :=
      Measurable.ite (measurableSet_le measurable_snd measurable_fst)
        ((hZ_meas.comp (measurable_fst.sub measurable_snd)).mul (hfT_meas.comp measurable_snd))
        measurable_const
    have hK_int : Integrable K ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
      refine ⟨hK_meas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hK_meas.enorm.aemeasurable]
      have hInner : ∀ t ∈ Set.Ioc (0 : ℝ) T,
          (∫⁻ y in Set.Ioi (0 : ℝ), ‖K (t, y)‖ₑ ∂volume) ≤ 1 := fun t ht => by
        rw [← hfT_lintegral]
        refine setLIntegral_mono' measurableSet_Ioi fun y hy => ?_
        dsimp only [K]; split_ifs with hyt
        · rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (hZ_bdd (t - y) (sub_nonneg.mpr hyt)).1 (hfT_nn y))]
          exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hfT_nn y) (hZ_bdd (t - y) (sub_nonneg.mpr hyt)).2)
        · simp
      calc ∫⁻ t in Set.Ioc (0 : ℝ) T, ∫⁻ y in Set.Ioi (0 : ℝ), ‖K (t, y)‖ₑ ∂volume ∂volume
          ≤ ∫⁻ _t in Set.Ioc (0 : ℝ) T, (1 : ℝ≥0∞) ∂volume :=
            setLIntegral_mono' measurableSet_Ioc hInner
        _ = volume (Set.Ioc (0 : ℝ) T) := by simp
        _ < ⊤ := measure_Ioc_lt_top
    have hSwap := integral_integral_swap (f := fun t y => K (t, y)) hK_int
    have hLHS_K : (∫ t in Set.Ioc (0 : ℝ) T, ∫ y in Set.Ioi (0 : ℝ), K (t, y) ∂volume ∂volume) =
        (∫ t in Set.Ioc (0 : ℝ) T, Z t ∂volume) - (∫ t in Set.Ioc (0 : ℝ) T, h t ∂volume) := by
      have hEq_t : ∀ t ∈ Set.Ioc (0 : ℝ) T,
          (∫ y in Set.Ioi (0 : ℝ), K (t, y) ∂volume) = Z t - h t := fun t ht => by
        have hInd : (fun y => K (t, y)) = (Set.Iic t).indicator (fun y => Z (t - y) * fTilde y) := by
          ext y; by_cases hyt : y ≤ t <;> simp [K, hyt]
        rw [hInd, setIntegral_indicator measurableSet_Iic]
        have hSet : Set.Ioi (0 : ℝ) ∩ Set.Iic t = Set.Ioc (0 : ℝ) t := rfl
        rw [hSet]
        linarith [hRenew t ht.1.le]
      rw [setIntegral_congr_fun measurableSet_Ioc hEq_t, integral_sub hZ_intT hH_intT]
    have hRHS_K : (∫ y in Set.Ioi (0 : ℝ), ∫ t in Set.Ioc (0 : ℝ) T, K (t, y) ∂volume ∂volume) =
        ∫ u in Set.Ioc (0 : ℝ) T, Z u * (1 - Gtilde (T - u)) ∂volume := by
      have hEq_y : ∀ y ∈ Set.Ioi (0 : ℝ),
          (∫ t in Set.Ioc (0 : ℝ) T, K (t, y) ∂volume) =
            if y ≤ T then fTilde y * ∫ u in Set.Ioc (0 : ℝ) (T - y), Z u ∂volume else 0 := fun y hy => by
        by_cases hyT : y ≤ T
        · rw [if_pos hyT]
          have hInd : (fun t => K (t, y)) = (Set.Ici y).indicator (fun t => Z (t - y) * fTilde y) := by
            ext t; by_cases hyt : y ≤ t <;> simp [K, hyt]
          rw [hInd, setIntegral_indicator measurableSet_Ici]
          have hSet : Set.Ioc (0 : ℝ) T ∩ Set.Ici y = Set.Icc y T := by
            ext t; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
            exact ⟨fun ⟨⟨_, htT⟩, hyt⟩ => ⟨hyt, htT⟩, fun ⟨hyt, htT⟩ => ⟨⟨lt_of_lt_of_le hy hyt, htT⟩, hyt⟩⟩
          rw [hSet, setIntegral_congr_set Ioc_ae_eq_Icc.symm, integral_mul_const, mul_comm]
          congr 1
          rw [← intervalIntegral.integral_of_le hyT, ← intervalIntegral.integral_of_le (sub_nonneg.mpr hyT)]
          simpa [sub_self] using intervalIntegral.integral_comp_sub_right Z y (a := y) (b := T)
        · rw [if_neg hyT]
          have h0 : ∀ t ∈ Set.Ioc (0 : ℝ) T, K (t, y) = 0 := fun t ht => by
            dsimp only [K]; rw [if_neg (by linarith [ht.2])]
          rw [setIntegral_congr_fun measurableSet_Ioc h0, integral_zero]
      rw [setIntegral_congr_fun measurableSet_Ioi hEq_y]
      have hInd_T : (fun y => if y ≤ T then fTilde y * ∫ u in Set.Ioc (0 : ℝ) (T - y), Z u ∂volume else 0) =
          (Set.Iic T).indicator (fun y => fTilde y * ∫ u in Set.Ioc (0 : ℝ) (T - y), Z u ∂volume) := by
        ext y; by_cases hyT : y ≤ T <;> simp [hyT]
      rw [hInd_T, setIntegral_indicator measurableSet_Iic]
      change (∫ y in Set.Ioc (0 : ℝ) T, fTilde y * ∫ u in Set.Ioc (0 : ℝ) (T - y), Z u ∂volume ∂volume) = _
      -- Second Fubini: swap y and u on (Ioc 0 T) × (Ioc 0 T) with u + y ≤ T
      let L : ℝ × ℝ → ℝ := fun p => if p.2 ≤ T - p.1 then fTilde p.1 * Z p.2 else 0
      have hL_meas : Measurable L :=
        Measurable.ite (measurableSet_le measurable_snd (measurable_const.sub measurable_fst))
          ((hfT_meas.comp measurable_fst).mul (hZ_meas.comp measurable_snd))
          measurable_const
      have hL_int : Integrable L ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod (volume.restrict (Set.Ioc (0 : ℝ) T))) := by
        refine ⟨hL_meas.aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hL_meas.enorm.aemeasurable]
        have hInner : ∀ y ∈ Set.Ioc (0 : ℝ) T,
            (∫⁻ u in Set.Ioc (0 : ℝ) T, ‖L (y, u)‖ₑ ∂volume) ≤
              ENNReal.ofReal (fTilde y) * volume (Set.Ioc (0 : ℝ) T) := fun y hy => by
          calc ∫⁻ u in Set.Ioc (0 : ℝ) T, ‖L (y, u)‖ₑ ∂volume
              ≤ ∫⁻ _u in Set.Ioc (0 : ℝ) T, ENNReal.ofReal (fTilde y) ∂volume := by
                refine setLIntegral_mono' measurableSet_Ioc fun u hu => ?_
                dsimp only [L]; split_ifs
                · rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (hfT_nn y) (hZ_bdd u hu.1.le).1)]
                  exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (hfT_nn y) (hZ_bdd u hu.1.le).2)
                · simp
            _ = ENNReal.ofReal (fTilde y) * volume (Set.Ioc (0 : ℝ) T) := by simp
        calc ∫⁻ y in Set.Ioc (0 : ℝ) T, ∫⁻ u in Set.Ioc (0 : ℝ) T, ‖L (y, u)‖ₑ ∂volume ∂volume
            ≤ ∫⁻ y in Set.Ioc (0 : ℝ) T, ENNReal.ofReal (fTilde y) * volume (Set.Ioc (0 : ℝ) T) ∂volume :=
              setLIntegral_mono' measurableSet_Ioc hInner
          _ = (∫⁻ y in Set.Ioc (0 : ℝ) T, ENNReal.ofReal (fTilde y) ∂volume) * volume (Set.Ioc (0 : ℝ) T) :=
              lintegral_mul_const _ (ENNReal.measurable_ofReal.comp hfT_meas)
          _ ≤ 1 * volume (Set.Ioc (0 : ℝ) T) := by
              gcongr; rw [← hfT_lintegral]
              exact lintegral_mono_set Set.Ioc_subset_Ioi_self
          _ < ⊤ := by simp [measure_Ioc_lt_top]
      have hL_left : (∫ y in Set.Ioc (0 : ℝ) T, fTilde y * ∫ u in Set.Ioc (0 : ℝ) (T - y), Z u ∂volume ∂volume) =
          ∫ y in Set.Ioc (0 : ℝ) T, ∫ u in Set.Ioc (0 : ℝ) T, L (y, u) ∂volume ∂volume := by
        refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
        rw [← integral_const_mul]
        have hInd : (fun u => L (y, u)) = (Set.Iic (T - y)).indicator (fun u => fTilde y * Z u) := by
          ext u; by_cases h : u ≤ T - y <;> simp [L, h]
        rw [hInd, setIntegral_indicator measurableSet_Iic]
        have hSet : Set.Ioc (0 : ℝ) T ∩ Set.Iic (T - y) = Set.Ioc (0 : ℝ) (T - y) := by
          ext u; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
          exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, by linarith [hy.1]⟩, h2⟩⟩
        rw [hSet]
      rw [hL_left, integral_integral_swap (f := fun y u => L (y, u)) hL_int]
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      have hInd : (fun y => L (y, u)) = (Set.Iic (T - u)).indicator (fun y => fTilde y * Z u) := by
        ext y; by_cases h : u ≤ T - y
        · have h' : y ≤ T - u := by linarith
          simp [L, h, h']
        · have h' : ¬ y ≤ T - u := by linarith
          simp [L, h, h']
      rw [hInd, setIntegral_indicator measurableSet_Iic]
      have hSet : Set.Ioc (0 : ℝ) T ∩ Set.Iic (T - u) = Set.Ioc (0 : ℝ) (T - u) := by
        ext y; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, by linarith [hu.1]⟩, h2⟩⟩
      rw [hSet, integral_mul_const, mul_comm]
      congr 1
      have hsplit : (∫ y in Set.Ioc (0 : ℝ) (T - u), fTilde y ∂volume) + Gtilde (T - u) = 1 := by
        dsimp only [Gtilde]
        have hset : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) (T - u) ∪ Set.Ioi (T - u) := by
          ext y; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
          constructor
          · intro hy; by_cases hle : y ≤ T - u
            · exact Or.inl ⟨hy, hle⟩
            · exact Or.inr (lt_of_not_ge hle)
          · rintro (⟨hy, _⟩ | hgt); exact hy; linarith [hu.2]
        have hdisj : Disjoint (Set.Ioc (0 : ℝ) (T - u)) (Set.Ioi (T - u)) :=
          Set.disjoint_left.mpr fun y h1 h2 => not_lt_of_ge h1.2 h2
        rw [← setIntegral_union hdisj measurableSet_Ioi
          (hfT_int.mono_set Set.Ioc_subset_Ioi_self)
          (hfT_int.mono_set (Set.Ioi_subset_Ioi (sub_nonneg.mpr hu.2))),
          ← hset, hfT_integral]
      linarith
    have hZG_int : IntegrableOn (fun u => Z u * Gtilde (T - u)) (Set.Ioc (0 : ℝ) T) volume := by
      refine (integrableOn_const (C := (1 : ℝ)) (hs := measure_Ioc_lt_top.ne)).mono'
        (hZ_meas.mul (hGtilde_anti.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hb1 := hZ_bdd u hu.1.le
      have hb2 := hGtilde_le1 (T - u) (sub_nonneg.mpr hu.2)
      rw [Real.norm_of_nonneg (mul_nonneg hb1.1 (hGtilde_nn _))]
      exact le_trans (mul_le_of_le_one_left (hGtilde_nn (T - u)) hb1.2) hb2
    have hEq_final : (∫ t in Set.Ioc (0 : ℝ) T, h t ∂volume) =
        ∫ u in Set.Ioc (0 : ℝ) T, Z u * Gtilde (T - u) ∂volume := by
      have h1 : (∫ u in Set.Ioc (0 : ℝ) T, Z u * (1 - Gtilde (T - u)) ∂volume) =
          (∫ u in Set.Ioc (0 : ℝ) T, Z u ∂volume) - (∫ u in Set.Ioc (0 : ℝ) T, Z u * Gtilde (T - u) ∂volume) := by
        rw [← integral_sub hZ_intT hZG_int]; congr 1; ext u; ring
      linarith [hLHS_K, hRHS_K, hSwap, h1]
    rw [hEq_final, ← intervalIntegral.integral_of_le hT, ← intervalIntegral.integral_of_le hT]
    have h := intervalIntegral.integral_comp_sub_left (fun v => Z (T - v) * Gtilde v) T (a := 0) (b := T)
    simpa [sub_zero, sub_self, sub_sub_cancel] using h
  exact hFubini

theorem solution
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (premium : ℝ) (hpremium : 0 < premium)
    (hnet : (rate : ℝ) * mu < premium)
    (nu : ℝ) (hnu : 0 < nu)
    (hexpint : Integrable (fun x : ℝ => Real.exp (nu * x)) F)
    (hlundberg :
      (rate : ℝ) * (∫ x, (Real.exp (nu * x) - 1) ∂F) = premium * nu)
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hetaSupport : eta (Set.Iio (0 : ℝ)) = 0)
    (heta : ∀ x : ℝ, 0 ≤ x →
      (eta (Set.Iic x)).toReal = integratedTailCDF F mu x) :
    let weightedTail : ℝ≥0∞ :=
      ∫⁻ y in Set.Ioi (0 : ℝ),
        ENNReal.ofReal
          (y * Real.exp (nu * y) * (F (Set.Ioi y)).toReal) ∂volume
    Tendsto (fun x : ℝ => Real.exp (nu * x) *
      (1 - pkCDF eta ((rate : ℝ) * mu / premium) x)) atTop
      (nhds (if weightedTail = ⊤ then 0 else
        (((rate : ℝ) * nu / (premium - (rate : ℝ) * mu)) *
          weightedTail.toReal)⁻¹)) := by
  intro weightedTail
  have hrateR : (0 : ℝ) < (rate : ℝ) := NNReal.coe_pos.mpr hrate
  set ρ : ℝ := (rate : ℝ) * mu / premium
  have hρ_pos : 0 < ρ := div_pos (mul_pos hrateR hmu) hpremium
  have hρ_lt1 : ρ < 1 := (div_lt_one hpremium).mpr hnet
  have heta_eq := integratedTail_eq_withDensity_cr F mu hmu eta hetaSupport heta
  let barF : ℝ → ℝ := fun y => (F (Set.Ioi y)).toReal
  have hbarF_anti : Antitone barF := fun a b hab =>
    ENNReal.toReal_mono (measure_ne_top F _) (measure_mono (Set.Ioi_subset_Ioi hab))
  have hbarF_nn : ∀ y, 0 ≤ barF y := fun _ => ENNReal.toReal_nonneg
  have hbarF_le1 : ∀ y, barF y ≤ 1 := fun y =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := F) (s := Set.Ioi y))
  have hbarF_meas : Measurable barF := hbarF_anti.measurable
  -- Step 1: Cramér-tilted density fTilde on (0, ∞) and ∫_{Ioi 0} fTilde = 1
  let fTilde : ℝ → ℝ := fun y =>
    if 0 < y then ((rate : ℝ) / premium) * Real.exp (nu * y) * barF y else 0
  have hfT_meas : Measurable fTilde :=
    Measurable.ite (measurableSet_lt measurable_const measurable_id)
      ((measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))).mul hbarF_meas)
      measurable_const
  have hfT_nn : ∀ y, 0 ≤ fTilde y := fun y => by
    dsimp only [fTilde]; split_ifs
    · exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (hbarF_nn y)
    · exact le_rfl
  have hF_pos : ∀ᵐ z ∂F, 0 < z := by
    rw [ae_iff]; convert hclaimpos using 2; ext z; simp [not_lt]
  have hfT_lintegral : (∫⁻ y in Set.Ioi (0 : ℝ), ENNReal.ofReal (fTilde y) ∂volume) = 1 := by
    let G : ℝ × ℝ → ℝ≥0∞ := fun p =>
      if p.1 < p.2 then ENNReal.ofReal (((rate : ℝ) / premium) * Real.exp (nu * p.1)) else 0
    have hG_meas : Measurable G :=
      Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
        (ENNReal.measurable_ofReal.comp
          (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_fst))))
        measurable_const
    have hL : (∫⁻ y in Set.Ioi (0 : ℝ), ENNReal.ofReal (fTilde y) ∂volume) =
        ∫⁻ y in Set.Ioi (0 : ℝ), ∫⁻ z, G (y, z) ∂F ∂volume := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      have hypos : 0 < y := hy
      have hEq_z : (fun z => G (y, z)) =
          (Set.Ioi y).indicator (fun _ => ENNReal.ofReal (((rate : ℝ) / premium) * Real.exp (nu * y))) := by
        ext z; by_cases h : y < z <;> simp [G, h]
      rw [hEq_z, lintegral_indicator measurableSet_Ioi, lintegral_const, Measure.restrict_apply_univ]
      dsimp only [fTilde, barF]
      rw [if_pos hypos, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal (measure_ne_top F _)]
    rw [hL, lintegral_lintegral_swap hG_meas.aemeasurable]
    have hInner : ∀ᵐ z ∂F, (∫⁻ y in Set.Ioi (0 : ℝ), G (y, z) ∂volume) =
        ENNReal.ofReal (((rate : ℝ) / (premium * nu)) * (Real.exp (nu * z) - 1)) := by
      filter_upwards [hF_pos] with z hz
      have hEq_y : (fun y => G (y, z)) =
          (Set.Iio z).indicator (fun y => ENNReal.ofReal (((rate : ℝ) / premium) * Real.exp (nu * y))) := by
        ext y; by_cases h : y < z <;> simp [G, h]
      rw [hEq_y, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
      have hSet : Set.Iio z ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) z := by
        ext y; simp [Set.mem_Ioo, Set.mem_Iio, Set.mem_Ioi, and_comm]
      rw [hSet]
      have hInt_Ioo : IntegrableOn (fun y : ℝ => ((rate : ℝ) / premium) * Real.exp (nu * y))
          (Set.Ioo (0 : ℝ) z) volume :=
        (Continuous.continuousOn (continuous_const.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id)))).integrableOn_Icc.mono_set
          Set.Ioo_subset_Icc_self
      rw [← ofReal_integral_eq_lintegral_ofReal hInt_Ioo
        (Filter.Eventually.of_forall fun _ => by positivity),
        setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hz.le,
        intervalIntegral.integral_const_mul]
      have hDeriv : ∀ y ∈ Set.uIcc (0 : ℝ) z,
          HasDerivAt (fun t : ℝ => Real.exp (nu * t) / nu) (Real.exp (nu * y)) y := fun y _ => by
        have h1 : HasDerivAt (fun t : ℝ => nu * t) nu y := by
          simpa using (hasDerivAt_id y).const_mul nu
        have h2 := h1.exp.div_const nu
        have hval : Real.exp (nu * y) * nu / nu = Real.exp (nu * y) := mul_div_cancel_right₀ _ hnu.ne'
        simpa only [hval] using h2
      have hCont : IntervalIntegrable (fun y : ℝ => Real.exp (nu * y)) volume 0 z :=
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 z
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hCont]
      congr 1
      simp only [mul_zero, Real.exp_zero]
      field_simp [hpremium.ne', hnu.ne']
    rw [lintegral_congr_ae hInner]
    have hInt_sub : Integrable (fun z : ℝ => ((rate : ℝ) / (premium * nu)) * (Real.exp (nu * z) - 1)) F :=
      (hexpint.sub (integrable_const 1)).const_mul _
    have hnn_sub : ∀ᵐ z ∂F, 0 ≤ ((rate : ℝ) / (premium * nu)) * (Real.exp (nu * z) - 1) := by
      filter_upwards [hF_pos] with z hz
      exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.one_le_exp (by positivity)))
    rw [← ofReal_integral_eq_lintegral_ofReal hInt_sub hnn_sub, integral_const_mul]
    have hVal : ((rate : ℝ) / (premium * nu)) * (∫ z, (Real.exp (nu * z) - 1) ∂F) = 1 := by
      have h1 : ((rate : ℝ) / (premium * nu)) * (∫ z, (Real.exp (nu * z) - 1) ∂F) =
          ((rate : ℝ) * (∫ z, (Real.exp (nu * z) - 1) ∂F)) / (premium * nu) := by ring
      rw [h1, hlundberg, div_self (mul_pos hpremium hnu).ne']
    rw [hVal, ENNReal.ofReal_one]
  have hfT_int : IntegrableOn fTilde (Set.Ioi (0 : ℝ)) volume := by
    refine ⟨hfT_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hEq : (∫⁻ y in Set.Ioi (0 : ℝ), ‖fTilde y‖ₑ ∂volume) =
        ∫⁻ y in Set.Ioi (0 : ℝ), ENNReal.ofReal (fTilde y) ∂volume := by
      refine lintegral_congr fun y => ?_
      rw [← ofReal_norm, Real.norm_of_nonneg (hfT_nn y)]
    rw [hEq, hfT_lintegral]; exact ENNReal.one_lt_top
  have hfT_integral : (∫ y in Set.Ioi (0 : ℝ), fTilde y ∂volume) = 1 := by
    have h := ofReal_integral_eq_lintegral_ofReal hfT_int (Filter.Eventually.of_forall hfT_nn)
    rw [hfT_lintegral] at h
    exact (ENNReal.ofReal_eq_one).mp h
  -- Step 2: h(x) = ρ * e^{νx} * eta(Ioi x), its continuity, limit 0, and ∫_0^∞ h = (c - λμ)/(cν)
  let h : ℝ → ℝ := fun x => ρ * Real.exp (nu * x) * (eta (Set.Ioi x)).toReal
  have hh_eq_int : ∀ x : ℝ, 0 ≤ x →
      h x = ∫ y in Set.Ioi x, Real.exp (-nu * (y - x)) * fTilde y ∂volume := by
    intro x hx
    have heta_Ioi : eta (Set.Ioi x) =
        ∫⁻ y in Set.Ioi x, ENNReal.ofReal ((1 / mu) * barF y) ∂volume := by
      rw [heta_eq, withDensity_apply _ measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
      have hSet : Set.Ioi x ∩ Set.Ioi (0 : ℝ) = Set.Ioi x :=
        Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi hx)
      rw [hSet]
    have hInt_tail : IntegrableOn (fun y : ℝ => (1 / mu) * barF y) (Set.Ioi x) volume := by
      refine ⟨(measurable_const.mul hbarF_meas).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have hEq : (∫⁻ y in Set.Ioi x, ‖(1 / mu) * barF y‖ₑ ∂volume) = eta (Set.Ioi x) := by
        rw [heta_Ioi]
        refine lintegral_congr fun y => ?_
        rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (by positivity) (hbarF_nn y))]
      rw [hEq]; exact measure_lt_top eta _
    have heta_toR : (eta (Set.Ioi x)).toReal = ∫ y in Set.Ioi x, (1 / mu) * barF y ∂volume := by
      have hof := ofReal_integral_eq_lintegral_ofReal hInt_tail
        (Filter.Eventually.of_forall fun y => mul_nonneg (by positivity) (hbarF_nn y))
      rw [← heta_Ioi] at hof
      rw [← hof, ENNReal.toReal_ofReal (integral_nonneg fun y => mul_nonneg (by positivity) (hbarF_nn y))]
    dsimp only [h]
    rw [heta_toR, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hypos : 0 < y := lt_of_le_of_lt hx hy
    dsimp only [fTilde]
    rw [if_pos hypos]
    have hexp : Real.exp (nu * x) = Real.exp (-nu * (y - x)) * Real.exp (nu * y) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp]
    dsimp only [ρ]
    field_simp [hmu.ne', hpremium.ne']
  have hh_nn : ∀ x, 0 ≤ h x := fun x =>
    mul_nonneg (mul_nonneg hρ_pos.le (Real.exp_pos _).le) ENNReal.toReal_nonneg
  let Gtilde : ℝ → ℝ := fun v => ∫ y in Set.Ioi v, fTilde y ∂volume
  have hGtilde_nn : ∀ v, 0 ≤ Gtilde v := fun v => integral_nonneg hfT_nn
  have hGtilde_le1 : ∀ v, 0 ≤ v → Gtilde v ≤ 1 := fun v hv => by
    dsimp only [Gtilde]
    rw [← hfT_integral]
    exact setIntegral_mono_set hfT_int (Filter.Eventually.of_forall hfT_nn)
      (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi hv))
  have hGtilde_anti : Antitone Gtilde := fun a b hab => by
    dsimp only [Gtilde]
    by_cases ha : 0 ≤ a
    · exact setIntegral_mono_set (hfT_int.mono_set (Set.Ioi_subset_Ioi ha))
        (Filter.Eventually.of_forall hfT_nn)
        (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi hab))
    · have hInt_a : IntegrableOn fTilde (Set.Ioi a) volume := by
        have hEq : fTilde = (Set.Ioi (0 : ℝ)).indicator fTilde := by
          ext y; by_cases hy : 0 < y
          · rw [Set.indicator_of_mem (show y ∈ Set.Ioi (0 : ℝ) from hy)]
          · rw [Set.indicator_of_notMem (show y ∉ Set.Ioi (0 : ℝ) from hy)]; simp [fTilde, hy]
        have hfull : Integrable fTilde volume := by
          rw [hEq, integrable_indicator_iff measurableSet_Ioi]; exact hfT_int
        exact hfull.integrableOn
      exact setIntegral_mono_set hInt_a (Filter.Eventually.of_forall hfT_nn)
        (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi hab))
  have hh_le_tail : ∀ x : ℝ, 0 ≤ x → h x ≤ Gtilde x := fun x hx => by
    rw [hh_eq_int x hx]
    have hInt1 : IntegrableOn (fun y : ℝ => Real.exp (-nu * (y - x)) * fTilde y) (Set.Ioi x) volume := by
      refine (hfT_int.mono_set (Set.Ioi_subset_Ioi hx)).mono'
        ((Real.continuous_exp.measurable.comp (measurable_const.mul (measurable_id.sub measurable_const))).mul
          hfT_meas).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hxy : x < y := hy
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hfT_nn y))]
      have hle1 : Real.exp (-nu * (y - x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      nlinarith [hfT_nn y]
    refine setIntegral_mono_on hInt1 (hfT_int.mono_set (Set.Ioi_subset_Ioi hx)) measurableSet_Ioi fun y hy => ?_
    have hxy : x < y := hy
    have hle1 : Real.exp (-nu * (y - x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    nlinarith [hfT_nn y]
  have hTail_tendsto_zero : Tendsto Gtilde atTop (𝓝 0) := by
    have hEq : ∀ x : ℝ, 0 ≤ x →
        Gtilde x = ∫ y in Set.Ioi (0 : ℝ), (if x < y then fTilde y else 0) ∂volume := fun x hx => by
      dsimp only [Gtilde]
      have hInd : (fun y => if x < y then fTilde y else 0) = (Set.Ioi x).indicator fTilde := by
        ext y; by_cases hy : x < y <;> simp [hy]
      rw [hInd, setIntegral_indicator measurableSet_Ioi,
        Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hx)]
    have hDCT := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (F := fun x y => if x < y then fTilde y else 0)
      (f := fun _ => (0 : ℝ))
      (bound := fTilde)
      (Filter.Eventually.of_forall fun x =>
        (Measurable.ite (measurableSet_lt measurable_const measurable_id) hfT_meas measurable_const).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall fun y => by
        split_ifs
        · rw [Real.norm_of_nonneg (hfT_nn y)]
        · simp [hfT_nn y])
      hfT_int
      (Filter.Eventually.of_forall fun y =>
        tendsto_atTop_of_eventually_const (i₀ := y + 1) fun x hx => by
          rw [if_neg (not_lt.mpr (by linarith))])
    have hDCT0 : Tendsto (fun x : ℝ => ∫ y in Set.Ioi (0 : ℝ), (if x < y then fTilde y else 0) ∂volume)
        atTop (𝓝 0) := by simpa using hDCT
    exact hDCT0.congr' (Filter.eventually_atTop.mpr ⟨0, fun x hx => (hEq x hx).symm⟩)
  have hh_tendsto_zero : Tendsto h atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hTail_tendsto_zero
      (Filter.Eventually.of_forall hh_nn) (Filter.eventually_atTop.mpr ⟨0, hh_le_tail⟩)
  have hh_contOn : ContinuousOn h (Set.Ici (0 : ℝ)) := by
    have heta_cont : ContinuousOn (fun x : ℝ => (eta (Set.Ioi x)).toReal) (Set.Ici (0 : ℝ)) := by
      have hEq : Set.EqOn (fun x : ℝ => (eta (Set.Ioi x)).toReal)
          (fun x : ℝ => 1 - integratedTailCDF F mu x) (Set.Ici (0 : ℝ)) := fun x hx => by
        dsimp only
        rw [← heta x hx, ← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
          ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
      refine ContinuousOn.congr ?_ hEq
      refine continuousOn_const.sub (continuousOn_const.mul ?_)
      have hEqI : Set.EqOn (fun x : ℝ => ∫ y in Set.Ioc (0 : ℝ) x, barF y ∂volume)
          (fun x : ℝ => ∫ y in (0 : ℝ)..x, barF y) (Set.Ici (0 : ℝ)) := fun x hx =>
        (intervalIntegral.integral_of_le hx).symm
      refine ContinuousOn.congr ?_ hEqI
      refine Continuous.continuousOn (intervalIntegral.continuous_primitive (fun a b => ?_) 0)
      rw [intervalIntegrable_iff]
      have hfin : volume (Set.uIoc a b) ≠ ⊤ := by
        rw [Set.uIoc]; exact measure_Ioc_lt_top.ne
      refine (integrableOn_const (C := (1 : ℝ)) (hs := hfin)).mono'
        hbarF_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_of_nonneg (hbarF_nn y)]; exact hbarF_le1 y
    exact ((continuousOn_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul heta_cont)
  have hh_unifCont : ∀ ε > 0, ∃ δ > 0, ∀ x1 : ℝ, 0 ≤ x1 → ∀ x2 : ℝ, 0 ≤ x2 →
      |x1 - x2| < δ → |h x1 - h x2| < ε := by
    intro ε hε
    have hEv := hh_tendsto_zero.eventually (Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < ε / 2))
    rw [Filter.eventually_atTop] at hEv
    obtain ⟨R0, hR0⟩ := hEv
    set R : ℝ := max R0 1
    have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hUC := isCompact_Icc.uniformContinuousOn_of_continuous
      (hh_contOn.mono (Set.Icc_subset_Ici_self : Set.Icc (0 : ℝ) (R + 1) ⊆ Set.Ici (0 : ℝ)))
    rw [Metric.uniformContinuousOn_iff] at hUC
    obtain ⟨δ0, hδ0_pos, hδ0⟩ := hUC ε hε
    refine ⟨min δ0 1, lt_min hδ0_pos zero_lt_one, fun x1 hx1 x2 hx2 hdist => ?_⟩
    have hlt1 : |x1 - x2| < 1 := lt_of_lt_of_le hdist (min_le_right _ _)
    have hltδ : |x1 - x2| < δ0 := lt_of_lt_of_le hdist (min_le_left _ _)
    by_cases h1 : x1 ≤ R
    · have h2 : x2 ≤ R + 1 := by linarith [(abs_lt.mp hlt1).1]
      exact hδ0 x1 ⟨hx1, by linarith⟩ x2 ⟨hx2, h2⟩ hltδ
    · by_cases h2 : x2 ≤ R
      · have h1' : x1 ≤ R + 1 := by linarith [(abs_lt.mp hlt1).2]
        exact hδ0 x1 ⟨hx1, h1'⟩ x2 ⟨hx2, by linarith⟩ hltδ
      · have hx1_ge : R0 ≤ x1 := le_trans (le_max_left _ _) (le_of_not_ge h1)
        have hx2_ge : R0 ≤ x2 := le_trans (le_max_left _ _) (le_of_not_ge h2)
        have hb1 : |h x1| < ε / 2 := by simpa [Real.dist_eq] using hR0 x1 hx1_ge
        have hb2 : |h x2| < ε / 2 := by simpa [Real.dist_eq] using hR0 x2 hx2_ge
        calc |h x1 - h x2| ≤ |h x1| + |h x2| := abs_sub _ _
          _ < ε / 2 + ε / 2 := add_lt_add hb1 hb2
          _ = ε := by ring
  -- ∫_{Ioi 0} h = (premium - rate * mu) / (premium * nu)
  have hh_int_val : IntegrableOn h (Set.Ioi (0 : ℝ)) volume ∧
      (∫ x in Set.Ioi (0 : ℝ), h x ∂volume) = (premium - (rate : ℝ) * mu) / (premium * nu) := by
    have hLint_h : (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (h x) ∂volume) =
        ENNReal.ofReal ((premium - (rate : ℝ) * mu) / (premium * nu)) := by
      let K : ℝ × ℝ → ℝ≥0∞ := fun p =>
        if p.1 < p.2 then ENNReal.ofReal (Real.exp (-nu * (p.2 - p.1)) * fTilde p.2) else 0
      have hK_meas : Measurable K :=
        Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
          (ENNReal.measurable_ofReal.comp
            ((Real.continuous_exp.measurable.comp
              (measurable_const.mul (measurable_snd.sub measurable_fst))).mul
              (hfT_meas.comp measurable_snd)))
          measurable_const
      have hL : (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (h x) ∂volume) =
          ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ y in Set.Ioi (0 : ℝ), K (x, y) ∂volume ∂volume := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        have hxpos : 0 < x := hx
        rw [hh_eq_int x hxpos.le]
        have hInt1 : IntegrableOn (fun y : ℝ => Real.exp (-nu * (y - x)) * fTilde y) (Set.Ioi x) volume := by
          refine (hfT_int.mono_set (Set.Ioi_subset_Ioi hxpos.le)).mono'
            ((Real.continuous_exp.measurable.comp (measurable_const.mul (measurable_id.sub measurable_const))).mul
              hfT_meas).aestronglyMeasurable ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
          have hxy : x < y := hy
          rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hfT_nn y))]
          have hle1 : Real.exp (-nu * (y - x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          nlinarith [hfT_nn y]
        rw [ofReal_integral_eq_lintegral_ofReal hInt1
          (Filter.Eventually.of_forall fun y => mul_nonneg (Real.exp_pos _).le (hfT_nn y))]
        have hInd : (fun y => K (x, y)) =
            (Set.Ioi x).indicator (fun y => ENNReal.ofReal (Real.exp (-nu * (y - x)) * fTilde y)) := by
          ext y; by_cases hxy : x < y <;> simp [K, hxy]
        rw [hInd, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
          Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi hxpos.le)]
      rw [hL, lintegral_lintegral_swap hK_meas.aemeasurable]
      have hInner : ∀ y ∈ Set.Ioi (0 : ℝ),
          (∫⁻ x in Set.Ioi (0 : ℝ), K (x, y) ∂volume) =
            ENNReal.ofReal (fTilde y * ((1 - Real.exp (-nu * y)) / nu)) := fun y hy => by
        have hypos : 0 < y := hy
        have hInd : (fun x => K (x, y)) =
            (Set.Iio y).indicator (fun x => ENNReal.ofReal (Real.exp (-nu * (y - x)) * fTilde y)) := by
          ext x; by_cases hxy : x < y <;> simp [K, hxy]
        rw [hInd, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
        have hSet : Set.Iio y ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) y := by
          ext x; simp [Set.mem_Ioo, Set.mem_Iio, Set.mem_Ioi, and_comm]
        rw [hSet]
        have hInt_Ioo : IntegrableOn (fun x : ℝ => Real.exp (-nu * (y - x)) * fTilde y)
            (Set.Ioo (0 : ℝ) y) volume :=
          (Continuous.continuousOn ((Real.continuous_exp.comp
            (continuous_const.mul (continuous_const.sub continuous_id))).mul continuous_const)).integrableOn_Icc.mono_set
            Set.Ioo_subset_Icc_self
        rw [← ofReal_integral_eq_lintegral_ofReal hInt_Ioo
          (Filter.Eventually.of_forall fun _ => mul_nonneg (Real.exp_pos _).le (hfT_nn y)),
          setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hypos.le,
          intervalIntegral.integral_mul_const]
        have hDeriv : ∀ x ∈ Set.uIcc (0 : ℝ) y,
            HasDerivAt (fun t : ℝ => Real.exp (-nu * (y - t)) / nu) (Real.exp (-nu * (y - x))) x := fun x _ => by
          have h1 : HasDerivAt (fun t : ℝ => -nu * (y - t)) nu x := by
            have hsub : HasDerivAt (fun t : ℝ => y - t) (-1) x := (hasDerivAt_id x).const_sub y
            simpa using hsub.const_mul (-nu)
          have h2 := h1.exp.div_const nu
          have hval : Real.exp (-nu * (y - x)) * nu / nu = Real.exp (-nu * (y - x)) :=
            mul_div_cancel_right₀ _ hnu.ne'
          simpa only [hval] using h2
        have hCont : IntervalIntegrable (fun x : ℝ => Real.exp (-nu * (y - x))) volume 0 y :=
          (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable 0 y
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hCont]
        congr 1
        simp only [sub_self, mul_zero, Real.exp_zero, sub_zero]
        ring
      rw [setLIntegral_congr_fun measurableSet_Ioi hInner]
      have hbarF_int : IntegrableOn barF (Set.Ioi (0 : ℝ)) volume ∧
          (∫ y in Set.Ioi (0 : ℝ), barF y ∂volume) = mu := by
        have heta_univ : eta (Set.Ioi (0 : ℝ)) = 1 := by
          have h1 : eta (Set.Iic (0 : ℝ)) = 0 := by
            have h0 := heta 0 le_rfl
            have hcdf0 : integratedTailCDF F mu 0 = 0 := by
              simp [integratedTailCDF]
            rw [hcdf0] at h0
            exact (ENNReal.toReal_eq_zero_iff _).mp h0 |>.resolve_right (measure_ne_top eta _)
          rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, h1, tsub_zero]
        have hL_bar : (∫⁻ y in Set.Ioi (0 : ℝ), ENNReal.ofReal ((1 / mu) * barF y) ∂volume) = 1 := by
          rw [← heta_univ, heta_eq, withDensity_apply _ measurableSet_Ioi,
            Measure.restrict_restrict measurableSet_Ioi, Set.inter_self]
        have hInt1 : IntegrableOn (fun y => (1 / mu) * barF y) (Set.Ioi (0 : ℝ)) volume := by
          refine ⟨(measurable_const.mul hbarF_meas).aestronglyMeasurable, ?_⟩
          rw [hasFiniteIntegral_iff_enorm]
          have hEq : (∫⁻ y in Set.Ioi (0 : ℝ), ‖(1 / mu) * barF y‖ₑ ∂volume) = 1 := by
            rw [← hL_bar]; refine lintegral_congr fun y => ?_
            rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (by positivity) (hbarF_nn y))]
          rw [hEq]; exact ENNReal.one_lt_top
        have hVal1 : (∫ y in Set.Ioi (0 : ℝ), (1 / mu) * barF y ∂volume) = 1 := by
          have hof := ofReal_integral_eq_lintegral_ofReal hInt1
            (Filter.Eventually.of_forall fun y => mul_nonneg (by positivity) (hbarF_nn y))
          rw [hL_bar] at hof
          exact (ENNReal.ofReal_eq_one).mp hof
        have hInt_b : IntegrableOn barF (Set.Ioi (0 : ℝ)) volume := by
          have := hInt1.const_mul mu
          refine this.congr (Filter.Eventually.of_forall fun y => ?_)
          field_simp [hmu.ne']
        refine ⟨hInt_b, ?_⟩
        rw [integral_const_mul] at hVal1
        have : mu * ((1 / mu) * ∫ y in Set.Ioi (0 : ℝ), barF y ∂volume) = mu * 1 := congrArg (mu * ·) hVal1
        have hsimp : mu * ((1 / mu) * ∫ y in Set.Ioi (0 : ℝ), barF y ∂volume) =
            ∫ y in Set.Ioi (0 : ℝ), barF y ∂volume := by field_simp [hmu.ne']
        linarith
      have hFun_eq : Set.EqOn (fun y => fTilde y * ((1 - Real.exp (-nu * y)) / nu))
          (fun y => (fTilde y - ((rate : ℝ) / premium) * barF y) / nu) (Set.Ioi (0 : ℝ)) := fun y hy => by
        have hypos : 0 < y := hy
        dsimp only [fTilde]
        rw [if_pos hypos]
        have hexp : Real.exp (nu * y) * Real.exp (-nu * y) = 1 := by
          rw [← Real.exp_add]; simp
        calc ((rate : ℝ) / premium) * Real.exp (nu * y) * barF y * ((1 - Real.exp (-nu * y)) / nu)
            = (((rate : ℝ) / premium) * Real.exp (nu * y) * barF y -
                ((rate : ℝ) / premium) * (Real.exp (nu * y) * Real.exp (-nu * y)) * barF y) / nu := by ring
          _ = (((rate : ℝ) / premium) * Real.exp (nu * y) * barF y -
                ((rate : ℝ) / premium) * barF y) / nu := by rw [hexp, mul_one]
      have hInt_diff : IntegrableOn (fun y => fTilde y * ((1 - Real.exp (-nu * y)) / nu))
          (Set.Ioi (0 : ℝ)) volume :=
        IntegrableOn.congr_fun ((hfT_int.sub (hbarF_int.1.const_mul _)).div_const nu) hFun_eq.symm measurableSet_Ioi
      have hnn_diff : ∀ᵐ y ∂(volume.restrict (Set.Ioi (0 : ℝ))),
          0 ≤ fTilde y * ((1 - Real.exp (-nu * y)) / nu) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        have hypos : 0 < y := hy
        exact mul_nonneg (hfT_nn y) (div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))) hnu.le)
      rw [← ofReal_integral_eq_lintegral_ofReal hInt_diff hnn_diff,
        setIntegral_congr_fun measurableSet_Ioi hFun_eq, integral_div,
        integral_sub hfT_int (hbarF_int.1.const_mul _), integral_const_mul,
        hfT_integral, hbarF_int.2]
      congr 1
      field_simp [hpremium.ne', hnu.ne']
    have hh_meas : Measurable h :=
      (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))).mul
        (Antitone.measurable fun a b hab =>
          ENNReal.toReal_mono (measure_ne_top eta _) (measure_mono (Set.Ioi_subset_Ioi hab)))
    have hh_int : IntegrableOn h (Set.Ioi (0 : ℝ)) volume := by
      refine ⟨hh_meas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have hEq : (∫⁻ x in Set.Ioi (0 : ℝ), ‖h x‖ₑ ∂volume) =
          ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (h x) ∂volume := by
        refine lintegral_congr fun x => ?_
        rw [← ofReal_norm, Real.norm_of_nonneg (hh_nn x)]
      rw [hEq, hLint_h]; exact ENNReal.ofReal_lt_top
    have hVal : (∫ x in Set.Ioi (0 : ℝ), h x ∂volume) =
        (premium - (rate : ℝ) * mu) / (premium * nu) := by
      have hof := ofReal_integral_eq_lintegral_ofReal hh_int (Filter.Eventually.of_forall hh_nn)
      rw [hLint_h] at hof
      have hpos : 0 ≤ (premium - (rate : ℝ) * mu) / (premium * nu) :=
        div_nonneg (by linarith) (mul_pos hpremium hnu).le
      exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hh_nn) hpos).mp hof
    exact ⟨hh_int, hVal⟩
  -- Step 3: Renewal equation and Lundberg bound 0 ≤ Z x ≤ 1
  let Fk : ℕ → ℝ → ℝ := fun k x => ((QueueingFundamentals.MG1.convPow eta k) (Set.Iic x)).toReal
  have hconvProb : ∀ k, IsProbabilityMeasure (QueueingFundamentals.MG1.convPow eta k) :=
    isProbabilityMeasure_convPow_cr eta
  have hconvSupp : ∀ k, QueueingFundamentals.MG1.convPow eta k (Set.Iio (0 : ℝ)) = 0 :=
    convPow_Iio_zero_cr eta hetaSupport
  have hFk_bdd : ∀ k x, 0 ≤ Fk k x ∧ Fk k x ≤ 1 := fun k x => by
    have := hconvProb k
    exact ⟨ENNReal.toReal_nonneg,
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := QueueingFundamentals.MG1.convPow eta k) (s := Set.Iic x))⟩
  have hFk_mono : ∀ k, Monotone (Fk k) := fun k a b hab => by
    have := hconvProb k
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr hab))
  have hFk_conv : ∀ k : ℕ, ∀ x : ℝ, 0 ≤ x →
      1 - Fk (k + 1) x = (eta (Set.Ioi x)).toReal +
        ∫ y in Set.Ioc (0 : ℝ) x, (1 - Fk k (x - y)) * ((1 / mu) * barF y) ∂volume := by
    intro k x hx
    have := hconvProb k
    have := hconvProb (k + 1)
    have hConv_eq : QueueingFundamentals.MG1.convPow eta (k + 1) (Set.Iic x) =
        ∫⁻ y in Set.Ioc (0 : ℝ) x,
          QueueingFundamentals.MG1.convPow eta k (Set.Iic (x - y)) *
            ENNReal.ofReal ((1 / mu) * barF y) ∂volume := by
      dsimp only [QueueingFundamentals.MG1.convPow]
      rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Iic]
      have hMeasS : MeasurableSet ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Set.Iic x) :=
        measurableSet_le (measurable_fst.add measurable_snd) measurable_const
      rw [Measure.prod_apply_symm hMeasS]
      have hpre : ∀ y : ℝ, (fun u : ℝ => (u, y)) ⁻¹' ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Set.Iic x) =
          Set.Iic (x - y) := fun y => by ext u; simp [le_sub_iff_add_le]
      simp_rw [hpre]
      have hDensity : (∫⁻ y, QueueingFundamentals.MG1.convPow eta k (Set.Iic (x - y)) ∂eta) =
          ∫⁻ y in Set.Ioi (0 : ℝ), ENNReal.ofReal ((1 / mu) * barF y) *
            QueueingFundamentals.MG1.convPow eta k (Set.Iic (x - y)) ∂volume := by
        have hMeas_k : Measurable (fun y => QueueingFundamentals.MG1.convPow eta k (Set.Iic (x - y))) := by
          have hEq_m : (fun y => QueueingFundamentals.MG1.convPow eta k (Set.Iic (x - y))) =
              fun y => ENNReal.ofReal (Fk k (x - y)) :=
            funext fun y => (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
          rw [hEq_m]
          exact ENNReal.measurable_ofReal.comp ((hFk_mono k).measurable.comp (measurable_const.sub measurable_id))
        have hD := lintegral_withDensity_eq_lintegral_mul (volume.restrict (Set.Ioi (0 : ℝ)))
          (f := fun y => ENNReal.ofReal ((1 / mu) * barF y))
          (ENNReal.measurable_ofReal.comp (measurable_const.mul hbarF_meas)) hMeas_k
        have heta_eq' : eta = (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
            (fun y => ENNReal.ofReal ((1 / mu) * barF y)) := heta_eq
        rw [← heta_eq'] at hD
        exact hD
      rw [hDensity]
      have hzero : ∀ y ∈ Set.Ioi (0 : ℝ), y ∉ Set.Ioc (0 : ℝ) x →
            ENNReal.ofReal ((1 / mu) * barF y) *
              QueueingFundamentals.MG1.convPow eta k (Set.Iic (x - y)) = 0 := fun y hy hnot => by
        have hgt : x < y := by
          by_contra hle; exact hnot ⟨hy, le_of_not_gt hle⟩
        have hsub : Set.Iic (x - y) ⊆ Set.Iio (0 : ℝ) := fun u hu => by
          have : u ≤ x - y := hu; show u < 0; linarith
        rw [measure_mono_null hsub (hconvSupp k), mul_zero]
      have hEq_ind : ∀ y ∈ Set.Ioi (0 : ℝ),
            ENNReal.ofReal ((1 / mu) * barF y) *
              QueueingFundamentals.MG1.convPow eta k (Set.Iic (x - y)) =
            (Set.Ioc (0 : ℝ) x).indicator (fun y =>
              QueueingFundamentals.MG1.convPow eta k (Set.Iic (x - y)) *
                ENNReal.ofReal ((1 / mu) * barF y)) y := fun y hy => by
          by_cases hmem : y ∈ Set.Ioc (0 : ℝ) x
          · rw [Set.indicator_of_mem hmem, mul_comm]
          · rw [Set.indicator_of_notMem hmem, hzero y hy hmem]
      rw [setLIntegral_congr_fun measurableSet_Ioi hEq_ind,
        lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
        Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self]
    have hInt_Fk : IntegrableOn (fun y : ℝ => Fk k (x - y) * ((1 / mu) * barF y))
        (Set.Ioc (0 : ℝ) x) volume := by
      refine (integrableOn_const (C := 1 / mu) (hs := measure_Ioc_lt_top.ne)).mono'
        (((hFk_mono k).measurable.comp (measurable_const.sub measurable_id)).mul
          (measurable_const.mul hbarF_meas)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      have h1 := hFk_bdd k (x - y)
      have h2 := hbarF_nn y
      have h3 := hbarF_le1 y
      rw [Real.norm_of_nonneg (mul_nonneg h1.1 (mul_nonneg (by positivity) h2))]
      calc Fk k (x - y) * (1 / mu * barF y)
          ≤ 1 * (1 / mu * barF y) := mul_le_mul_of_nonneg_right h1.2 (mul_nonneg (by positivity) h2)
        _ = 1 / mu * barF y := one_mul _
        _ ≤ 1 / mu * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 1 / mu := mul_one _
    have hInt_1 : IntegrableOn (fun y : ℝ => (1 / mu) * barF y) (Set.Ioc (0 : ℝ) x) volume := by
      refine (integrableOn_const (C := 1 / mu) (hs := measure_Ioc_lt_top.ne)).mono'
        (measurable_const.mul hbarF_meas).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hbarF_nn y))]
      nlinarith [hbarF_le1 y, div_pos one_pos hmu]
    have hFk_next_eq : Fk (k + 1) x =
        ∫ y in Set.Ioc (0 : ℝ) x, Fk k (x - y) * ((1 / mu) * barF y) ∂volume := by
      have hof := ofReal_integral_eq_lintegral_ofReal hInt_Fk
        (Filter.Eventually.of_forall fun y => mul_nonneg (hFk_bdd k (x - y)).1 (mul_nonneg (by positivity) (hbarF_nn y)))
      have hEq_l : (∫⁻ y in Set.Ioc (0 : ℝ) x,
          ENNReal.ofReal (Fk k (x - y) * ((1 / mu) * barF y)) ∂volume) =
          QueueingFundamentals.MG1.convPow eta (k + 1) (Set.Iic x) := by
        rw [hConv_eq]
        refine lintegral_congr fun y => ?_
        rw [ENNReal.ofReal_mul (hFk_bdd k (x - y)).1]
        dsimp only [Fk]
        rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rw [hEq_l] at hof
      dsimp only [Fk]
      rw [← hof, ENNReal.toReal_ofReal (integral_nonneg fun y =>
        mul_nonneg (hFk_bdd k (x - y)).1 (mul_nonneg (by positivity) (hbarF_nn y)))]
    have heta_Iic_int : (eta (Set.Iic x)).toReal =
        ∫ y in Set.Ioc (0 : ℝ) x, (1 / mu) * barF y ∂volume := by
      rw [heta x hx, integratedTailCDF, ← integral_const_mul]
    have heta_split : (eta (Set.Ioi x)).toReal + (eta (Set.Iic x)).toReal = 1 := by
      rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
        ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
      ring
    rw [hFk_next_eq]
    have hsub_int : (∫ y in Set.Ioc (0 : ℝ) x, (1 - Fk k (x - y)) * ((1 / mu) * barF y) ∂volume) =
        (∫ y in Set.Ioc (0 : ℝ) x, (1 / mu) * barF y ∂volume) -
          (∫ y in Set.Ioc (0 : ℝ) x, Fk k (x - y) * ((1 / mu) * barF y) ∂volume) := by
      rw [← integral_sub hInt_1 hInt_Fk]
      congr 1; ext y; ring
    rw [hsub_int, ← heta_Iic_int]
    linarith
  -- Partial sums Z_N(x) and exact limit Z(x) = exp(νx) * (1 - pkCDF eta ρ x)
  let Z : ℝ → ℝ := fun x => Real.exp (nu * x) * (1 - pkCDF eta ρ x)
  let ZN : ℕ → ℝ → ℝ := fun N x =>
    Real.exp (nu * x) * ((1 - ρ) * ∑ k ∈ Finset.range (N + 1), ρ ^ k * (1 - Fk k x))
  have hZ_eq_tsum : ∀ x : ℝ, 0 ≤ x →
      Tendsto (fun N => ZN N x) atTop (𝓝 (Z x)) := by
    intro x _
    have hSum1 : Summable (fun k : ℕ => ρ ^ k) := summable_geometric_of_lt_one hρ_pos.le hρ_lt1
    have hSum2 : Summable (fun k : ℕ => ρ ^ k * Fk k x) :=
      hSum1.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg hρ_pos.le k) (hFk_bdd k x).1)
        (fun k => mul_le_of_le_one_right (pow_nonneg hρ_pos.le k) (hFk_bdd k x).2)
    have hSum_diff : Summable (fun k : ℕ => ρ ^ k * (1 - Fk k x)) := by
      have hEq : (fun k : ℕ => ρ ^ k * (1 - Fk k x)) = fun k => ρ ^ k - ρ ^ k * Fk k x := by
        ext k; ring
      rw [hEq]; exact hSum1.sub hSum2
    have hTsum_val : (1 - ρ) * (∑' k : ℕ, ρ ^ k * (1 - Fk k x)) = 1 - pkCDF eta ρ x := by
      dsimp only [pkCDF, Fk]
      have hEq : (fun k : ℕ => ρ ^ k * (1 - ((QueueingFundamentals.MG1.convPow eta k) (Set.Iic x)).toReal)) =
          fun k => ρ ^ k - ρ ^ k * ((QueueingFundamentals.MG1.convPow eta k) (Set.Iic x)).toReal := by
        ext k; ring
      rw [hEq, hSum1.tsum_sub hSum2, tsum_geometric_of_lt_one hρ_pos.le hρ_lt1]
      have h1 : (1 - ρ) * (1 - ρ)⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
      calc (1 - ρ) * ((1 - ρ)⁻¹ - ∑' k, ρ ^ k * ((QueueingFundamentals.MG1.convPow eta k) (Set.Iic x)).toReal)
          = (1 - ρ) * (1 - ρ)⁻¹ - (1 - ρ) * ∑' k, ρ ^ k * ((QueueingFundamentals.MG1.convPow eta k) (Set.Iic x)).toReal := by ring
        _ = 1 - (1 - ρ) * ∑' k, ρ ^ k * ((QueueingFundamentals.MG1.convPow eta k) (Set.Iic x)).toReal := by rw [h1]
    have hLim := (hSum_diff.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_mul (1 - ρ)
    rw [hTsum_val] at hLim
    exact hLim.const_mul (Real.exp (nu * x))
  have hZN_rec : ∀ N : ℕ, ∀ x : ℝ, 0 ≤ x →
      ZN (N + 1) x = (1 - ρ ^ (N + 1)) * h x +
        ∫ y in Set.Ioc (0 : ℝ) x, ZN N (x - y) * fTilde y ∂volume := by
    intro N x hx
    have hFk0 : 1 - Fk 0 x = 0 := by
      dsimp only [Fk, QueueingFundamentals.MG1.convPow]
      rw [Measure.dirac_apply' _ measurableSet_Iic, Set.indicator_of_mem (show (0 : ℝ) ∈ Set.Iic x from hx)]
      simp
    have hSplit : ∑ k ∈ Finset.range (N + 2), ρ ^ k * (1 - Fk k x) =
        ∑ k ∈ Finset.range (N + 1), ρ ^ (k + 1) * (1 - Fk (k + 1) x) := by
      rw [Finset.sum_range_succ', pow_zero, one_mul, hFk0, add_zero]
    have hInt_k : ∀ k : ℕ, IntegrableOn (fun y : ℝ => (1 - Fk k (x - y)) * ((1 / mu) * barF y))
        (Set.Ioc (0 : ℝ) x) volume := fun k => by
      refine (integrableOn_const (C := 1 / mu) (hs := measure_Ioc_lt_top.ne)).mono'
        (((measurable_const.sub ((hFk_mono k).measurable.comp (measurable_const.sub measurable_id)))).mul
          (measurable_const.mul hbarF_meas)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      have h1 := hFk_bdd k (x - y)
      rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (mul_nonneg (by positivity) (hbarF_nn y)))]
      calc (1 - Fk k (x - y)) * (1 / mu * barF y)
          ≤ 1 * (1 / mu * barF y) := mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by positivity) (hbarF_nn y))
        _ = 1 / mu * barF y := one_mul _
        _ ≤ 1 / mu * 1 := mul_le_mul_of_nonneg_left (hbarF_le1 y) (by positivity)
        _ = 1 / mu := mul_one _
    dsimp only [ZN]
    rw [hSplit]
    have hSub : ∀ k ∈ Finset.range (N + 1),
        ρ ^ (k + 1) * (1 - Fk (k + 1) x) =
          ρ ^ (k + 1) * (eta (Set.Ioi x)).toReal +
            ∫ y in Set.Ioc (0 : ℝ) x, (ρ ^ (k + 1) * (1 - Fk k (x - y))) * ((1 / mu) * barF y) ∂volume := by
      intro k _
      rw [hFk_conv k x hx, mul_add, ← integral_const_mul]
      congr 1; refine setIntegral_congr_fun measurableSet_Ioc fun y _ => by ring
    rw [Finset.sum_congr rfl hSub, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← integral_finsetSum _ (fun k _ => by
        have := (hInt_k k).const_mul (ρ ^ (k + 1))
        exact this.congr (Filter.Eventually.of_forall fun y => by ring))]
    have hGeom : (1 - ρ) * (∑ k ∈ Finset.range (N + 1), ρ ^ (k + 1)) = ρ * (1 - ρ ^ (N + 1)) := by
      have h1 : ∑ k ∈ Finset.range (N + 1), ρ ^ (k + 1) = ρ * ∑ k ∈ Finset.range (N + 1), ρ ^ k := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      rw [h1]
      have h2 := geom_sum_mul ρ (N + 1)
      nlinarith
    rw [mul_add, mul_add, ← mul_assoc (1 - ρ), hGeom, ← integral_const_mul, ← integral_const_mul]
    congr 1
    · dsimp only [h]; ring
    · refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
      have hypos : 0 < y := hy.1
      dsimp only [fTilde]
      rw [if_pos hypos]
      have hexp : Real.exp (nu * x) = Real.exp (nu * (x - y)) * Real.exp (nu * y) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp]
      have hPull : ∑ k ∈ Finset.range (N + 1), ρ ^ (k + 1) * (1 - Fk k (x - y)) * ((1 / mu) * barF y) =
          (∑ k ∈ Finset.range (N + 1), ρ ^ k * (1 - Fk k (x - y))) * (ρ * ((1 / mu) * barF y)) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by ring
      rw [hPull]
      dsimp only [ρ]
      field_simp [hmu.ne', hpremium.ne']
  have hZN_bdd : ∀ N : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ ZN N x ∧ ZN N x ≤ 1 := by
    intro N
    induction N with
    | zero =>
        intro x hx
        have h0 : ZN 0 x = 0 := by
          dsimp only [ZN, Fk]
          change Real.exp (nu * x) * ((1 - ρ) * ∑ k ∈ Finset.range 1,
            ρ ^ k * (1 - ((Measure.dirac (0 : ℝ)) (Set.Iic x)).toReal)) = 0
          rw [Finset.sum_range_one, pow_zero, one_mul, Measure.dirac_apply' _ measurableSet_Iic,
            Set.indicator_of_mem (show (0 : ℝ) ∈ Set.Iic x from hx)]
          simp
        rw [h0]; exact ⟨le_rfl, zero_le_one⟩
    | succ N ih =>
        intro x hx
        have hnn : 0 ≤ ZN (N + 1) x := by
          dsimp only [ZN]
          refine mul_nonneg (Real.exp_pos _).le (mul_nonneg (by linarith) ?_)
          exact Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg hρ_pos.le k) (by linarith [(hFk_bdd k x).2])
        refine ⟨hnn, ?_⟩
        rw [hZN_rec N x hx]
        have hInt_ZN : IntegrableOn (fun y => ZN N (x - y) * fTilde y) (Set.Ioc (0 : ℝ) x) volume := by
          refine (hfT_int.mono_set Set.Ioc_subset_Ioi_self).mono' ?_ ?_
          · have hZN_meas : Measurable (ZN N) :=
              (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).mul
                (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
                  measurable_const.mul (measurable_const.sub (hFk_mono k).measurable)))
            exact ((hZN_meas.comp (measurable_const.sub measurable_id)).mul hfT_meas).aestronglyMeasurable
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
            have hxy : 0 ≤ x - y := sub_nonneg.mpr hy.2
            have hb := ih (x - y) hxy
            rw [Real.norm_of_nonneg (mul_nonneg hb.1 (hfT_nn y))]
            nlinarith [hfT_nn y]
        have hle_int : (∫ y in Set.Ioc (0 : ℝ) x, ZN N (x - y) * fTilde y ∂volume) ≤
            ∫ y in Set.Ioc (0 : ℝ) x, fTilde y ∂volume := by
          refine setIntegral_mono_on hInt_ZN (hfT_int.mono_set Set.Ioc_subset_Ioi_self) measurableSet_Ioc fun y hy => ?_
          have hb := ih (x - y) (sub_nonneg.mpr hy.2)
          nlinarith [hfT_nn y]
        have hle_h : (1 - ρ ^ (N + 1)) * h x ≤ Gtilde x := by
          have h1 : (1 - ρ ^ (N + 1)) * h x ≤ h x := by
            have : 0 ≤ ρ ^ (N + 1) := pow_nonneg hρ_pos.le _
            nlinarith [hh_nn x]
          exact le_trans h1 (hh_le_tail x hx)
        have hsplit : (∫ y in Set.Ioc (0 : ℝ) x, fTilde y ∂volume) + Gtilde x = 1 := by
          dsimp only [Gtilde]
          have hset : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) x ∪ Set.Ioi x := by
            ext y; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
            constructor
            · intro hy; by_cases hle : y ≤ x
              · exact Or.inl ⟨hy, hle⟩
              · exact Or.inr (lt_of_not_ge hle)
            · rintro (⟨hy, _⟩ | hgt); exact hy; linarith
          have hdisj : Disjoint (Set.Ioc (0 : ℝ) x) (Set.Ioi x) :=
            Set.disjoint_left.mpr fun y h1 h2 => not_lt_of_ge h1.2 h2
          rw [← setIntegral_union hdisj measurableSet_Ioi
            (hfT_int.mono_set Set.Ioc_subset_Ioi_self) (hfT_int.mono_set (Set.Ioi_subset_Ioi hx)),
            ← hset, hfT_integral]
        linarith
  have hZ_bdd : ∀ x : ℝ, 0 ≤ x → 0 ≤ Z x ∧ Z x ≤ 1 := fun x hx =>
    ⟨ge_of_tendsto (hZ_eq_tsum x hx) (Filter.Eventually.of_forall fun N => (hZN_bdd N x hx).1),
     le_of_tendsto (hZ_eq_tsum x hx) (Filter.Eventually.of_forall fun N => (hZN_bdd N x hx).2)⟩
  have hZ_meas : Measurable Z := by
    have hpk_mono : Monotone (fun x => pkCDF eta ρ x) := fun a b hab => by
      dsimp only [pkCDF]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      have hS : ∀ x, Summable (fun k : ℕ => ρ ^ k * Fk k x) := fun x =>
        (summable_geometric_of_lt_one hρ_pos.le hρ_lt1).of_nonneg_of_le
          (fun k => mul_nonneg (pow_nonneg hρ_pos.le k) (hFk_bdd k x).1)
          (fun k => mul_le_of_le_one_right (pow_nonneg hρ_pos.le k) (hFk_bdd k x).2)
      exact Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hFk_mono k hab) (pow_nonneg hρ_pos.le k))
        (hS a) (hS b)
    exact (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).mul
      (measurable_const.sub hpk_mono.measurable)
  -- Exact renewal equation Z(x) = h(x) + ∫_{Ioc 0 x} Z(x - y) * fTilde(y) dy for all x ≥ 0
  have hRenew : ∀ x : ℝ, 0 ≤ x →
      Z x = h x + ∫ y in Set.Ioc (0 : ℝ) x, Z (x - y) * fTilde y ∂volume := by
    intro x hx
    have hLHS : Tendsto (fun N => ZN (N + 1) x) atTop (𝓝 (Z x)) :=
      (hZ_eq_tsum x hx).comp (tendsto_add_atTop_nat 1)
    have hTerm1 : Tendsto (fun N => (1 - ρ ^ (N + 1)) * h x) atTop (𝓝 (h x)) := by
      have hpow : Tendsto (fun N => ρ ^ (N + 1)) atTop (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ_pos.le hρ_lt1).comp (tendsto_add_atTop_nat 1)
      have hlim := (tendsto_const_nhds (x := (1 : ℝ)).sub hpow).mul_const (h x)
      rwa [sub_zero, one_mul] at hlim
    have hTerm2 : Tendsto (fun N => ∫ y in Set.Ioc (0 : ℝ) x, ZN N (x - y) * fTilde y ∂volume)
        atTop (𝓝 (∫ y in Set.Ioc (0 : ℝ) x, Z (x - y) * fTilde y ∂volume)) := by
      refine tendsto_integral_of_dominated_convergence fTilde ?_ (hfT_int.mono_set Set.Ioc_subset_Ioi_self) ?_ ?_
      · intro N
        have hZN_meas : Measurable (ZN N) :=
          (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).mul
            (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul (measurable_const.sub (hFk_mono k).measurable)))
        exact ((hZN_meas.comp (measurable_const.sub measurable_id)).mul hfT_meas).aestronglyMeasurable
      · intro N
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        have hb := hZN_bdd N (x - y) (sub_nonneg.mpr hy.2)
        rw [Real.norm_of_nonneg (mul_nonneg hb.1 (hfT_nn y))]
        nlinarith [hfT_nn y]
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        exact (hZ_eq_tsum (x - y) (sub_nonneg.mpr hy.2)).mul_const (fTilde y)
    have hRHS := hTerm1.add hTerm2
    have hEq_seq : (fun N => ZN (N + 1) x) = fun N =>
        (1 - ρ ^ (N + 1)) * h x + ∫ y in Set.Ioc (0 : ℝ) x, ZN N (x - y) * fTilde y ∂volume :=
      funext fun N => hZN_rec N x hx
    rw [hEq_seq] at hLHS
    exact tendsto_nhds_unique hLHS hRHS
  have hZ_unifCont : ∀ ε > 0, ∃ δ > 0, ∀ x1 : ℝ, 0 ≤ x1 → ∀ x2 : ℝ, 0 ≤ x2 →
      |x1 - x2| < δ → |Z x1 - Z x2| < ε :=
    cramer_step4_unifCont rate premium nu hpremium hnu barF h Z hbarF_anti hbarF_le1
      hfT_meas hfT_nn hfT_int hTail_tendsto_zero hGtilde_nn hGtilde_anti hh_unifCont hZ_bdd hZ_meas hRenew
  have hFubini : ∀ T : ℝ, 0 ≤ T →
      (∫ t in Set.Ioc (0 : ℝ) T, h t ∂volume) =
        ∫ v in Set.Ioc (0 : ℝ) T, Z (T - v) * Gtilde v ∂volume :=
    cramer_step5_fubini fTilde h Z hfT_meas hfT_nn hfT_lintegral hfT_int hfT_integral
      hGtilde_nn hGtilde_le1 hGtilde_anti hh_int_val.1 hZ_bdd hZ_meas hRenew
  -- Step 6: Compute ∫⁻_{Ioi 0} Gtilde = ((rate/premium) * weightedTail) and find strict positivity window (0, a)
  have hGtilde_lintegral : (∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (Gtilde v) ∂volume) =
      ENNReal.ofReal ((rate : ℝ) / premium) * weightedTail := by
    let M : ℝ × ℝ → ℝ≥0∞ := fun p => if p.1 < p.2 then ENNReal.ofReal (fTilde p.2) else 0
    have hM_meas : Measurable M :=
      Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
        (ENNReal.measurable_ofReal.comp (hfT_meas.comp measurable_snd))
        measurable_const
    have hL : (∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (Gtilde v) ∂volume) =
        ∫⁻ v in Set.Ioi (0 : ℝ), ∫⁻ y in Set.Ioi (0 : ℝ), M (v, y) ∂volume ∂volume := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
      dsimp only [Gtilde]
      rw [ofReal_integral_eq_lintegral_ofReal (hfT_int.mono_set (Set.Ioi_subset_Ioi (le_of_lt hv)))
        (Filter.Eventually.of_forall hfT_nn)]
      have hInd : (fun y => M (v, y)) = (Set.Ioi v).indicator (fun y => ENNReal.ofReal (fTilde y)) := by
        ext y; by_cases hvy : v < y <;> simp [M, hvy]
      rw [hInd, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
        Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi (le_of_lt hv))]
    rw [hL, lintegral_lintegral_swap hM_meas.aemeasurable]
    have hInner : ∀ y ∈ Set.Ioi (0 : ℝ),
        (∫⁻ v in Set.Ioi (0 : ℝ), M (v, y) ∂volume) =
          ENNReal.ofReal ((rate : ℝ) / premium) *
            ENNReal.ofReal (y * Real.exp (nu * y) * barF y) := fun y hy => by
      have hypos : 0 < y := hy
      have hInd : (fun v => M (v, y)) = (Set.Iio y).indicator (fun _ => ENNReal.ofReal (fTilde y)) := by
        ext v; by_cases hvy : v < y <;> simp [M, hvy]
      rw [hInd, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
        lintegral_const]
      have hSet : Set.Iio y ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) y := by
        ext v; simp [Set.mem_Ioo, Set.mem_Iio, Set.mem_Ioi, and_comm]
      rw [hSet, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
        ← ENNReal.ofReal_mul (hfT_nn y), ← ENNReal.ofReal_mul (by positivity)]
      congr 1; dsimp only [fTilde]; rw [if_pos hypos]; ring
    rw [setLIntegral_congr_fun measurableSet_Ioi hInner, lintegral_const_mul]
    exact ENNReal.measurable_ofReal.comp
      ((measurable_id.mul (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))).mul hbarF_meas)
  have hPos_window : ∃ a : ℝ, 0 < a ∧ ∀ y ∈ Set.Ioo (0 : ℝ) a, (rate : ℝ) / (2 * premium) ≤ fTilde y := by
    have hUnion : Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Ioi (1 / ((n : ℝ) + 1)) := by
      ext y; simp only [Set.mem_Ioi, Set.mem_iUnion]
      constructor
      · intro hy; obtain ⟨n, hn⟩ := exists_nat_one_div_lt hy; exact ⟨n, hn⟩
      · rintro ⟨n, hn⟩; exact lt_trans (by positivity) hn
    have hMono : Monotone (fun n : ℕ => Set.Ioi (1 / ((n : ℝ) + 1))) := fun m n hmn =>
      Set.Ioi_subset_Ioi (one_div_le_one_div_of_le (by positivity) (by gcongr))
    have hLim := tendsto_measure_iUnion_atTop (μ := F) hMono
    rw [← hUnion] at hLim
    have hFIoi0 : F (Set.Ioi (0 : ℝ)) = 1 := by
      rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hclaimpos, tsub_zero]
    rw [hFIoi0] at hLim
    have hLim_toR : Tendsto (fun n : ℕ => (F (Set.Ioi (1 / ((n : ℝ) + 1)))).toReal) atTop (𝓝 1) := by
      have h1 := (ENNReal.continuousAt_toReal ENNReal.one_ne_top).tendsto.comp hLim
      rw [ENNReal.toReal_one] at h1
      exact h1
    have hEv := hLim_toR.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    rw [Filter.eventually_atTop] at hEv
    obtain ⟨N, hN⟩ := hEv
    refine ⟨1 / ((N : ℝ) + 1), by positivity, fun y hy => ?_⟩
    have hbar_ge : 1 / 2 ≤ barF y := le_trans (hN N le_rfl).le (hbarF_anti hy.2.le)
    have hexp_ge : 1 ≤ Real.exp (nu * y) := Real.one_le_exp (by nlinarith [hy.1])
    dsimp only [fTilde]
    rw [if_pos hy.1]
    have hpos : 0 < (rate : ℝ) / premium := by positivity
    have h1 : (rate : ℝ) / premium ≤ ((rate : ℝ) / premium) * Real.exp (nu * y) :=
      le_mul_of_one_le_right hpos.le hexp_ge
    calc (rate : ℝ) / (2 * premium) = ((rate : ℝ) / premium) * (1 / 2) := by ring
      _ ≤ (((rate : ℝ) / premium) * Real.exp (nu * y)) * barF y :=
          mul_le_mul h1 hbar_ge (by norm_num) (by positivity)
  exact cramer_step78_limit rate hrateR mu premium nu hpremium hnu hnet weightedTail
    fTilde h Z hfT_meas hfT_nn hfT_int hfT_integral hh_nn hGtilde_nn hGtilde_le1 hGtilde_anti
    hh_tendsto_zero hh_int_val hZ_bdd hZ_meas hRenew hZ_unifCont hFubini hGtilde_lintegral hPos_window
