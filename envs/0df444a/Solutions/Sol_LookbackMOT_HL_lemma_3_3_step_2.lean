-- Prove2me | solution 1 for LookbackMOT.HL.lemma_3_3_step_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:41:34.450277+00:00
-- url     : https://prove2.me/submissions/d08d8108-9f59-4306-b361-c5ff8f106d74

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL Filter Topology
open scoped NNReal ENNReal

lemma LB_layer (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgC1 : ContDiff ℝ 1 g) (hgmono : Monotone g)
    (ν : Measure ℝ) (hν : IsHLTransform μ ν) (hνg : Integrable g ν) :
    ∫⁻ x, ENNReal.ofReal (g x - g X₀) ∂ν =
      ∫⁻ y in Set.Ioi X₀, ν (Set.Ici y) * ENNReal.ofReal (deriv g y) := by
  obtain ⟨hνprob, hνI⟩ := hν
  -- call price facts
  have hint : ∀ ξ : ℝ, Integrable (fun y : ℝ => y - ξ) μ := fun ξ =>
    (hμ1.sub (integrable_const ξ))
  have hlin : ∀ ξ : ℝ, ∫ y, (y - ξ) ∂μ = X₀ - ξ := by
    intro ξ
    have := integral_sub hμ1 (integrable_const ξ) (μ := μ)
    simp only [id] at this
    rw [this, hmean]
    simp
  have hputint : ∀ ξ : ℝ, Integrable (fun y : ℝ => max (ξ - y) 0) μ := fun ξ =>
    ((integrable_const ξ).sub hμ1).pos_part
  have hcdec : ∀ ξ : ℝ, callPrice μ ξ = (X₀ - ξ) + ∫ y, max (ξ - y) 0 ∂μ := by
    intro ξ
    unfold callPrice
    rw [← hlin ξ, ← integral_add (hint ξ) (hputint ξ)]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only
    rcases le_total y ξ with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  set Pp : ℝ := ∫ y, max (X₀ - y) 0 ∂μ
  have hPp : 0 ≤ Pp := integral_nonneg (fun y => le_max_right _ _)
  have hput_le : ∀ ξ : ℝ, ξ ≤ X₀ → ∫ y, max (ξ - y) 0 ∂μ ≤ Pp := by
    intro ξ hξ
    exact integral_mono (hputint ξ) (hputint X₀) (fun y => max_le_max (by linarith) le_rfl)
  have hput_nn : ∀ ξ : ℝ, 0 ≤ ∫ y, max (ξ - y) 0 ∂μ := fun ξ =>
    integral_nonneg (fun y => le_max_right _ _)
  -- ν([X₀, ∞)) = 1
  have hinf : (⨅ ξ : Set.Iio X₀, callPrice μ ξ / (X₀ - ξ)) = 1 := by
    have hge : ∀ ξ : Set.Iio X₀, 1 ≤ callPrice μ ξ / (X₀ - ξ) := by
      rintro ⟨ξ, hξ⟩
      have hξ' : ξ < X₀ := hξ
      rw [le_div_iff₀ (by linarith), one_mul, hcdec]
      linarith [hput_nn ξ]
    have hbdd : BddBelow (Set.range fun ξ : Set.Iio X₀ => callPrice μ ξ / (X₀ - ξ)) :=
      ⟨1, by rintro _ ⟨i, rfl⟩; exact hge i⟩
    have : Nonempty (Set.Iio X₀) := ⟨⟨X₀ - 1, by simp⟩⟩
    apply le_antisymm _ (le_ciInf hge)
    apply le_of_forall_pos_lt_add
    intro ε hε
    set ξ : ℝ := X₀ - Pp / ε - 1
    have hξ : ξ ∈ Set.Iio X₀ := by
      simp only [Set.mem_Iio, ξ]; linarith [div_nonneg hPp hε.le]
    have hpos : 0 < X₀ - ξ := by simp only [ξ]; linarith [div_nonneg hPp hε.le]
    calc (⨅ ξ : Set.Iio X₀, callPrice μ ξ / (X₀ - ξ)) ≤ callPrice μ ξ / (X₀ - ξ) :=
          ciInf_le hbdd ⟨ξ, hξ⟩
      _ < 1 + ε := by
          rw [div_lt_iff₀ hpos, hcdec]
          have h1 := hput_le ξ (le_of_lt hξ)
          have h2 : X₀ - ξ = Pp / ε + 1 := by simp only [ξ]; ring
          rw [h2]
          have h3 : ε * (Pp / ε) = Pp := by field_simp
          nlinarith
  have hνX : ν (Set.Ici X₀) = 1 := by rw [hνI, hinf]; simp
  have hνae : ∀ᵐ x ∂ν, X₀ ≤ x := by
    rw [ae_iff]
    have h1 : {a : ℝ | ¬ X₀ ≤ a} = (Set.Ici X₀)ᶜ := by ext a; simp
    rw [h1, measure_compl measurableSet_Ici (measure_ne_top _ _), hνX, measure_univ]
    simp
  -- derivative facts
  set D := deriv g
  have hdiff : Differentiable ℝ g := hgC1.differentiable (by norm_num)
  have hDcont : Continuous D := hgC1.continuous_deriv (by norm_num)
  have hDnn : ∀ x, 0 ≤ D x := fun x => hgmono.deriv_nonneg
  have hFTC : ∀ s : ℝ, ∫ t in (0:ℝ)..s, D (X₀ + t) = g (X₀ + s) - g X₀ := by
    intro s
    rw [intervalIntegral.integral_comp_add_left (fun t => D t) X₀]
    simp only [add_zero]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x _; exact (hdiff x).hasDerivAt
    · exact hDcont.intervalIntegrable _ _
  -- layer cake
  have hlc := lintegral_comp_eq_lintegral_meas_le_mul ν (f := fun x => x - X₀)
    (g := fun t => D (X₀ + t))
    (by filter_upwards [hνae] with x hx; simp only [Pi.zero_apply]; linarith)
    (by fun_prop)
    (fun t _ => (hDcont.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
    (Filter.Eventually.of_forall (fun t => hDnn _))
  simp only [hFTC, add_sub_cancel] at hlc
  have hset : ∀ t : ℝ, {a : ℝ | t ≤ a - X₀} = Set.Ici (X₀ + t) := by
    intro t; ext a; simp; constructor <;> intro h <;> linarith
  simp only [hset] at hlc
  -- translate the right side
  have htrans : ∫⁻ t in Set.Ioi 0, ν (Set.Ici (X₀ + t)) * ENNReal.ofReal (D (X₀ + t)) =
      ∫⁻ y in Set.Ioi X₀, ν (Set.Ici y) * ENNReal.ofReal (D y) := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
    rw [← lintegral_add_left_eq_self (μ := (volume : Measure ℝ))
      (Set.indicator (Set.Ioi X₀) fun y => ν (Set.Ici y) * ENNReal.ofReal (D y)) X₀]
    congr 1
    ext t
    by_cases ht : 0 < t
    · rw [Set.indicator_of_mem (by simpa using ht), Set.indicator_of_mem (by simpa using ht)]
    · rw [Set.indicator_of_notMem (by simpa using ht), Set.indicator_of_notMem (by simpa using ht)]
  rw [htrans] at hlc
  exact hlc

/-- `G m ξ = ∫_{[ξ,∞)} (y - m) μ(dy)` written with an indicator. -/
lemma LB_G_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ1 : Integrable id μ) (m : ℝ)
    {l : Filter ℝ} [l.IsCountablyGenerated] {T : Set ℝ} (hT : MeasurableSet T)
    (hlim : ∀ y, Tendsto (fun ξ => (Set.Ici ξ).indicator (fun y => y - m) y) l
      (𝓝 (T.indicator (fun y => y - m) y))) :
    Tendsto (fun ξ => ∫ y, (Set.Ici ξ).indicator (fun y => y - m) y ∂μ) l
      (𝓝 (∫ y, T.indicator (fun y => y - m) y ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun y => |y - m|)
  · exact Eventually.of_forall fun ξ =>
      ((hμ1.sub (integrable_const m)).indicator measurableSet_Ici).aestronglyMeasurable
  · refine Eventually.of_forall fun ξ => Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs]
    by_cases hy : y ∈ Set.Ici ξ
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, abs_zero]; exact abs_nonneg _
  · exact (hμ1.sub (integrable_const m)).abs
  · exact Eventually.of_forall hlim

lemma LB_key (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀) (m : ℝ) (hXm : X₀ < m) (hpos : 0 < μ (Set.Ioi m)) :
    (∃ ξ, barycenter μ ξ ≤ m) ∧ (∀ ξ, barycenter μ ξ ≤ m → ξ ≤ m) ∧
    baryInv μ m < m ∧
    ∀ ξ, ξ < m → callPrice μ (baryInv μ m) / (m - baryInv μ m) ≤ callPrice μ ξ / (m - ξ) := by
  have hμ1' : Integrable (fun y : ℝ => y) μ := hμ1
  set G : ℝ → ℝ := fun ξ => ∫ y, (Set.Ici ξ).indicator (fun y => y - m) y ∂μ with hGdef
  have hint1 : Integrable (fun y : ℝ => y - m) μ := hμ1.sub (integrable_const m)
  have hGset : ∀ ξ, G ξ = (∫ y in Set.Ici ξ, y ∂μ) - (μ (Set.Ici ξ)).toReal * m := by
    intro ξ
    simp only [G]
    rw [integral_indicator measurableSet_Ici, integral_sub hμ1'.integrableOn (integrable_const m),
      setIntegral_const, smul_eq_mul, measureReal_def]
  -- characterisation of {b ≤ m}
  have hiff : ∀ ξ, barycenter μ ξ ≤ m ↔ ξ ≤ m ∧ G ξ ≤ 0 := by
    intro ξ
    unfold barycenter
    by_cases hξ : 0 < μ (Set.Ioi ξ)
    · rw [if_pos hξ]
      have hD : 0 < (μ (Set.Ici ξ)).toReal := ENNReal.toReal_pos
        (lt_of_lt_of_le hξ (measure_mono Set.Ioi_subset_Ici_self)).ne' (measure_ne_top _ _)
      have hI : ξ * (μ (Set.Ici ξ)).toReal ≤ ∫ y in Set.Ici ξ, y ∂μ := by
        have := setIntegral_mono_on (μ := μ) (integrable_const ξ).integrableOn hμ1'.integrableOn
          measurableSet_Ici (fun y (hy : ξ ≤ y) => hy)
        rw [setIntegral_const, smul_eq_mul, measureReal_def] at this
        linarith
      rw [div_le_iff₀ hD, hGset]
      constructor
      · intro h
        refine ⟨?_, by linarith⟩
        by_contra hc; push Not at hc
        nlinarith
      · rintro ⟨_, h⟩; linarith
    · rw [if_neg hξ]
      have h0 : μ (Set.Ioi ξ) = 0 := by simpa using hξ
      constructor
      · intro h
        refine ⟨h, ?_⟩
        simp only [G]
        rw [integral_indicator measurableSet_Ici]
        apply integral_nonpos_of_ae
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ici]
        have : ∀ᵐ y ∂μ, y ≤ ξ := by
          rw [ae_iff]
          have : {a : ℝ | ¬ a ≤ ξ} = Set.Ioi ξ := by ext; simp
          rw [this, h0]
        filter_upwards [this] with y hy _
        simp only [Pi.zero_apply]; linarith
      · exact fun h => h.1
  -- G is monotone on (-∞, m]
  have hGmono : ∀ ξ ξ', ξ ≤ ξ' → ξ' ≤ m → G ξ ≤ G ξ' := by
    intro ξ ξ' h h'
    apply integral_mono (hint1.indicator measurableSet_Ici) (hint1.indicator measurableSet_Ici)
    intro y
    by_cases hy : ξ' ≤ y
    · rw [Set.indicator_of_mem (show y ∈ Set.Ici ξ from le_trans h hy),
        Set.indicator_of_mem (show y ∈ Set.Ici ξ' from hy)]
    · rw [Set.indicator_of_notMem (show y ∉ Set.Ici ξ' from hy)]
      by_cases hy' : ξ ≤ y
      · rw [Set.indicator_of_mem (show y ∈ Set.Ici ξ from hy')]
        push Not at hy; linarith
      · rw [Set.indicator_of_notMem (show y ∉ Set.Ici ξ from hy')]
  -- G(m) = c(m) > 0
  have hcm : 0 < G m := by
    have : G m = callPrice μ m := by
      simp only [G, callPrice]
      congr 1; ext y
      by_cases hy : m ≤ y
      · rw [Set.indicator_of_mem (show y ∈ Set.Ici m from hy), max_eq_left (by linarith)]
      · rw [Set.indicator_of_notMem (show y ∉ Set.Ici m from hy), max_eq_right (by linarith)]
    rw [this]
    simp only [callPrice]
    rw [integral_pos_iff_support_of_nonneg (f := fun y => max (y - m) 0)
      (fun y => le_max_right _ _) hint1.pos_part]
    have : Function.support (fun y : ℝ => max (y - m) 0) = Set.Ioi m := by
      ext y
      simp only [Function.mem_support, Set.mem_Ioi, ne_eq]
      constructor
      · intro h; by_contra h'; push Not at h'; exact h (max_eq_right (by linarith))
      · intro h; rw [max_eq_left (by linarith)]; linarith
    rw [this]; exact hpos
  -- the set A is nonempty
  have hlimbot : Tendsto G atBot (𝓝 (X₀ - m)) := by
    have := LB_G_tendsto hμ1 m (l := atBot) MeasurableSet.univ (fun y => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_le_atBot y] with ξ hξ
      rw [Set.indicator_of_mem (show y ∈ Set.Ici ξ from hξ), Set.indicator_univ])
    simp only [Set.indicator_univ] at this
    convert this using 2
    have h := integral_sub hμ1 (integrable_const m) (μ := μ)
    simp only [id] at h
    rw [h, hmean]; simp
  obtain ⟨ξ0, hξ0G, hξ0m⟩ :=
    ((hlimbot.eventually (gt_mem_nhds (by linarith : X₀ - m < 0))).and
      (eventually_le_atBot m)).exists
  have hA_ne : ∃ ξ, barycenter μ ξ ≤ m := ⟨ξ0, (hiff ξ0).mpr ⟨hξ0m, hξ0G.le⟩⟩
  have hA_bdd : ∀ ξ, barycenter μ ξ ≤ m → ξ ≤ m := fun ξ h => ((hiff ξ).mp h).1
  refine ⟨hA_ne, hA_bdd, ?_⟩
  set A : Set ℝ := {ξ : ℝ | barycenter μ ξ ≤ m}
  set a := baryInv μ m
  have haA : a = sSup A := rfl
  have hAne : A.Nonempty := hA_ne
  have hAbdd : BddAbove A := ⟨m, fun ξ h => hA_bdd ξ h⟩
  have ha_le : a ≤ m := csSup_le hAne (fun ξ h => hA_bdd ξ h)
  -- (i) G(ξ) ≤ 0 for ξ < a, hence G(a) ≤ 0
  have hbelow : ∀ ξ, ξ < a → G ξ ≤ 0 := by
    intro ξ hξ
    obtain ⟨ξ', hξ'A, hξξ'⟩ := exists_lt_of_lt_csSup hAne hξ
    have := (hiff ξ').mp hξ'A
    exact (hGmono ξ ξ' hξξ'.le this.1).trans this.2
  have hGa : G a ≤ 0 := by
    have hlim := LB_G_tendsto hμ1 m (l := 𝓝[<] a) (T := Set.Ici a) measurableSet_Ici (fun y => by
      by_cases hy : a ≤ y
      · apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with ξ (hξ : ξ < a)
        rw [Set.indicator_of_mem (show y ∈ Set.Ici ξ from le_trans hξ.le hy),
          Set.indicator_of_mem (show y ∈ Set.Ici a from hy)]
      · push Not at hy
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioo_mem_nhdsLT hy] with ξ hξ
        rw [Set.indicator_of_notMem (show y ∉ Set.Ici ξ by simp; exact hξ.1),
          Set.indicator_of_notMem (show y ∉ Set.Ici a by simp; exact hy)])
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with ξ (hξ : ξ < a)
    exact hbelow ξ hξ
  have ham : a < m := by
    rcases lt_or_eq_of_le ha_le with h | h
    · exact h
    · exfalso; rw [h] at hGa; linarith
  refine ⟨ham, ?_⟩
  -- (ii) ∫_{(a,∞)} (y - m) ≥ 0
  have habove : ∀ ξ, a < ξ → ξ ≤ m → 0 < G ξ := by
    intro ξ hξ hξm
    by_contra hc; push Not at hc
    have : ξ ∈ A := (hiff ξ).mpr ⟨hξm, hc⟩
    exact absurd (le_csSup hAbdd this) (not_le.mpr hξ)
  have hGa' : 0 ≤ ∫ y, (Set.Ioi a).indicator (fun y => y - m) y ∂μ := by
    have hlim := LB_G_tendsto hμ1 m (l := 𝓝[>] a) (T := Set.Ioi a) measurableSet_Ioi (fun y => by
      by_cases hy : a < y
      · apply tendsto_const_nhds.congr'
        filter_upwards [Ioo_mem_nhdsGT hy] with ξ hξ
        rw [Set.indicator_of_mem (show y ∈ Set.Ici ξ from hξ.2.le),
          Set.indicator_of_mem (show y ∈ Set.Ioi a from hy)]
      · push Not at hy
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with ξ (hξ : a < ξ)
        rw [Set.indicator_of_notMem (show y ∉ Set.Ici ξ by simp; linarith),
          Set.indicator_of_notMem (show y ∉ Set.Ioi a by simp; exact hy)])
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT ham] with ξ hξ
    exact (habove ξ hξ.1 hξ.2.le).le
  -- translate into inequalities on c(a)
  set c := callPrice μ
  have hcint : ∀ ξ : ℝ, Integrable (fun y : ℝ => max (y - ξ) 0) μ := fun ξ =>
    (hμ1.sub (integrable_const ξ)).pos_part
  have hind1 : ∀ s : Set ℝ, MeasurableSet s → Integrable (s.indicator (1 : ℝ → ℝ)) μ :=
    fun s hs => (integrable_const (1:ℝ)).indicator hs
  -- c(a) ≤ μ[a,∞) (m - a)
  have hc1 : c a ≤ (μ (Set.Ici a)).toReal * (m - a) := by
    have e : G a = c a - (μ (Set.Ici a)).toReal * (m - a) := by
      rw [hGset]
      have : c a = ∫ y in Set.Ici a, (y - a) ∂μ := by
        simp only [c, callPrice]
        rw [← integral_indicator measurableSet_Ici]
        congr 1; ext y
        by_cases hy : a ≤ y
        · rw [Set.indicator_of_mem (show y ∈ Set.Ici a from hy), max_eq_left (by linarith)]
        · rw [Set.indicator_of_notMem (show y ∉ Set.Ici a from hy), max_eq_right (by linarith)]
      rw [this, integral_sub hμ1'.integrableOn (integrable_const a), setIntegral_const,
        smul_eq_mul, measureReal_def]
      ring
    linarith
  -- μ(a,∞) (m - a) ≤ c(a)
  have hc2 : (μ (Set.Ioi a)).toReal * (m - a) ≤ c a := by
    have e : ∫ y, (Set.Ioi a).indicator (fun y => y - m) y ∂μ =
        c a - (μ (Set.Ioi a)).toReal * (m - a) := by
      have : c a = ∫ y in Set.Ioi a, (y - a) ∂μ := by
        simp only [c, callPrice]
        rw [← integral_indicator measurableSet_Ioi]
        congr 1; ext y
        by_cases hy : a < y
        · rw [Set.indicator_of_mem (show y ∈ Set.Ioi a from hy), max_eq_left (by linarith)]
        · rw [Set.indicator_of_notMem (show y ∉ Set.Ioi a from hy), max_eq_right (by linarith)]
      rw [this, integral_indicator measurableSet_Ioi,
        integral_sub hμ1'.integrableOn (integrable_const m),
        integral_sub hμ1'.integrableOn (integrable_const a), setIntegral_const, setIntegral_const,
        smul_eq_mul, smul_eq_mul, measureReal_def]
      ring
    linarith
  -- the line through (a, c(a)) and (m, 0) lies below c
  intro ξ hξ
  have hma : 0 < m - a := by linarith
  have hmξ : 0 < m - ξ := by linarith
  rw [div_le_div_iff₀ hma hmξ]
  rcases le_total a ξ with h | h
  · -- c(ξ) ≥ c(a) - (ξ - a) μ(a,∞)
    have hlow : c a - (ξ - a) * (μ (Set.Ioi a)).toReal ≤ c ξ := by
      have e : ∫ y, (max (y - a) 0 - (ξ - a) * (Set.Ioi a).indicator 1 y) ∂μ =
          c a - (ξ - a) * (μ (Set.Ioi a)).toReal := by
        rw [integral_sub (hcint a) ((hind1 _ measurableSet_Ioi).const_mul _), integral_const_mul,
          integral_indicator_one measurableSet_Ioi, measureReal_def]
        rfl
      rw [← e]
      apply integral_mono ((hcint a).sub ((hind1 _ measurableSet_Ioi).const_mul _)) (hcint ξ)
      intro y
      simp only [Pi.sub_apply, Pi.add_apply]
      by_cases hy : a < y
      · rw [Set.indicator_of_mem (show y ∈ Set.Ioi a from hy), Pi.one_apply, mul_one,
          max_eq_left (by linarith : (0:ℝ) ≤ y - a)]
        rcases le_total ξ y with h' | h'
        · rw [max_eq_left (by linarith)]; linarith
        · rw [max_eq_right (by linarith)]; linarith
      · rw [Set.indicator_of_notMem (show y ∉ Set.Ioi a from hy), mul_zero, sub_zero,
          max_eq_right (by push Not at hy; linarith)]
        exact le_max_right _ _
    have hμI : 0 ≤ (μ (Set.Ioi a)).toReal := ENNReal.toReal_nonneg
    nlinarith
  · -- c(ξ) ≥ c(a) + (a - ξ) μ[a,∞)
    have hlow : c a + (a - ξ) * (μ (Set.Ici a)).toReal ≤ c ξ := by
      have e : ∫ y, (max (y - a) 0 + (a - ξ) * (Set.Ici a).indicator 1 y) ∂μ =
          c a + (a - ξ) * (μ (Set.Ici a)).toReal := by
        rw [integral_add (hcint a) ((hind1 _ measurableSet_Ici).const_mul _), integral_const_mul,
          integral_indicator_one measurableSet_Ici, measureReal_def]
        rfl
      rw [← e]
      apply integral_mono ((hcint a).add ((hind1 _ measurableSet_Ici).const_mul _)) (hcint ξ)
      intro y
      simp only [Pi.sub_apply, Pi.add_apply]
      by_cases hy : a ≤ y
      · rw [Set.indicator_of_mem (show y ∈ Set.Ici a from hy), Pi.one_apply, mul_one,
          max_eq_left (by linarith : (0:ℝ) ≤ y - a), max_eq_left (by linarith : (0:ℝ) ≤ y - ξ)]
        linarith
      · rw [Set.indicator_of_notMem (show y ∉ Set.Ici a from hy), mul_zero, add_zero,
          max_eq_right (by push Not at hy; linarith)]
        exact le_max_right _ _
    nlinarith

theorem solution (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgC1 : ContDiff ℝ 1 g) (hgmono : Monotone g)
    (ν : Measure ℝ) (hν : IsHLTransform μ ν) (hνg : Integrable g ν) :
    Measurable (lamStar μ X₀ g) ∧ Integrable (lamStar μ X₀ g) μ ∧
      (∀ x, 0 ≤ lamStar μ X₀ g x) ∧
      ConvexOn ℝ {x : ℝ | 0 < μ (Set.Ioi x)} (lamStar μ X₀ g) := by
  have hlayer := LB_layer X₀ μ hμ1 hmean g hg0 hgC1 hgmono ν hν hνg
  have hνP : IsProbabilityMeasure ν := hν.1
  set S : Set ℝ := {m : ℝ | X₀ < m ∧ 0 < μ (Set.Ioi m)} with hSdef
  set D := deriv g with hDdef
  have hDnn : ∀ x, 0 ≤ D x := fun x => hgmono.deriv_nonneg
  have hanti : Antitone (fun m : ℝ => μ (Set.Ioi m)) := fun x y h =>
    measure_mono (Set.Ioi_subset_Ioi h)
  have hSmeas : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_const hanti.measurable)
  have hkey : ∀ m ∈ S, _ := fun m (hm : m ∈ S) => LB_key X₀ μ hμ1 hmean m hm.1 hm.2
  have hamono : MonotoneOn (baryInv μ) S := by
    intro m₁ h₁ m₂ h₂ h12
    obtain ⟨hne, -, -, -⟩ := hkey m₁ h₁
    obtain ⟨-, hbdd, -, -⟩ := hkey m₂ h₂
    exact csSup_le_csSup ⟨m₂, fun ξ hξ => hbdd ξ hξ⟩ hne
      (fun ξ (hξ : barycenter μ ξ ≤ m₁) => (show barycenter μ ξ ≤ m₂ by linarith))
  have haAE : AEMeasurable (baryInv μ) (volume.restrict S) :=
    aemeasurable_restrict_of_monotoneOn hSmeas hamono
  set ã := haAE.mk (baryInv μ)
  have hãm : Measurable ã := haAE.measurable_mk
  have hãae : baryInv μ =ᵐ[volume.restrict S] ã := haAE.ae_eq_mk
  set F : ℝ → ℝ → ℝ≥0∞ := fun x m => ENNReal.ofReal (D m * max (x - ã m) 0 / (m - ã m))
    with hFdef
  have hDm : Measurable D := (hgC1.continuous_deriv (by norm_num)).measurable
  have hFmeas : Measurable (Function.uncurry F) := by
    apply ENNReal.measurable_ofReal.comp
    exact ((hDm.comp measurable_snd).mul ((measurable_fst.sub (hãm.comp measurable_snd)).max
      measurable_const)).div (measurable_snd.sub (hãm.comp measurable_snd))
  have hFw : ∀ x m, F x m = ENNReal.ofReal (D m / (m - ã m) * max (x - ã m) 0) := by
    intro x m; simp only [F]; rw [mul_div_right_comm]
  have hFmono : ∀ m, Monotone (fun x => F x m) := by
    intro m x y hxy
    simp only [hFw]
    rcases le_or_gt (D m / (m - ã m)) 0 with hw | hw
    · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hw (le_max_right _ _))]
      exact bot_le
    · exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hw.le)
  have hFconv : ∀ m x y s t : ℝ, 0 ≤ s → 0 ≤ t → s + t = 1 →
      F (s * x + t * y) m ≤ ENNReal.ofReal s * F x m + ENNReal.ofReal t * F y m := by
    intro m x y s t hs ht hst
    simp only [hFw]
    set w := D m / (m - ã m)
    rcases le_or_gt w 0 with hw | hw
    · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hw (le_max_right _ _))]
      exact bot_le
    · have hp : max (s * x + t * y - ã m) 0 ≤ s * max (x - ã m) 0 + t * max (y - ã m) 0 := by
        apply max_le
        · have h1 : s * (x - ã m) ≤ s * max (x - ã m) 0 :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) hs
          have h2 : t * (y - ã m) ≤ t * max (y - ã m) 0 :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) ht
          have : s * x + t * y - ã m = s * (x - ã m) + t * (y - ã m) := by
            have h3 : t = 1 - s := by linarith
            subst h3; ring
          linarith
        · exact add_nonneg (mul_nonneg hs (le_max_right _ _)) (mul_nonneg ht (le_max_right _ _))
      calc ENNReal.ofReal (w * max (s * x + t * y - ã m) 0)
          ≤ ENNReal.ofReal (s * (w * max (x - ã m) 0) + t * (w * max (y - ã m) 0)) := by
            apply ENNReal.ofReal_le_ofReal
            have := mul_le_mul_of_nonneg_left hp hw.le
            linarith
        _ = ENNReal.ofReal s * ENNReal.ofReal (w * max (x - ã m) 0) +
              ENNReal.ofReal t * ENNReal.ofReal (w * max (y - ã m) 0) := by
            rw [ENNReal.ofReal_add (mul_nonneg hs (mul_nonneg hw.le (le_max_right _ _)))
              (mul_nonneg ht (mul_nonneg hw.le (le_max_right _ _))), ENNReal.ofReal_mul hs,
              ENNReal.ofReal_mul ht]
  set Λ : ℝ → ℝ≥0∞ := fun x => ∫⁻ m in S, F x m with hΛdef
  have hΛeq : ∀ x, lamStar μ X₀ g x = (Λ x).toReal := by
    intro x
    unfold lamStar
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hãae] with m hm
    simp only [F, D, hm]
  have hlamfun : lamStar μ X₀ g = fun x => (Λ x).toReal := funext hΛeq
  have hΛmono : Monotone Λ := fun x y h => lintegral_mono (fun m => hFmono m h)
  have hΛmeas : Measurable Λ := hΛmono.measurable
  have hmeas : Measurable (lamStar μ X₀ g) := by
    rw [hlamfun]; exact ENNReal.measurable_toReal.comp hΛmeas
  -- integrability
  have hbound : ∫⁻ x, Λ x ∂μ ≤ ∫⁻ y in Set.Ioi X₀, ν (Set.Ici y) * ENNReal.ofReal (D y) := by
    calc ∫⁻ x, Λ x ∂μ = ∫⁻ m in S, ∫⁻ x, F x m ∂μ :=
          lintegral_lintegral_swap hFmeas.aemeasurable
      _ ≤ ∫⁻ m in S, ν (Set.Ici m) * ENNReal.ofReal (D m) := by
          apply lintegral_mono_ae
          have hãae' : ∀ᵐ m ∂(volume.restrict S), baryInv μ m = ã m := hãae
          rw [ae_restrict_iff' hSmeas] at hãae' ⊢
          filter_upwards [hãae'] with m hm hmS
          obtain ⟨-, -, ham, hmin⟩ := hkey m hmS
          set a := baryInv μ m
          have hma : 0 < m - a := by linarith
          have hw : 0 ≤ D m / (m - a) := div_nonneg (hDnn m) hma.le
          have e1 : ∫⁻ x, F x m ∂μ = ENNReal.ofReal (D m / (m - a)) *
              ENNReal.ofReal (callPrice μ a) := by
            simp only [hFw, ← hm hmS]
            simp_rw [ENNReal.ofReal_mul hw]
            rw [lintegral_const_mul _
              (show Measurable (fun x : ℝ => ENNReal.ofReal (max (x - a) 0)) by fun_prop)]
            congr 1
            rw [callPrice, ofReal_integral_eq_lintegral_ofReal (f := fun y => max (y - a) 0)
              ((hμ1.sub (integrable_const a)).pos_part)
              (Eventually.of_forall fun x => le_max_right _ _)]
          rw [e1, ← ENNReal.ofReal_mul hw]
          have hinf : callPrice μ a / (m - a) ≤ (ν (Set.Ici m)).toReal := by
            rw [hν.2 m, ENNReal.toReal_ofReal]
            · have : Nonempty (Set.Iio m) := ⟨⟨m - 1, by simp⟩⟩
              exact le_ciInf (fun ξ => hmin ξ ξ.2)
            · apply Real.iInf_nonneg
              intro ξ
              have : (ξ : ℝ) < m := ξ.2
              exact div_nonneg (integral_nonneg fun y => le_max_right _ _) (by linarith)
          calc ENNReal.ofReal (D m / (m - a) * callPrice μ a)
              = ENNReal.ofReal (D m * (callPrice μ a / (m - a))) := by ring_nf
            _ ≤ ENNReal.ofReal (D m * (ν (Set.Ici m)).toReal) :=
                ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hinf (hDnn m))
            _ = ν (Set.Ici m) * ENNReal.ofReal (D m) := by
                rw [ENNReal.ofReal_mul (hDnn m), ENNReal.ofReal_toReal (measure_ne_top _ _),
                  mul_comm]
      _ ≤ ∫⁻ y in Set.Ioi X₀, ν (Set.Ici y) * ENNReal.ofReal (D y) :=
          lintegral_mono_set (fun m hm => hm.1)
  have hfin : ∫⁻ x, Λ x ∂μ < ⊤ := by
    refine lt_of_le_of_lt hbound ?_
    rw [← hlayer]
    exact (hνg.sub (integrable_const (g X₀))).lintegral_lt_top
  have hnn : ∀ x, 0 ≤ lamStar μ X₀ g x := fun x => by rw [hΛeq]; exact ENNReal.toReal_nonneg
  have hint : Integrable (lamStar μ X₀ g) μ := by
    rw [← lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
      (Eventually.of_forall hnn)]
    apply ne_of_lt
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
    rw [hΛeq]; exact ENNReal.ofReal_toReal_le
  -- finiteness on {μ(x,∞) > 0}
  have hae_fin : ∀ᵐ x ∂μ, Λ x < ⊤ := ae_lt_top hΛmeas hfin.ne
  have hΛfin : ∀ x, 0 < μ (Set.Ioi x) → Λ x ≠ ⊤ := by
    intro x hx htop
    have hsub : Set.Ioi x ⊆ {x' | ¬ Λ x' < ⊤} := by
      intro x' hx'
      simp only [Set.mem_ofPred_eq, not_lt, top_le_iff]
      exact top_le_iff.mp (htop ▸ hΛmono (le_of_lt hx'))
    rw [ae_iff] at hae_fin
    exact absurd (measure_mono_null hsub hae_fin) hx.ne'
  refine ⟨hmeas, hint, hnn, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x hx y hy s t hs ht hst
    show 0 < μ (Set.Ioi (s • x + t • y))
    simp only [smul_eq_mul]
    rcases le_total x y with h | h
    · refine lt_of_lt_of_le hy (hanti ?_)
      have h1 := mul_le_mul_of_nonneg_left h hs
      have h2 : s * y + t * y = y := by rw [← add_mul, hst, one_mul]
      linarith
    · refine lt_of_lt_of_le hx (hanti ?_)
      have h1 := mul_le_mul_of_nonneg_left h ht
      have h2 : s * x + t * x = x := by rw [← add_mul, hst, one_mul]
      linarith
  · intro x hx y hy s t hs ht hst
    simp only [smul_eq_mul, hΛeq]
    have hx' := hΛfin x hx
    have hy' := hΛfin y hy
    have hle : Λ (s * x + t * y) ≤ ENNReal.ofReal s * Λ x + ENNReal.ofReal t * Λ y := by
      calc Λ (s * x + t * y) ≤ ∫⁻ m in S, (ENNReal.ofReal s * F x m + ENNReal.ofReal t * F y m) :=
            lintegral_mono (fun m => hFconv m x y s t hs ht hst)
        _ = ENNReal.ofReal s * Λ x + ENNReal.ofReal t * Λ y := by
            have hFx : ∀ z, Measurable (fun m => F z m) := fun z => by
              exact hFmeas.comp (measurable_const.prodMk measurable_id)
            rw [lintegral_add_left ((hFx x).const_mul _), lintegral_const_mul _ (hFx x),
              lintegral_const_mul _ (hFx y)]
    have hrhs : ENNReal.ofReal s * Λ x + ENNReal.ofReal t * Λ y ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx',
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy'⟩
    calc (Λ (s * x + t * y)).toReal ≤ (ENNReal.ofReal s * Λ x + ENNReal.ofReal t * Λ y).toReal :=
          ENNReal.toReal_mono hrhs hle
      _ = s * (Λ x).toReal + t * (Λ y).toReal := by
          rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx')
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy'), ENNReal.toReal_mul,
            ENNReal.toReal_mul, ENNReal.toReal_ofReal hs, ENNReal.toReal_ofReal ht]
