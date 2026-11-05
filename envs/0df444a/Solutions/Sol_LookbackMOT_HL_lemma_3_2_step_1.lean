-- Prove2me | solution 1 for LookbackMOT.HL.lemma_3_2_step_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:29:29.282122+00:00
-- url     : https://prove2.me/submissions/743eb132-9cc4-4dfa-baf8-a9307df70ce2

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL Filter Topology
open scoped NNReal ENNReal

theorem solution (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (lam : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ lam) (hint : Integrable lam μ)
    (ν₂ : Measure ℝ) (hν₂ : IsSecondDerivMeasure lam ν₂) :
    0 ≤ (∫ x, lam x ∂μ) - lam X₀ ∧
      ENNReal.ofReal ((∫ x, lam x ∂μ) - lam X₀) =
        ∫⁻ y, ENNReal.ofReal (callPrice μ y - c0 X₀ y) ∂ν₂ := by
  set R := rDeriv lam with hRdef
  have hRmono : Monotone R := fun a b hab =>
    hconv.monotoneOn_rightDeriv (by simp) (by simp) hab
  have hcont : Continuous lam := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hderiv : ∀ x, HasDerivWithinAt lam (R x) (Set.Ioi x) x := fun x =>
    hconv.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)
  have hFTC : ∀ a b, a ≤ b → ∫ t in a..b, R t = lam b - lam a := fun a b hab =>
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont.continuousOn
      (fun x _ => hderiv x) (hRmono.intervalIntegrable)
  have hRI : ∀ s t, s ≤ t → R t - R s = (ν₂ (Set.Ioc s t)).toReal := by
    intro s t hst
    rw [hν₂ s t hst, ENNReal.toReal_ofReal (by linarith [hRmono hst])]
  have hfin : ∀ s t, ν₂ (Set.Ioc s t) ≠ ⊤ := by
    intro s t
    rcases le_total s t with h | h
    · rw [hν₂ s t h]; exact ENNReal.ofReal_ne_top
    · rw [Set.Ioc_eq_empty (not_lt.mpr h)]; simp
  haveI : IsLocallyFiniteMeasure ν₂ := ⟨fun x => ⟨Set.Ioc (x - 1) (x + 1),
    Ioc_mem_nhds (by linarith) (by linarith), lt_top_iff_ne_top.mpr (hfin _ _)⟩⟩
  have hswap : ∀ S : Set (ℝ × ℝ), MeasurableSet S →
      ∫⁻ t, ν₂ (Prod.mk t ⁻¹' S) = ∫⁻ y, volume ((fun t => (t, y)) ⁻¹' S) ∂ν₂ := by
    intro S hS
    rw [← Measure.prod_apply hS, Measure.prod_apply_symm hS]
  -- the kernel
  set K : ℝ → ℝ → ℝ≥0∞ := fun x y =>
    if X₀ < y then ENNReal.ofReal (max (x - y) 0) else ENNReal.ofReal (max (y - x) 0) with hK
  set f : ℝ → ℝ := fun x => lam x - lam X₀ - R X₀ * (x - X₀) with hfdef
  have hf_nn : ∀ x, 0 ≤ f x := by
    intro x
    simp only [f]
    rcases lt_trichotomy X₀ x with h | rfl | h
    · have := hconv.rightDeriv_le_slope_of_mem_interior (x := X₀) (by simp) (Set.mem_univ x) h
      rw [slope_def_field, le_div_iff₀ (by linarith)] at this
      have h' : R X₀ * (x - X₀) ≤ lam x - lam X₀ := this
      linarith
    · simp
    · have := hconv.slope_le_leftDeriv_of_mem_interior (x := x) (y := X₀) (Set.mem_univ x)
        (by simp) h
      have h2 : derivWithin lam (Set.Iio X₀) X₀ ≤ R X₀ :=
        hconv.leftDeriv_le_rightDeriv_of_mem_interior (x := X₀) (by simp)
      rw [slope_def_field, div_le_iff₀ (by linarith)] at this
      have h3 := mul_le_mul_of_nonneg_right h2 (by linarith : (0:ℝ) ≤ X₀ - x)
      linarith
  have hTaylor : ∀ x, ENNReal.ofReal (f x) = ∫⁻ y, K x y ∂ν₂ := by
    intro x
    rcases le_or_gt X₀ x with hx | hx
    · -- case X₀ ≤ x
      have h1 : f x = ∫ t in Set.Ioc X₀ x, (R t - R X₀) := by
        rw [← intervalIntegral.integral_of_le hx, intervalIntegral.integral_sub
          hRmono.intervalIntegrable intervalIntegrable_const, hFTC X₀ x hx]
        simp only [f, intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [h1, ofReal_integral_eq_lintegral_ofReal]
      rotate_left
      · exact (hRmono.intervalIntegrable.sub intervalIntegrable_const).1
      · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall (fun t ht => by
          simp only [Pi.zero_apply]; linarith [hRmono ht.1.le])
      have h2 : ∫⁻ t in Set.Ioc X₀ x, ENNReal.ofReal (R t - R X₀) =
          ∫⁻ t in Set.Ioc X₀ x, ν₂ (Set.Ioc X₀ t) :=
        setLIntegral_congr_fun measurableSet_Ioc (fun t ht => (hν₂ X₀ t ht.1.le).symm)
      set S : Set (ℝ × ℝ) := {p | X₀ < p.1 ∧ p.1 ≤ x ∧ X₀ < p.2 ∧ p.2 ≤ p.1}
      have hS : MeasurableSet S := by
        simp only [S, Set.ofPred_and]
        exact (measurableSet_lt measurable_const measurable_fst).inter
          ((measurableSet_le measurable_fst measurable_const).inter
          ((measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_fst)))
      rw [h2, ← lintegral_indicator measurableSet_Ioc]
      have h3 : (Set.Ioc X₀ x).indicator (fun t => ν₂ (Set.Ioc X₀ t)) =
          fun t => ν₂ (Prod.mk t ⁻¹' S) := by
        ext t
        by_cases ht : t ∈ Set.Ioc X₀ x
        · rw [Set.indicator_of_mem ht]
          congr 1
          ext y; simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ioc]
          exact ⟨fun h => ⟨ht.1, ht.2, h⟩, fun h => ⟨h.2.2.1, h.2.2.2⟩⟩
        · rw [Set.indicator_of_notMem ht]
          symm
          convert measure_empty (μ := ν₂)
          ext y; simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
            iff_false]
          exact fun h => ht ⟨h.1, h.2.1⟩
      rw [h3, hswap S hS]
      apply lintegral_congr
      intro y
      simp only [K]
      by_cases hy : X₀ < y
      · rw [if_pos hy]
        have : (fun t => (t, y)) ⁻¹' S = Set.Icc y x := by
          ext t; simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc]
          constructor
          · intro h; exact ⟨h.2.2.2, h.2.1⟩
          · intro h; exact ⟨lt_of_lt_of_le hy h.1, h.2, hy, h.1⟩
        rw [this, Real.volume_Icc]
        rcases le_total y x with h | h
        · rw [max_eq_left (by linarith)]
        · rw [max_eq_right (by linarith), ENNReal.ofReal_of_nonpos (by linarith), ENNReal.ofReal_zero]
      · rw [if_neg hy]
        have : (fun t => (t, y)) ⁻¹' S = ∅ := by
          ext t; simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
            iff_false]
          exact fun h => hy h.2.2.1
        rw [this, measure_empty, max_eq_right (by push Not at hy; linarith)]
        exact ENNReal.ofReal_zero.symm
    · -- case x < X₀
      have h1 : f x = ∫ t in Set.Ioc x X₀, (R X₀ - R t) := by
        rw [← intervalIntegral.integral_of_le hx.le, intervalIntegral.integral_sub
          intervalIntegrable_const hRmono.intervalIntegrable, hFTC x X₀ hx.le]
        simp only [f, intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [h1, ofReal_integral_eq_lintegral_ofReal]
      rotate_left
      · exact (intervalIntegrable_const.sub hRmono.intervalIntegrable).1
      · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall (fun t ht => by
          simp only [Pi.zero_apply]; linarith [hRmono ht.2])
      have h2 : ∫⁻ t in Set.Ioc x X₀, ENNReal.ofReal (R X₀ - R t) =
          ∫⁻ t in Set.Ioc x X₀, ν₂ (Set.Ioc t X₀) :=
        setLIntegral_congr_fun measurableSet_Ioc (fun t ht => (hν₂ t X₀ ht.2).symm)
      set S : Set (ℝ × ℝ) := {p | x < p.1 ∧ p.1 ≤ X₀ ∧ p.1 < p.2 ∧ p.2 ≤ X₀}
      have hS : MeasurableSet S := by
        simp only [S, Set.ofPred_and]
        exact (measurableSet_lt measurable_const measurable_fst).inter
          ((measurableSet_le measurable_fst measurable_const).inter
          ((measurableSet_lt measurable_fst measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const)))
      rw [h2, ← lintegral_indicator measurableSet_Ioc]
      have h3 : (Set.Ioc x X₀).indicator (fun t => ν₂ (Set.Ioc t X₀)) =
          fun t => ν₂ (Prod.mk t ⁻¹' S) := by
        ext t
        by_cases ht : t ∈ Set.Ioc x X₀
        · rw [Set.indicator_of_mem ht]
          congr 1
          ext y; simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ioc]
          exact ⟨fun h => ⟨ht.1, ht.2, h⟩, fun h => ⟨h.2.2.1, h.2.2.2⟩⟩
        · rw [Set.indicator_of_notMem ht]
          symm
          convert measure_empty (μ := ν₂)
          ext y; simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
            iff_false]
          exact fun h => ht ⟨h.1, h.2.1⟩
      rw [h3, hswap S hS]
      apply lintegral_congr
      intro y
      simp only [K]
      by_cases hy : X₀ < y
      · rw [if_pos hy]
        have : (fun t => (t, y)) ⁻¹' S = ∅ := by
          ext t; simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
            iff_false]
          exact fun h => by linarith [h.2.2.2]
        rw [this, measure_empty, max_eq_right (by linarith)]
        exact ENNReal.ofReal_zero.symm
      · rw [if_neg hy]
        push Not at hy
        have : (fun t => (t, y)) ⁻¹' S = Set.Ioo x y := by
          ext t; simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ioo]
          constructor
          · intro h; exact ⟨h.1, h.2.2.1⟩
          · intro h; exact ⟨h.1, by linarith [h.2], h.2, hy⟩
        rw [this, Real.volume_Ioo]
        rcases le_total x y with h | h
        · rw [max_eq_left (by linarith)]
        · rw [max_eq_right (by linarith), ENNReal.ofReal_of_nonpos (by linarith), ENNReal.ofReal_zero]
  -- integrate in μ
  have hfint : Integrable f μ := by
    simp only [f]
    exact (hint.sub (integrable_const _)).sub ((hμ1.sub (integrable_const X₀)).const_mul (R X₀))
  have hfI : ∫ x, f x ∂μ = (∫ x, lam x ∂μ) - lam X₀ := by
    have hlin0 : ∫ z, (z - X₀) ∂μ = 0 := by
      have := integral_sub hμ1 (integrable_const X₀) (μ := μ)
      simp only [id] at this
      rw [this, hmean]
      simp
    have e1 : ∫ x, f x ∂μ = ∫ x, (lam x - lam X₀) ∂μ - ∫ x, R X₀ * (x - X₀) ∂μ :=
      integral_sub (hint.sub (integrable_const _))
        ((hμ1.sub (integrable_const X₀)).const_mul (R X₀))
    have e2 : ∫ x, (lam x - lam X₀) ∂μ = (∫ x, lam x ∂μ) - lam X₀ := by
      rw [integral_sub hint (integrable_const _)]; simp
    have e3 : ∫ x, R X₀ * (x - X₀) ∂μ = 0 := by
      rw [integral_const_mul, hlin0]; simp
    rw [e1, e2, e3, sub_zero]
  have hnn : 0 ≤ (∫ x, lam x ∂μ) - lam X₀ := by
    rw [← hfI]; exact integral_nonneg hf_nn
  refine ⟨hnn, ?_⟩
  have hKmeas : Measurable (Function.uncurry K) := by
    apply Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    · exact ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).max
        measurable_const)
    · exact ENNReal.measurable_ofReal.comp ((measurable_snd.sub measurable_fst).max
        measurable_const)
  rw [← hfI, ofReal_integral_eq_lintegral_ofReal hfint (Eventually.of_forall hf_nn)]
  simp_rw [hTaylor]
  rw [lintegral_lintegral_swap hKmeas.aemeasurable]
  apply lintegral_congr
  intro y
  simp only [K]
  by_cases hy : X₀ < y
  · simp only [if_pos hy]
    rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => max (x - y) 0)
      ((hμ1.sub (integrable_const y)).pos_part)
      (Eventually.of_forall fun x => le_max_right _ _)]
    congr 1
    simp only [callPrice, c0, max_eq_right (by linarith : X₀ - y ≤ 0), sub_zero]
  · simp only [if_neg hy]
    push Not at hy
    rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => max (y - x) 0)
      (((integrable_const y).sub hμ1).pos_part)
      (Eventually.of_forall fun x => le_max_right _ _)]
    congr 1
    simp only [c0, max_eq_left (by linarith : 0 ≤ X₀ - y), callPrice]
    have hlin : ∫ z, (z - y) ∂μ = X₀ - y := by
      have := integral_sub hμ1 (integrable_const y) (μ := μ)
      simp only [id] at this
      rw [this, hmean]
      simp
    rw [← hlin]
    rw [← integral_sub (f := fun z => max (z - y) 0) (g := fun z => z - y)
      ((hμ1.sub (integrable_const y)).pos_part) (hμ1.sub (integrable_const y))]
    apply integral_congr_ae
    refine Eventually.of_forall (fun z => ?_)
    simp only [id]
    rcases le_total z y with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
