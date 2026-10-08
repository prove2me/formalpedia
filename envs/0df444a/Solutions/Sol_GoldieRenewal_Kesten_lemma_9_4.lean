-- Prove2me | solution 1 for GoldieRenewal.Kesten.lemma_9_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T21:23:08.829915+00:00
-- url     : https://prove2.me/submissions/0b40114b-f77a-4f95-ad96-7bf634680553

import Mathlib



namespace GoldieRenewal.Kesten

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The integral of `t^(κ-1)` over `[a, b) ∩ (0, ∞)` for `0 ≤ a`, `0 ≤ b`. -/
lemma lint_Ico_rpow (κ : ℝ) (hκ : 0 < κ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫⁻ t in Set.Ioi (0:ℝ), (Set.Ico a b).indicator (fun s => ENNReal.ofReal (s ^ (κ - 1))) t
      = ENNReal.ofReal (κ⁻¹ * max (b ^ κ - a ^ κ) 0) := by
  rcases le_or_gt b a with hba | hab
  · have h1 : Set.Ico a b = ∅ := Set.Ico_eq_empty (not_lt.mpr hba)
    have h2 : b ^ κ - a ^ κ ≤ 0 := by
      have := Real.rpow_le_rpow hb hba hκ.le; linarith
    rw [h1, Set.indicator_empty, lintegral_zero, max_eq_right h2, mul_zero, ENNReal.ofReal_zero]
  · rw [lintegral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico]
    have hset : (Set.Ico a b ∩ Set.Ioi 0 : Set ℝ) =ᵐ[volume] Set.Ioc a b := by
      rw [ae_eq_set]
      constructor
      · apply measure_mono_null _ (Real.volume_singleton (a := a))
        intro x hx
        simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_Ico, Set.mem_Ioi, Set.mem_Ioc,
          not_and, not_le] at hx
        simp only [Set.mem_singleton_iff]
        rcases hx with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        by_contra hne
        have : a < x := lt_of_le_of_ne h1 (Ne.symm hne)
        linarith [h4 this]
      · apply measure_mono_null _ (Real.volume_singleton (a := b))
        intro x hx
        simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_Ico, Set.mem_Ioi, Set.mem_Ioc,
          not_and, not_lt] at hx
        simp only [Set.mem_singleton_iff]
        rcases hx with ⟨⟨h1, h2⟩, h4⟩
        by_contra hne
        have hlt : x < b := lt_of_le_of_ne h2 hne
        have := h4 ⟨h1.le, hlt⟩
        linarith
    rw [Measure.restrict_congr_set hset]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [← intervalIntegral.integral_of_le hab.le, integral_rpow (Or.inl (by linarith))]
      congr 1
      have h3 : 0 ≤ b ^ κ - a ^ κ := by
        have := Real.rpow_le_rpow ha hab.le hκ.le; linarith
      have e : κ - 1 + 1 = κ := by ring
      rw [max_eq_left h3, e, div_eq_inv_mul]
    · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact Real.rpow_nonneg (by linarith [ht.1]) _

/-- Tonelli: `∫₀^∞ P(Y ≤ t < X) t^{κ-1} dt = κ⁻¹ E[((X⁺)^κ − (Y⁺)^κ)⁺]`. -/
lemma tail_diff_lintegral (P : Measure Ω) [IsProbabilityMeasure P] (κ : ℝ) (hκ : 0 < κ)
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    ∫⁻ t in Set.Ioi (0:ℝ), P {ω | Y ω ≤ t ∧ t < X ω} * ENNReal.ofReal (t ^ (κ - 1))
      = ENNReal.ofReal κ⁻¹ *
        ∫⁻ ω, ENNReal.ofReal (max ((max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ) 0) ∂P := by
  set f : ℝ → Ω → ℝ≥0∞ := fun t ω =>
    (Set.Ico (max (Y ω) 0) (max (X ω) 0)).indicator (fun s => ENNReal.ofReal (s ^ (κ - 1))) t
    with hf
  have hS : MeasurableSet {p : ℝ × Ω | max (Y p.2) 0 ≤ p.1 ∧ p.1 < max (X p.2) 0} :=
    (measurableSet_le ((hY.comp measurable_snd).max measurable_const) measurable_fst).inter
      (measurableSet_lt measurable_fst ((hX.comp measurable_snd).max measurable_const))
  have hfm : Measurable (Function.uncurry f) := by
    have : Function.uncurry f =
        {p : ℝ × Ω | max (Y p.2) 0 ≤ p.1 ∧ p.1 < max (X p.2) 0}.indicator
          (fun p => ENNReal.ofReal (p.1 ^ (κ - 1))) := by
      ext ⟨t, ω⟩
      simp only [Function.uncurry_apply_pair, hf, Set.indicator, Set.mem_Ico, Set.mem_ofPred_eq]
    rw [this]
    exact (measurable_fst.pow_const _).ennreal_ofReal.indicator hS
  have step1 : ∫⁻ t in Set.Ioi (0:ℝ), P {ω | Y ω ≤ t ∧ t < X ω} * ENNReal.ofReal (t ^ (κ - 1))
      = ∫⁻ t in Set.Ioi (0:ℝ), ∫⁻ ω, f t ω ∂P := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht' : (0:ℝ) < t := ht
    have hmeas : MeasurableSet {ω | Y ω ≤ t ∧ t < X ω} :=
      (measurableSet_le hY measurable_const).inter (measurableSet_lt measurable_const hX)
    have : ∀ ω, f t ω = {ω | Y ω ≤ t ∧ t < X ω}.indicator
        (fun _ => ENNReal.ofReal (t ^ (κ - 1))) ω := by
      intro ω
      simp only [hf, Set.indicator, Set.mem_Ico, Set.mem_ofPred_eq]
      have e1 : max (Y ω) 0 ≤ t ↔ Y ω ≤ t := by
        constructor
        · intro h; exact le_trans (le_max_left _ _) h
        · intro h; exact max_le h ht'.le
      have e2 : t < max (X ω) 0 ↔ t < X ω := by
        constructor
        · intro h; rcases lt_max_iff.mp h with h | h; exact h; linarith
        · intro h; exact lt_max_of_lt_left h
      simp only [e1, e2]
    simp_rw [this]
    rw [lintegral_indicator_const hmeas, mul_comm]
  rw [step1, lintegral_lintegral_swap hfm.aemeasurable]
  have step2 : ∀ ω, ∫⁻ t in Set.Ioi (0:ℝ), f t ω
      = ENNReal.ofReal κ⁻¹ * ENNReal.ofReal (max ((max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ) 0) := by
    intro ω
    rw [hf]
    simp only
    rw [lint_Ico_rpow κ hκ _ _ (le_max_right _ _) (le_max_right _ _),
      ENNReal.ofReal_mul (by positivity)]
  simp_rw [step2]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Pointwise identity for the tail difference. -/
lemma tail_diff_eq (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (t : ℝ) :
    P.real {ω | t < X ω} - P.real {ω | t < Y ω}
      = P.real {ω | Y ω ≤ t ∧ t < X ω} - P.real {ω | X ω ≤ t ∧ t < Y ω} := by
  have hC : MeasurableSet {ω | t < X ω ∧ t < Y ω} :=
    (measurableSet_lt measurable_const hX).inter (measurableSet_lt measurable_const hY)
  have e1 : {ω | t < X ω} = {ω | Y ω ≤ t ∧ t < X ω} ∪ {ω | t < X ω ∧ t < Y ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      rcases le_or_gt (Y ω) t with h' | h'
      · exact Or.inl ⟨h', h⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩) <;> exact h
  have e2 : {ω | t < Y ω} = {ω | X ω ≤ t ∧ t < Y ω} ∪ {ω | t < X ω ∧ t < Y ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      rcases le_or_gt (X ω) t with h' | h'
      · exact Or.inl ⟨h', h⟩
      · exact Or.inr ⟨h', h⟩
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
  have d1 : Disjoint {ω | Y ω ≤ t ∧ t < X ω} {ω | t < X ω ∧ t < Y ω} := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    linarith [h1.1, h2.2]
  have d2 : Disjoint {ω | X ω ≤ t ∧ t < Y ω} {ω | t < X ω ∧ t < Y ω} := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    linarith [h1.1, h2.1]
  rw [e1, e2, measureReal_union d1 hC, measureReal_union d2 hC]
  ring

theorem lemma_9_4_core (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    (∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (|P.real {ω | t < X ω} - P.real {ω | t < Y ω}| * t ^ (κ - 1))
      ≤ ENNReal.ofReal κ⁻¹ *
        ∫⁻ ω, ENNReal.ofReal |(max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ| ∂P) ∧
    (Integrable (fun ω => (max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ) P →
      IntegrableOn (fun t : ℝ => (P.real {ω | t < X ω} - P.real {ω | t < Y ω}) * t ^ (κ - 1))
          (Set.Ioi 0) ∧
        ∫ t in Set.Ioi (0 : ℝ), (P.real {ω | t < X ω} - P.real {ω | t < Y ω}) * t ^ (κ - 1)
          = κ⁻¹ * ∫ ω, ((max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ) ∂P) := by
  -- measurability of the two "difference-set" tail functions
  have hS1 : MeasurableSet {p : ℝ × Ω | Y p.2 ≤ p.1 ∧ p.1 < X p.2} :=
    (measurableSet_le (hY.comp measurable_snd) measurable_fst).inter
      (measurableSet_lt measurable_fst (hX.comp measurable_snd))
  have hS2 : MeasurableSet {p : ℝ × Ω | X p.2 ≤ p.1 ∧ p.1 < Y p.2} :=
    (measurableSet_le (hX.comp measurable_snd) measurable_fst).inter
      (measurableSet_lt measurable_fst (hY.comp measurable_snd))
  have mA : Measurable fun t : ℝ => P {ω | Y ω ≤ t ∧ t < X ω} :=
    measurable_measure_prodMk_left hS1
  have mB : Measurable fun t : ℝ => P {ω | X ω ≤ t ∧ t < Y ω} :=
    measurable_measure_prodMk_left hS2
  have mg : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (κ - 1)) :=
    (measurable_id.pow_const _).ennreal_ofReal
  have mD : Measurable fun ω => (max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ :=
    ((hX.max measurable_const).pow_const _).sub ((hY.max measurable_const).pow_const _)
  have TA := tail_diff_lintegral P κ hκ X Y hX hY
  have TB := tail_diff_lintegral P κ hκ Y X hY hX
  have hdiff := tail_diff_eq P X Y hX hY
  constructor
  · calc ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (|P.real {ω | t < X ω} - P.real {ω | t < Y ω}| * t ^ (κ - 1))
        ≤ ∫⁻ t in Set.Ioi (0 : ℝ),
          (P {ω | Y ω ≤ t ∧ t < X ω} * ENNReal.ofReal (t ^ (κ - 1)) +
            P {ω | X ω ≤ t ∧ t < Y ω} * ENNReal.ofReal (t ^ (κ - 1))) := by
          apply setLIntegral_mono' measurableSet_Ioi
          intro t ht
          have ht' : (0:ℝ) < t := ht
          have hg : 0 ≤ t ^ (κ - 1) := Real.rpow_nonneg ht'.le _
          rw [hdiff t]
          have habs : |P.real {ω | Y ω ≤ t ∧ t < X ω} - P.real {ω | X ω ≤ t ∧ t < Y ω}|
              ≤ P.real {ω | Y ω ≤ t ∧ t < X ω} + P.real {ω | X ω ≤ t ∧ t < Y ω} := by
            refine (abs_sub _ _).trans ?_
            rw [abs_of_nonneg measureReal_nonneg, abs_of_nonneg measureReal_nonneg]
          calc ENNReal.ofReal (|P.real {ω | Y ω ≤ t ∧ t < X ω} -
                P.real {ω | X ω ≤ t ∧ t < Y ω}| * t ^ (κ - 1))
              ≤ ENNReal.ofReal ((P.real {ω | Y ω ≤ t ∧ t < X ω} +
                P.real {ω | X ω ≤ t ∧ t < Y ω}) * t ^ (κ - 1)) :=
                ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right habs hg)
            _ = _ := by
                rw [ENNReal.ofReal_mul (by positivity),
                  ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg, add_mul,
                  measureReal_def, measureReal_def,
                  ENNReal.ofReal_toReal (measure_ne_top _ _),
                  ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ = (∫⁻ t in Set.Ioi (0 : ℝ), P {ω | Y ω ≤ t ∧ t < X ω} * ENNReal.ofReal (t ^ (κ - 1))) +
          ∫⁻ t in Set.Ioi (0 : ℝ), P {ω | X ω ≤ t ∧ t < Y ω} * ENNReal.ofReal (t ^ (κ - 1)) := by
          have m1 : Measurable fun t : ℝ =>
              P {ω | Y ω ≤ t ∧ t < X ω} * ENNReal.ofReal (t ^ (κ - 1)) := mA.mul mg
          exact lintegral_add_left m1 _
      _ = ENNReal.ofReal κ⁻¹ *
          (∫⁻ ω, ENNReal.ofReal (max ((max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ) 0) ∂P +
           ∫⁻ ω, ENNReal.ofReal (max (-((max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ)) 0) ∂P) := by
          rw [TA, TB, ← mul_add]
          simp_rw [neg_sub]
      _ = ENNReal.ofReal κ⁻¹ *
          ∫⁻ ω, ENNReal.ofReal |(max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ| ∂P := by
          congr 1
          rw [← lintegral_add_left ((mD.max measurable_const).ennreal_ofReal)]
          congr 1
          funext ω
          rw [← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
            max_zero_add_max_neg_zero_eq_abs_self]
  · intro hD
    set D : Ω → ℝ := fun ω => (max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ with hDdef
    have hDp : Integrable (fun ω => max (D ω) 0) P := hD.pos_part
    have hDn : Integrable (fun ω => max (-D ω) 0) P := hD.neg.pos_part
    -- the two nonnegative pieces
    set A : ℝ → ℝ := fun t => P.real {ω | Y ω ≤ t ∧ t < X ω} * t ^ (κ - 1) with hA
    set B : ℝ → ℝ := fun t => P.real {ω | X ω ≤ t ∧ t < Y ω} * t ^ (κ - 1) with hB
    have mA' : Measurable A := mA.ennreal_toReal.mul (measurable_id.pow_const _)
    have mB' : Measurable B := mB.ennreal_toReal.mul (measurable_id.pow_const _)
    have hAnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] A := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg measureReal_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
    have hBnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] B := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg measureReal_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
    have lA : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (A t)
        = ENNReal.ofReal κ⁻¹ * ∫⁻ ω, ENNReal.ofReal (max (D ω) 0) ∂P := by
      rw [← TA]
      apply lintegral_congr
      intro t
      simp only [hA]
      rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have lB : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (B t)
        = ENNReal.ofReal κ⁻¹ * ∫⁻ ω, ENNReal.ofReal (max (-D ω) 0) ∂P := by
      have TB' : ∫⁻ t in Set.Ioi (0:ℝ), P {ω | X ω ≤ t ∧ t < Y ω} * ENNReal.ofReal (t ^ (κ - 1))
          = ENNReal.ofReal κ⁻¹ * ∫⁻ ω, ENNReal.ofReal (max (-D ω) 0) ∂P := by
        rw [TB]
        congr 1
        apply lintegral_congr
        intro ω
        simp only [hDdef, neg_sub]
      rw [← TB']
      apply lintegral_congr
      intro t
      simp only [hB]
      rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have finP : ∫⁻ ω, ENNReal.ofReal (max (D ω) 0) ∂P < ∞ := by
      have := hDp.hasFiniteIntegral
      rw [HasFiniteIntegral] at this
      refine lt_of_eq_of_lt ?_ this
      apply lintegral_congr
      intro ω
      rw [Real.enorm_eq_ofReal (le_max_right _ _)]
    have finN : ∫⁻ ω, ENNReal.ofReal (max (-D ω) 0) ∂P < ∞ := by
      have := hDn.hasFiniteIntegral
      rw [HasFiniteIntegral] at this
      refine lt_of_eq_of_lt ?_ this
      apply lintegral_congr
      intro ω
      rw [Real.enorm_eq_ofReal (le_max_right _ _)]
    have iA : IntegrableOn A (Set.Ioi 0) := by
      refine ⟨mA'.aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral]
      have : (fun t => ‖A t‖ₑ) =ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
          fun t => ENNReal.ofReal (A t) := by
        filter_upwards [hAnn] with t ht
        rw [Real.enorm_eq_ofReal ht]
      rw [lintegral_congr_ae this, lA]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top finP
    have iB : IntegrableOn B (Set.Ioi 0) := by
      refine ⟨mB'.aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral]
      have : (fun t => ‖B t‖ₑ) =ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
          fun t => ENNReal.ofReal (B t) := by
        filter_upwards [hBnn] with t ht
        rw [Real.enorm_eq_ofReal ht]
      rw [lintegral_congr_ae this, lB]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top finN
    have eP : ∫ ω, max (D ω) 0 ∂P = (∫⁻ ω, ENNReal.ofReal (max (D ω) 0) ∂P).toReal :=
      integral_eq_lintegral_of_nonneg_ae (f := fun ω => max (D ω) 0)
        (ae_of_all _ fun ω => le_max_right _ _) hDp.aestronglyMeasurable
    have eN : ∫ ω, max (-D ω) 0 ∂P = (∫⁻ ω, ENNReal.ofReal (max (-D ω) 0) ∂P).toReal :=
      integral_eq_lintegral_of_nonneg_ae (f := fun ω => max (-D ω) 0)
        (ae_of_all _ fun ω => le_max_right _ _) hDn.aestronglyMeasurable
    have vA : ∫ t in Set.Ioi (0:ℝ), A t = κ⁻¹ * ∫ ω, max (D ω) 0 ∂P := by
      rw [integral_eq_lintegral_of_nonneg_ae hAnn mA'.aestronglyMeasurable, lA, eP,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    have vB : ∫ t in Set.Ioi (0:ℝ), B t = κ⁻¹ * ∫ ω, max (-D ω) 0 ∂P := by
      rw [integral_eq_lintegral_of_nonneg_ae hBnn mB'.aestronglyMeasurable, lB, eN,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    have hfun : (fun t : ℝ => (P.real {ω | t < X ω} - P.real {ω | t < Y ω}) * t ^ (κ - 1))
        = fun t => A t - B t := by
      funext t
      rw [hdiff t]
      simp only [hA, hB]
      ring
    have hDsplit : ∫ ω, D ω ∂P = ∫ ω, max (D ω) 0 ∂P - ∫ ω, max (-D ω) 0 ∂P := by
      rw [← integral_sub hDp hDn]
      congr 1
      funext ω
      rw [max_zero_sub_max_neg_zero_eq_self]
    rw [hfun]
    refine ⟨iA.sub iB, ?_⟩
    rw [integral_sub iA iB, vA, vB]
    change _ = κ⁻¹ * ∫ ω, D ω ∂P
    rw [hDsplit]
    ring

end GoldieRenewal.Kesten

open GoldieRenewal.Kesten
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    (∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (|P.real {ω | t < X ω} - P.real {ω | t < Y ω}| * t ^ (κ - 1))
      ≤ ENNReal.ofReal κ⁻¹ *
        ∫⁻ ω, ENNReal.ofReal |(max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ| ∂P) ∧
    (Integrable (fun ω => (max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ) P →
      IntegrableOn (fun t : ℝ => (P.real {ω | t < X ω} - P.real {ω | t < Y ω}) * t ^ (κ - 1))
          (Set.Ioi 0) ∧
        ∫ t in Set.Ioi (0 : ℝ), (P.real {ω | t < X ω} - P.real {ω | t < Y ω}) * t ^ (κ - 1)
          = κ⁻¹ * ∫ ω, ((max (X ω) 0) ^ κ - (max (Y ω) 0) ^ κ) ∂P) := by
  exact lemma_9_4_core P κ hκ X Y hX hY
