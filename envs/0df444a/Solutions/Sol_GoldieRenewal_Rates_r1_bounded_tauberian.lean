-- Prove2me | solution 1 for GoldieRenewal.Rates.r1_bounded_tauberian
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:04:55.787758+00:00
-- url     : https://prove2.me/submissions/806a8a84-de2b-4836-b930-0c731322180c

import Mathlib
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Rates_Expansion
import Theorems.Thm_GoldieRenewal_Implicit_theorem_2_3
import Theorems.Thm_GoldieRenewal_Rates_contour_convolution_identity

open MeasureTheory ProbabilityTheory Complex Filter Topology
open GoldieRenewal.Rates
open QueueingFundamentals.MG1 (convPow)

lemma lattice_add_mem_aux (l : ℝ) {a b : ℝ} (ha : a ∈ Set.range (fun n : ℤ => (n : ℝ) * l))
    (hb : b ∈ Set.range (fun n : ℤ => (n : ℝ) * l)) :
    a + b ∈ Set.range (fun n : ℤ => (n : ℝ) * l) := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  exact ⟨m + n, by push_cast; ring⟩

lemma convPow_lattice_aux (μ : Measure ℝ) [SFinite μ] (l : ℝ)
    (h : μ (Set.range (fun n : ℤ => (n : ℝ) * l))ᶜ = 0) :
    ∀ n, convPow μ n (Set.range (fun n : ℤ => (n : ℝ) * l))ᶜ = 0 := by
  set L := Set.range (fun n : ℤ => (n : ℝ) * l) with hL
  have hLm : MeasurableSet L := (Set.countable_range _).measurableSet
  intro n
  induction n with
  | zero =>
    show (Measure.dirac (0 : ℝ)) Lᶜ = 0
    rw [Measure.dirac_apply' _ hLm.compl]
    simp only [Set.indicator, Set.mem_compl_iff, not_not]
    have : (0 : ℝ) ∈ L := ⟨0, by simp⟩
    simp [this]
  | succ n ih =>
    show Measure.map _ _ Lᶜ = 0
    rw [Measure.map_apply (by fun_prop) hLm.compl]
    have hsub : (fun x : ℝ × ℝ => x.1 + x.2) ⁻¹' Lᶜ ⊆ (Lᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ Lᶜ) := by
      intro p hp
      simp only [Set.mem_preimage, Set.mem_compl_iff] at hp
      by_contra hc
      simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true,
        true_and, not_or, not_not] at hc
      exact hp (lattice_add_mem_aux l hc.1 hc.2)
    refine measure_mono_null hsub (measure_union_null ?_ ?_)
    · rw [Measure.prod_prod, ih, zero_mul]
    · rw [Measure.prod_prod, h, mul_zero]

lemma spread_not_arith_aux (μ : Measure ℝ) [SFinite μ] (h : SpreadOut μ) :
    ¬ GoldieRenewal.Implicit.IsArithmetic μ := by
  rintro ⟨l, _, hl⟩
  obtain ⟨n, _, hn⟩ := h
  apply hn
  refine ⟨(Set.range (fun n : ℤ => (n : ℝ) * l))ᶜ,
    (Set.countable_range _).measurableSet.compl, convPow_lattice_aux μ l hl n, ?_⟩
  rw [compl_compl]
  exact (Set.countable_range _).measure_zero _

lemma cond_law_eq_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → ℝ)
    (hM : Measurable M) :
    ((P.map M)[|{x : ℝ | x ≠ 0}]).map (fun x => Real.log |x|) = logLawGivenNonzero P M := by
  have hS : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton 0).compl
  unfold logLawGivenNonzero ProbabilityTheory.cond
  rw [Measure.restrict_map hM hS, Measure.map_apply hM hS, Measure.map_smul, Measure.map_smul,
    Measure.map_map (by fun_prop) hM]
  rfl

lemma cramer_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → ℝ) (hM : Measurable M) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M)) :
    GoldieRenewal.Implicit.CramerConditions κ (P.map M) := by
  refine ⟨?_, hκ, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hM MeasurableSet.univ]; simp
  · rw [lintegral_map (by measurability) hM]; exact h_2_3
  · rw [lintegral_map (by measurability) hM]
    refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := β⁻¹)) h_3_3)
    rw [← lintegral_const_mul _ (by measurability)]
    apply lintegral_mono
    intro ω
    dsimp only
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have ha := abs_nonneg (M ω)
    have hlog := Real.log_le_rpow_div ha hβ
    have hp : 0 ≤ |M ω| ^ κ := Real.rpow_nonneg ha _
    have hmax : max (Real.log |M ω|) 0 ≤ |M ω| ^ β / β :=
      max_le hlog (by positivity)
    calc |M ω| ^ κ * max (Real.log |M ω|) 0 ≤ |M ω| ^ κ * (|M ω| ^ β / β) :=
          mul_le_mul_of_nonneg_left hmax hp
      _ = β⁻¹ * |M ω| ^ (κ + β) := by
          rw [Real.rpow_add' ha (by linarith)]; ring
  · rw [cond_law_eq_aux P M hM]
    have : IsFiniteMeasure (logLawGivenNonzero P M) := by
      unfold logLawGivenNonzero; infer_instance
    exact spread_not_arith_aux _ h_3_4

lemma tailcond_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_3_7 : IntegrableOn (fun t : ℝ =>
        (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1)) (Set.Ioi 0)) :
    GoldieRenewal.Implicit.TailCondPlus P M R κ := by
  unfold GoldieRenewal.Implicit.TailCondPlus GoldieRenewal.Implicit.tailDiffPlus
  have hmeas : Measurable (fun t : ℝ =>
      (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ - 1)) := by
    have h1 : Measurable (fun t : ℝ => P.real {ω | t < R ω}) := by
      apply Antitone.measurable; intro a b hab
      exact measureReal_mono (fun ω hω => by simp only [Set.mem_setOf_eq] at hω ⊢; linarith)
        (measure_ne_top _ _)
    have h2 : Measurable (fun t : ℝ => P.real {ω | t < M ω * R ω}) := by
      apply Antitone.measurable; intro a b hab
      exact measureReal_mono (fun ω hω => by simp only [Set.mem_setOf_eq] at hω ⊢; linarith)
        (measure_ne_top _ _)
    exact (h1.sub h2).mul (by measurability)
  have hdiff : ∀ t : ℝ, |P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}| ≤ 1 := by
    intro t
    rw [abs_sub_le_iff]
    have := measureReal_le_one (μ := P) (s := {ω | t < R ω})
    have := measureReal_le_one (μ := P) (s := {ω | t < M ω * R ω})
    have := measureReal_nonneg (μ := P) (s := {ω | t < R ω})
    have := measureReal_nonneg (μ := P) (s := {ω | t < M ω * R ω})
    constructor <;> linarith
  have hA : IntegrableOn (fun t : ℝ =>
      (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ - 1)) (Set.Ioc 0 1) := by
    have hpow : IntegrableOn (fun t : ℝ => t ^ (κ - 1)) (Set.Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine hpow.mono' hmeas.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    calc _ ≤ 1 * t ^ (κ - 1) :=
          mul_le_mul_of_nonneg_right (hdiff t) (Real.rpow_nonneg ht.1.le _)
      _ = _ := one_mul _
  have hB : IntegrableOn (fun t : ℝ =>
      (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ - 1)) (Set.Ioi 1) := by
    refine (h_3_7.mono_set (Set.Ioi_subset_Ioi zero_le_one)).norm.mono'
      hmeas.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht1 : (1 : ℝ) < t := ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    gcongr
    · exact ht1.le
    · linarith
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hA.union hB

lemma r_bounded_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (h_indep : IndepFun R M P) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M))
    (h_3_7 : IntegrableOn (fun t : ℝ =>
        (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1)) (Set.Ioi 0)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 0 ≤ GoldieRenewal.Implicit.rFun P R κ x ∧
      GoldieRenewal.Implicit.rFun P R κ x ≤ B := by
  have hC := cramer_aux P M hM κ β hκ hβ h_2_3 h_3_3 h_3_4
  have hT := ((GoldieRenewal.Implicit.theorem_2_3 P M R hM hR κ hC h_indep).1 hM_nonneg).1
    (tailcond_aux P M R κ β hκ hβ h_3_7)
  have hT' := hT.comp Real.tendsto_exp_atTop
  obtain ⟨T, hTb⟩ := (eventually_atTop.1 (hT'.eventually (Iic_mem_nhds
    (lt_add_one (GoldieRenewal.Implicit.Cplus P M R κ)))))
  have hrnn : ∀ x, 0 ≤ GoldieRenewal.Implicit.rFun P R κ x := fun x =>
    mul_nonneg (Real.exp_pos _).le measureReal_nonneg
  refine ⟨max (Real.exp (κ * T)) (GoldieRenewal.Implicit.Cplus P M R κ + 1),
    le_trans (Real.exp_pos _).le (le_max_left _ _), fun x => ⟨hrnn x, ?_⟩⟩
  rcases le_total T x with hx | hx
  · have := hTb x hx
    simp only [Function.comp_apply, Set.mem_Iic] at this
    refine le_trans (le_of_eq ?_) (le_trans this (le_max_right _ _))
    unfold GoldieRenewal.Implicit.rFun
    rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp, mul_comm x κ]
  · unfold GoldieRenewal.Implicit.rFun
    refine le_trans ?_ (le_max_left _ _)
    calc Real.exp (κ * x) * P.real {ω | Real.exp x < R ω} ≤ Real.exp (κ * x) * 1 := by
          gcongr; exact measureReal_le_one
      _ ≤ Real.exp (κ * T) := by
          rw [mul_one]; exact Real.exp_le_exp.2 (by nlinarith)

lemma re_neg_I_mul_aux (c : ℂ) (x : ℝ) : (-(I * c * (x : ℂ))).re = c.im * x := by
  simp [Complex.mul_re]

lemma side_aux (a b : ℝ) (hab : a ≤ b) (γ : ℝ → ℂ) (hγ : Continuous γ)
    (him : ∀ t ∈ Set.Icc a b, (γ t).im ≤ 0) (H : ℝ → ℂ) (hH : ContinuousOn H (Set.Icc a b)) :
    ∃ C L D : ℝ, 0 < D ∧ 0 ≤ L ∧ 0 ≤ C ∧
      Continuous (fun x : ℝ => ∫ t in a..b, Complex.exp (-(I * γ t * (x : ℂ))) * H t) ∧
      (∀ x : ℝ, 0 ≤ x → ‖∫ t in a..b, Complex.exp (-(I * γ t * (x : ℂ))) * H t‖ ≤ C) ∧
      (∀ x : ℝ, 0 ≤ x → ∀ y : ℝ, 0 ≤ y → y ≤ D →
        ‖(∫ t in a..b, Complex.exp (-(I * γ t * ((x + y : ℝ) : ℂ))) * H t) -
          ∫ t in a..b, Complex.exp (-(I * γ t * (x : ℂ))) * H t‖ ≤ L * y) := by
  obtain ⟨CH, hCH⟩ := isCompact_Icc.exists_bound_of_continuousOn hH
  obtain ⟨Kγ, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hγ.continuousOn
  set C' := max CH 0 with hC'
  set K' := max Kγ 0 with hK'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hCH' : ∀ t ∈ Set.Icc a b, ‖H t‖ ≤ C' := fun t ht => le_trans (hCH t ht) (le_max_left _ _)
  have hK2 : ∀ t ∈ Set.Icc a b, ‖γ t‖ ≤ K' := fun t ht => le_trans (hK t ht) (le_max_left _ _)
  have hexp : ∀ t ∈ Set.Icc a b, ∀ x : ℝ, 0 ≤ x →
      ‖Complex.exp (-(I * γ t * (x : ℂ)))‖ ≤ 1 := by
    intro t ht x hx
    rw [Complex.norm_exp, re_neg_I_mul_aux, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (him t ht) hx
  have huIoc : Set.uIoc a b ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hab]; exact Set.Ioc_subset_Icc_self
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  refine ⟨C' * (b - a), 2 * K' * C' * (b - a), 1 / (K' + 1), by positivity,
    by have : 0 ≤ b - a := by linarith
       positivity,
    by have : 0 ≤ b - a := by linarith
       positivity, ?_, ?_, ?_⟩
  · -- continuity
    set H' : ℝ → ℂ := fun t => H (Set.projIcc a b hab t) with hH'
    have hH'c : Continuous H' :=
      hH.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        (fun t => (Set.projIcc a b hab t).2)
    have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun (x : ℝ) (t : ℝ) => Complex.exp (-(I * γ t * (x : ℂ))) * H' t)
      (by
        show Continuous (fun p : ℝ × ℝ => Complex.exp (-(I * γ p.2 * (p.1 : ℂ))) * H' p.2)
        fun_prop) a b
    convert hc using 2 with x
    apply intervalIntegral.integral_congr
    intro t ht
    rw [huIcc] at ht
    simp only [hH', Set.projIcc_of_mem hab ht]
  · intro x hx
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := C') (f := fun t => Complex.exp (-(I * γ t * (x : ℂ))) * H t)
      (fun t ht => by
        rw [norm_mul]
        calc _ ≤ 1 * C' := mul_le_mul (hexp t (huIoc ht) x hx) (hCH' t (huIoc ht))
              (norm_nonneg _) zero_le_one
          _ = C' := one_mul _)
    rwa [abs_of_nonneg (by linarith)] at this
  · intro x hx y hy hyD
    have hcont : ∀ s : ℝ, IntervalIntegrable
        (fun t => Complex.exp (-(I * γ t * (s : ℂ))) * H t) volume a b := by
      intro s
      apply ContinuousOn.intervalIntegrable
      rw [huIcc]
      exact ((by fun_prop : Continuous fun t => Complex.exp (-(I * γ t * (s : ℂ))))).continuousOn.mul hH
    rw [← intervalIntegral.integral_sub (hcont (x + y)) (hcont x)]
    have hyK : K' * y ≤ 1 := by
      have : y * (K' + 1) ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at hyD; linarith
      nlinarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := 2 * K' * C' * y)
      (f := fun t => Complex.exp (-(I * γ t * ((x + y : ℝ) : ℂ))) * H t -
        Complex.exp (-(I * γ t * (x : ℂ))) * H t)
      (fun t ht => by
        have ht' := huIoc ht
        have hsplit : Complex.exp (-(I * γ t * ((x + y : ℝ) : ℂ))) * H t -
            Complex.exp (-(I * γ t * (x : ℂ))) * H t =
            Complex.exp (-(I * γ t * (x : ℂ))) * (Complex.exp (-(I * γ t * (y : ℂ))) - 1) * H t := by
          have : Complex.exp (-(I * γ t * ((x + y : ℝ) : ℂ))) =
              Complex.exp (-(I * γ t * (x : ℂ))) * Complex.exp (-(I * γ t * (y : ℂ))) := by
            rw [← Complex.exp_add]; congr 1; push_cast; ring
          rw [this]; ring
        rw [hsplit, norm_mul, norm_mul]
        have hz : ‖-(I * γ t * (y : ℂ))‖ ≤ K' * y := by
          rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hy]
          exact mul_le_mul_of_nonneg_right (hK2 t ht') hy
        have h2 := Complex.norm_exp_sub_one_le (le_trans hz hyK)
        calc ‖Complex.exp (-(I * γ t * (x : ℂ)))‖ * ‖Complex.exp (-(I * γ t * (y : ℂ))) - 1‖ *
              ‖H t‖ ≤ 1 * (2 * (K' * y)) * C' := by
              gcongr
              · exact hexp t ht' x hx
              · exact le_trans h2 (by linarith)
              · exact hCH' t ht'
          _ = 2 * K' * C' * y := by ring)
    rw [abs_of_nonneg (by linarith)] at this
    calc _ ≤ 2 * K' * C' * y * (b - a) := this
      _ = _ := by ring

lemma tail_antitone_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) : Measurable (fun t : ℝ => P.real {ω | t < Z ω}) := by
  apply Antitone.measurable
  intro a b hab
  refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
  simp only [Set.mem_setOf_eq] at hω ⊢
  linarith

lemma abs_diff_prob_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Set Ω) : |P.real A - P.real B| ≤ 1 := by
  rw [abs_sub_le_iff]
  have h1 := measureReal_le_one (μ := P) (s := A)
  have h2 := measureReal_le_one (μ := P) (s := B)
  have h3 := measureReal_nonneg (μ := P) (s := A)
  have h4 := measureReal_nonneg (μ := P) (s := B)
  constructor <;> linarith

lemma gPos_measurable_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (κ : ℝ) : Measurable (gPos P M R κ) := by
  unfold gPos
  have h1 := (tail_antitone_aux P R).comp Real.measurable_exp
  have h2 := (tail_antitone_aux P (fun ω => M ω * R ω)).comp Real.measurable_exp
  exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul (h1.sub h2)

lemma gPos_integrable_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_3_7 : IntegrableOn (fun t : ℝ =>
        (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1)) (Set.Ioi 0)) :
    Integrable (gPos P M R κ) ∧ Integrable (fun u => gPos P M R κ u * Real.exp (β * u)) := by
  have hm := gPos_measurable_aux P M R κ
  have hm2 : Measurable (fun u => gPos P M R κ u * Real.exp (β * u)) :=
    hm.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  -- weighted, on Ioi 0
  have hIoi : IntegrableOn (fun u => gPos P M R κ u * Real.exp (β * u)) (Set.Ioi 0) := by
    have key := (integrableOn_comp_exp_Ioi (fun t : ℝ =>
        (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1)) 0).2
      (by rw [Real.exp_zero]; exact h_3_7.mono_set (Set.Ioi_subset_Ioi zero_le_one))
    refine key.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul, gPos]
    rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
    have : Real.exp x * Real.exp (x * (κ + β - 1)) = Real.exp (κ * x) * Real.exp (β * x) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.exp x * ((P.real {ω | Real.exp x < R ω} - P.real {ω | Real.exp x < M ω * R ω}) *
          Real.exp (x * (κ + β - 1)))
        = (Real.exp x * Real.exp (x * (κ + β - 1))) *
          (P.real {ω | Real.exp x < R ω} - P.real {ω | Real.exp x < M ω * R ω}) := by ring
      _ = _ := by rw [this]; ring
  have hgabs : ∀ u, |gPos P M R κ u| ≤ Real.exp (κ * u) := by
    intro u
    unfold gPos
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (κ * u) * |_| ≤ Real.exp (κ * u) * 1 := by
          gcongr; exact abs_diff_prob_le P _ _
      _ = _ := mul_one _
  have hIic : IntegrableOn (fun u => gPos P M R κ u * Real.exp (β * u)) (Set.Iic 0) := by
    refine (integrableOn_exp_mul_Iic (by linarith : 0 < κ + β) 0).mono'
      hm2.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |gPos P M R κ u| * Real.exp (β * u) ≤ Real.exp (κ * u) * Real.exp (β * u) := by
          gcongr; exact hgabs u
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h2 : Integrable (fun u => gPos P M R κ u * Real.exp (β * u)) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    exact hIic.union hIoi
  have h1a : IntegrableOn (gPos P M R κ) (Set.Ioi 0) := by
    refine hIoi.norm.mono' hm.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have : 1 ≤ Real.exp (β * u) := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by nlinarith [Set.mem_Ioi.1 hu])
    nlinarith [abs_nonneg (gPos P M R κ u)]
  have h1b : IntegrableOn (gPos P M R κ) (Set.Iic 0) := by
    refine (integrableOn_exp_mul_Iic hκ 0).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs]; exact hgabs u
  refine ⟨?_, h2⟩
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact h1b.union h1a
lemma tilted_prob_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → ℝ) (hM : Measurable M) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω) (κ : ℝ) (hκ : 0 < κ)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1) :
    IsProbabilityMeasure (tiltedLaw P M κ) := by
  constructor
  have hS : MeasurableSet {ω | 0 < M ω} := measurableSet_lt measurable_const hM
  unfold tiltedLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_map (by fun_prop) (by fun_prop)]
  rw [← h_2_3]
  conv_rhs => rw [← lintegral_add_compl _ hS]
  have h2 : ∫⁻ ω in {ω | 0 < M ω}ᶜ, ENNReal.ofReal (|M ω| ^ κ) ∂P = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    refine (ae_restrict_iff' hS.compl).2 (hM_nonneg.mono fun ω h hω => ?_)
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hω
    have : M ω = 0 := le_antisymm hω h
    simp [this, Real.zero_rpow (ne_of_gt hκ)]
  rw [h2, add_zero]
  apply setLIntegral_congr_fun hS
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  simp only [abs_of_pos hω, Real.rpow_def_of_pos hω, mul_comm]

lemma tilted_exp_integrable_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (M : Ω → ℝ) (hM : Measurable M) (κ β : ℝ)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤) :
    Integrable (fun t : ℝ => Real.exp (β * t)) (tiltedLaw P M κ) := by
  have hS : MeasurableSet {ω | 0 < M ω} := measurableSet_lt measurable_const hM
  refine ⟨(Real.measurable_exp.comp (measurable_const.mul measurable_id)).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hle : ∫⁻ t, ‖Real.exp (β * t)‖ₑ ∂(tiltedLaw P M κ) ≤
      ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P := by
    unfold tiltedLaw
    rw [lintegral_withDensity_eq_lintegral_mul _ (by measurability) (by measurability),
      lintegral_map (by measurability) (by fun_prop)]
    refine le_trans (le_of_eq ?_)
      (setLIntegral_le_lintegral {ω | 0 < M ω} (fun ω => ENNReal.ofReal (|M ω| ^ (κ + β))))
    apply setLIntegral_congr_fun hS
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Pi.mul_apply, Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _),
      abs_of_pos hω]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      Real.rpow_def_of_pos hω]
    congr 2; ring
  exact lt_of_le_of_lt hle h_3_3

lemma norm_exp_char_aux (θ : ℂ) (t β : ℝ) (h1 : -β ≤ θ.im) (h2 : θ.im ≤ 0) :
    ‖Complex.exp (I * θ * (t : ℂ))‖ ≤ 1 + Real.exp (β * t) := by
  rw [Complex.norm_exp]
  have hre : (I * θ * (t : ℂ)).re = -θ.im * t := by simp [Complex.mul_re]
  rw [hre]
  rcases le_total 0 t with ht | ht
  · have : -θ.im * t ≤ β * t := by nlinarith
    linarith [Real.exp_le_exp.2 this, Real.exp_pos (β * t)]
  · have : -θ.im * t ≤ 0 := by nlinarith
    have := Real.exp_le_exp.2 this
    rw [Real.exp_zero] at this
    linarith [Real.exp_pos (β * t)]

lemma charTransform_continuousOn_aux (η : Measure ℝ) [IsFiniteMeasure η] (β : ℝ)
    (hint : Integrable (fun t : ℝ => Real.exp (β * t)) η) :
    ContinuousOn (charTransform η) {θ : ℂ | -β ≤ θ.im ∧ θ.im ≤ 0} := by
  unfold charTransform
  refine continuousOn_of_dominated (bound := fun t => 1 + Real.exp (β * t)) ?_ ?_
    ((integrable_const 1).add hint) ?_
  · intro θ _
    exact (by fun_prop : Continuous fun t : ℝ => Complex.exp (I * θ * (t : ℂ))).aestronglyMeasurable
  · intro θ hθ
    exact Filter.Eventually.of_forall fun t => norm_exp_char_aux θ t β hθ.1 hθ.2
  · exact Filter.Eventually.of_forall fun t =>
      (by fun_prop : Continuous fun θ : ℂ => Complex.exp (I * θ * (t : ℂ))).continuousOn


lemma fourier_continuousOn_aux (g : ℝ → ℝ) (hgm : Measurable g) (β : ℝ) (hg1 : Integrable g)
    (hg2 : Integrable (fun u => g u * Real.exp (β * u))) :
    ContinuousOn (fourierTransform (fun v => (g v : ℂ))) {θ : ℂ | -β ≤ θ.im ∧ θ.im ≤ 0} := by
  unfold fourierTransform
  refine continuousOn_of_dominated (bound := fun t => |g t| + |g t * Real.exp (β * t)|) ?_ ?_
    (hg1.abs.add hg2.abs) ?_
  · intro θ _
    exact ((by fun_prop : Continuous fun t : ℝ => Complex.exp (I * θ * (t : ℂ))).aestronglyMeasurable).mul
      (Complex.measurable_ofReal.comp hgm).aestronglyMeasurable
  · intro θ hθ
    refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have := norm_exp_char_aux θ t β hθ.1 hθ.2
    nlinarith [abs_nonneg (g t)]
  · exact Filter.Eventually.of_forall fun t =>
      ((by fun_prop : Continuous fun θ : ℂ => Complex.exp (I * θ * (t : ℂ)) * (g t : ℂ))).continuousOn

lemma combo_norm_aux (w1 w2 w3 w4 : ℂ) :
    ‖(1 / (2 * Real.pi : ℂ)) * (w1 - w2 + I * w3 - I * w4)‖ ≤
      (1 / (2 * Real.pi)) * (‖w1‖ + ‖w2‖ + ‖w3‖ + ‖w4‖) := by
  have h2pi : ‖(1 / (2 * Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    simp
  rw [norm_mul, h2pi]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ‖w1 - w2 + I * w3 - I * w4‖ ≤ ‖w1 - w2 + I * w3‖ + ‖I * w4‖ := norm_sub_le _ _
    _ ≤ ‖w1 - w2‖ + ‖I * w3‖ + ‖I * w4‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖w1‖ + ‖w2‖ + ‖I * w3‖ + ‖I * w4‖ := by gcongr; exact norm_sub_le _ _
    _ = _ := by rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]

lemma exp_sub_one_le_aux (κ y : ℝ) (hκ : 0 < κ) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp (κ * y) - 1 ≤ κ * Real.exp κ * y := by
  have h1 := Real.add_one_le_exp (-(κ * y))
  have h2 : Real.exp (-(κ * y)) * Real.exp (κ * y) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : Real.exp (κ * y) ≤ Real.exp κ := Real.exp_le_exp.2 (by nlinarith)
  have hpos := Real.exp_pos (κ * y)
  have : Real.exp (κ * y) - 1 ≤ κ * y * Real.exp (κ * y) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h3 (mul_nonneg hκ.le hy)]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (h_indep : IndepFun R M P) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M))
    (h_stone : StoneConditions (tiltedLaw P M κ) β)
    (h_3_7 : IntegrableOn (fun t : ℝ =>
        (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1)) (Set.Ioi 0))
    (z w : ℂ)
    (h_C : EnclosesZerosInStrip (fun θ => 1 - charTransform (tiltedLaw P M κ) θ) β z w) :
    Measurable (fun t : ℝ => (r1Fun P M R κ z w t).re) ∧
    (∃ B : ℝ, ∀ x : ℝ, |(r1Fun P M R κ z w x).re| ≤ B) ∧
    ∃ A x₀ : ℝ, ∀ x : ℝ, x₀ < x → ∀ y : ℝ, 0 ≤ y → y ≤ Real.exp (-(β * x) / 2) →
      (r1Fun P M R κ z w x).re - (r1Fun P M R κ z w (x + y)).re ≤
        A * Real.exp (-(β * x) / 2) := by
  have hident := contour_convolution_identity P M R hM hR hM_nonneg h_indep κ β
    hκ hβ h_2_3 h_3_3 h_3_4 h_stone h_3_7 z w h_C
  obtain ⟨Br, hBr0, hBr⟩ := r_bounded_aux P M R hM hR hM_nonneg h_indep κ β hκ hβ h_2_3 h_3_3
    h_3_4 h_3_7
  set η := tiltedLaw P M κ with hη
  set g := gPos P M R κ with hg
  have : IsProbabilityMeasure η := tilted_prob_aux P M hM hM_nonneg κ hκ h_2_3
  have hgm : Measurable g := gPos_measurable_aux P M R κ
  obtain ⟨hg1, hg2⟩ := gPos_integrable_aux P M R κ β hκ hβ h_3_7
  have hcont := charTransform_continuousOn_aux η β
    (tilted_exp_integrable_aux P M hM κ β h_3_3)
  have hgcont := fourier_continuousOn_aux g hgm β hg1 hg2
  obtain ⟨hzw, hz1, hz2, hw2, hzeros⟩ := h_C
  have hzw' : z.im ≤ w.im := hz2.le
  have hnz : ∀ θ : ℂ, z.im ≤ θ.im → θ.im ≤ w.im → z.re ≤ θ.re → θ.re ≤ w.re →
      (θ.im = z.im ∨ θ.im = w.im ∨ θ.re = z.re ∨ θ.re = w.re) →
      1 - charTransform η θ ≠ 0 := by
    intro θ h1 h2 h3 h4 hside h0
    have := hzeros θ (by linarith) (by linarith) h0
    rcases hside with h | h | h | h <;> linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]
  have hmaps : ∀ θ : ℂ, z.im ≤ θ.im → θ.im ≤ w.im → θ ∈ {θ : ℂ | -β ≤ θ.im ∧ θ.im ≤ 0} :=
    fun θ h1 h2 => ⟨by linarith, by linarith⟩
  -- continuity of the side densities
  have hHc : ∀ (γ : ℝ → ℂ) (a b : ℝ), Continuous γ →
      (∀ t ∈ Set.Icc a b, z.im ≤ (γ t).im ∧ (γ t).im ≤ w.im) →
      (∀ t ∈ Set.Icc a b, 1 - charTransform η (γ t) ≠ 0) →
      ContinuousOn (fun t => fourierTransform (fun v => (g v : ℂ)) (γ t) /
        (1 - charTransform η (γ t))) (Set.Icc a b) := by
    intro γ a b hγ hγS hγ0
    have hmap : Set.MapsTo γ (Set.Icc a b) {θ : ℂ | -β ≤ θ.im ∧ θ.im ≤ 0} :=
      fun t ht => hmaps _ (hγS t ht).1 (hγS t ht).2
    exact (hgcont.comp hγ.continuousOn hmap).div
      (continuousOn_const.sub (hcont.comp hγ.continuousOn hmap)) hγ0
  obtain ⟨C1, L1, D1, hD1, hL1, hC1, hc1, hb1, hl1⟩ := side_aux z.re w.re hzw.le
    (fun x : ℝ => (x : ℂ) + (z.im : ℂ) * I) (by fun_prop) (fun x _ => by simp; linarith)
    _ (hHc (fun x : ℝ => (x : ℂ) + (z.im : ℂ) * I) z.re w.re (by fun_prop) (fun x _ => by simp; linarith)
      (fun x hx => hnz _ (by simp) (by simp; linarith) (by simp; exact hx.1) (by simp; exact hx.2)
        (Or.inl (by simp))))
  obtain ⟨C2, L2, D2, hD2, hL2, hC2, hc2, hb2, hl2⟩ := side_aux z.re w.re hzw.le
    (fun x : ℝ => (x : ℂ) + (w.im : ℂ) * I) (by fun_prop) (fun x _ => by simp; linarith)
    _ (hHc (fun x : ℝ => (x : ℂ) + (w.im : ℂ) * I) z.re w.re (by fun_prop) (fun x _ => by simp; linarith)
      (fun x hx => hnz _ (by simp; linarith) (by simp) (by simp; exact hx.1) (by simp; exact hx.2)
        (Or.inr (Or.inl (by simp)))))
  obtain ⟨C3, L3, D3, hD3, hL3, hC3, hc3, hb3, hl3⟩ := side_aux z.im w.im hzw'
    (fun y : ℝ => (w.re : ℂ) + (y : ℂ) * I) (by fun_prop) (fun y hy => by simp; linarith [hy.2])
    _ (hHc (fun y : ℝ => (w.re : ℂ) + (y : ℂ) * I) z.im w.im (by fun_prop) (fun y hy => by simp; exact hy)
      (fun y hy => hnz _ (by simp; exact hy.1) (by simp; exact hy.2) (by simp; linarith) (by simp)
        (Or.inr (Or.inr (Or.inr (by simp))))))
  obtain ⟨C4, L4, D4, hD4, hL4, hC4, hc4, hb4, hl4⟩ := side_aux z.im w.im hzw'
    (fun y : ℝ => (z.re : ℂ) + (y : ℂ) * I) (by fun_prop) (fun y hy => by simp; linarith [hy.2])
    _ (hHc (fun y : ℝ => (z.re : ℂ) + (y : ℂ) * I) z.im w.im (by fun_prop) (fun y hy => by simp; exact hy)
      (fun y hy => hnz _ (by simp; exact hy.1) (by simp; exact hy.2) (by simp) (by simp; linarith)
        (Or.inr (Or.inr (Or.inl (by simp))))))
  set F1 : ℝ → ℂ := fun x => ∫ t in z.re..w.re,
    Complex.exp (-(I * ((t : ℂ) + (z.im : ℂ) * I) * (x : ℂ))) *
      (fourierTransform (fun v => (g v : ℂ)) ((t : ℂ) + (z.im : ℂ) * I) /
        (1 - charTransform η ((t : ℂ) + (z.im : ℂ) * I))) with hF1
  set F2 : ℝ → ℂ := fun x => ∫ t in z.re..w.re,
    Complex.exp (-(I * ((t : ℂ) + (w.im : ℂ) * I) * (x : ℂ))) *
      (fourierTransform (fun v => (g v : ℂ)) ((t : ℂ) + (w.im : ℂ) * I) /
        (1 - charTransform η ((t : ℂ) + (w.im : ℂ) * I))) with hF2
  set F3 : ℝ → ℂ := fun x => ∫ t in z.im..w.im,
    Complex.exp (-(I * ((w.re : ℂ) + (t : ℂ) * I) * (x : ℂ))) *
      (fourierTransform (fun v => (g v : ℂ)) ((w.re : ℂ) + (t : ℂ) * I) /
        (1 - charTransform η ((w.re : ℂ) + (t : ℂ) * I))) with hF3
  set F4 : ℝ → ℂ := fun x => ∫ t in z.im..w.im,
    Complex.exp (-(I * ((z.re : ℂ) + (t : ℂ) * I) * (x : ℂ))) *
      (fourierTransform (fun v => (g v : ℂ)) ((z.re : ℂ) + (t : ℂ) * I) /
        (1 - charTransform η ((z.re : ℂ) + (t : ℂ) * I))) with hF4
  set Kf : ℝ → ℂ := fun x => (1 / (2 * Real.pi : ℂ)) * (F1 x - F2 x + I * F3 x - I * F4 x)
    with hKf
  have hKid : ∀ x : ℝ, ∫ u : ℝ, (g u : ℂ) * cFun η z w (x - u) = Kf x := by
    intro x
    rw [hident x]
    simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul, mul_div_assoc, hKf, hF1,
      hF2, hF3, hF4]
  have hf : ∀ x : ℝ, (r1Fun P M R κ z w x).re =
      CPlus P M R κ - GoldieRenewal.Implicit.rFun P R κ x -
        (if 0 < x then (Kf x).re else 0) := by
    intro x
    unfold r1Fun
    rw [← hg, ← hη]
    split_ifs with h
    · rw [hKid x]; simp [Complex.sub_re]
    · simp
  have hKc : Continuous Kf :=
    continuous_const.mul (((hc1.sub hc2).add (continuous_const.mul hc3)).sub
      (continuous_const.mul hc4))
  have hKb : ∀ x : ℝ, 0 ≤ x → ‖Kf x‖ ≤ (1 / (2 * Real.pi)) * (C1 + C2 + C3 + C4) := by
    intro x hx
    refine le_trans (combo_norm_aux _ _ _ _) ?_
    gcongr
    · exact hb1 x hx
    · exact hb2 x hx
    · exact hb3 x hx
    · exact hb4 x hx
  refine ⟨?_, ?_, ?_⟩
  · have hfun : (fun t : ℝ => (r1Fun P M R κ z w t).re) = fun t =>
        CPlus P M R κ - GoldieRenewal.Implicit.rFun P R κ t -
          (if 0 < t then (Kf t).re else 0) := funext hf
    rw [hfun]
    have hrm : Measurable (GoldieRenewal.Implicit.rFun P R κ) := by
      unfold GoldieRenewal.Implicit.rFun
      exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
        ((tail_antitone_aux P R).comp Real.measurable_exp)
    exact (measurable_const.sub hrm).sub (Measurable.ite
      (measurableSet_lt measurable_const measurable_id)
      (Complex.continuous_re.comp hKc).measurable measurable_const)
  · refine ⟨|CPlus P M R κ| + Br + (1 / (2 * Real.pi)) * (C1 + C2 + C3 + C4), fun x => ?_⟩
    rw [hf x]
    obtain ⟨hr0, hr1⟩ := hBr x
    have hpos : 0 ≤ (1 / (2 * Real.pi)) * (C1 + C2 + C3 + C4) := by positivity
    split_ifs with h
    · have hre := Complex.abs_re_le_norm (Kf x)
      have hk := hKb x h.le
      calc |CPlus P M R κ - GoldieRenewal.Implicit.rFun P R κ x - (Kf x).re|
          ≤ |CPlus P M R κ - GoldieRenewal.Implicit.rFun P R κ x| + |(Kf x).re| := abs_sub _ _
        _ ≤ |CPlus P M R κ| + |GoldieRenewal.Implicit.rFun P R κ x| + |(Kf x).re| := by
            gcongr; exact abs_sub _ _
        _ ≤ _ := by rw [abs_of_nonneg hr0]; linarith
    · rw [sub_zero]
      calc |CPlus P M R κ - GoldieRenewal.Implicit.rFun P R κ x|
          ≤ |CPlus P M R κ| + |GoldieRenewal.Implicit.rFun P R κ x| := abs_sub _ _
        _ ≤ _ := by rw [abs_of_nonneg hr0]; linarith
  · set D := min (min (min D1 D2) (min D3 D4)) 1 with hDdef
    have hD : 0 < D := lt_min (lt_min (lt_min hD1 hD2) (lt_min hD3 hD4)) one_pos
    set A := κ * Real.exp κ * Br + (1 / (2 * Real.pi)) * (L1 + L2 + L3 + L4) with hA
    have hA0 : 0 ≤ A := by positivity
    refine ⟨A, max 0 (-(2 / β) * Real.log D), fun x hx y hy hyx => ?_⟩
    have hx0 : 0 < x := lt_of_le_of_lt (le_max_left _ _) hx
    have hx1 : -(2 / β) * Real.log D < x := lt_of_le_of_lt (le_max_right _ _) hx
    have hexpD : Real.exp (-(β * x) / 2) ≤ D := by
      rw [← Real.exp_log hD]
      apply Real.exp_le_exp.2
      have : -(2 / β) * Real.log D * (β / 2) < x * (β / 2) :=
        mul_lt_mul_of_pos_right hx1 (by positivity)
      have h2 : -(2 / β) * Real.log D * (β / 2) = -Real.log D := by field_simp
      linarith
    have hyD : y ≤ D := le_trans hyx hexpD
    have hy1 : y ≤ 1 := le_trans hyD (min_le_right _ _)
    have hyD1 : y ≤ D1 := le_trans hyD (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _)))
    have hyD2 : y ≤ D2 := le_trans hyD (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _)))
    have hyD3 : y ≤ D3 := le_trans hyD (le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hyD4 : y ≤ D4 := le_trans hyD (le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
    rw [hf x, hf (x + y), if_pos hx0, if_pos (by linarith)]
    -- the r part
    have hr : GoldieRenewal.Implicit.rFun P R κ (x + y) - GoldieRenewal.Implicit.rFun P R κ x ≤
        κ * Real.exp κ * Br * y := by
      have hmono : P.real {ω | Real.exp (x + y) < R ω} ≤ P.real {ω | Real.exp x < R ω} := by
        refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
        simp only [Set.mem_setOf_eq] at hω ⊢
        exact lt_of_le_of_lt (Real.exp_le_exp.2 (by linarith)) hω
      have h1 : GoldieRenewal.Implicit.rFun P R κ (x + y) ≤
          Real.exp (κ * y) * GoldieRenewal.Implicit.rFun P R κ x := by
        unfold GoldieRenewal.Implicit.rFun
        rw [show κ * (x + y) = κ * y + κ * x by ring, Real.exp_add, mul_assoc]
        gcongr
      have h2 := exp_sub_one_le_aux κ y hκ hy hy1
      obtain ⟨hr0, hr1⟩ := hBr x
      have h3 : 0 ≤ Real.exp (κ * y) - 1 := by
        have := Real.one_le_exp (mul_nonneg hκ.le hy); linarith
      calc _ ≤ (Real.exp (κ * y) - 1) * GoldieRenewal.Implicit.rFun P R κ x := by nlinarith
        _ ≤ (Real.exp (κ * y) - 1) * Br := mul_le_mul_of_nonneg_left hr1 h3
        _ ≤ κ * Real.exp κ * y * Br := mul_le_mul_of_nonneg_right h2 hBr0
        _ = _ := by ring
    have hK : (Kf (x + y)).re - (Kf x).re ≤ (1 / (2 * Real.pi)) * (L1 + L2 + L3 + L4) * y := by
      have heq : Kf (x + y) - Kf x = (1 / (2 * Real.pi : ℂ)) *
          ((F1 (x + y) - F1 x) - (F2 (x + y) - F2 x) + I * (F3 (x + y) - F3 x) -
            I * (F4 (x + y) - F4 x)) := by
        simp only [hKf]; ring
      have hnorm : ‖Kf (x + y) - Kf x‖ ≤ (1 / (2 * Real.pi)) * (L1 + L2 + L3 + L4) * y := by
        rw [heq]
        refine le_trans (combo_norm_aux _ _ _ _) ?_
        have e1 := hl1 x hx0.le y hy hyD1
        have e2 := hl2 x hx0.le y hy hyD2
        have e3 := hl3 x hx0.le y hy hyD3
        have e4 := hl4 x hx0.le y hy hyD4
        have hpi : 0 ≤ 1 / (2 * Real.pi) := by positivity
        calc (1 / (2 * Real.pi)) * (‖F1 (x + y) - F1 x‖ + ‖F2 (x + y) - F2 x‖ +
              ‖F3 (x + y) - F3 x‖ + ‖F4 (x + y) - F4 x‖)
            ≤ (1 / (2 * Real.pi)) * (L1 * y + L2 * y + L3 * y + L4 * y) := by
              gcongr
          _ = _ := by ring
      have := Complex.re_le_norm (Kf (x + y) - Kf x)
      rw [Complex.sub_re] at this
      linarith
    have htot : A * y ≤ A * Real.exp (-(β * x) / 2) := mul_le_mul_of_nonneg_left hyx hA0
    have hAy : A * y = κ * Real.exp κ * Br * y + (1 / (2 * Real.pi)) * (L1 + L2 + L3 + L4) * y := by
      rw [hA]; ring
    linarith
