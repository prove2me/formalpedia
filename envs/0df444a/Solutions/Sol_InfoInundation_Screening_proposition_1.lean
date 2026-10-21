-- Prove2me | solution 1 for InfoInundation.Screening.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:57:14.966656+00:00
-- url     : https://prove2.me/submissions/5b75aecb-9a90-4076-a0a0-b408d845a95b

import Mathlib
import Definitions.Def_InfoInundation_Screening_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InfoInundation.Screening

lemma ii_aux_int (G : Measure ℝ) [IsFiniteMeasure G] (s r p : ℝ) (hs : 0 < s) (hp : 0 ≤ p) :
    Integrable (fun σ : ℝ => (σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) G := by
  have hw : ∀ σ : ℝ, 0 < σ ^ 2 + s ^ 2 := fun σ => by positivity
  have hc : Continuous (fun σ : ℝ => (σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) := by
    apply Continuous.mul
    · exact Continuous.rpow_const (by fun_prop) (fun x => Or.inl (hw x).ne')
    · apply Real.continuous_exp.comp
      apply Continuous.neg
      exact continuous_const.div (by fun_prop) (fun x => by have := hw x; positivity)
  refine Integrable.of_bound hc.aestronglyMeasurable ((s ^ 2) ^ (-p) * Real.exp (|r| / (2 * s ^ 2))) ?_
  refine Filter.Eventually.of_forall (fun σ => ?_)
  have h1 : (σ ^ 2 + s ^ 2) ^ (-p) ≤ (s ^ 2) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg σ]) (by linarith)
  have h2 : Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))) ≤ Real.exp (|r| / (2 * s ^ 2)) := by
    apply Real.exp_le_exp.2
    have a1 : -(r / (2 * (σ ^ 2 + s ^ 2))) ≤ |r| / (2 * (σ ^ 2 + s ^ 2)) := by
      rw [← neg_div]
      apply div_le_div_of_nonneg_right _ (by have := hw σ; positivity)
      linarith [neg_abs_le r]
    have a2 : |r| / (2 * (σ ^ 2 + s ^ 2)) ≤ |r| / (2 * s ^ 2) := by
      apply div_le_div_of_nonneg_left (abs_nonneg r) (by positivity)
      nlinarith [sq_nonneg σ]
    linarith
  rw [Real.norm_of_nonneg (by have := hw σ; positivity)]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

lemma ii_aux_pos (G : Measure ℝ) [IsProbabilityMeasure G] (s r p : ℝ) (hs : 0 < s) (hp : 0 ≤ p) :
    0 < auxMoment G s r p := by
  unfold auxMoment
  rw [integral_pos_iff_support_of_nonneg (fun σ => by have : 0 < σ ^ 2 + s ^ 2 := by positivity
                                                      positivity) (ii_aux_int G s r p hs hp)]
  have : Function.support (fun σ : ℝ => (σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) = Set.univ := by
    ext σ
    have : 0 < σ ^ 2 + s ^ 2 := by positivity
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    positivity
  rw [this]; simp

lemma ii_lik (μ s σ z : ℝ) (hs : 0 < s) :
    likelihood μ s σ z = (Real.sqrt (2 * Real.pi))⁻¹ *
      ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-((z - μ) ^ 2 / (2 * (σ ^ 2 + s ^ 2))))) := by
  have hw : 0 < σ ^ 2 + s ^ 2 := by positivity
  unfold likelihood psi
  rw [Real.sq_sqrt (by positivity)]
  have e1 : (σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (σ ^ 2 + s ^ 2))⁻¹ := by
    rw [Real.rpow_neg hw.le, Real.sqrt_eq_rpow]
  rw [e1, Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num)]
  have : 0 < Real.sqrt (σ ^ 2 + s ^ 2) := Real.sqrt_pos.2 hw
  have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  field_simp

lemma ii_lik_int (G : Measure ℝ) [IsFiniteMeasure G] (μ s z : ℝ) (hs : 0 < s) :
    Integrable (fun σ => likelihood μ s σ z) G := by
  have := (ii_aux_int G s ((z - μ) ^ 2) (1 / 2) hs (by norm_num)).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  refine this.congr (Filter.Eventually.of_forall (fun σ => ?_))
  simp only
  rw [ii_lik μ s σ z hs]

/-- `∫ (σ²+s²)^(-q) · likelihood = c · auxMoment (q + 1/2)`. -/
lemma ii_num (G : Measure ℝ) (μ s z q : ℝ) (hs : 0 < s) :
    ∫ σ, (σ ^ 2 + s ^ 2) ^ (-q) * likelihood μ s σ z ∂G =
      (Real.sqrt (2 * Real.pi))⁻¹ * auxMoment G s ((z - μ) ^ 2) (q + 1 / 2) := by
  unfold auxMoment
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun σ => ?_))
  simp only
  have hw : 0 < σ ^ 2 + s ^ 2 := by positivity
  rw [ii_lik μ s σ z hs, neg_add, Real.rpow_add hw]
  ring

lemma ii_den (G : Measure ℝ) (μ s z : ℝ) (hs : 0 < s) :
    ∫ σ, likelihood μ s σ z ∂G =
      (Real.sqrt (2 * Real.pi))⁻¹ * auxMoment G s ((z - μ) ^ 2) (0 + 1 / 2) := by
  have := ii_num G μ s z 0 hs
  simpa using this

lemma ii_quad (G : Measure ℝ) [IsProbabilityMeasure G] (s r : ℝ) (hs : 0 < s) (x : ℝ) :
    ∫ σ, (x * (σ ^ 2 + s ^ 2) ^ (-(1 / 4 : ℝ)) + (σ ^ 2 + s ^ 2) ^ (-(5 / 4 : ℝ))) ^ 2 *
        Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))) ∂G =
      auxMoment G s r (1 / 2) * (x * x) + (2 * auxMoment G s r (3 / 2)) * x + auxMoment G s r (5 / 2) := by
  have i1 := ii_aux_int G s r (1 / 2) hs (by norm_num)
  have i2 := ii_aux_int G s r (3 / 2) hs (by norm_num)
  have i3 := ii_aux_int G s r (5 / 2) hs (by norm_num)
  have hpt : ∀ σ : ℝ, (x * (σ ^ 2 + s ^ 2) ^ (-(1 / 4 : ℝ)) + (σ ^ 2 + s ^ 2) ^ (-(5 / 4 : ℝ))) ^ 2 *
        Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))) =
      (x * x) * ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) +
      (2 * x) * ((σ ^ 2 + s ^ 2) ^ (-(3 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) +
      ((σ ^ 2 + s ^ 2) ^ (-(5 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) := by
    intro σ
    have hw : 0 < σ ^ 2 + s ^ 2 := by positivity
    have e1 : (σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) = (σ ^ 2 + s ^ 2) ^ (-(1 / 4 : ℝ)) * (σ ^ 2 + s ^ 2) ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_add hw]; norm_num
    have e2 : (σ ^ 2 + s ^ 2) ^ (-(3 / 2 : ℝ)) = (σ ^ 2 + s ^ 2) ^ (-(1 / 4 : ℝ)) * (σ ^ 2 + s ^ 2) ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add hw]; norm_num
    have e3 : (σ ^ 2 + s ^ 2) ^ (-(5 / 2 : ℝ)) = (σ ^ 2 + s ^ 2) ^ (-(5 / 4 : ℝ)) * (σ ^ 2 + s ^ 2) ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add hw]; norm_num
    rw [e1, e2, e3]; ring
  simp_rw [hpt]
  unfold auxMoment
  have I1 := i1.const_mul (x * x)
  have I2 := i2.const_mul (2 * x)
  have h1' := integral_add (I1.add I2) i3
  have h2' := integral_add I1 I2
  simp only [Pi.add_apply] at h1' h2'
  rw [h1', h2', integral_const_mul, integral_const_mul]
  ring

lemma ii_cs_weak (G : Measure ℝ) [IsProbabilityMeasure G] (s r : ℝ) (hs : 0 < s) :
    auxMoment G s r (3 / 2) ^ 2 ≤ auxMoment G s r (5 / 2) * auxMoment G s r (1 / 2) := by
  have h : ∀ x : ℝ, 0 ≤ auxMoment G s r (1 / 2) * (x * x) + (2 * auxMoment G s r (3 / 2)) * x + auxMoment G s r (5 / 2) := by
    intro x
    rw [← ii_quad G s r hs x]
    apply integral_nonneg
    intro σ
    have : 0 < σ ^ 2 + s ^ 2 := by positivity
    positivity
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith

lemma ii_auxM_deriv (G : Measure ℝ) [IsProbabilityMeasure G] (s p : ℝ) (hs : 0 < s) (hp : 0 ≤ p) (r : ℝ) :
    HasDerivAt (fun r' => auxMoment G s r' p) (-(1 / 2) * auxMoment G s r (p + 1)) r := by
  have hw : ∀ σ : ℝ, 0 < σ ^ 2 + s ^ 2 := fun σ => by positivity
  have hF : ∀ r' : ℝ, Integrable (fun σ : ℝ => (σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r' / (2 * (σ ^ 2 + s ^ 2))))) G :=
    fun r' => ii_aux_int G s r' p hs hp
  have hF' : ∀ r' : ℝ, Integrable (fun σ : ℝ => (σ ^ 2 + s ^ 2) ^ (-(p + 1)) * Real.exp (-(r' / (2 * (σ ^ 2 + s ^ 2))))) G :=
    fun r' => ii_aux_int G s r' (p + 1) hs (by linarith)
  have hder : ∀ σ : ℝ, ∀ x : ℝ, HasDerivAt (fun r' : ℝ => (σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r' / (2 * (σ ^ 2 + s ^ 2)))))
      ((σ ^ 2 + s ^ 2) ^ (-p) * (Real.exp (-(x / (2 * (σ ^ 2 + s ^ 2)))) * (-(1 / (2 * (σ ^ 2 + s ^ 2)))))) x := by
    intro σ x
    have h1 : HasDerivAt (fun r' : ℝ => -(r' / (2 * (σ ^ 2 + s ^ 2)))) (-(1 / (2 * (σ ^ 2 + s ^ 2)))) x :=
      ((hasDerivAt_id x).div_const _).neg
    exact (h1.exp).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := G) (x₀ := r) (s := Metric.ball r 1)
    (F := fun r' σ => (σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r' / (2 * (σ ^ 2 + s ^ 2)))))
    (F' := fun x σ => (σ ^ 2 + s ^ 2) ^ (-p) * (Real.exp (-(x / (2 * (σ ^ 2 + s ^ 2)))) * (-(1 / (2 * (σ ^ 2 + s ^ 2))))))
    (Metric.ball_mem_nhds r one_pos)
    (Filter.Eventually.of_forall (fun r' => (hF r').aestronglyMeasurable)) (hF r)
    (by
      have := ((hF' r).const_mul (-(1 / 2 : ℝ))).aestronglyMeasurable
      refine this.congr (Filter.Eventually.of_forall (fun σ => ?_))
      have hw' := hw σ
      simp only
      rw [neg_add, Real.rpow_add hw', Real.rpow_neg_one]
      field_simp)
    (bound := fun _ => (s ^ 2) ^ (-p) * (Real.exp ((|r| + 1) / (2 * s ^ 2)) * (1 / (2 * s ^ 2))))
    (Filter.Eventually.of_forall (fun σ x hx => by
      have hw' := hw σ
      have hx' : |x| ≤ |r| + 1 := by
        have := Metric.mem_ball.1 hx
        rw [Real.dist_eq] at this
        have := abs_sub_abs_le_abs_sub x r
        linarith [abs_lt.1 (show |x - r| < 1 from by assumption)]
      have h1 : (σ ^ 2 + s ^ 2) ^ (-p) ≤ (s ^ 2) ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg σ]) (by linarith)
      have h2 : Real.exp (-(x / (2 * (σ ^ 2 + s ^ 2)))) ≤ Real.exp ((|r| + 1) / (2 * s ^ 2)) := by
        apply Real.exp_le_exp.2
        have a1 : -(x / (2 * (σ ^ 2 + s ^ 2))) ≤ |x| / (2 * (σ ^ 2 + s ^ 2)) := by
          rw [← neg_div]
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith [neg_abs_le x]
        have a2 : |x| / (2 * (σ ^ 2 + s ^ 2)) ≤ (|r| + 1) / (2 * s ^ 2) := by
          calc |x| / (2 * (σ ^ 2 + s ^ 2)) ≤ |x| / (2 * s ^ 2) :=
                div_le_div_of_nonneg_left (abs_nonneg x) (by positivity) (by nlinarith [sq_nonneg σ])
            _ ≤ (|r| + 1) / (2 * s ^ 2) := div_le_div_of_nonneg_right hx' (by positivity)
        linarith
      have h3 : (1 / (2 * (σ ^ 2 + s ^ 2))) ≤ 1 / (2 * s ^ 2) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg σ])
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (σ ^ 2 + s ^ 2) ^ (-p)),
        abs_mul, abs_of_nonneg (Real.exp_pos _).le, abs_neg, abs_of_nonneg (by positivity)]
      exact mul_le_mul h1 (mul_le_mul h2 h3 (by positivity) (by positivity)) (by positivity) (by positivity)))
    (integrable_const _)
    (Filter.Eventually.of_forall (fun σ x _ => hder σ x))
  have e : ∫ σ, (σ ^ 2 + s ^ 2) ^ (-p) * (Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))) * (-(1 / (2 * (σ ^ 2 + s ^ 2))))) ∂G =
      -(1 / 2) * auxMoment G s r (p + 1) := by
    unfold auxMoment
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun σ => ?_))
    have hw' := hw σ
    simp only
    rw [neg_add, Real.rpow_add hw', Real.rpow_neg_one]
    field_simp
  rw [e] at key
  exact key.2

lemma ii_eq_dirac (G : Measure ℝ) [IsProbabilityMeasure G] (a0 : ℝ) (h : ∀ᵐ σ ∂G, σ = a0) :
    G = Measure.dirac a0 := by
  have h' : G {σ : ℝ | ¬ σ = a0} = 0 := ae_iff.1 h
  refine Measure.ext (fun A hA => ?_)
  rw [Measure.dirac_apply' _ hA]
  by_cases ha : a0 ∈ A
  · rw [Set.indicator_of_mem ha]
    simp only [Pi.one_apply]
    have : G Aᶜ = 0 := by
      apply measure_mono_null _ h'
      intro σ hσ hσ'
      exact hσ (hσ' ▸ ha)
    exact (prob_compl_eq_zero_iff hA).1 this
  · rw [Set.indicator_of_notMem ha]
    apply measure_mono_null _ h'
    intro σ hσ hσ'
    exact ha (hσ' ▸ hσ)

lemma ii_cs_strict (G : Measure ℝ) (hG : AccuracyLaw G) (s r : ℝ) (hs : 0 < s)
    (hne : ∀ σ : ℝ, G ≠ Measure.dirac σ) :
    auxMoment G s r (3 / 2) ^ 2 < auxMoment G s r (5 / 2) * auxMoment G s r (1 / 2) := by
  haveI := hG.isProb
  have hweak := ii_cs_weak G s r hs
  by_contra hcon
  have heq : auxMoment G s r (3 / 2) ^ 2 = auxMoment G s r (5 / 2) * auxMoment G s r (1 / 2) :=
    le_antisymm hweak (not_lt.1 hcon)
  have hM1 : 0 < auxMoment G s r (1 / 2) := ii_aux_pos G s r (1 / 2) hs (by norm_num)
  set x0 : ℝ := -(auxMoment G s r (3 / 2) / auxMoment G s r (1 / 2)) with hx0
  have hq := ii_quad G s r hs x0
  have hval : auxMoment G s r (1 / 2) * (x0 * x0) + (2 * auxMoment G s r (3 / 2)) * x0 + auxMoment G s r (5 / 2) = 0 := by
    rw [hx0]
    field_simp
    nlinarith [heq]
  rw [hval] at hq
  -- integrability of the nonneg integrand
  have i1 := ii_aux_int G s r (1 / 2) hs (by norm_num)
  have i2 := ii_aux_int G s r (3 / 2) hs (by norm_num)
  have i3 := ii_aux_int G s r (5 / 2) hs (by norm_num)
  set f : ℝ → ℝ := fun σ => (x0 * (σ ^ 2 + s ^ 2) ^ (-(1 / 4 : ℝ)) + (σ ^ 2 + s ^ 2) ^ (-(5 / 4 : ℝ))) ^ 2 *
        Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))) with hf
  have hpt : ∀ σ : ℝ, f σ =
      (x0 * x0) * ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) +
      (2 * x0) * ((σ ^ 2 + s ^ 2) ^ (-(3 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) +
      ((σ ^ 2 + s ^ 2) ^ (-(5 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) := by
    intro σ
    have hw : 0 < σ ^ 2 + s ^ 2 := by positivity
    have e1 : (σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) = (σ ^ 2 + s ^ 2) ^ (-(1 / 4 : ℝ)) * (σ ^ 2 + s ^ 2) ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_add hw]; norm_num
    have e2 : (σ ^ 2 + s ^ 2) ^ (-(3 / 2 : ℝ)) = (σ ^ 2 + s ^ 2) ^ (-(1 / 4 : ℝ)) * (σ ^ 2 + s ^ 2) ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add hw]; norm_num
    have e3 : (σ ^ 2 + s ^ 2) ^ (-(5 / 2 : ℝ)) = (σ ^ 2 + s ^ 2) ^ (-(5 / 4 : ℝ)) * (σ ^ 2 + s ^ 2) ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add hw]; norm_num
    simp only [hf]
    rw [e1, e2, e3]; ring
  have hfi : Integrable f G := by
    have := ((i1.const_mul (x0 * x0)).add (i2.const_mul (2 * x0))).add i3
    refine this.congr (Filter.Eventually.of_forall (fun σ => ?_))
    simp only [Pi.add_apply]
    rw [hpt σ]
  have hf0 : 0 ≤ f := fun σ => by
    have : 0 < σ ^ 2 + s ^ 2 := by positivity
    simp only [hf]; positivity
  have hzero : f =ᵐ[G] 0 := by
    rw [← integral_eq_zero_iff_of_nonneg hf0 hfi]
    exact hq
  -- from f = 0 a.e. to a point mass
  obtain ⟨lo, hi, hlo, hlohi, hbd⟩ := hG.bdd
  have hmem : ∀ᵐ σ ∂G, σ ∈ Set.Icc lo hi := ae_iff.2 hbd
  have hM3 : 0 < auxMoment G s r (3 / 2) := ii_aux_pos G s r (3 / 2) hs (by norm_num)
  have hxneg : x0 < 0 := by
    rw [hx0]; have := div_pos hM3 hM1; linarith
  have hae : ∀ᵐ σ ∂G, σ = Real.sqrt ((-x0)⁻¹ - s ^ 2) := by
    filter_upwards [hzero, hmem] with σ h1 h2
    have hw : 0 < σ ^ 2 + s ^ 2 := by positivity
    have h1' : f σ = 0 := h1
    simp only [hf] at h1'
    have hE : Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))) ≠ 0 := (Real.exp_pos _).ne'
    have hq0 : x0 * (σ ^ 2 + s ^ 2) ^ (-(1 / 4 : ℝ)) + (σ ^ 2 + s ^ 2) ^ (-(5 / 4 : ℝ)) = 0 := by
      rcases mul_eq_zero.1 h1' with h | h
      · exact pow_eq_zero_iff (by norm_num) |>.1 h
      · exact absurd h hE
    have hb : (σ ^ 2 + s ^ 2) ^ (-(5 / 4 : ℝ)) = (σ ^ 2 + s ^ 2) ^ (-(1 / 4 : ℝ)) * (σ ^ 2 + s ^ 2)⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hw]; norm_num
    have ha : 0 < (σ ^ 2 + s ^ 2) ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hw _
    rw [hb] at hq0
    have hq1 : x0 + (σ ^ 2 + s ^ 2)⁻¹ = 0 := by
      have : (σ ^ 2 + s ^ 2) ^ (-(1 / 4 : ℝ)) * (x0 + (σ ^ 2 + s ^ 2)⁻¹) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h ha.ne'
      · exact h
    have hw2 : σ ^ 2 + s ^ 2 = (-x0)⁻¹ := by
      have : (σ ^ 2 + s ^ 2)⁻¹ = -x0 := by linarith
      rw [← this, inv_inv]
    have hσ2 : σ ^ 2 = (-x0)⁻¹ - s ^ 2 := by linarith
    rw [← hσ2, Real.sqrt_sq (by linarith [h2.1])]
  exact hne _ (ii_eq_dirac G _ hae)

lemma ii_Phi_deriv (G : Measure ℝ) [IsProbabilityMeasure G] (s : ℝ) (hs : 0 < s) (r : ℝ) :
    HasDerivAt (fun r' => auxMoment G s r' (3 / 2) / auxMoment G s r' (1 / 2))
      ((1 / 2) * (-(auxMoment G s r (5 / 2) * auxMoment G s r (1 / 2)) + auxMoment G s r (3 / 2) ^ 2) /
        auxMoment G s r (1 / 2) ^ 2) r := by
  have hM1 : 0 < auxMoment G s r (1 / 2) := ii_aux_pos G s r (1 / 2) hs (by norm_num)
  have h3 := ii_auxM_deriv G s (3 / 2) hs (by norm_num) r
  have h1 := ii_auxM_deriv G s (1 / 2) hs (by norm_num) r
  have e1 : (3 / 2 : ℝ) + 1 = 5 / 2 := by norm_num
  have e2 : (1 / 2 : ℝ) + 1 = 3 / 2 := by norm_num
  rw [e1] at h3
  rw [e2] at h1
  refine (h3.div h1 hM1.ne').congr_deriv ?_
  field_simp
  ring

lemma ii_post_eq (G : Measure ℝ) [IsProbabilityMeasure G] (μ s z : ℝ) (hs : 0 < s) :
    postExp G μ s z (fun σ => (s ^ 2 + σ ^ 2)⁻¹) =
      auxMoment G s ((z - μ) ^ 2) (3 / 2) / auxMoment G s ((z - μ) ^ 2) (1 / 2) := by
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hnum : ∫ σ, (s ^ 2 + σ ^ 2)⁻¹ * likelihood μ s σ z ∂G =
      (Real.sqrt (2 * Real.pi))⁻¹ * auxMoment G s ((z - μ) ^ 2) (3 / 2) := by
    have := ii_num G μ s z 1 hs
    have e : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
    rw [e] at this
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun σ => ?_))
    simp only
    rw [Real.rpow_neg_one, add_comm]
  have hden := ii_den G μ s z hs
  rw [zero_add] at hden
  unfold postExp
  rw [hnum, hden, mul_div_mul_left _ _ hc]

lemma ii_nextSd_eq (s σ : ℝ) (hs : 0 < s) :
    nextSd s σ = Real.sqrt (s ^ 2 - s ^ 4 * (σ ^ 2 + s ^ 2)⁻¹) := by
  unfold nextSd
  congr 1
  have : 0 < σ ^ 2 + s ^ 2 := by positivity
  rw [add_comm (s ^ 2) (σ ^ 2)]
  field_simp
  ring

lemma ii_nextSd_cont (s : ℝ) (hs : 0 < s) : Continuous (fun σ : ℝ => nextSd s σ) := by
  have : (fun σ : ℝ => nextSd s σ) = fun σ => Real.sqrt (s ^ 2 - s ^ 4 * (σ ^ 2 + s ^ 2)⁻¹) := by
    funext σ; exact ii_nextSd_eq s σ hs
  rw [this]
  refine Continuous.sqrt (continuous_const.sub (continuous_const.mul (Continuous.inv₀ (by fun_prop) (fun σ => ?_))))
  have : 0 < σ ^ 2 + s ^ 2 := by positivity
  exact this.ne'

lemma ii_nextSd_bd (s σ : ℝ) (hs : 0 < s) : ‖nextSd s σ‖ ≤ s := by
  unfold nextSd
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hw : 0 < s ^ 2 + σ ^ 2 := by positivity
  calc Real.sqrt (s ^ 2 * σ ^ 2 / (s ^ 2 + σ ^ 2)) ≤ Real.sqrt (s ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [div_le_iff₀ hw]
        nlinarith [sq_nonneg σ, sq_nonneg s, mul_nonneg (sq_nonneg s) (sq_nonneg s)]
    _ = s := Real.sqrt_sq hs.le

lemma ii_h_int (G : Measure ℝ) [IsFiniteMeasure G] (h : ℝ → ℝ) (hc : Continuous h) (B : ℝ)
    (hB : ∀ σ, ‖h σ‖ ≤ B) (s r p : ℝ) (hs : 0 < s) (hp : 0 ≤ p) :
    Integrable (fun σ : ℝ => h σ * ((σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))))) G :=
  (ii_aux_int G s r p hs hp).bdd_mul hc.aestronglyMeasurable (Filter.Eventually.of_forall hB)

lemma ii_hM_deriv (G : Measure ℝ) [IsProbabilityMeasure G] (h : ℝ → ℝ) (hc : Continuous h) (B : ℝ)
    (hB : ∀ σ, ‖h σ‖ ≤ B) (s p : ℝ) (hs : 0 < s) (hp : 0 ≤ p) (r : ℝ) :
    HasDerivAt (fun r' => ∫ σ, h σ * ((σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r' / (2 * (σ ^ 2 + s ^ 2))))) ∂G)
      (-(1 / 2) * ∫ σ, h σ * ((σ ^ 2 + s ^ 2) ^ (-(p + 1)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) ∂G) r := by
  have hw : ∀ σ : ℝ, 0 < σ ^ 2 + s ^ 2 := fun σ => by positivity
  have hF := fun r' : ℝ => ii_h_int G h hc B hB s r' p hs hp
  have hF' := fun r' : ℝ => ii_h_int G h hc B hB s r' (p + 1) hs (by linarith)
  have hder : ∀ σ : ℝ, ∀ x : ℝ, HasDerivAt (fun r' : ℝ => h σ * ((σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r' / (2 * (σ ^ 2 + s ^ 2))))))
      (h σ * ((σ ^ 2 + s ^ 2) ^ (-p) * (Real.exp (-(x / (2 * (σ ^ 2 + s ^ 2)))) * (-(1 / (2 * (σ ^ 2 + s ^ 2))))))) x := by
    intro σ x
    have h1 : HasDerivAt (fun r' : ℝ => -(r' / (2 * (σ ^ 2 + s ^ 2)))) (-(1 / (2 * (σ ^ 2 + s ^ 2)))) x :=
      ((hasDerivAt_id x).div_const _).neg
    exact ((h1.exp).const_mul _).const_mul _
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := G) (x₀ := r) (s := Metric.ball r 1)
    (F := fun r' σ => h σ * ((σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r' / (2 * (σ ^ 2 + s ^ 2))))))
    (F' := fun x σ => h σ * ((σ ^ 2 + s ^ 2) ^ (-p) * (Real.exp (-(x / (2 * (σ ^ 2 + s ^ 2)))) * (-(1 / (2 * (σ ^ 2 + s ^ 2)))))))
    (Metric.ball_mem_nhds r one_pos)
    (Filter.Eventually.of_forall (fun r' => (hF r').aestronglyMeasurable)) (hF r)
    (by
      have := ((hF' r).const_mul (-(1 / 2 : ℝ))).aestronglyMeasurable
      refine this.congr (Filter.Eventually.of_forall (fun σ => ?_))
      have hw' := hw σ
      simp only
      rw [neg_add, Real.rpow_add hw', Real.rpow_neg_one]
      field_simp)
    (bound := fun _ => B * ((s ^ 2) ^ (-p) * (Real.exp ((|r| + 1) / (2 * s ^ 2)) * (1 / (2 * s ^ 2)))))
    (Filter.Eventually.of_forall (fun σ x hx => by
      have hw' := hw σ
      have hx' : |x| ≤ |r| + 1 := by
        have h1 := Metric.mem_ball.1 hx
        rw [Real.dist_eq] at h1
        have := abs_sub_abs_le_abs_sub x r
        linarith [abs_lt.1 h1]
      have h1 : (σ ^ 2 + s ^ 2) ^ (-p) ≤ (s ^ 2) ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg σ]) (by linarith)
      have h2 : Real.exp (-(x / (2 * (σ ^ 2 + s ^ 2)))) ≤ Real.exp ((|r| + 1) / (2 * s ^ 2)) := by
        apply Real.exp_le_exp.2
        have a1 : -(x / (2 * (σ ^ 2 + s ^ 2))) ≤ |x| / (2 * (σ ^ 2 + s ^ 2)) := by
          rw [← neg_div]
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith [neg_abs_le x]
        have a2 : |x| / (2 * (σ ^ 2 + s ^ 2)) ≤ (|r| + 1) / (2 * s ^ 2) := by
          calc |x| / (2 * (σ ^ 2 + s ^ 2)) ≤ |x| / (2 * s ^ 2) :=
                div_le_div_of_nonneg_left (abs_nonneg x) (by positivity) (by nlinarith [sq_nonneg σ])
            _ ≤ (|r| + 1) / (2 * s ^ 2) := div_le_div_of_nonneg_right hx' (by positivity)
        linarith
      have h3 : (1 / (2 * (σ ^ 2 + s ^ 2))) ≤ 1 / (2 * s ^ 2) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg σ])
      have hA : 0 ≤ (σ ^ 2 + s ^ 2) ^ (-p) := by positivity
      have hE : 0 ≤ Real.exp (-(x / (2 * (σ ^ 2 + s ^ 2)))) := (Real.exp_pos _).le
      have hF : 0 ≤ 1 / (2 * (σ ^ 2 + s ^ 2)) := by positivity
      rw [norm_mul, norm_mul, norm_mul, norm_neg, Real.norm_of_nonneg hA, Real.norm_of_nonneg hE,
        Real.norm_of_nonneg hF]
      exact mul_le_mul (hB σ) (mul_le_mul h1 (mul_le_mul h2 h3 hF (by positivity)) (mul_nonneg hE hF)
        (by positivity)) (by positivity) hB0))
    (integrable_const _)
    (Filter.Eventually.of_forall (fun σ x _ => hder σ x))
  have e : ∫ σ, h σ * ((σ ^ 2 + s ^ 2) ^ (-p) * (Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))) * (-(1 / (2 * (σ ^ 2 + s ^ 2)))))) ∂G =
      -(1 / 2) * ∫ σ, h σ * ((σ ^ 2 + s ^ 2) ^ (-(p + 1)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) ∂G := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun σ => ?_))
    have hw' := hw σ
    simp only
    rw [neg_add, Real.rpow_add hw', Real.rpow_neg_one]
    field_simp
  rw [e] at key
  exact key.2

lemma ii_dirac_of_w (G : Measure ℝ) (hG : AccuracyLaw G) (s c : ℝ)
    (h : ∀ᵐ σ ∂G, σ ^ 2 + s ^ 2 = c) : ∃ a0 : ℝ, G = Measure.dirac a0 := by
  haveI := hG.isProb
  obtain ⟨lo, hi, hlo, hlohi, hbd⟩ := hG.bdd
  have hmem : ∀ᵐ σ ∂G, σ ∈ Set.Icc lo hi := ae_iff.2 hbd
  refine ⟨Real.sqrt (c - s ^ 2), ii_eq_dirac G _ ?_⟩
  filter_upwards [h, hmem] with σ h1 h2
  have : σ ^ 2 = c - s ^ 2 := by linarith
  rw [← this, Real.sqrt_sq (by linarith [h2.1])]

lemma ii_key (G : Measure ℝ) (hG : AccuracyLaw G) (s r : ℝ) (hs : 0 < s)
    (hne : ∀ σ : ℝ, G ≠ Measure.dirac σ) :
    (∫ σ, nextSd s σ * ((σ ^ 2 + s ^ 2) ^ (-(3 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) ∂G) *
        auxMoment G s r (1 / 2) <
      (∫ σ, nextSd s σ * ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) ∂G) *
        auxMoment G s r (3 / 2) := by
  haveI := hG.isProb
  have hcont := ii_nextSd_cont s hs
  have hbd := fun σ => ii_nextSd_bd s σ hs
  have hD : 0 < auxMoment G s r (1 / 2) := ii_aux_pos G s r (1 / 2) hs (by norm_num)
  have hI1 := ii_aux_int G s r (1 / 2) hs (by norm_num)
  have hI3 := ii_aux_int G s r (3 / 2) hs (by norm_num)
  have hIN := ii_h_int G _ hcont s hbd s r (1 / 2) hs (by norm_num)
  have hIK := ii_h_int G _ hcont s hbd s r (3 / 2) hs (by norm_num)
  -- notation
  set φ : ℝ → ℝ := fun x => Real.sqrt (s ^ 2 - s ^ 4 * x) with hφ
  set a : ℝ := auxMoment G s r (3 / 2) / auxMoment G s r (1 / 2) with ha
  set N := ∫ σ, nextSd s σ * ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) ∂G with hN
  set K := ∫ σ, nextSd s σ * ((σ ^ 2 + s ^ 2) ^ (-(3 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) ∂G with hK
  have hw : ∀ σ : ℝ, 0 < σ ^ 2 + s ^ 2 := fun σ => by positivity
  have hv : ∀ σ : ℝ, 0 < (σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))) :=
    fun σ => by have := hw σ; positivity
  have huv : ∀ σ : ℝ, (σ ^ 2 + s ^ 2) ^ (-(3 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))) =
      (σ ^ 2 + s ^ 2)⁻¹ * ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) := by
    intro σ
    have h := hw σ
    have : (σ ^ 2 + s ^ 2) ^ (-(3 / 2 : ℝ)) = (σ ^ 2 + s ^ 2)⁻¹ * (σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add h]; norm_num
    rw [this]; ring
  have hhφ : ∀ σ : ℝ, nextSd s σ = φ ((σ ^ 2 + s ^ 2)⁻¹) := fun σ => ii_nextSd_eq s σ hs
  have hφanti : ∀ x y : ℝ, x ≤ y → φ y ≤ φ x := by
    intro x y hxy
    apply Real.sqrt_le_sqrt
    nlinarith [pow_nonneg hs.le 4]
  have hφarg : ∀ x : ℝ, x ≤ (s ^ 2)⁻¹ → 0 ≤ s ^ 2 - s ^ 4 * x := by
    intro x hx
    have h1 := mul_le_mul_of_nonneg_left hx (pow_nonneg hs.le 4)
    have e : s ^ 4 * (s ^ 2)⁻¹ = s ^ 2 := by
      rw [show s ^ 4 = s ^ 2 * s ^ 2 by ring, mul_assoc, mul_inv_cancel₀ (pow_pos hs 2).ne', mul_one]
    linarith
  have hu_le : ∀ σ : ℝ, (σ ^ 2 + s ^ 2)⁻¹ ≤ (s ^ 2)⁻¹ := fun σ =>
    inv_anti₀ (by positivity) (by nlinarith [sq_nonneg σ])
  have ha_le : a ≤ (s ^ 2)⁻¹ := by
    rw [ha, div_le_iff₀ hD]
    have : ∫ σ, (σ ^ 2 + s ^ 2) ^ (-(3 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))) ∂G ≤
        ∫ σ, (s ^ 2)⁻¹ * ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) ∂G := by
      apply integral_mono hI3 (hI1.const_mul _)
      intro σ
      simp only
      rw [huv σ]
      exact mul_le_mul_of_nonneg_right (hu_le σ) (hv σ).le
    rw [integral_const_mul] at this
    exact this
  -- the nonneg integrand
  set g : ℝ → ℝ := fun σ => (φ a - nextSd s σ) * ((σ ^ 2 + s ^ 2)⁻¹ - a) *
      ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) with hg
  have hg0 : ∀ σ, 0 ≤ g σ := by
    intro σ
    simp only [hg]
    apply mul_nonneg _ (hv σ).le
    rw [hhφ σ]
    rcases le_total a ((σ ^ 2 + s ^ 2)⁻¹) with h | h
    · exact mul_nonneg (sub_nonneg.2 (hφanti _ _ h)) (sub_nonneg.2 h)
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hφanti _ _ h)) (sub_nonpos.2 h)
  have hgexp : ∀ σ, g σ =
      φ a * ((σ ^ 2 + s ^ 2) ^ (-(3 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) -
      (φ a * a) * ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) -
      nextSd s σ * ((σ ^ 2 + s ^ 2) ^ (-(3 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) +
      a * (nextSd s σ * ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))))) := by
    intro σ
    simp only [hg]
    rw [huv σ]; ring
  have hgi : Integrable g G := by
    have := ((((hI3.const_mul (φ a)).sub (hI1.const_mul (φ a * a))).sub hIK).add (hIN.const_mul a))
    refine this.congr (Filter.Eventually.of_forall (fun σ => ?_))
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hgexp σ]
  have hgint : ∫ σ, g σ ∂G = a * N - K := by
    have e1 : ∫ σ, g σ ∂G = φ a * auxMoment G s r (3 / 2) - (φ a * a) * auxMoment G s r (1 / 2) - K + a * N := by
      have := integral_congr_ae (μ := G) (Filter.Eventually.of_forall hgexp)
      rw [this]
      have s1 := integral_sub (hI3.const_mul (φ a)) (hI1.const_mul (φ a * a))
      have s2 := integral_sub ((hI3.const_mul (φ a)).sub (hI1.const_mul (φ a * a))) hIK
      have s3 := integral_add (((hI3.const_mul (φ a)).sub (hI1.const_mul (φ a * a))).sub hIK) (hIN.const_mul a)
      simp only [Pi.add_apply, Pi.sub_apply] at s1 s2 s3
      rw [s3, s2, s1, integral_const_mul, integral_const_mul, integral_const_mul]
      rfl
    rw [e1]
    have : a * auxMoment G s r (1 / 2) = auxMoment G s r (3 / 2) := by
      rw [ha]; field_simp
    have h2 : (φ a * a) * auxMoment G s r (1 / 2) = φ a * auxMoment G s r (3 / 2) := by
      rw [mul_assoc, this]
    rw [h2]; ring
  have hg0' : 0 ≤ g := hg0
  have hpos : 0 < ∫ σ, g σ ∂G := by
    rcases (integral_nonneg hg0').lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : g =ᵐ[G] 0 := (integral_eq_zero_iff_of_nonneg hg0' hgi).1 h.symm
      have hua : ∀ᵐ σ ∂G, σ ^ 2 + s ^ 2 = a⁻¹ := by
        filter_upwards [hz] with σ hσ
        have hσ' : g σ = 0 := hσ
        simp only [hg] at hσ'
        have hvσ := hv σ
        have hp : (φ a - nextSd s σ) * ((σ ^ 2 + s ^ 2)⁻¹ - a) = 0 := by
          rcases mul_eq_zero.1 hσ' with h | h
          · exact h
          · exact absurd h hvσ.ne'
        have hu : (σ ^ 2 + s ^ 2)⁻¹ = a := by
          rcases mul_eq_zero.1 hp with h | h
          · have h' : φ ((σ ^ 2 + s ^ 2)⁻¹) = φ a := by rw [← hhφ σ]; linarith
            simp only [hφ] at h'
            have := (Real.sqrt_inj (hφarg _ (hu_le σ)) (hφarg _ ha_le)).1 h'
            have h4 : 0 < s ^ 4 := pow_pos hs 4
            nlinarith
          · linarith
        rw [← hu, inv_inv]
      obtain ⟨a0, ha0⟩ := ii_dirac_of_w G hG s _ hua
      exact hne a0 ha0
  rw [hgint] at hpos
  have hDa : a * auxMoment G s r (1 / 2) = auxMoment G s r (3 / 2) := by
    rw [ha]; field_simp
  have e : auxMoment G s r (1 / 2) * (a * N - K) = (a * auxMoment G s r (1 / 2)) * N - K * auxMoment G s r (1 / 2) := by ring
  rw [hDa] at e
  have := mul_pos hD hpos
  linarith

lemma ii_post_h (G : Measure ℝ) [IsProbabilityMeasure G] (μ s z : ℝ) (hs : 0 < s) (h : ℝ → ℝ) :
    postExp G μ s z h =
      (∫ σ, h σ * ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-((z - μ) ^ 2 / (2 * (σ ^ 2 + s ^ 2))))) ∂G) /
        auxMoment G s ((z - μ) ^ 2) (1 / 2) := by
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hnum : ∫ σ, h σ * likelihood μ s σ z ∂G =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ σ, h σ * ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-((z - μ) ^ 2 / (2 * (σ ^ 2 + s ^ 2))))) ∂G := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun σ => ?_))
    simp only
    rw [ii_lik μ s σ z hs]; ring
  have hden := ii_den G μ s z hs
  rw [zero_add] at hden
  unfold postExp
  rw [hnum, hden, mul_div_mul_left _ _ hc]

lemma ii_Psi_strictMono (G : Measure ℝ) (hG : AccuracyLaw G) (s : ℝ) (hs : 0 < s)
    (hne : ∀ σ : ℝ, G ≠ Measure.dirac σ) :
    StrictMono (fun r : ℝ => (∫ σ, nextSd s σ * ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) ∂G) / auxMoment G s r (1 / 2)) := by
  haveI := hG.isProb
  have hcont := ii_nextSd_cont s hs
  have hbd := fun σ => ii_nextSd_bd s σ hs
  have hd : ∀ r : ℝ, HasDerivAt (fun r : ℝ => (∫ σ, nextSd s σ * ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) ∂G) / auxMoment G s r (1 / 2))
      ((-(1 / 2) * (∫ σ, nextSd s σ * ((σ ^ 2 + s ^ 2) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) ∂G) * auxMoment G s r (1 / 2) -
        (∫ σ, nextSd s σ * ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) ∂G) * (-(1 / 2) * auxMoment G s r (3 / 2))) /
        auxMoment G s r (1 / 2) ^ 2) r := by
    intro r
    have hN := ii_hM_deriv G _ hcont s hbd s (1 / 2) hs (by norm_num) r
    have hD := ii_auxM_deriv G s (1 / 2) hs (by norm_num) r
    have e : (1 / 2 : ℝ) + 1 = 3 / 2 := by norm_num
    rw [e] at hN hD
    exact hN.div hD (ii_aux_pos G s r (1 / 2) hs (by norm_num)).ne'
  apply strictMono_of_deriv_pos
  intro r
  rw [(hd r).deriv]
  have key := ii_key G hG s r hs hne
  have hD := ii_aux_pos G s r (1 / 2) hs (by norm_num)
  apply div_pos _ (by positivity)
  nlinarith [key]

lemma ii_Phi_strictAnti (G : Measure ℝ) (hG : AccuracyLaw G) (s : ℝ) (hs : 0 < s)
    (hne : ∀ σ : ℝ, G ≠ Measure.dirac σ) :
    StrictAnti (fun r' => auxMoment G s r' (3 / 2) / auxMoment G s r' (1 / 2)) := by
  haveI := hG.isProb
  have hM1 : ∀ r : ℝ, 0 < auxMoment G s r (1 / 2) := fun r => ii_aux_pos G s r (1 / 2) hs (by norm_num)
  apply strictAnti_of_deriv_neg
  intro r
  rw [(ii_Phi_deriv G s hs r).deriv]
  have hcs := ii_cs_strict G hG s r hs hne
  apply div_neg_of_neg_of_pos
  · nlinarith
  · have := hM1 r; positivity

lemma ii_var_eq (G : Measure ℝ) (hG : AccuracyLaw G) (μ s : ℝ) (hs : 0 < s) (z : ℝ) :
    varScore G μ s z = s ^ 4 * postExp G μ s z (fun σ => (s ^ 2 + σ ^ 2)⁻¹) := by
  haveI := hG.isProb
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hD : ∫ σ, likelihood μ s σ z ∂G ≠ 0 := by
    rw [ii_den G μ s z hs]
    exact mul_ne_zero hc (ii_aux_pos G s _ _ hs (by norm_num)).ne'
  have hB : Integrable (fun σ => (s ^ 2 + σ ^ 2)⁻¹ * likelihood μ s σ z) G := by
    have := (ii_aux_int G s ((z - μ) ^ 2) (1 + 1 / 2) hs (by norm_num)).const_mul (Real.sqrt (2 * Real.pi))⁻¹
    refine this.congr (Filter.Eventually.of_forall (fun σ => ?_))
    simp only
    have hw : 0 < σ ^ 2 + s ^ 2 := by positivity
    rw [ii_lik μ s σ z hs, neg_add, Real.rpow_add hw, add_comm (s ^ 2) (σ ^ 2), Real.rpow_neg_one]
    ring
  have hL := ii_lik_int G μ s z hs
  have hpt : ∀ σ : ℝ, nextSd s σ ^ 2 * likelihood μ s σ z =
      s ^ 2 * likelihood μ s σ z - s ^ 4 * ((s ^ 2 + σ ^ 2)⁻¹ * likelihood μ s σ z) := by
    intro σ
    have hw : 0 < s ^ 2 + σ ^ 2 := by positivity
    unfold nextSd
    rw [Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hint : ∫ σ, nextSd s σ ^ 2 * likelihood μ s σ z ∂G =
      s ^ 2 * ∫ σ, likelihood μ s σ z ∂G - s ^ 4 * ∫ σ, (s ^ 2 + σ ^ 2)⁻¹ * likelihood μ s σ z ∂G := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub (hL.const_mul _) (hB.const_mul _),
      integral_const_mul, integral_const_mul]
  unfold varScore postExp
  rw [hint]
  field_simp
  ring

lemma ii_partb (σ : ℝ) (μ s : ℝ) (hs : 0 < s) (z : ℝ) :
    sdScore (Measure.dirac σ) μ s z = s - nextSd s σ ∧
      varScore (Measure.dirac σ) μ s z = s ^ 2 - nextSd s σ ^ 2 := by
  have hL : likelihood μ s σ z ≠ 0 := by
    have hw : 0 < Real.sqrt (2 * (σ ^ 2 + s ^ 2)) := Real.sqrt_pos.2 (by positivity)
    unfold likelihood psi
    have : 0 < 1 / (Real.sqrt Real.pi * Real.sqrt (2 * (σ ^ 2 + s ^ 2))) *
      Real.exp (-((z - μ) ^ 2 / Real.sqrt (2 * (σ ^ 2 + s ^ 2)) ^ 2)) := by positivity
    exact this.ne'
  have key : ∀ h : ℝ → ℝ, postExp (Measure.dirac σ) μ s z h = h σ := by
    intro h
    unfold postExp
    rw [integral_dirac, integral_dirac]
    field_simp
  constructor
  · unfold sdScore; rw [key]
  · unfold varScore; rw [key]

lemma ii_argmax {K : ℕ} (μ : ℝ) (F : ℝ → ℝ) (hF : StrictAnti F) (f : ℝ → ℝ)
    (hf : ∀ z, f z = F ((z - μ) ^ 2)) (Z : Fin K → ℝ) : argmaxMenu f Z = closestPosts μ Z := by
  ext i
  simp only [argmaxMenu, closestPosts, Finset.mem_filter, Finset.mem_univ, true_and, hf]
  exact forall_congr' (fun j => hF.le_iff_ge)

theorem solution (G : Measure ℝ) (hG : AccuracyLaw G) (μ s : ℝ) (hs : 0 < s)
    {K : ℕ} (Z : Fin K → ℝ) :
    ((∀ σ : ℝ, G ≠ Measure.dirac σ) →
        argmaxMenu (sdScore G μ s) Z = closestPosts μ Z ∧
          argmaxMenu (varScore G μ s) Z = closestPosts μ Z) ∧
      (∀ σ : ℝ, 0 < σ → G = Measure.dirac σ →
        argmaxMenu (sdScore G μ s) Z = Finset.univ ∧
          argmaxMenu (varScore G μ s) Z = Finset.univ) := by
  haveI := hG.isProb
  constructor
  · intro hne
    constructor
    · have hΨ := ii_Psi_strictMono G hG s hs hne
      refine ii_argmax μ (fun r => s - (∫ σ, nextSd s σ * ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) ∂G) / auxMoment G s r (1 / 2)) ?_ _ ?_ Z
      · intro a b hab
        have := hΨ hab
        simp only at this ⊢
        linarith
      · intro z
        unfold sdScore
        rw [ii_post_h G μ s z hs]
    · have hΦ := ii_Phi_strictAnti G hG s hs hne
      refine ii_argmax μ (fun r => s ^ 4 * (auxMoment G s r (3 / 2) / auxMoment G s r (1 / 2))) ?_ _ ?_ Z
      · intro a b hab
        exact mul_lt_mul_of_pos_left (hΦ hab) (by positivity)
      · intro z
        rw [ii_var_eq G hG μ s hs z, ii_post_eq G μ s z hs]
  · intro σ hσ hG'
    subst hG'
    have h1 := fun z => (ii_partb σ μ s hs z).1
    have h2 := fun z => (ii_partb σ μ s hs z).2
    constructor
    · refine Finset.eq_univ_iff_forall.2 (fun i => ?_)
      simp [argmaxMenu, h1]
    · refine Finset.eq_univ_iff_forall.2 (fun i => ?_)
      simp [argmaxMenu, h2]
