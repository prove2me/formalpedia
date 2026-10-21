-- Prove2me | solution 1 for InfoInundation.Screening.monotone_in_distance
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:47:36.285368+00:00
-- url     : https://prove2.me/submissions/ab43d2fb-b78f-43b9-9558-d49985a35796

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

theorem solution (G : Measure ℝ) (hG : AccuracyLaw G) (μ s : ℝ) (hs : 0 < s) :
    (∀ z z' : ℝ, (z - μ) ^ 2 ≤ (z' - μ) ^ 2 →
        postExp G μ s z' (fun σ => (s ^ 2 + σ ^ 2)⁻¹) ≤ postExp G μ s z (fun σ => (s ^ 2 + σ ^ 2)⁻¹)) ∧
      ((∀ σ : ℝ, G ≠ Measure.dirac σ) → ∀ z z' : ℝ, (z - μ) ^ 2 < (z' - μ) ^ 2 →
        postExp G μ s z' (fun σ => (s ^ 2 + σ ^ 2)⁻¹) <
          postExp G μ s z (fun σ => (s ^ 2 + σ ^ 2)⁻¹)) := by
  haveI := hG.isProb
  set Φ : ℝ → ℝ := fun r' => auxMoment G s r' (3 / 2) / auxMoment G s r' (1 / 2) with hΦ
  have hM1 : ∀ r : ℝ, 0 < auxMoment G s r (1 / 2) := fun r => ii_aux_pos G s r (1 / 2) hs (by norm_num)
  have hd : ∀ r, HasDerivAt Φ ((1 / 2) * (-(auxMoment G s r (5 / 2) * auxMoment G s r (1 / 2)) +
      auxMoment G s r (3 / 2) ^ 2) / auxMoment G s r (1 / 2) ^ 2) r := fun r => ii_Phi_deriv G s hs r
  have hpost : ∀ z, postExp G μ s z (fun σ => (s ^ 2 + σ ^ 2)⁻¹) = Φ ((z - μ) ^ 2) :=
    fun z => ii_post_eq G μ s z hs
  constructor
  · have hanti : Antitone Φ := by
      apply antitone_of_deriv_nonpos
      · exact fun r => (hd r).differentiableAt
      · intro r
        rw [(hd r).deriv]
        have hcs := ii_cs_weak G s r hs
        apply div_nonpos_of_nonpos_of_nonneg
        · nlinarith
        · have := hM1 r; positivity
    intro z z' h
    rw [hpost, hpost]
    exact hanti h
  · intro hne
    have hanti : StrictAnti Φ := by
      apply strictAnti_of_deriv_neg
      intro r
      rw [(hd r).deriv]
      have hcs := ii_cs_strict G hG s r hs hne
      apply div_neg_of_neg_of_pos
      · nlinarith
      · have := hM1 r; positivity
    intro z z' h
    rw [hpost, hpost]
    exact hanti h
