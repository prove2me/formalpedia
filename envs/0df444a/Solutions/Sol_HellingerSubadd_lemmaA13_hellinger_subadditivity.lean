-- Prove2me | solution 1 for HellingerSubadd.lemmaA13_hellinger_subadditivity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T08:25:01.68923+00:00
-- url     : https://prove2.me/submissions/350f9b3f-03c5-4fab-9c42-a20f6a38e69e

import Mathlib
import Definitions.Def_HellingerSubadd_hellingerSq
import Definitions.Def_HellingerSubadd_seqLaw
import Definitions.Def_HellingerSubadd_condHellingerSum

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace HSA

section Affinity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- real density of `μ` against `ρ` -/
noncomputable def fd (ρ μ : Measure Ω) (x : Ω) : ℝ := (μ.rnDeriv ρ x).toReal

/-- Hellinger affinity (Bhattacharyya coefficient) against `μ + ν`. -/
noncomputable def aff (μ ν : Measure Ω) : ℝ :=
  ∫ x, Real.sqrt (fd (μ + ν) μ x * fd (μ + ν) ν x) ∂(μ + ν)

lemma ac_left (μ ν : Measure Ω) : μ ≪ μ + ν :=
  Measure.AbsolutelyContinuous.rfl.add_right ν

lemma ac_right (μ ν : Measure Ω) : ν ≪ μ + ν := by
  intro s hs
  rw [Measure.add_apply] at hs
  exact (add_eq_zero.mp hs).2

lemma fd_meas (ρ μ : Measure Ω) : Measurable (fd ρ μ) :=
  (Measure.measurable_rnDeriv μ ρ).ennreal_toReal

lemma fd_nonneg (ρ μ : Measure Ω) (x : Ω) : 0 ≤ fd ρ μ x := ENNReal.toReal_nonneg

lemma fd_int (ρ μ : Measure Ω) [IsFiniteMeasure μ] : Integrable (fd ρ μ) ρ :=
  Measure.integrable_toReal_rnDeriv

lemma fd_integral (ρ μ : Measure Ω) [IsProbabilityMeasure μ] [SigmaFinite ρ] (h : μ ≪ ρ) :
    ∫ x, fd ρ μ x ∂ρ = 1 := by
  unfold fd
  rw [Measure.integral_toReal_rnDeriv h]
  simp

lemma sq_int (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun x => Real.sqrt (fd (μ + ν) μ x * fd (μ + ν) ν x)) (μ + ν) := by
  refine ((fd_int (μ + ν) μ).add (fd_int (μ + ν) ν)).mono' ?_ ?_
  · exact ((fd_meas _ _).mul (fd_meas _ _)).sqrt.aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    have ha := fd_nonneg (μ + ν) μ x
    have hb := fd_nonneg (μ + ν) ν x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (fd (μ + ν) μ x * fd (μ + ν) ν x)
        ≤ Real.sqrt ((fd (μ + ν) μ x + fd (μ + ν) ν x) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = fd (μ + ν) μ x + fd (μ + ν) ν x := Real.sqrt_sq (by linarith)

lemma aff_nonneg (μ ν : Measure Ω) : 0 ≤ aff μ ν :=
  integral_nonneg (fun _ => Real.sqrt_nonneg _)

lemma sqdiff_eq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 = a + b - 2 * Real.sqrt (a * b) := by
  rw [sub_sq, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_mul ha]
  ring

lemma sqdiff_int (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun x => (Real.sqrt (fd (μ + ν) μ x) - Real.sqrt (fd (μ + ν) ν x)) ^ 2) (μ + ν) := by
  refine (((fd_int (μ + ν) μ).add (fd_int (μ + ν) ν)).sub ((sq_int μ ν).const_mul 2)).congr
    (Filter.Eventually.of_forall (fun x => ?_))
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [sqdiff_eq _ _ (fd_nonneg _ _ x) (fd_nonneg _ _ x)]

lemma sqdiff_integral (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∫ x, (Real.sqrt (fd (μ + ν) μ x) - Real.sqrt (fd (μ + ν) ν x)) ^ 2 ∂(μ + ν)
      = 2 - 2 * aff μ ν := by
  have e : (fun x => (Real.sqrt (fd (μ + ν) μ x) - Real.sqrt (fd (μ + ν) ν x)) ^ 2)
      = fun x => (fd (μ + ν) μ x + fd (μ + ν) ν x)
          - 2 * Real.sqrt (fd (μ + ν) μ x * fd (μ + ν) ν x) := by
    funext x; exact sqdiff_eq _ _ (fd_nonneg _ _ x) (fd_nonneg _ _ x)
  have h1 : Integrable (fun x => fd (μ + ν) μ x + fd (μ + ν) ν x) (μ + ν) :=
    (fd_int _ _).add (fd_int _ _)
  rw [e, integral_sub h1 ((sq_int μ ν).const_mul 2),
    integral_add (fd_int _ _) (fd_int _ _), integral_const_mul,
    fd_integral _ _ (ac_left μ ν), fd_integral _ _ (ac_right μ ν)]
  unfold aff
  ring

lemma aff_le_one (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    aff μ ν ≤ 1 := by
  have h := sqdiff_integral μ ν
  have h0 : 0 ≤ ∫ x, (Real.sqrt (fd (μ + ν) μ x) - Real.sqrt (fd (μ + ν) ν x)) ^ 2 ∂(μ + ν) :=
    integral_nonneg (fun _ => sq_nonneg _)
  linarith

theorem hell_eq (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    HellingerSubadd.hellingerSq μ ν = ENNReal.ofReal (2 - 2 * aff μ ν) := by
  unfold HellingerSubadd.hellingerSq
  show ∫⁻ x, ENNReal.ofReal ((Real.sqrt (fd (μ + ν) μ x) - Real.sqrt (fd (μ + ν) ν x)) ^ 2)
    ∂(μ + ν) = _
  rw [← ofReal_integral_eq_lintegral_ofReal (sqdiff_int μ ν)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)), sqdiff_integral]

theorem hell_toReal (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (HellingerSubadd.hellingerSq μ ν).toReal = 2 - 2 * aff μ ν := by
  rw [hell_eq, ENNReal.toReal_ofReal (by linarith [aff_le_one μ ν])]

/-- real AM-GM with a parameter -/
lemma amgm_real (u v s : ℝ) (hs : 0 < s) :
    2 * (u * v) ≤ u ^ 2 * s + v ^ 2 * s⁻¹ := by
  have e : u ^ 2 * s + v ^ 2 * s⁻¹ - 2 * (u * v) = s⁻¹ * (u * s - v) ^ 2 := by
    field_simp
    ring
  have : 0 ≤ s⁻¹ * (u * s - v) ^ 2 := by positivity
  linarith

lemma amgm_le (a b t : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    2 * ENNReal.ofReal (Real.sqrt (a.toReal * b.toReal)) ≤ a * t + b * t⁻¹ := by
  rcases eq_or_ne t 0 with rfl | ht0
  · rcases eq_or_ne b 0 with rfl | hb0
    · simp
    · simp [hb0]
  rcases eq_or_ne t ⊤ with rfl | htt
  · rcases eq_or_ne a 0 with rfl | ha0
    · simp
    · simp [ha0]
  have hR : a * t + b * t⁻¹ ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ha htt, ENNReal.mul_ne_top hb ?_⟩
    exact ENNReal.inv_ne_top.2 ht0
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_le_iff_le_toReal hR, ENNReal.toReal_add (ENNReal.mul_ne_top ha htt)
      (ENNReal.mul_ne_top hb (ENNReal.inv_ne_top.2 ht0)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hs : 0 < t.toReal := ENNReal.toReal_pos ht0 htt
  have h := amgm_real (Real.sqrt a.toReal) (Real.sqrt b.toReal) t.toReal hs
  rw [Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ENNReal.toReal_nonneg] at h
  rw [Real.sqrt_mul ENNReal.toReal_nonneg]
  linarith

lemma amgm_eq (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a * (ENNReal.ofReal (Real.sqrt b.toReal) / ENNReal.ofReal (Real.sqrt a.toReal))
      + b * (ENNReal.ofReal (Real.sqrt b.toReal) / ENNReal.ofReal (Real.sqrt a.toReal))⁻¹
      ≤ 2 * ENNReal.ofReal (Real.sqrt (a.toReal * b.toReal)) := by
  set u := Real.sqrt a.toReal with hu
  set v := Real.sqrt b.toReal with hv
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hau : a = ENNReal.ofReal (u ^ 2) := by
    rw [hu, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha]
  have hbv : b = ENNReal.ofReal (v ^ 2) := by
    rw [hv, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hb]
  rcases hu0.eq_or_lt with hu' | hupos
  · -- a = 0
    have ha0 : a = 0 := by rw [hau, ← hu']; simp
    rw [ha0, zero_mul, zero_add]
    rcases hv0.eq_or_lt with hv' | hvpos
    · have hb0 : b = 0 := by rw [hbv, ← hv']; simp
      rw [hb0, zero_mul]; exact bot_le
    · rw [← hu', ENNReal.ofReal_zero, ENNReal.div_zero (by simp [hvpos]), ENNReal.inv_top,
        mul_zero]
      exact bot_le
  rcases hv0.eq_or_lt with hv' | hvpos
  · have hb0 : b = 0 := by rw [hbv, ← hv']; simp
    rw [hb0, zero_mul, add_zero, ← hv', ENNReal.ofReal_zero, ENNReal.zero_div, mul_zero]
    exact bot_le
  rw [← ENNReal.ofReal_div_of_pos hupos, ← ENNReal.ofReal_inv_of_pos (div_pos hvpos hupos),
    hau, hbv, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num)]
  apply le_of_eq
  congr 1
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    Real.sqrt_mul (by positivity), Real.sqrt_sq hu0, Real.sqrt_sq hv0]
  field_simp
  ring

lemma two_ofReal_aff (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    2 * ENNReal.ofReal (aff μ ν)
      = ∫⁻ x, 2 * ENNReal.ofReal (Real.sqrt (fd (μ + ν) μ x * fd (μ + ν) ν x)) ∂(μ + ν) := by
  have hm : Measurable (fun x => ENNReal.ofReal (Real.sqrt (fd (μ + ν) μ x * fd (μ + ν) ν x))) :=
    ((fd_meas (μ + ν) μ).mul (fd_meas (μ + ν) ν)).sqrt.ennreal_ofReal
  rw [lintegral_const_mul _ hm, aff,
    ofReal_integral_eq_lintegral_ofReal (sq_int μ ν)
      (Filter.Eventually.of_forall (fun _ => Real.sqrt_nonneg _))]

lemma hmul {Ω' : Type*} [MeasurableSpace Ω'] (μ ν : Measure Ω') (φ : Ω' → ℝ≥0∞)
    (hφ : Measurable φ) : Measurable (fun x => μ.rnDeriv (μ + ν) x * φ x) :=
  (Measure.measurable_rnDeriv _ _).mul hφ

lemma var_form (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (φ : Ω → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂μ + ∫⁻ x, (φ x)⁻¹ ∂ν
      = ∫⁻ x, (μ.rnDeriv (μ + ν) x * φ x + ν.rnDeriv (μ + ν) x * (φ x)⁻¹) ∂(μ + ν) := by
  rw [← lintegral_rnDeriv_mul (f := φ) (ac_left μ ν) hφ.aemeasurable,
    ← lintegral_rnDeriv_mul (f := fun x => (φ x)⁻¹) (ac_right μ ν) hφ.inv.aemeasurable,
    ← lintegral_add_left (hmul μ ν φ hφ)]

/-- variational lower bound for the affinity -/
theorem var_lower (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (φ : Ω → ℝ≥0∞) (hφ : Measurable φ) :
    2 * ENNReal.ofReal (aff μ ν) ≤ ∫⁻ x, φ x ∂μ + ∫⁻ x, (φ x)⁻¹ ∂ν := by
  rw [var_form μ ν φ hφ, two_ofReal_aff]
  apply lintegral_mono_ae
  filter_upwards [Measure.rnDeriv_ne_top μ (μ + ν), Measure.rnDeriv_ne_top ν (μ + ν)]
    with x h1 h2
  exact amgm_le _ _ _ h1 h2

/-- the optimal test function -/
noncomputable def phiOpt (μ ν : Measure Ω) (x : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (fd (μ + ν) ν x)) / ENNReal.ofReal (Real.sqrt (fd (μ + ν) μ x))

lemma phiOpt_meas (μ ν : Measure Ω) : Measurable (phiOpt μ ν) :=
  (fd_meas _ _).sqrt.ennreal_ofReal.div (fd_meas _ _).sqrt.ennreal_ofReal

/-- the variational bound is attained -/
theorem var_attained (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∃ φ : Ω → ℝ≥0∞, Measurable φ ∧
      ∫⁻ x, φ x ∂μ + ∫⁻ x, (φ x)⁻¹ ∂ν ≤ 2 * ENNReal.ofReal (aff μ ν) := by
  refine ⟨phiOpt μ ν, phiOpt_meas μ ν, ?_⟩
  rw [var_form μ ν _ (phiOpt_meas μ ν), two_ofReal_aff]
  apply lintegral_mono_ae
  filter_upwards [Measure.rnDeriv_ne_top μ (μ + ν), Measure.rnDeriv_ne_top ν (μ + ν)]
    with x h1 h2
  exact amgm_eq _ _ h1 h2

/-- pointwise mixing inequality -/
lemma mix_le (f g a b X : ℝ≥0∞) (hf : f ≠ ⊤) (hg : g ≠ ⊤)
    (hX : ∀ t : ℝ≥0∞, t ≠ 0 → t ≠ ⊤ → X ≤ t * a + t⁻¹ * b) :
    ENNReal.ofReal (Real.sqrt (f.toReal * g.toReal)) * X ≤ f * a + g * b := by
  set u := Real.sqrt f.toReal with hu
  set v := Real.sqrt g.toReal with hv
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hfu : f = ENNReal.ofReal (u ^ 2) := by
    rw [hu, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hf]
  have hgv : g = ENNReal.ofReal (v ^ 2) := by
    rw [hv, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hg]
  rw [Real.sqrt_mul ENNReal.toReal_nonneg, ← hu, ← hv]
  rcases hu0.eq_or_lt with hu' | hupos
  · rw [← hu', zero_mul, ENNReal.ofReal_zero, zero_mul]; exact bot_le
  rcases hv0.eq_or_lt with hv' | hvpos
  · rw [← hv', mul_zero, ENNReal.ofReal_zero, zero_mul]; exact bot_le
  have ht0 : ENNReal.ofReal (u / v) ≠ 0 := by simp [div_pos hupos hvpos]
  have hti : (ENNReal.ofReal (u / v))⁻¹ = ENNReal.ofReal (v / u) := by
    rw [← ENNReal.ofReal_inv_of_pos (div_pos hupos hvpos), inv_div]
  calc ENNReal.ofReal (u * v) * X
      ≤ ENNReal.ofReal (u * v) * (ENNReal.ofReal (u / v) * a + (ENNReal.ofReal (u / v))⁻¹ * b) :=
        by gcongr; exact hX _ ht0 ENNReal.ofReal_ne_top
    _ = f * a + g * b := by
        rw [hti, mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), hfu, hgv]
        congr 3
        · field_simp
        · field_simp

lemma hell_self (μ : Measure Ω) : HellingerSubadd.hellingerSq μ μ = 0 := by
  unfold HellingerSubadd.hellingerSq
  simp

lemma aff_self (μ : Measure Ω) [IsProbabilityMeasure μ] : aff μ μ = 1 := by
  have h := hell_eq μ μ
  rw [hell_self, eq_comm, ENNReal.ofReal_eq_zero] at h
  linarith [aff_le_one μ μ]

lemma hell_toReal_le_two (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (HellingerSubadd.hellingerSq μ ν).toReal ≤ 2 := by
  rw [hell_toReal]; linarith [aff_nonneg μ ν]

lemma const_le_log (n : ℕ) (hn : 2 ≤ n) : (40 / 3 : ℝ) ≤ 10 ^ 2 * Real.log n := by
  have h2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have := Real.log_two_gt_d9
  nlinarith

end Affinity

section Chain

variable {W Ω : Type*} [MeasurableSpace W] [MeasurableSpace Ω]

/-- chain lower bound for the affinity of two mixtures -/
theorem chain (p q : Measure W) [IsProbabilityMeasure p] [IsProbabilityMeasure q]
    (K L : W → Measure Ω) (hK : ∀ w, IsProbabilityMeasure (K w))
    (hL : ∀ w, IsProbabilityMeasure (L w))
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : ∀ φ : Ω → ℝ≥0∞, Measurable φ → ∫⁻ x, φ x ∂P = ∫⁻ w, ∫⁻ x, φ x ∂(K w) ∂p)
    (hQ : ∀ φ : Ω → ℝ≥0∞, Measurable φ → ∫⁻ x, φ x ∂Q = ∫⁻ w, ∫⁻ x, φ x ∂(L w) ∂q)
    (hKm : ∀ φ : Ω → ℝ≥0∞, Measurable φ → Measurable (fun w => ∫⁻ x, φ x ∂(K w)))
    (hLm : ∀ φ : Ω → ℝ≥0∞, Measurable φ → Measurable (fun w => ∫⁻ x, φ x ∂(L w))) :
    ∫⁻ w, ENNReal.ofReal (Real.sqrt (fd (p + q) p w * fd (p + q) q w))
        * (2 * ENNReal.ofReal (aff (K w) (L w))) ∂(p + q)
      ≤ 2 * ENNReal.ofReal (aff P Q) := by
  obtain ⟨φ, hφ, hle⟩ := var_attained P Q
  refine le_trans ?_ hle
  rw [hP φ hφ, hQ (fun x => (φ x)⁻¹) hφ.inv,
    ← lintegral_rnDeriv_mul (ac_left p q) (hKm φ hφ).aemeasurable,
    ← lintegral_rnDeriv_mul (ac_right p q) (hLm (fun x => (φ x)⁻¹) hφ.inv).aemeasurable,
    ← lintegral_add_left (hmul p q _ (hKm φ hφ))]
  apply lintegral_mono_ae
  filter_upwards [Measure.rnDeriv_ne_top p (p + q), Measure.rnDeriv_ne_top q (p + q)]
    with w h1 h2
  apply mix_le _ _ _ _ _ h1 h2
  intro t ht0 htt
  have := hK w
  have := hL w
  have h := var_lower (K w) (L w) (fun x => t * φ x) (hφ.const_mul t)
  have e : ∀ x, (t * φ x)⁻¹ = t⁻¹ * (φ x)⁻¹ := fun x =>
    ENNReal.mul_inv (Or.inl ht0) (Or.inl htt)
  simp only [e] at h
  rwa [lintegral_const_mul _ hφ, lintegral_const_mul (f := fun x => (φ x)⁻¹) _ hφ.inv] at h

/-- the weighted claim is preserved by mixing (the induction step) -/
theorem claim_step (p q : Measure W) [IsProbabilityMeasure p] [IsProbabilityMeasure q]
    (K L : W → Measure Ω) (hK : ∀ w, IsProbabilityMeasure (K w))
    (hL : ∀ w, IsProbabilityMeasure (L w))
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : ∀ φ : Ω → ℝ≥0∞, Measurable φ → ∫⁻ x, φ x ∂P = ∫⁻ w, ∫⁻ x, φ x ∂(K w) ∂p)
    (hQ : ∀ φ : Ω → ℝ≥0∞, Measurable φ → ∫⁻ x, φ x ∂Q = ∫⁻ w, ∫⁻ x, φ x ∂(L w) ∂q)
    (hKm : ∀ φ : Ω → ℝ≥0∞, Measurable φ → Measurable (fun w => ∫⁻ x, φ x ∂(K w)))
    (hLm : ∀ φ : Ω → ℝ≥0∞, Measurable φ → Measurable (fun w => ∫⁻ x, φ x ∂(L w)))
    (c : W → ℝ) (hc : Measurable c) (hc0 : ∀ w, 0 ≤ c w) (B : ℝ) (hcB : ∀ w, c w ≤ B)
    (hchild : ∀ w (α β : ℝ), 0 ≤ α → 0 ≤ β →
      3 / 8 * (α * β) * (1 - aff (K w) (L w)) ≤ 5 / 2 * α ^ 2 * c w + 5 / 16 * (α - β) ^ 2)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    3 / 8 * (α * β) * (1 - aff P Q)
      ≤ 5 / 2 * α ^ 2 * ((2 - 2 * aff p q) + ∫ w, c w ∂p) + 5 / 16 * (α - β) ^ 2 := by
  have hA1 := aff_le_one p q
  have hA0 := aff_nonneg p q
  have hAP1 := aff_le_one P Q
  have hAP0 := aff_nonneg P Q
  have hE : 0 ≤ ∫ w, c w ∂p := integral_nonneg hc0
  have hab := mul_nonneg hα hβ
  have hrest : 0 ≤ 5 / 2 * α ^ 2 * ((2 - 2 * aff p q) + ∫ w, c w ∂p) := by
    have : 0 ≤ (2 - 2 * aff p q) + ∫ w, c w ∂p := by linarith
    positivity
  rcases hab.eq_or_lt with h0 | hpos
  · rw [← h0]
    nlinarith [sq_nonneg (α - β)]
  by_cases h5 : β ≤ 5 * α
  swap
  · push Not at h5
    have h1 : 3 / 8 * (α * β) * (1 - aff P Q) ≤ 3 / 8 * (α * β) := by nlinarith
    have h2 : 3 / 8 * (α * β) ≤ 5 / 16 * (α - β) ^ 2 := by nlinarith
    linarith
  -- main case
  set ρ := p + q with hρ
  set fr := fd ρ p with hfr
  set gr := fd ρ q with hgr
  set s : W → ℝ := fun w => Real.sqrt (fr w * gr w) with hs
  set R : W → ℝ := fun w => (8 / 3 * (α * β)) * s w - (20 / 3 * α ^ 2) * (fr w * c w)
      - (5 / 6 * α ^ 2) * fr w - (5 / 6 * β ^ 2) * gr w with hR
  have hfrI : Integrable fr ρ := fd_int ρ p
  have hgrI : Integrable gr ρ := fd_int ρ q
  have hsI : Integrable s ρ := sq_int p q
  have hcI : Integrable c p := by
    refine (integrable_const B).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun w => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hc0 w)]
    exact hcB w
  have hfcI : Integrable (fun w => fr w * c w) ρ :=
    (integrable_toReal_rnDeriv_mul_iff (ac_left p q)).2 hcI
  have h1 : Integrable (fun w => 8 / 3 * (α * β) * s w) ρ := hsI.const_mul _
  have h2 : Integrable (fun w => 20 / 3 * α ^ 2 * (fr w * c w)) ρ := hfcI.const_mul _
  have h3 : Integrable (fun w => 5 / 6 * α ^ 2 * fr w) ρ := hfrI.const_mul _
  have h4 : Integrable (fun w => 5 / 6 * β ^ 2 * gr w) ρ := hgrI.const_mul _
  have h12 : Integrable (fun w => 8 / 3 * (α * β) * s w - 20 / 3 * α ^ 2 * (fr w * c w)) ρ :=
    h1.sub h2
  have h123 : Integrable (fun w => 8 / 3 * (α * β) * s w - 20 / 3 * α ^ 2 * (fr w * c w)
      - 5 / 6 * α ^ 2 * fr w) ρ := h12.sub h3
  have hRI : Integrable R ρ := h123.sub h4
  have hfcE : ∫ w, fr w * c w ∂ρ = ∫ w, c w ∂p := by
    have := integral_rnDeriv_smul (f := c) (ac_left p q)
    simp only [smul_eq_mul] at this
    exact this
  have hRE : ∫ w, R w ∂ρ = 8 / 3 * (α * β) * aff p q - 20 / 3 * α ^ 2 * (∫ w, c w ∂p)
      - 5 / 6 * α ^ 2 - 5 / 6 * β ^ 2 := by
    simp only [hR]
    rw [integral_sub h123 h4, integral_sub h12 h3, integral_sub h1 h2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, hfcE,
      fd_integral ρ p (ac_left p q), fd_integral ρ q (ac_right p q)]
    rw [show ∫ a, s a ∂ρ = aff p q from rfl]
    ring
  -- pointwise: 2 R w ≤ αβ · s w · 2 A_w
  have hpt : ∀ w, ENNReal.ofReal (2 * R w)
      ≤ ENNReal.ofReal (α * β) * (ENNReal.ofReal (s w) * (2 * ENNReal.ofReal (aff (K w) (L w)))) := by
    intro w
    have hf0 := fd_nonneg ρ p w
    have hg0 := fd_nonneg ρ q w
    have hch := hchild w (α * Real.sqrt (fr w)) (β * Real.sqrt (gr w))
      (mul_nonneg hα (Real.sqrt_nonneg _)) (mul_nonneg hβ (Real.sqrt_nonneg _))
    have e1 : α * Real.sqrt (fr w) * (β * Real.sqrt (gr w)) = α * β * s w := by
      simp only [hs]; rw [Real.sqrt_mul hf0]; ring
    have e2 : (α * Real.sqrt (fr w)) ^ 2 = α ^ 2 * fr w := by
      rw [mul_pow, Real.sq_sqrt hf0]
    have e3 : (α * Real.sqrt (fr w) - β * Real.sqrt (gr w)) ^ 2
        = α ^ 2 * fr w + β ^ 2 * gr w - 2 * (α * β * s w) := by
      rw [← e1, sub_sq, e2, mul_pow, Real.sq_sqrt hg0]; ring
    rw [e1, e2, e3] at hch
    have hA := aff_nonneg (K w) (L w)
    have hsw : 0 ≤ s w := Real.sqrt_nonneg _
    have key : 2 * R w ≤ α * β * s w * (2 * aff (K w) (L w)) := by
      simp only [hR]
      nlinarith
    calc ENNReal.ofReal (2 * R w) ≤ ENNReal.ofReal (α * β * s w * (2 * aff (K w) (L w))) :=
          ENNReal.ofReal_le_ofReal key
      _ = _ := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
            ← ENNReal.ofReal_mul hsw, ← ENNReal.ofReal_mul hab]
          congr 1
          ring
  have hch := chain p q K L hK hL P Q hP hQ hKm hLm
  have hlint : ∫⁻ w, ENNReal.ofReal (2 * R w) ∂ρ ≤ ENNReal.ofReal (2 * (α * β * aff P Q)) := by
    calc ∫⁻ w, ENNReal.ofReal (2 * R w) ∂ρ
        ≤ ∫⁻ w, ENNReal.ofReal (α * β) * (ENNReal.ofReal (s w)
            * (2 * ENNReal.ofReal (aff (K w) (L w)))) ∂ρ := lintegral_mono hpt
      _ = ENNReal.ofReal (α * β) * ∫⁻ w, ENNReal.ofReal (s w)
            * (2 * ENNReal.ofReal (aff (K w) (L w))) ∂ρ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (α * β) * (2 * ENNReal.ofReal (aff P Q)) := by gcongr
      _ = ENNReal.ofReal (2 * (α * β * aff P Q)) := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
            ← ENNReal.ofReal_mul hab]
          congr 1
          ring
  -- back to reals
  have hmaxI : Integrable (fun w => max (2 * R w) 0) ρ := (hRI.const_mul 2).sup (integrable_zero _ _ _)
  have hmax : ∫ w, max (2 * R w) 0 ∂ρ ≤ 2 * (α * β * aff P Q) := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => max (2 * R w) 0)
      (Filter.Eventually.of_forall (fun _ => le_max_right _ _))
      hmaxI.aestronglyMeasurable]
    have e : (fun w => ENNReal.ofReal (max (2 * R w) 0)) = fun w => ENNReal.ofReal (2 * R w) := by
      funext w; rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (zero_le' : (0:ℝ≥0∞) ≤ _)]
    rw [e]
    have h2 : 0 ≤ 2 * (α * β * aff P Q) := by positivity
    calc (∫⁻ w, ENNReal.ofReal (2 * R w) ∂ρ).toReal
        ≤ (ENNReal.ofReal (2 * (α * β * aff P Q))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
      _ = _ := ENNReal.toReal_ofReal h2
  have hle : ∫ w, 2 * R w ∂ρ ≤ ∫ w, max (2 * R w) 0 ∂ρ :=
    integral_mono (hRI.const_mul 2) hmaxI (fun w => le_max_left _ _)
  rw [integral_const_mul, hRE] at hle
  have hmain : 0 ≤ α * (1 - aff p q) * (5 * α - β) := by
    have : 0 ≤ 1 - aff p q := by linarith
    have : 0 ≤ 5 * α - β := by linarith
    positivity
  nlinarith

end Chain

section Traj

variable {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]

/-- the weighted claim -/
def Claim {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) (C : ℝ) : Prop :=
  ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → 3 / 8 * (α * β) * (1 - aff μ ν) ≤ 5 / 2 * α ^ 2 * C + 5 / 16 * (α - β) ^ 2

/-- extend a trajectory by one point -/
noncomputable def ext (a : ℕ) (y : Π i : Iic a, X i) (z : X (a + 1)) : Π i : Iic (a + 1), X i :=
  IicProdIoc a (a + 1) (y, MeasurableEquiv.piSingleton a z)

lemma ext_meas (a : ℕ) (y : Π i : Iic a, X i) : Measurable (ext (X := X) a y) := by
  unfold ext
  exact measurable_IicProdIoc.comp (measurable_prodMk_left.comp (MeasurableEquiv.measurable _))

lemma split (κ : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1))) [∀ k, IsMarkovKernel (κ k)]
    {a n : ℕ} (h : a < n) (y : Π i : Iic a, X i) (φ : (Π i : Iic n, X i) → ℝ≥0∞)
    (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂(Kernel.partialTraj κ a n y)
      = ∫⁻ z, ∫⁻ x, φ x ∂(Kernel.partialTraj κ (a + 1) n (ext a y z)) ∂(κ a y) := by
  have hg : Measurable (fun w => ∫⁻ x, φ x ∂(Kernel.partialTraj κ (a + 1) n w)) :=
    hφ.lintegral_kernel
  rw [← Kernel.partialTraj_comp_partialTraj (Nat.le_succ a) h, Kernel.lintegral_comp _ _ _ hφ,
    Kernel.partialTraj_succ_self, Kernel.map_apply _ measurable_IicProdIoc,
    lintegral_map hg measurable_IicProdIoc,
    Kernel.lintegral_id_prod (f := fun p => ∫⁻ x, φ x ∂(Kernel.partialTraj κ (a + 1) n
      (IicProdIoc a (a + 1) p))) (hg.comp measurable_IicProdIoc),
    Kernel.map_apply _ (MeasurableEquiv.measurable _),
    lintegral_map (f := fun b => ∫⁻ x, φ x ∂(Kernel.partialTraj κ (a + 1) n
      (IicProdIoc a (a + 1) (y, b))))
      ((hg.comp measurable_IicProdIoc).comp measurable_prodMk_left)
      (MeasurableEquiv.measurable _)]
  rfl

lemma restr (κ : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1))) [∀ k, IsMarkovKernel (κ k)]
    {a n : ℕ} (h : a ≤ n) (y : Π i : Iic a, X i) (f : (Π i : Iic a, X i) → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, f (Preorder.frestrictLe₂ (π := X) h x) ∂(Kernel.partialTraj κ a n y) = f y := by
  rw [← lintegral_map hf (Preorder.measurable_frestrictLe₂ h),
    Kernel.partialTraj_map_frestrictLe₂_apply, Kernel.partialTraj_self, Kernel.id_apply,
    lintegral_dirac' _ hf]

variable (κ η : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1))) (n : ℕ)

/-- tail sum of conditional Hellinger terms -/
noncomputable def S (a : ℕ) (x : Π i : Iic n, X i) : ℝ≥0∞ :=
  ∑ k : Fin n, if a ≤ (k : ℕ) then
    HellingerSubadd.hellingerSq (κ k (Preorder.frestrictLe₂ (π := X) k.2.le x))
      (η k (Preorder.frestrictLe₂ (π := X) k.2.le x)) else 0

lemma S_zero : S κ η n 0 = HellingerSubadd.condHellingerSum κ η n := by
  funext x
  simp [S, HellingerSubadd.condHellingerSum]

lemma S_succ {a : ℕ} (h : a < n) (x : Π i : Iic n, X i) :
    S κ η n a x = HellingerSubadd.hellingerSq (κ a (Preorder.frestrictLe₂ (π := X) h.le x))
      (η a (Preorder.frestrictLe₂ (π := X) h.le x)) + S κ η n (a + 1) x := by
  unfold S
  set g : Fin n → ℝ≥0∞ := fun k => HellingerSubadd.hellingerSq
    (κ k (Preorder.frestrictLe₂ (π := X) k.2.le x)) (η k (Preorder.frestrictLe₂ (π := X) k.2.le x))
    with hg
  have e : ∀ k : Fin n, (if a ≤ (k : ℕ) then g k else 0)
      = (if k = ⟨a, h⟩ then g k else 0) + (if a + 1 ≤ (k : ℕ) then g k else 0) := by
    intro k
    by_cases hk : k = ⟨a, h⟩
    · subst hk; simp
    · have hk' : (k : ℕ) ≠ a := fun e => hk (Fin.ext e)
      by_cases h1 : a + 1 ≤ (k : ℕ)
      · rw [if_pos (by omega), if_neg hk, if_pos h1, zero_add]
      · rw [if_neg (by omega), if_neg hk, if_neg h1, zero_add]
  show ∑ k : Fin n, (if a ≤ (k : ℕ) then g k else 0) = _
  rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rfl

lemma S_meas (hmeas : ∀ k < n, Measurable (fun y => HellingerSubadd.hellingerSq (κ k y) (η k y)))
    (a : ℕ) : Measurable (S κ η n a) := by
  unfold S
  refine Finset.measurable_sum _ (fun k _ => ?_)
  by_cases hk : a ≤ (k : ℕ)
  · simp only [hk, if_true]
    exact (hmeas k k.2).comp (Preorder.measurable_frestrictLe₂ _)
  · simp only [hk, if_false]
    exact measurable_const

lemma hell_le_two {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : HellingerSubadd.hellingerSq μ ν ≤ 2 := by
  rw [hell_eq]
  calc ENNReal.ofReal (2 - 2 * aff μ ν) ≤ ENNReal.ofReal 2 :=
        ENNReal.ofReal_le_ofReal (by linarith [aff_nonneg μ ν])
    _ = 2 := by simp

lemma S_le [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)] (a : ℕ)
    (x : Π i : Iic n, X i) : S κ η n a x ≤ 2 * n := by
  unfold S
  calc (∑ k : Fin n, if a ≤ (k : ℕ) then
      HellingerSubadd.hellingerSq (κ k (Preorder.frestrictLe₂ (π := X) k.2.le x))
        (η k (Preorder.frestrictLe₂ (π := X) k.2.le x)) else 0)
      ≤ ∑ _k : Fin n, (2 : ℝ≥0∞) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        split_ifs
        · exact hell_le_two _ _
        · exact zero_le'
    _ = 2 * n := by simp [mul_comm]

/-- expected tail sum -/
noncomputable def D (a : ℕ) (y : Π i : Iic a, X i) : ℝ≥0∞ :=
  ∫⁻ x, S κ η n a x ∂(Kernel.partialTraj κ a n y)

noncomputable def Ca (a : ℕ) (y : Π i : Iic a, X i) : ℝ := (D κ η n a y).toReal

lemma D_le [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)] (a : ℕ)
    (y : Π i : Iic a, X i) : D κ η n a y ≤ 2 * n := by
  unfold D
  calc ∫⁻ x, S κ η n a x ∂(Kernel.partialTraj κ a n y) ≤ ∫⁻ _x, (2 * n : ℝ≥0∞) ∂(Kernel.partialTraj κ a n y) :=
        lintegral_mono (fun x => S_le κ η n a x)
    _ = 2 * n := by simp

lemma D_ne_top [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)] (a : ℕ)
    (y : Π i : Iic a, X i) : D κ η n a y ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp [ENNReal.mul_eq_top]) (D_le κ η n a y)

lemma D_meas (hmeas : ∀ k < n, Measurable (fun y => HellingerSubadd.hellingerSq (κ k y) (η k y)))
    (a : ℕ) : Measurable (D κ η n a) := by
  unfold D
  exact (S_meas κ η n hmeas a).lintegral_kernel

lemma Ca_nonneg (a : ℕ) (y : Π i : Iic a, X i) : 0 ≤ Ca κ η n a y := ENNReal.toReal_nonneg

lemma Ca_le [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)] (a : ℕ)
    (y : Π i : Iic a, X i) : Ca κ η n a y ≤ 2 * n := by
  unfold Ca
  have := ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) (D_le κ η n a y)
  simpa using this

lemma D_succ [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)]
    (hmeas : ∀ k < n, Measurable (fun y => HellingerSubadd.hellingerSq (κ k y) (η k y)))
    {a : ℕ} (h : a < n) (y : Π i : Iic a, X i) :
    D κ η n a y = HellingerSubadd.hellingerSq (κ a y) (η a y)
      + ∫⁻ z, D κ η n (a + 1) (ext a y z) ∂(κ a y) := by
  unfold D
  simp_rw [S_succ κ η n h]
  have hf : Measurable (fun w => HellingerSubadd.hellingerSq (κ a w) (η a w)) := hmeas a h
  have hr := restr κ h.le y (fun w => HellingerSubadd.hellingerSq (κ a w) (η a w)) hf
  beta_reduce at hr
  rw [lintegral_add_left (f := fun x => HellingerSubadd.hellingerSq
      (κ a (Preorder.frestrictLe₂ (π := X) h.le x)) (η a (Preorder.frestrictLe₂ (π := X) h.le x)))
      (hf.comp (Preorder.measurable_frestrictLe₂ h.le)),
    hr, split κ h y _ (S_meas κ η n hmeas (a + 1))]

lemma Ca_succ [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)]
    (hmeas : ∀ k < n, Measurable (fun y => HellingerSubadd.hellingerSq (κ k y) (η k y)))
    {a : ℕ} (h : a < n) (y : Π i : Iic a, X i) :
    Ca κ η n a y = (2 - 2 * aff (κ a y) (η a y))
      + ∫ z, Ca κ η n (a + 1) (ext a y z) ∂(κ a y) := by
  have hm : Measurable (fun z => D κ η n (a + 1) (ext a y z)) :=
    (D_meas κ η n hmeas (a + 1)).comp (ext_meas a y)
  have hI : ∫⁻ z, D κ η n (a + 1) (ext a y z) ∂(κ a y) ≤ 2 * n := by
    calc _ ≤ ∫⁻ _z, (2 * n : ℝ≥0∞) ∂(κ a y) := lintegral_mono (fun z => D_le κ η n (a + 1) _)
      _ = 2 * n := by simp
  have h2 : (2 : ℝ≥0∞) * n ≠ ⊤ := by simp [ENNReal.mul_eq_top]
  have hH : HellingerSubadd.hellingerSq (κ a y) (η a y) ≠ ⊤ :=
    ne_top_of_le_ne_top (b := 2) (by simp) (hell_le_two _ _)
  unfold Ca
  rw [D_succ κ η n hmeas h y, ENNReal.toReal_add hH (ne_top_of_le_ne_top h2 hI),
    hell_toReal, integral_toReal hm.aemeasurable
      (Filter.Eventually.of_forall (fun z => (D_ne_top κ η n (a + 1) _).lt_top))]

theorem traj_claim [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)]
    (hmeas : ∀ k < n, Measurable (fun y => HellingerSubadd.hellingerSq (κ k y) (η k y)))
    (m : ℕ) : ∀ a, a + m = n → ∀ y : Π i : Iic a, X i,
      Claim (Kernel.partialTraj κ a n y) (Kernel.partialTraj η a n y) (Ca κ η n a y) := by
  induction m with
  | zero =>
    intro a ha y α β hα hβ
    simp only [add_zero] at ha
    subst ha
    rw [Kernel.partialTraj_self, Kernel.partialTraj_self, Kernel.id_apply, aff_self]
    have h0 := Ca_nonneg κ η a a y
    have h1 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 5 / 2) (sq_nonneg α)) h0
    nlinarith [sq_nonneg (α - β)]
  | succ m ih =>
    intro a ha y α β hα hβ
    have h : a < n := by omega
    have hc : Measurable (fun z => Ca κ η n (a + 1) (ext a y z)) :=
      ((D_meas κ η n hmeas (a + 1)).comp (ext_meas a y)).ennreal_toReal
    rw [Ca_succ κ η n hmeas h y]
    exact claim_step (κ a y) (η a y)
      (fun z => Kernel.partialTraj κ (a + 1) n (ext a y z))
      (fun z => Kernel.partialTraj η (a + 1) n (ext a y z))
      (fun _ => inferInstance) (fun _ => inferInstance)
      (Kernel.partialTraj κ a n y) (Kernel.partialTraj η a n y)
      (fun φ hφ => split κ h y φ hφ) (fun φ hφ => split η h y φ hφ)
      (fun φ hφ => (hφ.lintegral_kernel).comp (ext_meas a y))
      (fun φ hφ => (hφ.lintegral_kernel).comp (ext_meas a y))
      (fun z => Ca κ η n (a + 1) (ext a y z)) hc (fun z => Ca_nonneg κ η n _ _) (2 * n)
      (fun z => Ca_le κ η n _ _)
      (fun z => ih (a + 1) (by omega) (ext a y z)) α β hα hβ

end Traj

end HSA

open MeasureTheory ProbabilityTheory Finset in
theorem solution {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ η : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1)))
    [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)]
    (x₀ : Π i : Iic 0, X i) (n : ℕ) (hn : 2 ≤ n)
    (hmeas : ∀ k < n, Measurable (fun y => HellingerSubadd.hellingerSq (κ k y) (η k y))) :
    HellingerSubadd.hellingerSq (HellingerSubadd.seqLaw κ n x₀) (HellingerSubadd.seqLaw η n x₀)
      ≤ ENNReal.ofReal (10 ^ 2 * Real.log n)
          * ∫⁻ x, HellingerSubadd.condHellingerSum κ η n x ∂(HellingerSubadd.seqLaw κ n x₀) := by
  unfold HellingerSubadd.seqLaw
  have hc := HSA.traj_claim κ η n hmeas n 0 (by simp) x₀ 1 1 zero_le_one zero_le_one
  have hD : ∫⁻ x, HellingerSubadd.condHellingerSum κ η n x ∂(Kernel.partialTraj κ 0 n x₀)
      = ENNReal.ofReal (HSA.Ca κ η n 0 x₀) := by
    rw [HSA.Ca, ENNReal.ofReal_toReal (HSA.D_ne_top κ η n 0 x₀), HSA.D, HSA.S_zero]
  have h0 := HSA.Ca_nonneg κ η n 0 x₀
  have hlog := HSA.const_le_log n hn
  rw [hD, HSA.hell_eq, ← ENNReal.ofReal_mul (by nlinarith)]
  apply ENNReal.ofReal_le_ofReal
  have hA := HSA.aff_le_one (Kernel.partialTraj κ 0 n x₀) (Kernel.partialTraj η 0 n x₀)
  nlinarith
