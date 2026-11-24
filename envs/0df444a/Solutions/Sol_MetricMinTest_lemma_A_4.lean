-- Prove2me | solution 1 for MetricMinTest.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:59:50.165129+00:00
-- url     : https://prove2.me/submissions/ab647773-20c6-4881-8157-01fb1003ff0b

import Mathlib
import Definitions.Def_MetricMinTest_signedBernoulli

open MeasureTheory

namespace MetricMinTestA4Aux

lemma withDensity_dirac_eq (f : ℝ → ENNReal) (hf : Measurable f) (x : ℝ) :
    (Measure.dirac x).withDensity f = f x • Measure.dirac x := by
  classical
  ext s hs
  rw [withDensity_apply _ hs, setLIntegral_dirac' hf hs]
  by_cases h : x ∈ s <;> simp [h, hs]

lemma isFinite_sB (w : ℝ) : IsFiniteMeasure (MetricMinTest.signedBernoulli w) := by
  constructor
  simp [MetricMinTest.signedBernoulli, ENNReal.add_lt_top]

/-- Binary Pinsker on `[3/8, 5/8]`. -/
lemma pinsker_binary (a b : ℝ) (ha0 : 3 / 8 ≤ a) (ha1 : a ≤ 5 / 8) (hb0 : 3 / 8 ≤ b)
    (hb1 : b ≤ 5 / 8) :
    2 * (a - b) ^ 2 ≤ a * (Real.log a - Real.log b) +
      (1 - a) * (Real.log (1 - a) - Real.log (1 - b)) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, φ = fun s => a * (Real.log a - Real.log s) +
      (1 - a) * (Real.log (1 - a) - Real.log (1 - s)) - 2 * (a - s) ^ 2 := ⟨_, rfl⟩
  have hderiv : ∀ s, 0 < s → s < 1 →
      HasDerivAt φ ((s - a) * (1 - 2 * s) ^ 2 / (s * (1 - s))) s := by
    intro s hs0 hs1
    rw [hφ]
    have h1 : HasDerivAt Real.log s⁻¹ s := Real.hasDerivAt_log hs0.ne'
    have h2 : HasDerivAt (fun x => Real.log (1 - x)) (-1 / (1 - s)) s :=
      ((hasDerivAt_id' s).const_sub 1).log (by linarith)
    have h3 : HasDerivAt (fun x => (a - x) ^ 2) (2 * (a - s) * (-1)) s := by
      have h0 : HasDerivAt (fun x => a - x) (-1) s := (hasDerivAt_id' s).const_sub a
      exact (h0.pow 2).congr_deriv (by norm_num)
    have := (((h1.const_sub (Real.log a)).const_mul a).add
      ((h2.const_sub (Real.log (1 - a))).const_mul (1 - a))).sub (h3.const_mul 2)
    have hs1' : (1 - s) ≠ 0 := by linarith
    refine this.congr_deriv ?_
    field_simp
    ring
  have hφa : φ a = 0 := by simp [hφ]
  have hcont : ∀ x, 3 / 8 ≤ x → x ≤ 5 / 8 → ContinuousAt φ x := fun x h0 h1 =>
    (hderiv x (by linarith) (by linarith)).continuousAt
  have key : φ a ≤ φ b := by
    rcases le_total a b with hab | hab
    · have hm : MonotoneOn φ (Set.Icc a b) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
        · intro x hx
          exact (hcont x (by linarith [hx.1]) (by linarith [hx.2])).continuousWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          exact (hderiv x (by linarith [hx.1]) (by linarith [hx.2])).hasDerivWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          apply div_nonneg
          · exact mul_nonneg (by linarith [hx.1]) (sq_nonneg _)
          · exact (mul_pos (by linarith [hx.1]) (by linarith [hx.2])).le
      exact hm ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
    · have hm : AntitoneOn φ (Set.Icc b a) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc b a)
        · intro x hx
          exact (hcont x (by linarith [hx.1]) (by linarith [hx.2])).continuousWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          exact (hderiv x (by linarith [hx.1]) (by linarith [hx.2])).hasDerivWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          apply div_nonpos_of_nonpos_of_nonneg
          · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (sq_nonneg _)
          · exact (mul_pos (by linarith [hx.1]) (by linarith [hx.2])).le
      exact hm ⟨le_refl b, hab⟩ ⟨hab, le_refl a⟩ hab
  have : φ b = a * (Real.log a - Real.log b) +
      (1 - a) * (Real.log (1 - a) - Real.log (1 - b)) - 2 * (a - b) ^ 2 := by rw [hφ]
  linarith

end MetricMinTestA4Aux

open MetricMinTestA4Aux in
theorem solution (u v : ℝ) (hu : u ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4))
    (hv : v ∈ Set.Icc (-1 / 4 : ℝ) (1 / 4)) :
    ENNReal.ofReal ((u - v) ^ 2 / 2) ≤
        InformationTheory.klDiv (MetricMinTest.signedBernoulli u)
          (MetricMinTest.signedBernoulli v) ∧
    InformationTheory.klDiv (MetricMinTest.signedBernoulli u)
          (MetricMinTest.signedBernoulli v) ≤
        ENNReal.ofReal ((u - v) ^ 2 / (1 - v ^ 2)) ∧
    (u - v) ^ 2 / (1 - v ^ 2) ≤ 16 / 15 * (u - v) ^ 2 ∧
    16 / 15 * (u - v) ^ 2 ≤ 2 * (u - v) ^ 2 := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hv
  have := isFinite_sB u
  have := isFinite_sB v
  set a := (1 + u) / 2 with ha
  set a' := (1 - u) / 2 with ha'
  set b := (1 + v) / 2 with hb
  set b' := (1 - v) / 2 with hb'
  have hapos : 0 < a := by rw [ha]; linarith
  have ha'pos : 0 < a' := by rw [ha']; linarith
  have hbpos : 0 < b := by rw [hb]; linarith
  have hb'pos : 0 < b' := by rw [hb']; linarith
  set g : ℝ → ENNReal := fun x => if x = 1 then ENNReal.ofReal (a / b)
    else ENNReal.ofReal (a' / b') with hg
  have hgm : Measurable g :=
    Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const
  have hμ : MetricMinTest.signedBernoulli u = (MetricMinTest.signedBernoulli v).withDensity g := by
    simp only [MetricMinTest.signedBernoulli]
    rw [withDensity_add_measure, withDensity_smul_measure, withDensity_smul_measure,
      withDensity_dirac_eq g hgm, withDensity_dirac_eq g hgm, smul_smul, smul_smul]
    have h1 : g 1 = ENNReal.ofReal (a / b) := by simp [hg]
    have h2 : g (-1) = ENNReal.ofReal (a' / b') := by
      simp only [hg]; rw [if_neg (by norm_num)]
    rw [h1, h2, ← ENNReal.ofReal_mul hbpos.le, ← ENNReal.ofReal_mul hb'pos.le]
    rw [show b * (a / b) = a by field_simp, show b' * (a' / b') = a' by field_simp]
  have hac : MetricMinTest.signedBernoulli u ≪ MetricMinTest.signedBernoulli v := by
    rw [hμ]; exact withDensity_absolutelyContinuous _ _
  have hr : (MetricMinTest.signedBernoulli u).rnDeriv (MetricMinTest.signedBernoulli v)
      =ᵐ[MetricMinTest.signedBernoulli v] g := by
    rw [hμ]; exact Measure.rnDeriv_withDensity _ hgm
  set K : ℝ := b * InformationTheory.klFun (a / b) + b' * InformationTheory.klFun (a' / b')
    with hK
  have hKl : InformationTheory.klDiv (MetricMinTest.signedBernoulli u)
      (MetricMinTest.signedBernoulli v) = ENNReal.ofReal K := by
    have hint : ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun
        ((MetricMinTest.signedBernoulli u).rnDeriv (MetricMinTest.signedBernoulli v) x).toReal)
        ∂(MetricMinTest.signedBernoulli v) =
        ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (g x).toReal)
        ∂(MetricMinTest.signedBernoulli v) :=
      lintegral_congr_ae (hr.mono fun x hx =>
        congrArg (fun r => ENNReal.ofReal (InformationTheory.klFun r.toReal)) hx)
    rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac, hint]
    have hsv : MetricMinTest.signedBernoulli v = ENNReal.ofReal b • Measure.dirac 1 +
        ENNReal.ofReal b' • Measure.dirac (-1) := rfl
    rw [hsv, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac, lintegral_dirac]
    have h1 : g 1 = ENNReal.ofReal (a / b) := by simp [hg]
    have h2 : g (-1) = ENNReal.ofReal (a' / b') := by
      simp only [hg]; rw [if_neg (by norm_num)]
    rw [h1, h2, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
      smul_eq_mul, smul_eq_mul, ← ENNReal.ofReal_mul hbpos.le, ← ENNReal.ofReal_mul hb'pos.le,
      ← ENNReal.ofReal_add]
    · exact mul_nonneg hbpos.le (InformationTheory.klFun_nonneg (by positivity))
    · exact mul_nonneg hb'pos.le (InformationTheory.klFun_nonneg (by positivity))
  have hKform : K = a * (Real.log a - Real.log b) + a' * (Real.log a' - Real.log b') := by
    rw [hK, InformationTheory.klFun_apply, InformationTheory.klFun_apply,
      Real.log_div hapos.ne' hbpos.ne', Real.log_div ha'pos.ne' hb'pos.ne']
    field_simp
    rw [ha, ha', hb, hb']
    ring
  have hv2 : (15 / 16 : ℝ) ≤ 1 - v ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hKl]
    apply ENNReal.ofReal_le_ofReal
    have hP := pinsker_binary a b (by rw [ha]; linarith) (by rw [ha]; linarith)
      (by rw [hb]; linarith) (by rw [hb]; linarith)
    have e1 : 1 - a = a' := by rw [ha, ha']; ring
    have e2 : 1 - b = b' := by rw [hb, hb']; ring
    rw [e1, e2] at hP
    rw [hKform]
    have : (u - v) ^ 2 / 2 = 2 * (a - b) ^ 2 := by rw [ha, hb]; ring
    linarith
  · rw [hKl]
    apply ENNReal.ofReal_le_ofReal
    rw [hKform, ← Real.log_div hapos.ne' hbpos.ne', ← Real.log_div ha'pos.ne' hb'pos.ne']
    have l1 := Real.log_le_sub_one_of_pos (div_pos hapos hbpos)
    have l2 := Real.log_le_sub_one_of_pos (div_pos ha'pos hb'pos)
    have s1 : a * Real.log (a / b) ≤ a * (a / b - 1) := mul_le_mul_of_nonneg_left l1 hapos.le
    have s2 : a' * Real.log (a' / b') ≤ a' * (a' / b' - 1) :=
      mul_le_mul_of_nonneg_left l2 ha'pos.le
    have hsum : a * (a / b - 1) + a' * (a' / b' - 1) = (u - v) ^ 2 / (1 - v ^ 2) := by
      rw [ha, ha', hb, hb']
      have : (1 - v ^ 2) ≠ 0 := by linarith
      have : (1 + v) ≠ 0 := by linarith
      have : (1 - v) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  · rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg (u - v), mul_nonneg (sq_nonneg (u - v)) (sub_nonneg.mpr hv2)]
  · nlinarith [sq_nonneg (u - v)]
