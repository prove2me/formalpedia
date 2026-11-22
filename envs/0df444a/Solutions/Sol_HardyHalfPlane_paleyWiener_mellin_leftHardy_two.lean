-- Prove2me | solution 1 for HardyHalfPlane.paleyWiener_mellin_leftHardy_two
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:23:21.853524+00:00
-- url     : https://prove2.me/submissions/ac197113-0b13-40b4-8a07-009b9984c9d8

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy
import Theorems.Thm_HardyHalfPlane_paleyWiener_laplace_memLeftHardy_two
import Theorems.Thm_HardyHalfPlane_paleyWiener_exists_laplace_of_memLeftHardy_two

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace Sol_HardyHalfPlane_paleyWiener_mellin_leftHardy_two

open Set

lemma image_exp_univ : Real.exp '' univ = Ioi 0 := by
  rw [image_univ, Real.range_exp]

lemma cpow_exp (x : ℝ) (s : ℂ) : ((Real.exp x : ℝ) : ℂ) ^ s = Complex.exp (s * x) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]

/-- Mellin transform after the substitution `t = e^x`. -/
lemma mellin_eq (u : ℝ → ℂ) (s : ℂ) :
    mellin u s = ∫ x : ℝ, u (Real.exp x) * Complex.exp (s * x) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t : ℝ => ((t : ℂ) ^ (s - 1)) • u t)
  rw [image_exp_univ, Measure.restrict_univ] at h
  rw [mellin, h]
  congr 1
  ext x
  rw [abs_of_pos (Real.exp_pos x), cpow_exp, Complex.real_smul, smul_eq_mul, Complex.ofReal_exp,
    ← mul_assoc, ← Complex.exp_add, mul_comm]
  congr 2
  ring

lemma mellinConvergent_iff (u : ℝ → ℂ) (s : ℂ) :
    MellinConvergent u s ↔ Integrable (fun x : ℝ => u (Real.exp x) * Complex.exp (s * x)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t : ℝ => ((t : ℂ) ^ (s - 1)) • u t)
  rw [image_exp_univ, integrableOn_univ] at h
  unfold MellinConvergent
  rw [h]
  refine integrable_congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [abs_of_pos (Real.exp_pos x), cpow_exp, Complex.real_smul, smul_eq_mul, Complex.ofReal_exp,
    ← mul_assoc, ← Complex.exp_add, mul_comm]
  congr 2
  ring

lemma enorm_ofReal_exp (y : ℝ) : ‖((Real.exp y : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (Real.exp y) := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos y).le]

lemma lintegral_eq (u : ℝ → ℂ) (b : ℝ) :
    ∫⁻ t in Ioi 0, ‖u t‖ₑ ^ 2 * ENNReal.ofReal (t ^ (2 * b - 1)) =
      ∫⁻ x : ℝ, ‖u (Real.exp x) * ((Real.exp (b * x) : ℝ) : ℂ)‖ₑ ^ 2 := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t : ℝ => ‖u t‖ₑ ^ 2 * ENNReal.ofReal (t ^ (2 * b - 1)))
  rw [image_exp_univ, Measure.restrict_univ] at h
  rw [h]
  congr 1
  ext x
  rw [enorm_mul, mul_pow, enorm_ofReal_exp,
    ← ENNReal.ofReal_pow (Real.exp_pos _).le, abs_of_pos (Real.exp_pos x), mul_left_comm,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_nat_mul]
  congr 3
  push_cast
  ring

lemma volume_preimage_exp {N : Set ℝ} (hN : volume N = 0) : volume (Real.exp ⁻¹' N) = 0 := by
  have : Real.exp ⁻¹' N = Real.log '' (N ∩ Ioi 0) := by
    ext x
    constructor
    · intro hx
      exact ⟨Real.exp x, ⟨hx, Real.exp_pos x⟩, Real.log_exp x⟩
    · rintro ⟨t, ⟨htN, ht0⟩, rfl⟩
      simpa [mem_preimage, Real.exp_log ht0] using htN
  rw [this]
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null inter_subset_left hN)
  exact Real.differentiableOn_log.mono (fun t ht => ne_of_gt ht.2)

lemma qmp_exp : Measure.QuasiMeasurePreserving Real.exp volume (volume.restrict (Ioi 0)) := by
  refine ⟨Real.measurable_exp, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply Real.measurable_exp hs]
  rw [Measure.restrict_apply hs] at h0
  have : Real.exp ⁻¹' s = Real.exp ⁻¹' (s ∩ Ioi 0) := by
    ext x; simp [Real.exp_pos x]
  rw [this]
  exact volume_preimage_exp h0

lemma eLpNorm_two_eq (f : ℝ → ℂ) :
    eLpNorm f 2 volume = (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp

lemma leftHardyNorm_comp_sub (Φ : ℂ → ℂ) (a c : ℝ) (p : ℝ≥0∞) :
    HardyHalfPlane.leftHardyNorm (fun s => Φ (s - c)) a p =
      HardyHalfPlane.leftHardyNorm Φ (a - c) p := by
  unfold HardyHalfPlane.leftHardyNorm
  apply le_antisymm
  · refine iSup₂_le fun σ hσ => ?_
    refine le_iSup₂_of_le (σ - c) (by linarith) (le_of_eq ?_)
    have h : ∀ y : ℝ, (σ : ℂ) + (y : ℂ) * Complex.I - (c : ℂ) =
        ((σ - c : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
      intro y; push_cast; ring
    simp only [h]
  · refine iSup₂_le fun σ hσ => ?_
    refine le_iSup₂_of_le (σ + c) (by linarith) (le_of_eq ?_)
    have h : ∀ y : ℝ, ((σ + c : ℝ) : ℂ) + (y : ℂ) * Complex.I - (c : ℂ) =
        (σ : ℂ) + (y : ℂ) * Complex.I := by
      intro y; push_cast; ring
    simp only [h]

lemma differentiableOn_comp_sub (Φ : ℂ → ℂ) (a c : ℝ)
    (h : DifferentiableOn ℂ Φ {s : ℂ | s.re < a - c}) :
    DifferentiableOn ℂ (fun s => Φ (s - c)) {s : ℂ | s.re < a} := by
  refine h.comp (differentiableOn_id.sub_const _) ?_
  intro s hs
  simp only [mem_ofPred_eq, Complex.sub_re, Complex.ofReal_re] at hs ⊢
  linarith

lemma memLeftHardy_comp_sub (Φ : ℂ → ℂ) (a c : ℝ) (p : ℝ≥0∞)
    (h : HardyHalfPlane.MemLeftHardy Φ (a - c) p) :
    HardyHalfPlane.MemLeftHardy (fun s => Φ (s - c)) a p :=
  ⟨differentiableOn_comp_sub Φ a c h.1, by rw [leftHardyNorm_comp_sub]; exact h.2⟩

end Sol_HardyHalfPlane_paleyWiener_mellin_leftHardy_two

open Set Sol_HardyHalfPlane_paleyWiener_mellin_leftHardy_two in
theorem solution (b : ℝ) :
    (∀ u : ℝ → ℂ, AEStronglyMeasurable u (volume.restrict (Set.Ioi 0)) →
      (∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioo 0 1 → u t = 0) →
      (∫⁻ t in Set.Ioi 0, ‖u t‖ₑ ^ 2 * ENNReal.ofReal (t ^ (2 * b - 1))) < ⊤ →
      (∀ s : ℂ, s.re < b → MellinConvergent u s) ∧
      HardyHalfPlane.MemLeftHardy (mellin u) b 2 ∧
      HardyHalfPlane.leftHardyNorm (mellin u) b 2 =
        ENNReal.ofReal (Real.sqrt (2 * Real.pi)) *
          (∫⁻ t in Set.Ioi 0, ‖u t‖ₑ ^ 2 * ENNReal.ofReal (t ^ (2 * b - 1))) ^ (1 / 2 : ℝ)) ∧
    (∀ Φ : ℂ → ℂ, HardyHalfPlane.MemLeftHardy Φ b 2 →
      ∃ u : ℝ → ℂ, AEStronglyMeasurable u (volume.restrict (Set.Ioi 0)) ∧
        (∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioo 0 1 → u t = 0) ∧
        (∫⁻ t in Set.Ioi 0, ‖u t‖ₑ ^ 2 * ENNReal.ofReal (t ^ (2 * b - 1))) < ⊤ ∧
        ∀ s : ℂ, s.re < b → Φ s = mellin u s) := by
  constructor
  · intro u hu hu0 hfin
    obtain ⟨f, hf_def⟩ : ∃ f : ℝ → ℂ,
        f = fun x => u (Real.exp x) * ((Real.exp (b * x) : ℝ) : ℂ) := ⟨_, rfl⟩
    have hfm : AEStronglyMeasurable f volume := by
      have h1 : AEStronglyMeasurable (fun x => u (Real.exp x)) volume :=
        hu.comp_quasiMeasurePreserving qmp_exp
      rw [hf_def]
      exact h1.mul (Continuous.aestronglyMeasurable (by fun_prop))
    have hfL : ∫⁻ x, ‖f x‖ₑ ^ 2 =
        ∫⁻ t in Ioi 0, ‖u t‖ₑ ^ 2 * ENNReal.ofReal (t ^ (2 * b - 1)) := by
      rw [hf_def]; exact (lintegral_eq u b).symm
    have hfe : eLpNorm f 2 volume =
        (∫⁻ t in Ioi 0, ‖u t‖ₑ ^ 2 * ENNReal.ofReal (t ^ (2 * b - 1))) ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_two_eq, hfL]
    have hf2 : MemLp f 2 volume :=
      ⟨hfm, by rw [hfe]; exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne⟩
    have hf0 : ∀ᵐ x : ℝ ∂volume, x < 0 → f x = 0 := by
      have := qmp_exp.ae (ae_restrict_of_ae hu0)
      filter_upwards [this] with x hx hx0
      rw [hf_def]
      simp only [hx ⟨Real.exp_pos x, Real.exp_lt_one_iff.mpr hx0⟩, zero_mul]
    obtain ⟨hint, hmem, hnorm⟩ := HardyHalfPlane.paleyWiener_laplace_memLeftHardy_two f hf2 hf0
    have hpt : ∀ s : ℂ, ∀ x : ℝ,
        f x * Complex.exp ((s - b) * x) = u (Real.exp x) * Complex.exp (s * x) := by
      intro s x
      rw [hf_def]
      simp only
      rw [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    have hM : mellin u = fun s => (fun w : ℂ => ∫ x : ℝ, f x * Complex.exp (w * x)) (s - b) := by
      funext s
      rw [mellin_eq]
      simp only [hpt]
    refine ⟨fun s hs => ?_, ?_, ?_⟩
    · rw [mellinConvergent_iff]
      have := hint (s - b) (by simp only [Complex.sub_re, Complex.ofReal_re]; linarith)
      simpa only [hpt] using this
    · rw [hM]
      exact memLeftHardy_comp_sub (fun w : ℂ => ∫ x : ℝ, f x * Complex.exp (w * x)) b b 2
        (by rw [sub_self]; exact hmem)
    · rw [hM, leftHardyNorm_comp_sub (fun w : ℂ => ∫ x : ℝ, f x * Complex.exp (w * x)) b b 2,
        sub_self, hnorm, hfe]
  · intro Φ hΦ
    have hΨ : HardyHalfPlane.MemLeftHardy (fun s => Φ (s - ((-b : ℝ) : ℂ))) 0 2 := by
      apply memLeftHardy_comp_sub
      rw [zero_sub, neg_neg]
      exact hΦ
    obtain ⟨f, hf2, hf0, hrep⟩ :=
      HardyHalfPlane.paleyWiener_exists_laplace_of_memLeftHardy_two _ hΨ
    obtain ⟨g, hg_def⟩ : ∃ g : ℝ → ℂ, g = (Ici (0 : ℝ)).indicator (hf2.1.mk f) := ⟨_, rfl⟩
    have hgm : Measurable g := by
      rw [hg_def]
      exact (hf2.1.stronglyMeasurable_mk.indicator measurableSet_Ici).measurable
    have hgf : g =ᵐ[volume] f := by
      filter_upwards [hf2.1.ae_eq_mk, hf0] with x h1 h2
      rw [hg_def]
      by_cases hx : 0 ≤ x
      · rw [indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx), h1]
      · rw [indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx), h2 (lt_of_not_ge hx)]
    have hg0 : ∀ x : ℝ, x < 0 → g x = 0 := by
      intro x hx
      rw [hg_def, indicator_of_notMem (show x ∉ Ici (0 : ℝ) from not_le.mpr hx)]
    obtain ⟨u, hu_def⟩ : ∃ u : ℝ → ℂ,
        u = fun t => g (Real.log t) * ((t ^ (-b) : ℝ) : ℂ) := ⟨_, rfl⟩
    have hum : Measurable u := by
      rw [hu_def]
      exact (hgm.comp Real.measurable_log).mul
        (Complex.measurable_ofReal.comp (measurable_id.pow_const _))
    have hux : ∀ x : ℝ, u (Real.exp x) * ((Real.exp (b * x) : ℝ) : ℂ) = g x := by
      intro x
      rw [hu_def]
      simp only [Real.log_exp]
      rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_mul, ← Real.exp_add]
      have : x * -b + b * x = 0 := by ring
      rw [this, Real.exp_zero, Complex.ofReal_one, mul_one]
    have hux2 : ∀ s : ℂ, ∀ x : ℝ,
        u (Real.exp x) * Complex.exp (s * x) = g x * Complex.exp ((s - b) * x) := by
      intro s x
      rw [hu_def]
      simp only [Real.log_exp]
      rw [← Real.exp_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    have hLg : ∫⁻ x, ‖g x‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 :=
      lintegral_congr_ae (hgf.mono fun x hx => by simp only [hx])
    refine ⟨u, hum.aestronglyMeasurable, ?_, ?_, ?_⟩
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [hu_def]
      simp only
      rw [hg0 _ (Real.log_neg ht.1 ht.2), zero_mul]
    · rw [lintegral_eq u b]
      simp only [hux]
      rw [hLg]
      have h := hf2.2
      rw [eLpNorm_two_eq] at h
      exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h
    · intro s hs
      have h1 := hrep (s + ((-b : ℝ) : ℂ))
        (by simp only [Complex.add_re, Complex.ofReal_re]; linarith)
      have h2 : s + ((-b : ℝ) : ℂ) - ((-b : ℝ) : ℂ) = s := by ring
      rw [h2] at h1
      rw [h1, mellin_eq]
      simp only [hux2]
      refine integral_congr_ae ?_
      filter_upwards [hgf] with x hx
      rw [hx]
      congr 2
      push_cast
      ring
