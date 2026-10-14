-- Prove2me | solution 1 for IntroMatrixConc.GaussianSeries.tail_integration
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T03:45:02.153784+00:00
-- url     : https://prove2.me/submissions/7dea0d47-cb44-434d-a394-60f411d9f258

import Mathlib
import Definitions.Def_TroppMatrixConcentration_ch4_scalar_laws
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator ENNReal
namespace TroppTailIntegration

lemma exponential_integral (K c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => K * Real.exp (-t / c)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, K * Real.exp (-t / c)) = K * c := by
  have he : (fun t : ℝ => K * Real.exp (-t / c)) =
      (fun t => K * Real.exp ((-c⁻¹) * t)) := by
    funext t
    congr 1
    congr 1
    ring
  rw [he]
  have hn : -c⁻¹ < 0 := neg_neg_of_pos (inv_pos.mpr hc)
  refine ⟨(integrableOn_exp_mul_Ioi hn 0).const_mul K, ?_⟩
  rw [integral_const_mul, integral_exp_mul_Ioi hn 0]
  simp [ne_of_gt hc]

lemma nonnegative_exp_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hm : Measurable f) (hn : ∀ ω, 0 ≤ f ω)
    (K c : ℝ) (hK : 0 ≤ K) (hc : 0 < c)
    (htail : ∀ t : ℝ, 0 < t → (μ {ω | t ≤ f ω}).toReal ≤ K * Real.exp (-t / c)) :
    Integrable f μ ∧ (∫ ω, f ω ∂μ) ≤ K * c := by
  have hnn : 0 ≤ᵐ[μ] f := Eventually.of_forall hn
  obtain ⟨hmajor, hvalue⟩ := exponential_integral K c hc
  have hmajnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun t => K * Real.exp (-t / c)) :=
    Eventually.of_forall (fun t => mul_nonneg hK (Real.exp_pos _).le)
  have hbound : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≤
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (K * Real.exp (-t / c)) := by
    rw [lintegral_eq_lintegral_meas_le μ hnn hm.aemeasurable]
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (mul_nonneg hK (Real.exp_pos _).le)).mpr
      (htail t ht)
  have hfin : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top hmajor.lintegral_lt_top.ne hbound
  have hi : Integrable f μ := (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hnn).mp hfin
  refine ⟨hi, ?_⟩
  have he := ENNReal.toReal_mono hmajor.lintegral_lt_top.ne hbound
  rw [← integral_eq_lintegral_of_nonneg_ae hnn hi.aestronglyMeasurable,
    ← integral_eq_lintegral_of_nonneg_ae hmajnn hmajor.aestronglyMeasurable, hvalue] at he
  exact he

lemma square_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω → ℝ) (hu : ∀ ω, 0 ≤ u ω)
    (K c : ℝ) (htail : ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ u ω}).toReal ≤ K * Real.exp (-(t ^ 2) / c)) :
    ∀ t : ℝ, 0 < t → (μ {ω | t ≤ u ω ^ 2}).toReal ≤ K * Real.exp (-t / c) := by
  intro t ht
  have he : {ω | t ≤ u ω ^ 2} = {ω | Real.sqrt t ≤ u ω} := by
    ext ω
    change t ≤ u ω ^ 2 ↔ Real.sqrt t ≤ u ω
    rw [Real.sqrt_le_iff]
    exact ⟨fun h => ⟨hu ω, h⟩, fun h => h.2⟩
  rw [he]
  simpa only [Real.sq_sqrt (le_of_lt ht)] using htail (Real.sqrt t) (Real.sqrt_nonneg t)

lemma split_square_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω → ℝ)
    (hm : Measurable u) (hu : ∀ ω, 0 ≤ u ω)
    (K c : ℝ) (hK : 0 ≤ K) (hc : 0 < c)
    (htail : ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ u ω}).toReal ≤ K * Real.exp (-(t ^ 2) / c))
    (a : ℝ) :
    Integrable (fun ω => u ω ^ 2) μ ∧
      (∫ ω, u ω ^ 2 ∂μ) ≤ a ^ 2 + c * K * Real.exp (-(a ^ 2) / c) := by
  have ht := square_tail μ u hu K c htail
  have hY := (nonnegative_exp_tail μ (fun ω => u ω ^ 2) (hm.pow_const 2)
    (fun ω => sq_nonneg _) K c hK hc ht).1
  let f : Ω → ℝ := fun ω => max (u ω ^ 2 - a ^ 2) 0
  have hfmeas : Measurable f := by unfold f; fun_prop
  have hfnn : ∀ ω, 0 ≤ f ω := fun ω => le_max_right _ _
  have hfTail : ∀ t : ℝ, 0 < t → (μ {ω | t ≤ f ω}).toReal ≤
      (K * Real.exp (-(a ^ 2) / c)) * Real.exp (-t / c) := by
    intro t htpos
    have he : {ω | t ≤ f ω} = {ω | a ^ 2 + t ≤ u ω ^ 2} := by
      ext ω
      change t ≤ max (u ω ^ 2 - a ^ 2) 0 ↔ a ^ 2 + t ≤ u ω ^ 2
      rw [le_max_iff]
      constructor
      · intro h
        rcases h with h | h <;> linarith
      · intro h
        exact Or.inl (by linarith)
    rw [he]
    have heexp : Real.exp (-(a ^ 2 + t) / c) =
        Real.exp (-(a ^ 2) / c) * Real.exp (-t / c) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hpos : 0 < a ^ 2 + t := by nlinarith [sq_nonneg a]
    have hh := ht (a ^ 2 + t) hpos
    rw [heexp] at hh
    simpa only [mul_assoc] using hh
  obtain ⟨hfi, hfb⟩ := nonnegative_exp_tail μ f hfmeas hfnn
    (K * Real.exp (-(a ^ 2) / c)) c (mul_nonneg hK (Real.exp_pos _).le) hc hfTail
  refine ⟨hY, ?_⟩
  have hdom : ∀ ω, u ω ^ 2 ≤ a ^ 2 + f ω := by
    intro ω
    have h := le_max_left (u ω ^ 2 - a ^ 2) 0
    change u ω ^ 2 ≤ a ^ 2 + max (u ω ^ 2 - a ^ 2) 0
    linarith
  have hi := integral_mono hY ((integrable_const (a ^ 2)).add hfi) hdom
  change (∫ ω, u ω ^ 2 ∂μ) ≤ ∫ ω, a ^ 2 + f ω ∂μ at hi
  rw [integral_add (f := fun _ => a ^ 2) (g := f) (integrable_const _) hfi] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  nlinarith

end TroppTailIntegration

open TroppTailIntegration

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂]
    (Z : Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (hMeas : Measurable Z)
    (hv : 0 < rectSecondMoment μ Z)
    (hTail : ∀ t : ℝ, 0 ≤ t →
      (μ {ω | t ≤ spectralNorm (Z ω)}).toReal ≤
        (d₁ + d₂ : ℕ) * Real.exp (-(t ^ 2) / (2 * rectSecondMoment μ Z)))
    (a : ℝ) (ha : 0 < a) :
    Integrable (fun ω => spectralNorm (Z ω) ^ 2) μ ∧
      (∫ ω, spectralNorm (Z ω) ^ 2 ∂μ) ≤
        a ^ 2 + 2 * rectSecondMoment μ Z * (d₁ + d₂ : ℕ) *
          Real.exp (-(a ^ 2) / (2 * rectSecondMoment μ Z)) := by
  exact split_square_bound μ (fun ω => ‖Z ω‖) hMeas.norm (fun ω => norm_nonneg _)
    (d₁ + d₂ : ℕ) (2 * rectSecondMoment μ Z) (by positivity) (by positivity) hTail a

#print axioms solution
