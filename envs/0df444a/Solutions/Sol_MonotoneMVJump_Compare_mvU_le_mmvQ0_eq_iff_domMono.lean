-- Prove2me | solution 1 for MonotoneMVJump.Compare.mvU_le_mmvQ0_eq_iff_domMono
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:51:53.72399+00:00
-- url     : https://prove2.me/submissions/4c6a2eef-7b23-428e-a44b-cee3487ebce0

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_PDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MMVJAux

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The key quadratic identity. -/
lemma key_identity {μ : Measure Ω} [IsProbabilityMeasure μ] {θ : ℝ} (hθ : 0 < θ)
    {X f : Ω → ℝ} (hX : MemLp X 2 μ) (hf : MemLp f 2 μ) (hf1 : ∫ ω, f ω ∂μ = 1) :
    ∫ ω, f ω * X ω ∂μ + 1 / (2 * θ) * (∫ ω, f ω ^ 2 ∂μ - 1)
      = (∫ ω, X ω ∂μ - θ / 2 * variance X μ)
        + 1 / (2 * θ) * ∫ ω, (f ω - (1 - θ * (X ω - ∫ ω', X ω' ∂μ))) ^ 2 ∂μ := by
  set m := ∫ ω', X ω' ∂μ with hm
  have hXi : Integrable X μ := hX.integrable one_le_two
  have hfi : Integrable f μ := hf.integrable one_le_two
  have hfX : Integrable (fun ω => f ω * X ω) μ := hf.integrable_mul hX
  have hf2 : Integrable (fun ω => f ω ^ 2) μ := hf.integrable_sq
  have hXm : MemLp (fun ω => X ω - m) 2 μ := hX.sub (memLp_const m)
  have hXm2 : Integrable (fun ω => (X ω - m) ^ 2) μ := hXm.integrable_sq
  have hvar : variance X μ = ∫ ω, (X ω - m) ^ 2 ∂μ :=
    variance_eq_integral hX.aestronglyMeasurable.aemeasurable
  have hexp : ∀ ω, (f ω - (1 - θ * (X ω - m))) ^ 2
      = (f ω ^ 2 + 2 * θ * (f ω * X ω)) + ((-2 - 2 * θ * m) * f ω + (-2 * θ) * X ω)
        + (θ ^ 2 * (X ω - m) ^ 2 + (1 + 2 * θ * m)) := by
    intro ω; ring
  have hI : ∫ ω, (f ω - (1 - θ * (X ω - m))) ^ 2 ∂μ
      = (∫ ω, f ω ^ 2 ∂μ + 2 * θ * ∫ ω, f ω * X ω ∂μ)
        + ((-2 - 2 * θ * m) * ∫ ω, f ω ∂μ + (-2 * θ) * m)
        + (θ ^ 2 * ∫ ω, (X ω - m) ^ 2 ∂μ + (1 + 2 * θ * m)) := by
    simp_rw [hexp]
    rw [integral_add, integral_add, integral_add, integral_add, integral_add]
    · rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const]
      simp [hm]
    all_goals first
      | exact hf2
      | exact hfX.const_mul _
      | exact hfi.const_mul _
      | exact hXi.const_mul _
      | exact hXm2.const_mul _
      | exact integrable_const _
      | exact (hfi.const_mul _).add (hXi.const_mul _)
      | exact (hXm2.const_mul _).add (integrable_const _)
      | exact hf2.add (hfX.const_mul _)
      | exact (hf2.add (hfX.const_mul _)).add ((hfi.const_mul _).add (hXi.const_mul _))
  rw [hI, hvar, hf1]
  field_simp
  ring


/-- Value of the MMV objective at a measure `Q ∈ 𝒬₀`. -/
lemma val_eq {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q] {θ : ℝ}
    (hθ : 0 < θ) {X : Ω → ℝ} (hX : MemLp X 2 μ) (hQ : Q ≪ μ)
    (h2 : ∫⁻ ω, Q.rnDeriv μ ω ^ 2 ∂μ < ⊤) :
    MemLp (fun ω => (Q.rnDeriv μ ω).toReal) 2 μ ∧
    (∫ ω, X ω ∂Q) + 1 / (2 * θ) * ((∫⁻ ω, Q.rnDeriv μ ω ^ 2 ∂μ).toReal - 1)
      = (∫ ω, X ω ∂μ - θ / 2 * variance X μ)
        + 1 / (2 * θ) * ∫ ω, ((Q.rnDeriv μ ω).toReal - (1 - θ * (X ω - ∫ ω', X ω' ∂μ))) ^ 2 ∂μ := by
  set f : Ω → ℝ := fun ω => (Q.rnDeriv μ ω).toReal with hfdef
  have hrm : AEMeasurable (fun ω => Q.rnDeriv μ ω ^ 2) μ :=
    ((Measure.measurable_rnDeriv Q μ).pow_const 2).aemeasurable
  have hsq : ∀ ω, f ω ^ 2 = (Q.rnDeriv μ ω ^ 2).toReal := fun ω => by
    simp [hfdef, ENNReal.toReal_pow]
  have hf2i : Integrable (fun ω => f ω ^ 2) μ := by
    simp_rw [hsq]; exact integrable_toReal_of_lintegral_ne_top hrm h2.ne
  have hfm : AEStronglyMeasurable f μ :=
    (Measure.measurable_rnDeriv Q μ).ennreal_toReal.aestronglyMeasurable
  have hf : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfm).2 hf2i
  have hf1 : ∫ ω, f ω ∂μ = 1 := by
    rw [hfdef, Measure.integral_toReal_rnDeriv hQ]; simp
  have hQX : ∫ ω, X ω ∂Q = ∫ ω, f ω * X ω ∂μ := by
    rw [← integral_rnDeriv_smul hQ]; rfl
  have hlt : ∀ᵐ ω ∂μ, Q.rnDeriv μ ω ^ 2 < ⊤ := by
    filter_upwards [Measure.rnDeriv_lt_top Q μ] with ω hω
    exact ENNReal.pow_lt_top hω
  have hL : (∫⁻ ω, Q.rnDeriv μ ω ^ 2 ∂μ).toReal = ∫ ω, f ω ^ 2 ∂μ := by
    simp_rw [hsq]; rw [integral_toReal hrm hlt]
  refine ⟨hf, ?_⟩
  rw [hQX, hL]
  exact key_identity hθ hX hf hf1


lemma sq_min_le {a b : ℝ} (ha : 0 ≤ a) : (min b 0) ^ 2 ≤ (a - b) ^ 2 := by
  rcases le_total b 0 with hb | hb
  · rw [min_eq_left hb]; nlinarith
  · rw [min_eq_right hb]; simpa using sq_nonneg (a - b)

end MMVJAux

open MMVJAux

open MonotoneMVJump.Compare

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω)
    (hP : IsProbabilityMeasure M.P) (θ : ℝ) (hθ : 0 < θ) (X : Ω → ℝ) (hX : MemLp X 2 M.P) :
    ((M.mvU θ X : ℝ) : EReal) ≤ M.mmvQ0 θ X ∧
      (((M.mvU θ X : ℝ) : EReal) = M.mmvQ0 θ X ↔ InDomMono M.P θ X) := by
  set μ := M.P with hμ
  set m := ∫ ω', X ω' ∂μ with hm
  set fs : Ω → ℝ := fun ω => 1 - θ * (X ω - m) with hfsdef
  have hc : 0 < 1 / (2 * θ) := by positivity
  have hfs : MemLp fs 2 μ := (memLp_const 1).sub ((hX.sub (memLp_const m)).const_mul θ)
  -- general lower bound with a margin
  have hlow : ∀ δ : ℝ, (∀ Q : Measure Ω, IsProbabilityMeasure Q → Q ≪ μ →
      ∫⁻ ω, Q.rnDeriv μ ω ^ 2 ∂μ < ⊤ →
        δ ≤ ∫ ω, ((Q.rnDeriv μ ω).toReal - fs ω) ^ 2 ∂μ) →
      (((M.mvU θ X + 1 / (2 * θ) * δ : ℝ)) : EReal) ≤ M.mmvQ0 θ X := by
    intro δ hδ
    unfold Market.mmvQ0
    refine le_iInf₂ fun Q hQ => ?_
    obtain ⟨hQp, hQP, h2⟩ := hQ
    have := hQp
    rw [EReal.coe_le_coe_iff, (val_eq hθ hX hQP h2).2]
    have := hδ Q hQp hQP h2
    unfold Market.mvU
    rw [← hμ]
    have : 1 / (2 * θ) * δ ≤ 1 / (2 * θ) * ∫ ω, ((Q.rnDeriv μ ω).toReal - fs ω) ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_left this hc.le
    simpa [hfsdef, hm] using this
  have hle : ((M.mvU θ X : ℝ) : EReal) ≤ M.mmvQ0 θ X := by
    have := hlow 0 (fun Q _ _ _ => integral_nonneg fun ω => sq_nonneg _)
    simpa using this
  refine ⟨hle, ⟨fun heq => ?_, fun hdom => ?_⟩⟩
  · -- strictness when outside the domain of monotonicity
    by_contra hnd
    have hbad : μ {ω | ¬ (X ω - m ≤ 1 / θ)} ≠ 0 := by
      intro h0
      exact hnd ⟨hX, ae_iff.2 h0⟩
    set g : Ω → ℝ := fun ω => (min (fs ω) 0) ^ 2 with hgdef
    have hgi : Integrable g μ := by
      refine Integrable.mono' hfs.integrable_sq ?_ (Eventually.of_forall fun ω => ?_)
      · exact (hfs.aestronglyMeasurable.inf aestronglyMeasurable_const).pow 2
      · simp only [hgdef, Real.norm_eq_abs, abs_pow, sq_abs]
        rcases le_total (fs ω) 0 with hb | hb
        · rw [min_eq_left hb]
        · rw [min_eq_right hb]; simpa using sq_nonneg (fs ω)
    have hgpos : 0 < ∫ ω, g ω ∂μ := by
      rw [integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _) hgi]
      refine lt_of_lt_of_le (pos_iff_ne_zero.2 hbad) (measure_mono fun ω hω => ?_)
      simp only [Set.mem_ofPred_eq, not_le] at hω
      have h1 : fs ω < 0 := by
        have : θ * (1 / θ) < θ * (X ω - m) := mul_lt_mul_of_pos_left hω hθ
        rw [mul_one_div_cancel hθ.ne'] at this
        simp only [hfsdef]; linarith
      simp only [Function.mem_support, min_eq_left h1.le]
      exact pow_ne_zero _ h1.ne
    have := hlow (∫ ω, g ω ∂μ) (fun Q hQp hQP h2 => by
      have := hQp
      have hfQ := (val_eq hθ hX hQP h2).1
      exact integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
        (hfQ.sub hfs).integrable_sq
        (Eventually.of_forall fun ω => sq_min_le ENNReal.toReal_nonneg))
    rw [← heq, EReal.coe_le_coe_iff] at this
    have : 0 < 1 / (2 * θ) * ∫ ω, g ω ∂μ := mul_pos hc hgpos
    linarith
  · -- equality inside the domain of monotonicity
    refine le_antisymm hle ?_
    have hfs0 : 0 ≤ᵐ[μ] fs := by
      filter_upwards [hdom.2] with ω hω
      have : θ * (X ω - m) ≤ θ * (1 / θ) := mul_le_mul_of_nonneg_left hω hθ.le
      rw [mul_one_div_cancel hθ.ne'] at this
      simp only [Pi.zero_apply, hfsdef]; linarith
    have hfsi : Integrable fs μ := hfs.integrable one_le_two
    have hfs1 : ∫ ω, fs ω ∂μ = 1 := by
      have hXi : Integrable X μ := hX.integrable one_le_two
      have h1 : Integrable (fun ω => θ * (X ω - m)) μ :=
        (hXi.sub (integrable_const m)).const_mul θ
      have h2 : Integrable (fun ω => X ω - m) μ := hXi.sub (integrable_const m)
      simp only [hfsdef]
      rw [integral_sub (integrable_const _) h1, integral_const_mul, integral_sub hXi (integrable_const _)]
      simp [hm]
    have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (fs ω)) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable hfs.aestronglyMeasurable.aemeasurable
    set Q := μ.withDensity (fun ω => ENNReal.ofReal (fs ω)) with hQdef
    have hQp : IsProbabilityMeasure Q := by
      constructor
      rw [hQdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← ofReal_integral_eq_lintegral_ofReal hfsi hfs0, hfs1, ENNReal.ofReal_one]
    have hQP : Q ≪ μ := withDensity_absolutelyContinuous _ _
    have hrn := Measure.rnDeriv_withDensity₀ μ hmeas
    have h2 : ∫⁻ ω, Q.rnDeriv μ ω ^ 2 ∂μ < ⊤ := by
      have : ∫⁻ ω, Q.rnDeriv μ ω ^ 2 ∂μ = ∫⁻ ω, ENNReal.ofReal (fs ω ^ 2) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hrn, hfs0] with ω hω h0
        rw [hQdef, hω, ENNReal.ofReal_pow h0]
      rw [this]
      exact hfs.integrable_sq.lintegral_lt_top
    have := hQp
    have hv := (val_eq hθ hX hQP h2).2
    have hz : ∫ ω, ((Q.rnDeriv μ ω).toReal - (1 - θ * (X ω - ∫ ω', X ω' ∂μ))) ^ 2 ∂μ = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hrn, hfs0] with ω hω h0
      rw [hQdef, hω, ENNReal.toReal_ofReal h0]
      simp [hfsdef, hm]
    unfold Market.mmvQ0
    refine (iInf₂_le Q ⟨hQp, hQP, h2⟩).trans_eq ?_
    rw [hv, hz]
    unfold Market.mvU
    simp [hμ]
