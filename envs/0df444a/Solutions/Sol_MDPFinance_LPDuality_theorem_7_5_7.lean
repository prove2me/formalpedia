-- Prove2me | solution 1 for MDPFinance.LPDuality.theorem_7_5_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:11:27.831644+00:00
-- url     : https://prove2.me/submissions/0afc0ca1-d0d5-4f5e-89c6-b9bbde5ce4e1

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_LP

open MeasureTheory ProbabilityTheory
open MDPFinance.LPDuality

namespace LP757Aux

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

theorem ae_mem_D (M : MarkovDecisionModel E A) (b : E → ℝ) (hb1 : ∀ x, 1 ≤ b x)
    (μ : Measure (E × A)) (hμ : μ ∈ Mb M b) : ∀ᵐ xa ∂μ, xa ∈ M.D := by
  have hfin : μ Set.univ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hμ.2.ne ?_
    calc μ Set.univ = ∫⁻ _, 1 ∂μ := by simp
      _ ≤ ∫⁻ xa, ENNReal.ofReal (b xa.1) ∂μ := by
        apply lintegral_mono; intro xa
        simpa using ENNReal.ofReal_le_ofReal (hb1 xa.1)
  rw [ae_iff]
  have : {a | ¬ a ∈ M.D} = M.Dᶜ := rfl
  rw [this, measure_compl M.hD_meas (ne_top_of_le_ne_top hfin (measure_mono (Set.subset_univ _))),
    hμ.1, tsub_self]

theorem integrable_of_bound (M : MarkovDecisionModel E A) (b : E → ℝ) (hbm : Measurable b)
    (hb0 : ∀ x, 0 ≤ b x) (hb1 : ∀ x, 1 ≤ b x)
    (μ : Measure (E × A)) (hμ : μ ∈ Mb M b) (f : E × A → ℝ) (hf : AEStronglyMeasurable f μ)
    (C : ℝ) (hC : ∀ xa ∈ M.D, |f xa| ≤ C * b xa.1) : Integrable f μ := by
  have hbI : Integrable (fun xa : E × A => b xa.1) μ :=
    ⟨(hbm.comp measurable_fst).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => hb0 _)).2 hμ.2⟩
  refine (hbI.const_mul C).mono' hf ?_
  filter_upwards [ae_mem_D M b hb1 μ hμ] with xa hxa
  simpa [Real.norm_eq_abs] using hC xa hxa

theorem int_bound (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (v : E → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hv : ∀ x, |v x| ≤ c * b x) (xa : E × A) (hxa : xa ∈ M.D) :
    |∫ x', v x' ∂(M.Q xa)| ≤ c * (αb * b xa.1) := by
  haveI := M.isMarkovQ
  have hlt : ∫⁻ x', ENNReal.ofReal (b x') ∂(M.Q xa) < ⊤ :=
    lt_of_le_of_lt (hb.hQ xa hxa) ENNReal.ofReal_lt_top
  have hbI : Integrable b (M.Q xa) :=
    ⟨hb.hb_meas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => hb.hb_nonneg _)).2 hlt⟩
  have h1 : ‖∫ x', v x' ∂(M.Q xa)‖ ≤ ∫ x', c * b x' ∂(M.Q xa) :=
    norm_integral_le_of_norm_le (hbI.const_mul c) (ae_of_all _ fun x => by
      simpa [Real.norm_eq_abs] using hv x)
  have h2 : ∫ x', b x' ∂(M.Q xa) ≤ αb * b xa.1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hb.hb_nonneg)
      hb.hb_meas.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hb.hαb (hb.hb_nonneg _)) (hb.hQ xa hxa)
  rw [integral_const_mul] at h1
  rw [← Real.norm_eq_abs]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hc)

/-- integrability of `xa ↦ v xa.1 - β ∫ v dQ(xa)` and of `r`. -/
theorem integrable_gv (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hb1 : ∀ x, 1 ≤ b x)
    (μ : Measure (E × A)) (hμ : μ ∈ Mb M b) (v : E → ℝ) (hv : v ∈ IBb b) :
    Integrable (fun xa : E × A => v xa.1 - M.β * ∫ x', v x' ∂(M.Q xa)) μ := by
  obtain ⟨hvm, c, hc, hvc⟩ := hv
  refine integrable_of_bound M b hb.hb_meas hb.hb_nonneg hb1 μ hμ _ ?_ (c + M.β * (c * αb)) ?_
  · refine ((hvm.comp measurable_fst).stronglyMeasurable.sub
      (stronglyMeasurable_const.mul ?_)).aestronglyMeasurable
    exact hvm.stronglyMeasurable.integral_kernel
  · intro xa hxa
    have h1 := int_bound M b cr αb hb v c hc hvc xa hxa
    have h2 := hvc xa.1
    have hβ := M.hβ0
    calc |v xa.1 - M.β * ∫ x', v x' ∂(M.Q xa)|
        ≤ |v xa.1| + |M.β * ∫ x', v x' ∂(M.Q xa)| := abs_sub _ _
      _ = |v xa.1| + M.β * |∫ x', v x' ∂(M.Q xa)| := by rw [abs_mul, abs_of_pos hβ]
      _ ≤ c * b xa.1 + M.β * (c * (αb * b xa.1)) := by gcongr
      _ = (c + M.β * (c * αb)) * b xa.1 := by ring

theorem integrable_r (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hb1 : ∀ x, 1 ≤ b x)
    (μ : Measure (E × A)) (hμ : μ ∈ Mb M b) : Integrable M.r μ :=
  integrable_of_bound M b hb.hb_meas hb.hb_nonneg hb1 μ hμ _
    M.hr_meas.aestronglyMeasurable cr hb.hr

theorem weak (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hb1 : ∀ x, 1 ≤ b x)
    (IMs : Set (E → ℝ)) (hIM : IsClosedSubspaceOf b IMs) (p : Measure E)
    (v : E → ℝ) (hv : v ∈ ZP M IMs) (μ : Measure (E × A)) (hμ : μ ∈ ZD M b IMs p) :
    ∫ xa, M.r xa ∂μ ≤ ∫ x, v x ∂p := by
  rw [← hμ.2 v hv.1]
  apply integral_mono_ae (integrable_r M b cr αb hb hb1 μ hμ.1)
    (integrable_gv M b cr αb hb hb1 μ hμ.1 v (hIM.1 hv.1))
  filter_upwards [ae_mem_D M b hb1 μ hμ.1] with xa hxa
  have := hv.2 xa hxa
  linarith

end LP757Aux

open LP757Aux in
theorem solution {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hb1 : ∀ x, 1 ≤ b x)
    (hαb : M.β * αb < 1) (IMs : Set (E → ℝ)) (hIM : IsClosedSubspaceOf b IMs) (hbIM : b ∈ IMs)
    (p : Measure E) (hpb : ∫⁻ x, ENNReal.ofReal (b x) ∂p < ⊤) (v : E → ℝ) (hv : v ∈ ZP M IMs)
    (μ : Measure (E × A)) (hμ : μ ∈ ZD M b IMs p) :
    (((∫ x, v x ∂p : ℝ) : EReal) = valP M IMs p ∧
        ((∫ xa, M.r xa ∂μ : ℝ) : EReal) = valD M b IMs p ∧ valP M IMs p = valD M b IMs p) ↔
      (∀ᵐ xa ∂μ, xa ∈ M.D → v xa.1 = M.r xa + M.β * ∫ x', v x' ∂(M.Q xa)) := by
  have hDP : valD M b IMs p ≤ valP M IMs p :=
    iSup₂_le fun μ' hμ' => le_iInf₂ fun v' hv' =>
      EReal.coe_le_coe_iff.2 (weak M b cr αb hb hb1 IMs hIM p v' hv' μ' hμ')
  have hPle : valP M IMs p ≤ ((∫ x, v x ∂p : ℝ) : EReal) := iInf₂_le v hv
  have hDge : ((∫ xa, M.r xa ∂μ : ℝ) : EReal) ≤ valD M b IMs p := le_iSup₂ (f := fun μ' _ =>
    ((∫ xa, M.r xa ∂μ' : ℝ) : EReal)) μ hμ
  have hgI := integrable_gv M b cr αb hb hb1 μ hμ.1 v (hIM.1 hv.1)
  have hrI := integrable_r M b cr αb hb hb1 μ hμ.1
  have hZD := hμ.2 v hv.1
  constructor
  · rintro ⟨h1, h2, h3⟩
    have heq : ∫ x, v x ∂p = ∫ xa, M.r xa ∂μ := by
      have : ((∫ x, v x ∂p : ℝ) : EReal) = ((∫ xa, M.r xa ∂μ : ℝ) : EReal) := by
        rw [h1, h2, h3]
      exact_mod_cast this
    have hint : ∫ xa, ((v xa.1 - M.β * ∫ x', v x' ∂(M.Q xa)) - M.r xa) ∂μ = 0 := by
      rw [integral_sub hgI hrI, hZD, heq, sub_self]
    have hnn : 0 ≤ᵐ[μ] fun xa => (v xa.1 - M.β * ∫ x', v x' ∂(M.Q xa)) - M.r xa := by
      filter_upwards [ae_mem_D M b hb1 μ hμ.1] with xa hxa
      have := hv.2 xa hxa
      simp only [Pi.zero_apply]; linarith
    have := (integral_eq_zero_iff_of_nonneg_ae hnn (hgI.sub hrI)).1 hint
    filter_upwards [this] with xa hxa _
    simp only [Pi.zero_apply] at hxa
    linarith
  · intro h
    have hcongr : ∫ xa, M.r xa ∂μ = ∫ xa, (v xa.1 - M.β * ∫ x', v x' ∂(M.Q xa)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [h, ae_mem_D M b hb1 μ hμ.1] with xa hxa hD
      have := hxa hD
      linarith
    have heq : ∫ xa, M.r xa ∂μ = ∫ x, v x ∂p := hcongr.trans hZD
    have e1 : ((∫ x, v x ∂p : ℝ) : EReal) = valP M IMs p := by
      apply le_antisymm _ hPle
      rw [← heq]; exact hDge.trans hDP
    have e2 : ((∫ xa, M.r xa ∂μ : ℝ) : EReal) = valD M b IMs p := by
      apply le_antisymm hDge
      rw [heq]; exact hDP.trans hPle
    refine ⟨e1, e2, ?_⟩
    rw [← e1, ← e2, heq]
