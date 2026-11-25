-- Prove2me | solution 1 for Newton.convolution_fiber_integrable_L2_L1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:27:45.635939+00:00
-- url     : https://prove2.me/submissions/1464de5b-282a-4f25-a14f-48169fd1dad4

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Theorems.Thm_Newton_tonelli_ae_section_lt_top_of_aemeasurable_left

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open Newton
variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}
namespace Newton
theorem _root_.solution
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [SFinite μ] [μ.IsAddRightInvariant] [μ.IsNegInvariant]
    (f g : G → ℂ)
    (hf : MemLp f 2 μ) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Integrable (fun y => f (x - y) * g y) μ := by
  -- Weighted finite measure ν with density ‖g‖ₑ.
  set ν : Measure G := μ.withDensity (fun y => ‖g y‖ₑ) with hν_def
  -- L²(ν) control of y ↦ f (x - y) for a.e. x.
  -- This follows from Tonelli on the nonnegative kernel
  --   (x, y) ↦ ‖f (x - y)‖ₑ^2 · ‖g y‖ₑ,
  -- together with the L²(μ) control of f and L¹(μ) control of g.
  have hL2_ae : ∀ᵐ x ∂μ, MemLp (fun y => f (x - y)) 2 ν := by
    -- Build ℝ≥0∞-valued factors Af, Ag.
    set Af : G → ℝ≥0∞ := fun z => ‖f z‖ₑ ^ (2 : ℝ) with hAf_def
    set Ag : G → ℝ≥0∞ := fun y => ‖g y‖ₑ with hAg_def
    have hf_meas : AEMeasurable (fun z => ‖f z‖ₑ) μ := hf.aestronglyMeasurable.enorm
    have hAf_meas : AEMeasurable Af μ := by
      simpa [Af, hAf_def] using hf_meas.pow_const (2 : ℝ)
    have hg_meas : AEMeasurable (fun y => ‖g y‖ₑ) μ := hg.aestronglyMeasurable.enorm
    have hAg_meas : AEMeasurable Ag μ := by simpa [Ag, hAg_def] using hg_meas
    -- Finiteness of the separated integrals
    have hAf_lt_top : (∫⁻ z, Af z ∂μ) < ∞ := by
      -- From `hf : MemLp f 2 μ` via the characterization by lintegral of the r-power of ‖f‖ₑ
      have :=
        lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := μ)
            (p := (2 : ℝ≥0∞)) (f := f)
            two_ne_zero ENNReal.ofNat_ne_top hf.eLpNorm_lt_top
      simpa [Af, hAf_def, ENNReal.toReal_ofNat] using this
    have hAg_lt_top : (∫⁻ y, Ag y ∂μ) < ∞ := by
      -- From integrability of g
      simpa [Ag, hAg_def, HasFiniteIntegral] using hg.hasFiniteIntegral
    -- Define the nonnegative kernel on the product space.
    set H : G × G → ℝ≥0∞ := fun q => Af (q.1 - q.2) * Ag q.2 with hH_def
    -- A.E.-measurability of H on μ × μ.
    have h_sub_qmp :
        Measure.QuasiMeasurePreserving (fun q : G × G => q.1 - q.2)
          (μ.prod μ) μ := by
      have h_sub_prod :
          MeasurePreserving (fun q : G × G => (q.1 - q.2, q.2))
            (μ.prod μ) (μ.prod μ) :=
        measurePreserving_sub_prod (μ := μ) (ν := μ)
      have h_fst_qmp :
          Measure.QuasiMeasurePreserving (fun q : G × G => q.1)
            (μ.prod μ) μ :=
        MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
      exact h_fst_qmp.comp h_sub_prod.quasiMeasurePreserving
    have hAf_comp_aemeas :
        AEMeasurable (fun q : G × G => Af (q.1 - q.2)) (μ.prod μ) :=
      hAf_meas.comp_quasiMeasurePreserving h_sub_qmp
    have hAg_comp_aemeas :
        AEMeasurable (fun q : G × G => Ag q.2) (μ.prod μ) :=
      hAg_meas.comp_quasiMeasurePreserving
        (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
    have hH_aemeas : AEMeasurable H (μ.prod μ) :=
      (hAf_comp_aemeas.mul hAg_comp_aemeas)
    -- Compute the product lintegral via the shear change of variables and Tonelli.
    have h_change :
        ∫⁻ q : G × G, H q ∂(μ.prod μ)
          = ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ) := by
      -- Use the measure-preserving shear τ(q) = (q.1 - q.2, q.2)
      set τ : G × G → G × G := fun q => (q.1 - q.2, q.2)
      have h_pres : MeasurePreserving τ (μ.prod μ) (μ.prod μ) :=
        measurePreserving_sub_prod (μ := μ) (ν := μ)
      have h_map : Measure.map τ (μ.prod μ) = μ.prod μ := h_pres.map_eq
      have h_prod_aemeas :
          AEMeasurable (fun q : G × G => Af q.1 * Ag q.2) (μ.prod μ) :=
        (hAf_meas.comp_quasiMeasurePreserving
            (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))).mul
          (hAg_meas.comp_quasiMeasurePreserving
            (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)))
      have h_prod_map :
          AEMeasurable (fun q : G × G => Af q.1 * Ag q.2)
            (Measure.map τ (μ.prod μ)) := by
        simpa [h_map] using h_prod_aemeas
      have h_map_eq :=
        lintegral_map' h_prod_map (aemeasurable_id'.comp_measurable h_pres.measurable)
      have h_eval :
          ∫⁻ q, Af q.1 * Ag q.2 ∂(μ.prod μ)
            = ∫⁻ q, Af (τ q).1 * Ag (τ q).2 ∂(μ.prod μ) := by
        simpa [τ, h_map] using h_map_eq
      have hH_eval :
          (fun q : G × G => Af (τ q).1 * Ag (τ q).2) = H := by
        funext q
        simp [H, τ]
      simpa [hH_eval] using h_eval.symm
    have h_split :
        ∫⁻ q : G × G, Af q.1 * Ag q.2 ∂(μ.prod μ)
          = (∫⁻ z, Af z ∂μ) * (∫⁻ y, Ag y ∂μ) := by
      -- Tonelli on the separated kernel Af(x)·Ag(y).
      have h_prod_aemeas :
          AEMeasurable (fun q : G × G => Af q.1 * Ag q.2) (μ.prod μ) :=
        (hAf_meas.comp_quasiMeasurePreserving
            (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))).mul
          (hAg_meas.comp_quasiMeasurePreserving
            (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)))
      have h_tonelli :=
        MeasureTheory.lintegral_prod (μ := μ) (ν := μ)
          (f := fun q : G × G => Af q.1 * Ag q.2) h_prod_aemeas
      have h_inner :
          ∀ x, ∫⁻ y, Af x * Ag y ∂μ = Af x * ∫⁻ y, Ag y ∂μ := by
        intro x; simpa using lintegral_const_mul'' (μ := μ) (r := Af x) (f := Ag) hAg_meas
      have h_outer :
          ∫⁻ x, Af x * ∫⁻ y, Ag y ∂μ ∂μ
            = (∫⁻ y, Ag y ∂μ) * ∫⁻ x, Af x ∂μ := by
        simpa [mul_comm]
          using lintegral_mul_const'' (μ := μ) (r := ∫⁻ y, Ag y ∂μ) (f := Af) hAf_meas
      calc
        ∫⁻ q, Af q.1 * Ag q.2 ∂(μ.prod μ)
            = ∫⁻ x, ∫⁻ y, Af x * Ag y ∂μ ∂μ := by
                simpa [Function.uncurry] using h_tonelli
        _ = ∫⁻ x, Af x * ∫⁻ y, Ag y ∂μ ∂μ := by
                simp [h_inner]
        _ = (∫⁻ y, Ag y ∂μ) * ∫⁻ x, Af x ∂μ := h_outer
        _ = (∫⁻ x, Af x ∂μ) * (∫⁻ y, Ag y ∂μ) := by simp [mul_comm]
    have h_prod_lt_top : ∫⁻ q : G × G, H q ∂(μ.prod μ) < ∞ := by
      have := ENNReal.mul_lt_top hAf_lt_top hAg_lt_top
      simpa [h_change, h_split] using this
    -- Tonelli consequence: for a.e. x, the y-section has finite lintegral.
    have h_section_fin : ∀ᵐ x ∂μ, ∫⁻ y, H (x, y) ∂μ < ∞ :=
      tonelli_ae_section_lt_top_of_aemeasurable_left
        (μ := μ) (f := H) hH_aemeas h_prod_lt_top
    -- Identify the section integral with the L²(ν) seminorm of y ↦ f (x − y).
    -- Also record measurability for MemLp.
    have hν_ac : ν ≪ μ := by
      -- withDensity is absolutely continuous with respect to the base measure
      simpa [hν_def] using withDensity_absolutelyContinuous (μ := μ)
        (f := fun y => ‖g y‖ₑ)
    -- For a fixed x, measurability of y ↦ f (x - y) under μ then lift to ν.
    have h_meas_x : ∀ x, AEStronglyMeasurable (fun y => f (x - y)) ν := by
      intro x
      -- y ↦ x - y is measurable
      have h_sub_meas : Measurable (fun y : G => x - y) := measurable_const.sub measurable_id
      -- Get a strongly measurable representative of f
      obtain ⟨f0, hf0_strong, hf_ae⟩ := hf.aestronglyMeasurable
      -- f0 ∘ (x - ·) is strongly measurable
      have hf0_comp : StronglyMeasurable (fun y => f0 (x - y)) :=
        hf0_strong.comp_measurable h_sub_meas
      -- f (x - ·) =ᵐ[μ] f0 (x - ·)
      have h_ae_comp : (fun y => f (x - y)) =ᵐ[μ] (fun y => f0 (x - y)) := by
        -- Use measure preservation: y ↦ x - y preserves μ
        have h_mp : MeasurePreserving (fun y : G => x - y) μ μ := by
          -- x - y = -(y - x), and both transformations preserve μ
          have h1 : (fun y : G => x - y) = Neg.neg ∘ (fun y => y - x) := by
            ext y; simp [Function.comp, sub_eq_add_neg]
          -- y - x is measure-preserving (right invariance)
          have h_sub_right : MeasurePreserving (fun y : G => y - x) μ μ :=
            measurePreserving_sub_right μ x
          -- Need to show that Neg.neg is also measure-preserving
          -- For an abelian group with right-invariant measure, neg preserves the measure
          have h_neg : MeasurePreserving (Neg.neg : G → G) μ μ :=
            Measure.measurePreserving_neg (μ := μ)
          rw [h1]
          exact h_neg.comp h_sub_right
        exact h_mp.quasiMeasurePreserving.ae_eq_comp hf_ae
      -- Package into AEStronglyMeasurable on μ, then transfer to ν
      have h_aestrong_μ : AEStronglyMeasurable (fun y => f (x - y)) μ :=
        ⟨fun y => f0 (x - y), hf0_comp, h_ae_comp⟩
      exact h_aestrong_μ.mono_ac hν_ac
    -- Conclude MemLp from the finite weighted lintegral and measurability.
    refine h_section_fin.mono ?_
    intro x hx
    -- Expand withDensity to match the weighted section integral.
    have h_expand :
        ∫⁻ y, (‖f (x - y)‖ₑ) ^ (2 : ℝ) ∂ν
          = ∫⁻ y, (‖f (x - y)‖ₑ) ^ (2 : ℝ) * ‖g y‖ₑ ∂μ := by
      have h_aestrong_μ : AEStronglyMeasurable (fun y => f (x - y)) μ := by
        -- Reconstruct the a.e. strong measurability on μ
        have h_sub_meas : Measurable (fun y : G => x - y) := by
          have : (fun y : G => x - y) = (fun y => x + (-y)) := by ext; simp [sub_eq_add_neg]
          rw [this]
          exact measurable_const.add measurable_neg
        obtain ⟨f0, hf0, hf_ae⟩ := hf.aestronglyMeasurable
        have hf0_comp : StronglyMeasurable (fun y => f0 (x - y)) :=
          hf0.comp_measurable h_sub_meas
        have h_ae_comp : (fun y => f (x - y)) =ᵐ[μ] (fun y => f0 (x - y)) := by
          -- Use measure preservation: y ↦ x - y preserves μ
          have h_mp : MeasurePreserving (fun y : G => x - y) μ μ := by
            -- x - y = -(y - x), and both transformations preserve μ
            have h1 : (fun y : G => x - y) = Neg.neg ∘ (fun y => y - x) := by
              ext y; simp [Function.comp, sub_eq_add_neg]
            -- y - x is measure-preserving (right invariance)
            have h_sub_right : MeasurePreserving (fun y : G => y - x) μ μ :=
              measurePreserving_sub_right μ x
            -- Negation is measure-preserving under IsNegInvariant
            have h_neg : MeasurePreserving (Neg.neg : G → G) μ μ :=
              Measure.measurePreserving_neg (μ := μ)
            rw [h1]
            exact h_neg.comp h_sub_right
          exact h_mp.quasiMeasurePreserving.ae_eq_comp hf_ae
        exact ⟨fun y => f0 (x - y), hf0_comp, h_ae_comp⟩
      have hf_pow_ae_μ : AEMeasurable (fun y => (‖f (x - y)‖ₑ) ^ (2 : ℝ)) μ :=
        h_aestrong_μ.enorm.pow_const (2 : ℝ)
      have hg_ae : AEMeasurable (fun y => ‖g y‖ₑ) μ := hg_meas
      have h :=
        lintegral_withDensity_eq_lintegral_mul₀ (μ := μ)
          (f := fun y => ‖g y‖ₑ) hg_ae
          (g := fun y => (‖f (x - y)‖ₑ) ^ (2 : ℝ)) hf_pow_ae_μ
      simpa [ν, hν_def, mul_comm] using h
    -- Now H (x, y) = Af (x - y) * Ag y by definition.
    have hH_section : ∫⁻ y, H (x, y) ∂μ
        = ∫⁻ y, (‖f (x - y)‖ₑ) ^ (2 : ℝ) * ‖g y‖ₑ ∂μ := by
      simp [H, Af, Ag]
    -- Package into `MemLp`.
    refine ⟨h_meas_x x, ?_⟩
    -- Compare the weighted L² seminorm with the finite section lintegral from Tonelli.
    have : ∫⁻ y, (‖f (x - y)‖ₑ) ^ (2 : ℝ) ∂ν < ∞ := by
      rw [h_expand, ← hH_section]
      exact hx
    -- Turn it into `eLpNorm < ∞`.
    -- Use the characterization `eLpNorm_eq_lintegral_rpow_enorm` with p = 2.
    have h_eq :
        eLpNorm (fun y => f (x - y)) 2 ν
          = (∫⁻ y, (‖f (x - y)‖ₑ) ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) := by
      simpa [one_div, ENNReal.toReal_ofNat]
        using (MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
                (μ := ν) (f := fun y => f (x - y))
                (p := (2 : ℝ≥0∞)) two_ne_zero ENNReal.ofNat_ne_top)
    -- From finiteness of the inside lintegral, deduce `eLpNorm < ∞`.
    have h_lt_top : eLpNorm (fun y => f (x - y)) 2 ν < ∞ := by
      -- If the inner lintegral is finite, then its positive r-power is finite.
      refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (μ := ν) (p := (2 : ℝ≥0∞)) (f := fun y => f (x - y))
        (hp_ne_zero := two_ne_zero) (hp_ne_top := ENNReal.ofNat_ne_top)).2 ?_
      simpa using this
    exact h_lt_top
  -- Cauchy–Schwarz on (G, ν) for each fibre x.
  -- Since ν is finite (by hg), we have 1 ∈ L²(ν). Combining with hL2_ae gives
  --   ∫ ‖f (x - ·)‖ dν < ∞
  -- hence ∫ ‖f (x - y)‖ · ‖g y‖ dμ(y) < ∞.
  -- First, establish that ν is a finite measure
  have hν_finite : IsFiniteMeasure ν := by
    -- ν = μ.withDensity (fun y => ‖g y‖ₑ)
    -- Since g is integrable, ∫⁻ y, ‖g y‖ₑ ∂μ < ∞
    rw [hν_def]
    have h_int : ∫⁻ y, ‖g y‖ₑ ∂μ < ∞ := by
      simpa [HasFiniteIntegral] using hg.hasFiniteIntegral
    have h_ne_top : ∫⁻ y, ‖g y‖ₑ ∂μ ≠ ⊤ := ne_of_lt h_int
    exact MeasureTheory.isFiniteMeasure_withDensity h_ne_top
  have h_int_norm_ae : ∀ᵐ x ∂μ, Integrable (fun y => ‖f (x - y)‖) ν := by
    -- Deduce L¹(ν) from L²(ν) via exponent monotonicity, then take norms.
    refine hL2_ae.mono ?_
    intro x hx
    haveI : IsFiniteMeasure ν := hν_finite
    have hx_L1 : MemLp (fun y => f (x - y)) 1 ν :=
      hx.mono_exponent (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (by norm_num)
    have hx_int : Integrable (fun y => f (x - y)) ν :=
      (memLp_one_iff_integrable (μ := ν)).1 hx_L1
    exact hx_int.norm
  -- Pull back from ν to μ via withDensity and conclude integrability
  -- of the complex-valued section y ↦ f (x - y) * g y on μ.
  refine h_int_norm_ae.mono ?_
  intro x hx
  -- `hx` gives ∫ ‖f (x - ·)‖ dν < ∞
  -- By definition of ν = μ.withDensity ‖g‖ₑ, this means ∫ ‖f (x - y)‖ · ‖g y‖ dμ(y) < ∞
  -- We need to show Integrable (fun y => f (x - y) * g y) μ

  -- First, expand the integral over ν to an integral over μ
  have h_expand : ∫⁻ y, ‖f (x - y)‖ₑ ∂ν = ∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂μ := by
    rw [hν_def]
    have h_aemeas_f : AEMeasurable (fun y => ‖f (x - y)‖ₑ) μ := by
      have h_aestrong : AEStronglyMeasurable (fun y => f (x - y)) μ := by
        have h_sub_meas : Measurable (fun y : G => x - y) := measurable_const.sub measurable_id
        obtain ⟨f0, hf0, hf_ae⟩ := hf.aestronglyMeasurable
        have hf0_comp : StronglyMeasurable (fun y => f0 (x - y)) :=
          hf0.comp_measurable h_sub_meas
        have h_ae_comp : (fun y => f (x - y)) =ᵐ[μ] (fun y => f0 (x - y)) := by
          have h_mp : MeasurePreserving (fun y : G => x - y) μ μ := by
            have h1 : (fun y : G => x - y) = Neg.neg ∘ (fun y => y - x) := by
              ext y
              simp [Function.comp, sub_eq_add_neg]
            have h_sub_right : MeasurePreserving (fun y : G => y - x) μ μ :=
              measurePreserving_sub_right μ x
            have h_neg : MeasurePreserving (Neg.neg : G → G) μ μ :=
              Measure.measurePreserving_neg (μ := μ)
            rw [h1]
            exact h_neg.comp h_sub_right
          exact h_mp.quasiMeasurePreserving.ae_eq_comp hf_ae
        exact ⟨fun y => f0 (x - y), hf0_comp, h_ae_comp⟩
      exact h_aestrong.enorm
    have h_aemeas_g : AEMeasurable (fun y => ‖g y‖ₑ) μ := hg.aestronglyMeasurable.enorm
    have h_eq := lintegral_withDensity_eq_lintegral_mul₀ (μ := μ) h_aemeas_g h_aemeas_f
    simpa [mul_comm] using h_eq
  -- From hx, we have ∫⁻ y, ‖f (x - y)‖ₑ ∂ν < ∞
  have h_int_prod : ∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂μ < ∞ := by
    rw [← h_expand]
    -- hx : Integrable (fun y => ‖f (x - y)‖) ν
    -- Need to convert to ∫⁻ y, ‖f (x - y)‖ₑ ∂ν < ∞
    have : HasFiniteIntegral (fun y => ‖f (x - y)‖) ν := hx.hasFiniteIntegral
    simpa [HasFiniteIntegral] using this
  -- Now show that f (x - y) * g y is integrable
  -- We have ‖f (x - y) * g y‖ = ‖f (x - y)‖ * ‖g y‖
  have h_aestrong_prod : AEStronglyMeasurable (fun y => f (x - y) * g y) μ := by
    have h_aestrong_f : AEStronglyMeasurable (fun y => f (x - y)) μ := by
      have h_sub_meas : Measurable (fun y : G => x - y) := measurable_const.sub measurable_id
      obtain ⟨f0, hf0, hf_ae⟩ := hf.aestronglyMeasurable
      have hf0_comp : StronglyMeasurable (fun y => f0 (x - y)) :=
        hf0.comp_measurable h_sub_meas
      have h_ae_comp : (fun y => f (x - y)) =ᵐ[μ] (fun y => f0 (x - y)) := by
        have h_mp : MeasurePreserving (fun y : G => x - y) μ μ := by
          have h1 : (fun y : G => x - y) = Neg.neg ∘ (fun y => y - x) := by
            ext y; simp [Function.comp, sub_eq_add_neg]
          have h_sub_right : MeasurePreserving (fun y : G => y - x) μ μ :=
            measurePreserving_sub_right μ x
          have h_neg : MeasurePreserving (Neg.neg : G → G) μ μ :=
            Measure.measurePreserving_neg (μ := μ)
          rw [h1]
          exact h_neg.comp h_sub_right
        exact h_mp.quasiMeasurePreserving.ae_eq_comp hf_ae
      exact ⟨fun y => f0 (x - y), hf0_comp, h_ae_comp⟩
    exact h_aestrong_f.mul hg.aestronglyMeasurable
  have h_norm_eq : (fun y => ‖f (x - y) * g y‖ₑ) = (fun y => ‖f (x - y)‖ₑ * ‖g y‖ₑ) := by
    ext y
    simp
  refine ⟨h_aestrong_prod, ?_⟩
  simpa [HasFiniteIntegral, h_norm_eq] using h_int_prod
end Newton
