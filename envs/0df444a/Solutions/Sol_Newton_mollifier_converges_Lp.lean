-- Prove2me | solution 1 for Newton.mollifier_converges_Lp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:48:25.55606+00:00
-- url     : https://prove2.me/submissions/9219e0a2-0484-4b1b-b241-b26951bb0b59

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity
import Theorems.Thm_Newton_scaledMollifier_nonneg
import Theorems.Thm_Newton_hasCompactSupport_scaledMollifier
import Theorems.Thm_Newton_tsupport_scaledMollifier_subset
import Theorems.Thm_Newton_integral_scaledMollifier_eq_one
import Theorems.Thm_Newton_core_indicator_eLpNorm_bound
import Theorems.Thm_Newton_mollifier_converges_continuous
import Theorems.Thm_Newton_eLpNorm_triangle_three
import Theorems.Thm_Newton_convolution_support_ball_subset
import Theorems.Thm_Newton_conjugate_exponent_formula
import Theorems.Thm_Newton_continuous_compactSupport_dense_Lp
import Theorems.Thm_Newton_tsupport_subset_closedBall
import Theorems.Thm_Newton_young_convolution_inequality


set_option autoImplicit false
open MeasureTheory Complex NNReal SchwartzMap
open scoped ENNReal ContDiff Topology Pointwise
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f : (Fin n → ℝ) → ℂ)
    (ψ : (Fin n → ℝ) → ℝ)
    (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hp_ne_top : p ≠ ⊤)
    (hf : MemLp f p volume)
    (hψ : IsApproximateIdentity ψ) :
    ∀ ε > 0, ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
      eLpNorm (fun x => f x - ∫ y, f (x - y) * (scaledMollifier ψ η y)) p volume <
        ENNReal.ofReal ε := by
  intro ε hε
  -- Approximate f in Lᵖ by a continuous compactly supported g
  obtain ⟨g, hg_cont, hg_compact, hg_memLp, hfg_small⟩ :=
    continuous_compactSupport_dense_Lp (p := p) (hp_ne_top := hp_ne_top)
      f hf (ε := ε / 4) (by positivity)
  -- A convenient symmetric form: ‖g - f‖ₚ = ‖f - g‖ₚ
  have hgf_small : eLpNorm (fun x => g x - f x) p volume < ENNReal.ofReal (ε / 4) := by
    have : eLpNorm (fun x => g x - f x) p volume = eLpNorm (g - f) p volume := rfl
    rw [this, eLpNorm_sub_comm]
    exact hfg_small
  -- Choose a finite-measure core set covering the supports uniformly in small η
  obtain ⟨R, hR_subset, hR_ge_one⟩ := tsupport_subset_closedBall g hg_compact
  set S : Set (Fin n → ℝ) := Metric.closedBall (0 : Fin n → ℝ) (R + 1) with hS_def
  have hS_meas : MeasurableSet S := by
    simpa [hS_def] using
      (Metric.isClosed_closedBall
        : IsClosed (Metric.closedBall (0 : Fin n → ℝ) (R + 1))).measurableSet
  have hμS_lt_top : volume S < ⊤ := by
    simpa [hS_def]
      using (MeasureTheory.measure_closedBall_lt_top (x := (0 : Fin n → ℝ)) (r := R + 1))
  have hμS_ne_top : volume S ≠ ⊤ := ne_of_lt hμS_lt_top
  have hμS_pos : 0 < volume S := by
    have hR_pos : 0 < R + 1 := by linarith [hR_ge_one]
    calc 0 < volume (Metric.ball (0 : Fin n → ℝ) (R + 1)) := Metric.measure_ball_pos volume 0 hR_pos
      _ ≤ volume S := by
        rw [hS_def]
        exact measure_mono Metric.ball_subset_closedBall
  -- Uniform (sup-norm) control for g − g * ψ_η from continuity + compact support
  -- Pick a small target on S so that its Lᵖ bound is ≤ ε/2.
  have h_exponent_nonneg : 0 ≤ 1 / p.toReal := by
    have hp_toReal_nonneg : 0 ≤ p.toReal := ENNReal.toReal_nonneg
    exact div_nonneg zero_le_one hp_toReal_nonneg
  have h_powS_ne_top : (volume S) ^ (1 / p.toReal) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg h_exponent_nonneg hμS_ne_top
  -- Choose δ₀ from the uniform convergence theorem for g with a small target on S.
  -- Let target δg satisfy: (μ S)^{1/p} * δg ≤ ε/2.
  -- We can simply ask the sup-norm error be ≤ ε / (2 * ((μ S)^{1/p}).toReal).
  set δg : ℝ := ε / (2 * ((volume S) ^ (1 / p.toReal)).toReal) with hδg_def
  have hδg_pos : 0 < δg := by
    have hden_pos : 0 < 2 * ((volume S) ^ (1 / p.toReal)).toReal := by
      have hpos1 : (0 : ℝ) < 2 := by norm_num
      have hS_toReal_pos : 0 < ((volume S) ^ (1 / p.toReal)).toReal := by
        refine ENNReal.toReal_pos ?_ h_powS_ne_top
        intro h_zero
        have : volume S = 0 := by
          by_contra h_ne_zero
          have : 0 < volume S ^ (1 / p.toReal) :=
            ENNReal.rpow_pos_of_nonneg hμS_pos h_exponent_nonneg
          exact this.ne' h_zero
        exact (ne_of_gt hμS_pos) this
      exact mul_pos hpos1 hS_toReal_pos
    exact div_pos hε hden_pos
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ :=
    mollifier_converges_continuous g ψ hg_cont hg_compact hψ δg hδg_pos
  -- We will require η < min δ₀ 1 to also control the support of ψ_η.
  refine ⟨min δ₀ 1, lt_min hδ₀_pos zero_lt_one, ?_⟩
  intro η hη_pos hη_lt
  -- Abbreviations
  set mη : (Fin n → ℝ) → ℝ := fun y => scaledMollifier ψ η y with hmη
  let mηC : (Fin n → ℝ) → ℂ := fun y => (mη y : ℝ)
  -- Estimate by three-way triangle inequality in Lᵖ
  -- Define the two convolutions
  set conv_f : (Fin n → ℝ) → ℂ :=
    fun x => ∫ y, f (x - y) * mηC y with hconvf
  set conv_g : (Fin n → ℝ) → ℂ :=
    fun x => ∫ y, g (x - y) * mηC y with hconvg
  -- Show measurability of the subterms needed for the triangle inequality
  have hfg_meas : AEStronglyMeasurable (fun x => f x - g x) volume :=
    hf.aestronglyMeasurable.sub hg_memLp.aestronglyMeasurable
  -- Continuity and compact support properties needed throughout
  have h_div_cont :
      Continuous (fun y : (Fin n → ℝ) => fun i => y i / η) := by
    have :
        (fun y : (Fin n → ℝ) => fun i => y i / η)
          = fun y : (Fin n → ℝ) => (η⁻¹ : ℝ) • y := by
      funext y i; simp [div_eq_mul_inv, mul_comm]
    simpa [this] using (continuous_const_smul (η⁻¹ : ℝ))
  have h_mη_cont : Continuous mη :=
    continuous_const.mul (hψ.smooth.continuous.comp h_div_cont)
  have h_mηC_cont : Continuous mηC :=
    continuous_ofReal.comp h_mη_cont
  have h_mηC_compact : HasCompactSupport mηC := by
    -- transfer compact support from the real-valued scaled mollifier
    have h_real := hasCompactSupport_scaledMollifier hψ.compact_support hη_pos
    -- upgrade to ℂ-valued by eventual equality
    rw [hasCompactSupport_iff_eventuallyEq] at h_real ⊢
    exact h_real.mono (by
      intro y hy
      simp only [mηC, mη]
      have : scaledMollifier ψ η y = 0 := hy
      rw [this]
      simp)
  have hmη_memLp_one : MemLp mηC 1 volume := by
    -- Move integrability from ℝ to ℂ via continuous/compact support
    -- (mηC has compact support and is continuous)
    have h_intC : Integrable mηC volume :=
      h_mηC_cont.integrable_of_hasCompactSupport h_mηC_compact
    simpa [memLp_one_iff_integrable (μ := volume)] using h_intC
  -- Convolution bounds (Young with r = p, q = 1): obtain MemLp and eLpNorm bounds
  have h_conv_f_memLp : MemLp conv_f p volume ∧
      eLpNorm conv_f p volume ≤ eLpNorm f p volume * eLpNorm mηC 1 volume := by
    simpa [conv_f, hconvf]
      using
        (young_convolution_inequality (f := f) (g := mηC)
          (p := p) (q := (1 : ℝ≥0∞)) (r := p)
          hp (by rfl) (by simp [add_comm]) hf hmη_memLp_one)
  have h_conv_g_memLp : MemLp conv_g p volume ∧
      eLpNorm conv_g p volume ≤ eLpNorm g p volume * eLpNorm mηC 1 volume := by
    simpa [conv_g, hconvg]
      using
        (young_convolution_inequality (f := g) (g := mηC)
          (p := p) (q := (1 : ℝ≥0∞)) (r := p)
          hp (by rfl) (by simp [add_comm]) hg_memLp hmη_memLp_one)
  have h_conv_f_meas : AEStronglyMeasurable conv_f volume :=
    (h_conv_f_memLp.1).aestronglyMeasurable
  have h_conv_g_meas : AEStronglyMeasurable conv_g volume :=
    (h_conv_g_memLp.1).aestronglyMeasurable
  have hg_conv_meas : AEStronglyMeasurable (fun x => g x - conv_g x) volume :=
    hg_cont.aestronglyMeasurable.sub h_conv_g_meas
  have hconv_diff_meas :
      AEStronglyMeasurable (fun x => conv_g x - conv_f x) volume :=
    h_conv_g_meas.sub h_conv_f_meas
  -- Apply the three-term triangle inequality
  have h_triangle :=
    eLpNorm_triangle_three (f := f) (g := g)
      (ψ := conv_g) (φ := conv_f) (p := p) hp hfg_meas hg_conv_meas hconv_diff_meas
  -- We will now bound each of the three terms on the right-hand side.
  -- Term A: ‖f - g‖ₚ < ε/4 (by density choice)
  have hA_lt :
      eLpNorm (fun x => f x - g x) p volume < ENNReal.ofReal (ε / 4) := hfg_small
  -- Term C: ‖conv_g - conv_f‖ₚ ≤ ‖g - f‖ₚ · ‖mηC‖₁, and ‖mηC‖₁ = 1
  have h_conv_sub_ae :
      (fun x => ∫ a, (g (x - a) - f (x - a)) * mηC a) =ᶠ[ae volume]
        (fun x => conv_g x - conv_f x) := by
    -- Use linearity of convolution on differences; provide integrability in y for a.e. x
    have h_int_g : ∀ᵐ x ∂volume, Integrable (fun y => g (x - y) * mηC y) volume := by
      -- actually for all x: product of continuous with compact support is integrable
      have h_all : ∀ x, Integrable (fun y => g (x - y) * mηC y) volume := by
        intro x
        have h_transl : Continuous (fun y : (Fin n → ℝ) => g (x - y)) := by
          have h_sub : Continuous (fun y : (Fin n → ℝ) => x - y) :=
            continuous_const.sub continuous_id
          exact hg_cont.comp h_sub
        have h_prod_cont : Continuous (fun y => g (x - y) * mηC y) :=
          h_transl.mul h_mηC_cont
        have h_prod_compact :
            HasCompactSupport (fun y => g (x - y) * mηC y) := by
          -- compact support from mηC
          have : Function.support (fun y => g (x - y) * mηC y) ⊆ Function.support mηC := by
            apply Function.support_mul_subset_right
          exact h_mηC_compact.mono this
        exact h_prod_cont.integrable_of_hasCompactSupport h_prod_compact
      exact Filter.Eventually.of_forall h_all
    have h_int_g_ae :
        ∀ᵐ x ∂volume, Integrable (fun y => g (x - y) * mηC y) volume := by
      -- we actually prove a stronger statement: for all x
      refine Filter.Eventually.of_forall ?_
      intro x
      -- As above (h_int_g), the product of continuous compactly supported functions is integrable
      have h_transl : Continuous (fun y : (Fin n → ℝ) => g (x - y)) := by
        have h_sub : Continuous (fun y : (Fin n → ℝ) => x - y) :=
          continuous_const.sub continuous_id
        exact hg_cont.comp h_sub
      have h_prod_cont : Continuous (fun y => g (x - y) * mηC y) :=
        h_transl.mul h_mηC_cont
      have h_prod_compact :
          HasCompactSupport (fun y => g (x - y) * mηC y) := by
        have : Function.support (fun y => g (x - y) * mηC y)
                ⊆ Function.support mηC := by
          apply Function.support_mul_subset_right
        exact h_mηC_compact.mono this
      exact h_prod_cont.integrable_of_hasCompactSupport h_prod_compact
    have h_int_f_ae :
        ∀ᵐ x ∂volume, Integrable (fun y => f (x - y) * mηC y) volume := by
      by_cases hp_one : p = 1
      · -- Case p = 1, take q = ∞
        have hmηC_mem_top : MemLp mηC ∞ volume :=
          h_mηC_cont.memLp_of_hasCompactSupport h_mηC_compact
        -- Build the Holder triple instance for (p,q,r) = (1,∞,1)
        have p_inv_add : p⁻¹ + (∞ : ℝ≥0∞)⁻¹ = (1 : ℝ≥0∞) := by
          simp [hp_one]
        haveI : ENNReal.HolderTriple p ∞ 1 := ⟨by simpa [p_inv_add, inv_one]⟩
        -- Prove integrability for all x via MemLp.integrable_mul on y
        refine Filter.Eventually.of_forall ?_
        intro x
        -- Translation preserves MemLp in y
        have h_pres_neg : MeasurePreserving (fun y : (Fin n → ℝ) => -y) volume volume :=
          Measure.measurePreserving_neg (volume : Measure (Fin n → ℝ))
        have h_pres_add :
            MeasurePreserving (fun y : (Fin n → ℝ) => y + x) volume volume :=
          measurePreserving_add_right (μ := volume) x
        have h_pres :
            MeasurePreserving (fun y : (Fin n → ℝ) => x - y) volume volume := by
          -- x - y = x + (-y)
          have := h_pres_add.comp h_pres_neg
          simpa [Function.comp_def, sub_eq_add_neg, add_comm] using this
        have hf_shift_mem : MemLp (fun y => f (x - y)) p volume :=
          hf.comp_measurePreserving h_pres
        -- Apply Hölder (product lies in L¹)
        have : Integrable (fun y => (fun y => f (x - y)) y * mηC y) volume :=
          (MemLp.integrable_mul (μ := volume) (p := p) (q := (∞ : ℝ≥0∞))
            hf_shift_mem hmηC_mem_top)
        simpa using this
      · -- Case 1 < p < ∞: choose q the conjugate exponent to p
        have hp_one_lt : (1 : ℝ≥0∞) < p := lt_of_le_of_ne hp (by simpa [eq_comm] using hp_one)
        have hp_lt_top : p < ⊤ := lt_of_le_of_ne le_top hp_ne_top
        obtain ⟨q, hpq, -⟩ :=
          conjugate_exponent_formula (p := p) hp_one_lt hp_lt_top
        -- Extract 1/p + 1/q = 1 from `IsConjugateExponent` proof
        have hpq_sum : 1 / p + 1 / q = 1 := by
          rcases hpq with h1 | h2 | hpq'
          · -- Case p = 1, q = ∞: contradicts 1 < p
            rcases h1 with ⟨hp_eq, -⟩
            rw [hp_eq] at hp_one_lt
            norm_num at hp_one_lt
          · -- Case p = ∞, q = 1: contradicts p < ∞
            rcases h2 with ⟨hp_eq, -⟩
            rw [hp_eq] at hp_lt_top
            simp at hp_lt_top
          · -- Case 1 < p < ∞ and 1 < q < ∞ and 1/p + 1/q = 1
            rcases hpq' with ⟨_, _, _, _, hsum⟩
            exact hsum
        have p_inv_add : p⁻¹ + q⁻¹ = 1 := by simpa [one_div] using hpq_sum
        haveI : ENNReal.HolderTriple p q 1 := ⟨by simp [p_inv_add, inv_one]⟩
        have hmηC_mem_q : MemLp mηC q volume :=
          h_mηC_cont.memLp_of_hasCompactSupport h_mηC_compact
        -- Prove integrability for all x via MemLp.integrable_mul on y
        refine Filter.Eventually.of_forall ?_
        intro x
        have h_pres_neg : MeasurePreserving (fun y : (Fin n → ℝ) => -y) volume volume :=
          Measure.measurePreserving_neg (volume : Measure (Fin n → ℝ))
        have h_pres_add :
            MeasurePreserving (fun y : (Fin n → ℝ) => y + x) volume volume :=
          measurePreserving_add_right (μ := volume) x
        have h_pres :
            MeasurePreserving (fun y : (Fin n → ℝ) => x - y) volume volume := by
          have := h_pres_add.comp h_pres_neg
          simpa [Function.comp_def, sub_eq_add_neg, add_comm] using this
        have hf_shift_mem : MemLp (fun y => f (x - y)) p volume :=
          hf.comp_measurePreserving h_pres
        have : Integrable (fun y => (fun y => f (x - y)) y * mηC y) volume :=
          (MemLp.integrable_mul (μ := volume) (p := p) (q := q)
            hf_shift_mem hmηC_mem_q)
        simpa using this
    -- Aggregate both fibrewise integrability results
    have h_ae_both :
        ∀ᵐ x ∂volume,
          Integrable (fun y => g (x - y) * mηC y) volume ∧
          Integrable (fun y => f (x - y) * mηC y) volume := by
      filter_upwards [h_int_g_ae, h_int_f_ae] with x hxg hxf
      exact ⟨hxg, hxf⟩
    -- On the a.e. set where both integrals exist, use linearity to rewrite the difference
    have h_eq_ae :
        (fun x => ∫ a, (g (x - a) - f (x - a)) * mηC a)
          =ᶠ[ae volume]
        (fun x => conv_g x - conv_f x) := by
      filter_upwards [h_ae_both] with x hx
      rcases hx with ⟨hg_int, hf_int⟩
      have h_sub_int :
          Integrable (fun a => g (x - a) * mηC a - f (x - a) * mηC a) volume :=
        hg_int.sub hf_int
      have h_eq :
          ∫ a, ((g (x - a) - f (x - a)) * mηC a) =
            (∫ a, g (x - a) * mηC a) - ∫ a, f (x - a) * mηC a := by
        have h_left :
            (fun a => (g (x - a) - f (x - a)) * mηC a)
              = fun a => g (x - a) * mηC a - f (x - a) * mηC a := by
          funext a; ring
        simp [h_left, integral_sub hg_int hf_int]
      simpa [conv_g, conv_f, hconvg, hconvf] using h_eq
    -- Conclude the desired a.e. equality
    simpa [MeasureTheory.convolution] using h_eq_ae
  have h_conv_diff_bound :
      eLpNorm (fun x => conv_g x - conv_f x) p volume
        ≤ eLpNorm (fun x => g x - f x) p volume * eLpNorm mηC 1 volume := by
    -- Apply Young to (g - f) * mηC and compare a.e.
    have hY :=
      (young_convolution_inequality
        (f := fun x => g x - f x) (g := mηC)
        (p := p) (q := (1 : ℝ≥0∞)) (r := p)
        hp (by rfl) (by simp [add_comm])
        (hg_memLp.sub hf) hmη_memLp_one).2
    -- Conclude using a.e.-congruence
    refine (le_trans ?_ hY)
    have h_congr :=
      eLpNorm_congr_ae (μ := volume) (p := p) (f :=
        (fun x => ∫ a, (g (x - a) - f (x - a)) * mηC a))
        (g := fun x => conv_g x - conv_f x) h_conv_sub_ae
    simpa [MeasureTheory.convolution] using ge_of_eq h_congr
  -- Evaluate ‖mηC‖₁ = 1 using normalization and nonnegativity
  have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
  have hmη_nonneg : ∀ x, 0 ≤ mη x :=
    scaledMollifier_nonneg hψ.nonneg hη_nonneg
  have hmηC_norm_eq : ∀ x, ‖mηC x‖ = mη x := by
    intro x
    have := hmη_nonneg x
    simp [mηC, Real.norm_eq_abs, abs_of_nonneg this]
  have h_enorm_eq :
      eLpNorm mηC 1 volume
        = ENNReal.ofReal (∫ x, mη x) := by
    -- eLpNorm for p = 1 equals the lintegral of the extended norm
    have h_nonneg_ae : 0 ≤ᵐ[volume] fun x => ‖mηC x‖ :=
      Filter.Eventually.of_forall (by intro x; exact norm_nonneg _)
    have h_integrable_norm : Integrable (fun x => ‖mηC x‖) volume := by
      -- From integrability of mηC
      have h_intC : Integrable mηC volume :=
        (memLp_one_iff_integrable (μ := volume)).1 hmη_memLp_one
      exact h_intC.norm
    have h_lint_eq :
        ∫⁻ x, ‖mηC x‖ₑ ∂volume
          = ENNReal.ofReal (∫ x, ‖mηC x‖ ∂volume) := by
      simpa [ofReal_norm_eq_enorm]
        using
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            h_integrable_norm h_nonneg_ae).symm
    have h_norm_eq : ∫ x, ‖mηC x‖ ∂volume = ∫ x, mη x ∂volume := by
      have h1 : (fun x => ‖mηC x‖) = fun x => mη x := by
        funext x; simp [hmηC_norm_eq x]
      simp [h1]
    simp [MeasureTheory.eLpNorm_one_eq_lintegral_enorm, h_lint_eq, h_norm_eq]
  have hmη_one : eLpNorm mηC 1 volume = 1 := by
    rw [h_enorm_eq]
    rw [integral_scaledMollifier_eq_one hψ hη_pos]
    simp
  -- Now convert Term C into < ε/4 using the bound on ‖g - f‖ₚ
  have hC_lt :
      eLpNorm (fun x => conv_g x - conv_f x) p volume < ENNReal.ofReal (ε / 4) := by
    -- Bound by product and then use hmη_one
    have h_mul_le :
        eLpNorm (fun x => conv_g x - conv_f x) p volume
          ≤ eLpNorm (fun x => g x - f x) p volume := by
      calc eLpNorm (fun x => conv_g x - conv_f x) p volume
          ≤ eLpNorm (fun x => g x - f x) p volume * eLpNorm mηC 1 volume := h_conv_diff_bound
        _ = eLpNorm (fun x => g x - f x) p volume * 1 := by rw [hmη_one]
        _ = eLpNorm (fun x => g x - f x) p volume := by ring
    exact lt_of_le_of_lt h_mul_le hgf_small
  -- Term B: ‖g - conv_g‖ₚ on the finite-measure core set S is small by uniform bound
  -- First, note that outside S, both g and conv_g vanish once η < 1.
  -- Hence the difference equals its indicator on S.
  have hη_lt_one : η < 1 := lt_of_lt_of_le hη_lt (min_le_right _ _)
  have hS_contains_support :
      tsupport conv_g ⊆ S := by
    -- support(conv_g) ⊆ B_{R + η} ⊆ B_{R + 1} = S
    -- First, upgrade the tsupport bound for the real-valued kernel to the complex-valued one.
    have h_mη_real :
        tsupport (scaledMollifier ψ η)
          ⊆ Metric.closedBall (0 : Fin n → ℝ) η :=
      tsupport_scaledMollifier_subset hψ hη_pos
    have h_support_subset :
        Function.support mηC ⊆ Function.support (scaledMollifier ψ η) := by
      intro x hx
      have : mηC x ≠ 0 := hx
      -- If mη x = 0 then mηC x = 0; hence mη x ≠ 0
      have : mη x ≠ 0 := by
        intro hzero
        apply hx
        show mηC x = 0
        calc mηC x = ↑(mη x) := rfl
          _ = ↑(0 : ℝ) := by rw [hzero]
          _ = (0 : ℂ) := by norm_num
      convert this
    have h_mηC_tsupport_subset :
        tsupport mηC ⊆ Metric.closedBall (0 : Fin n → ℝ) η := by
      -- tsupport mηC ⊆ tsupport mη by support inclusion, then use h_mη_real
      have h_ts_subset : tsupport mηC ⊆ tsupport (scaledMollifier ψ η) := by
        intro x hx
        have hx' : x ∈ closure (Function.support mηC) := by
          simpa [tsupport] using hx
        have hx'' : x ∈ closure (Function.support (scaledMollifier ψ η)) :=
          closure_mono h_support_subset hx'
        simpa [tsupport] using hx''
      exact h_ts_subset.trans h_mη_real
    have h_ball_subset :
        Metric.closedBall (0 : Fin n → ℝ) (R + η)
          ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 1) := by
      intro x hx
      have hx_norm : ‖x‖ ≤ R + η := by
        simpa [dist_eq_norm] using Metric.mem_closedBall.mp hx
      have h_le : R + η ≤ R + 1 := by
        have : (η : ℝ) ≤ 1 := le_of_lt hη_lt_one
        linarith
      have hx_norm' : ‖x‖ ≤ R + 1 := le_trans hx_norm h_le
      exact Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hx_norm')
    -- Use convolution support bound
    have h_conv_support :=
      convolution_support_ball_subset
        (f := g) (g := mηC) (R := R) (δ := η)
        hR_subset h_mηC_tsupport_subset
    -- Finish by transitivity
    exact h_conv_support.trans h_ball_subset
  have h_indicator_eq :
      (fun x => g x - conv_g x)
        = (fun x => Set.indicator S (fun z => g z - conv_g z) x) := by
    funext x
    by_cases hxS : x ∈ S
    · simp [Set.indicator, hxS]
    · -- outside S: both g and conv_g vanish
      have hx_notin_BR : x ∉ Metric.closedBall (0 : Fin n → ℝ) R := by
        intro hxBR
        have hxS' : x ∈ S := by
          have hxBR' : ‖x‖ ≤ R := by
            simpa [dist_eq_norm] using Metric.mem_closedBall.mp hxBR
          have hxS'' : ‖x‖ ≤ R + 1 := by linarith
          exact Metric.mem_closedBall.mpr (by simpa [hS_def, dist_eq_norm] using hxS'')
        exact hxS hxS'
      have hg_zero : g x = 0 := by
        -- use support inclusion: tsupport g ⊆ closedBall(0,R)
        by_contra hx_nonzero
        have hx_support : x ∈ Function.support g := by
          have : g x ≠ 0 := hx_nonzero
          simpa [Function.support] using this
        have hx_tsupport : x ∈ tsupport g :=
          subset_tsupport _ hx_support
        exact hx_notin_BR (hR_subset hx_tsupport)
      have hconv_zero : conv_g x = 0 := by
        have hx_notin : x ∉ tsupport conv_g := by
          intro hx_in
          have hxS' : x ∈ S := hS_contains_support hx_in
          exact hxS hxS'
        exact image_eq_zero_of_notMem_tsupport hx_notin
      simp [Set.indicator, hxS, hg_zero, hconv_zero]
  -- Use the indicator bound on S with the uniform ε-control given by mollifier_converges_continuous
  have h_pointwise_uniform : ∀ᵐ x ∂volume.restrict S,
      ‖g x - conv_g x‖ ≤ δg := by
    have h_all : ∀ x, ‖g x - conv_g x‖ ≤ δg := by
      intro x
      have : ‖g x - ∫ y, g (x - y) * mηC y‖ < δg := by
        -- apply the uniform convergence result for g with η < δ₀
        have hη_lt_δ₀ : η < δ₀ := lt_of_lt_of_le hη_lt (min_le_left _ _)
        have := hδ₀ η hη_pos hη_lt_δ₀ x
        simpa [conv_g, hconvg] using this
      exact le_of_lt this
    -- The bound holds on S
    apply Filter.Eventually.of_forall
    intro x
    exact h_all x
  have hB_bound :
      eLpNorm (fun x => g x - conv_g x) p volume
        ≤ (volume S) ^ (1 / p.toReal) * ENNReal.ofReal δg := by
    -- Since the function vanishes off S, apply the indicator restriction bound
    have h_indicator_eq' :
        eLpNorm (fun x => g x - conv_g x) p volume
          = eLpNorm (fun x => Set.indicator S (fun z => g z - conv_g z) x) p volume := by
      congr 1
    have h_core :=
      core_indicator_eLpNorm_bound (p := p) (coreSet := S)
        (h_core_meas := hS_meas)
        (g := fun x => g x - conv_g x) (δ := δg)
        (h_bound := by
          -- a.e. bound on S
          simpa using h_pointwise_uniform)
    simpa [h_indicator_eq'] using h_core
  -- Evaluate the right-hand side as ENNReal.ofReal (ε/2)
  have h_mul_eq :
      (volume S) ^ (1 / p.toReal) * ENNReal.ofReal δg
        = ENNReal.ofReal ((volume S) ^ (1 / p.toReal)).toReal * ENNReal.ofReal δg := by
    rw [ENNReal.ofReal_toReal h_powS_ne_top]
  have h_prod_eq :
      (volume S) ^ (1 / p.toReal) * ENNReal.ofReal δg
        = ENNReal.ofReal (ε / 2) := by
    -- Use δg = ε / (2 * ((μ S)^{1/p}).toReal)
    have hμS_toReal_nonneg : 0 ≤ ((volume S) ^ (1 / p.toReal)).toReal := ENNReal.toReal_nonneg
    have h_mul :
        ENNReal.ofReal ((volume S) ^ (1 / p.toReal)).toReal * ENNReal.ofReal δg
          = ENNReal.ofReal (((volume S) ^ (1 / p.toReal)).toReal * δg) := by
      rw [← ENNReal.ofReal_mul hμS_toReal_nonneg]
    have h_target : ((volume S) ^ (1 / p.toReal)).toReal * δg = ε / 2 := by
      rw [hδg_def]
      have hpow_pos : 0 < ((volume S) ^ (1 / p.toReal)).toReal := by
        apply ENNReal.toReal_pos
        · exact ne_of_gt (ENNReal.rpow_pos_of_nonneg hμS_pos h_exponent_nonneg)
        · exact h_powS_ne_top
      field_simp [ne_of_gt hpow_pos]
    -- Put the pieces together
    calc
      (volume S) ^ (1 / p.toReal) * ENNReal.ofReal δg
          = ENNReal.ofReal ((volume S) ^ (1 / p.toReal)).toReal * ENNReal.ofReal δg := h_mul_eq
      _ = ENNReal.ofReal (((volume S) ^ (1 / p.toReal)).toReal * δg) := h_mul
      _ = ENNReal.ofReal (ε / 2) := by rw [h_target]
  have hB_le :
      eLpNorm (fun x => g x - conv_g x) p volume ≤ ENNReal.ofReal (ε / 2) := by
    calc eLpNorm (fun x => g x - conv_g x) p volume
        ≤ (volume S) ^ (1 / p.toReal) * ENNReal.ofReal δg := hB_bound
      _ = ENNReal.ofReal (ε / 2) := h_prod_eq
  -- Finally, add the three bounds: ε/4 + ε/2 + ε/4 = ε
  -- Use monotonicity of addition in ℝ≥0∞.
  have h_sum_le :
      eLpNorm (fun x => f x - g x) p volume
        + eLpNorm (fun x => g x - conv_g x) p volume
        ≤ ENNReal.ofReal (ε / 4 + ε / 2) := by
    calc eLpNorm (fun x => f x - g x) p volume
            + eLpNorm (fun x => g x - conv_g x) p volume
          ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 2) := by
            exact add_le_add (le_of_lt hA_lt) hB_le
        _ = ENNReal.ofReal (ε / 4 + ε / 2) := by
            rw [← ENNReal.ofReal_add] <;> linarith
  have h_total_lt :
      eLpNorm (fun x => f x - g x) p volume
        + eLpNorm (fun x => g x - conv_g x) p volume
        + eLpNorm (fun x => conv_g x - conv_f x) p volume
        < ENNReal.ofReal (ε / 4 + ε / 2 + ε / 4) := by
    have h_sum_ne_top : eLpNorm (fun x => f x - g x) p volume
          + eLpNorm (fun x => g x - conv_g x) p volume ≠ ⊤ := by
      apply ne_of_lt
      calc eLpNorm (fun x => f x - g x) p volume
              + eLpNorm (fun x => g x - conv_g x) p volume
            ≤ ENNReal.ofReal (ε / 4 + ε / 2) := h_sum_le
          _ < ⊤ := ENNReal.ofReal_lt_top
    calc eLpNorm (fun x => f x - g x) p volume
            + eLpNorm (fun x => g x - conv_g x) p volume
            + eLpNorm (fun x => conv_g x - conv_f x) p volume
          < ENNReal.ofReal (ε / 4 + ε / 2) + ENNReal.ofReal (ε / 4) := by
            exact ENNReal.add_lt_add_of_le_of_lt h_sum_ne_top h_sum_le hC_lt
        _ = ENNReal.ofReal (ε / 4 + ε / 2 + ε / 4) := by
            rw [← ENNReal.ofReal_add] <;> linarith
  -- Conclude by triangle inequality
  have h_target_le :=
    calc
      eLpNorm (fun x => f x - conv_f x) p volume
          ≤ eLpNorm (fun x => f x - g x) p volume
              + eLpNorm (fun x => g x - conv_g x) p volume
              + eLpNorm (fun x => conv_g x - conv_f x) p volume :=
            h_triangle
      _ < ENNReal.ofReal (ε / 4 + ε / 2 + ε / 4) := h_total_lt
  -- ε/4 + ε/2 + ε/4 = ε
  have hε_sum : ε / 4 + ε / 2 + ε / 4 = ε := by ring
  simpa [conv_f, hconvf, hε_sum]
    using h_target_le
end Newton
