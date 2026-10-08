-- Prove2me | solution 1 for MDPFinance.Semicontinuous.weakly_continuous_kernel_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T03:46:36.102296+00:00
-- url     : https://prove2.me/submissions/4062538b-f77b-4a99-9bf3-bace5e97743f

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous


namespace MDPFinance.Semicontinuous

namespace MDPWk

open Filter Topology Set MeasureTheory

variable {X Ω : Type*} [TopologicalSpace X] [MeasurableSpace Ω] [TopologicalSpace Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [OpensMeasurableSpace Ω]

lemma open_liminf (μ : X → Measure Ω) [hμ : ∀ p, IsProbabilityMeasure (μ p)]
    (hcont : ∀ g : Ω → ℝ, Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Continuous (fun p => ∫ x, g x ∂(μ p)))
    {xs : ℕ → X} {p : X} (hx : Tendsto xs atTop (𝓝 p)) (G : Set Ω) (hG : IsOpen G) :
    μ p G ≤ atTop.liminf (fun k => μ (xs k) G) := by
  let νs : ℕ → ProbabilityMeasure Ω := fun k => ⟨μ (xs k), hμ _⟩
  let ν : ProbabilityMeasure Ω := ⟨μ p, hμ _⟩
  have ht : Tendsto νs atTop (𝓝 ν) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have := ((hcont f f.continuous ⟨‖f‖, fun x => by
      have := f.norm_coe_le_norm x; rwa [Real.norm_eq_abs] at this⟩).tendsto p).comp hx
    exact this
  exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto ht hG

lemma real_liminf (μ : X → Measure Ω) [hμ : ∀ p, IsProbabilityMeasure (μ p)]
    (hcont : ∀ g : Ω → ℝ, Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Continuous (fun p => ∫ x, g x ∂(μ p)))
    {xs : ℕ → X} {p : X} (hx : Tendsto xs atTop (𝓝 p))
    {f : Ω → ℝ} (hf : LowerSemicontinuous f) (f_nn : 0 ≤ f) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂(μ p) ≤
      atTop.liminf (fun k => ∫⁻ x, ENNReal.ofReal (f x) ∂(μ (xs k))) := by
  have hfm : Measurable f := hf.measurable
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall f_nn) hfm.aemeasurable]
  calc ∫⁻ (t : ℝ) in Set.Ioi 0, μ p {a | t < f a}
      ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, atTop.liminf (fun k ↦ (μ (xs k)) {a | t < f a}) :=
        lintegral_mono (fun t ↦ open_liminf μ hcont hx _ (hf.isOpen_preimage t))
    _ ≤ atTop.liminf (fun k ↦ ∫⁻ (t : ℝ) in Set.Ioi 0, (μ (xs k)) {a | t < f a}) :=
        lintegral_liminf_le (fun n ↦ Antitone.measurable (fun s t hst ↦
            measure_mono (fun ω hω ↦ lt_of_le_of_lt hst hω)))

lemma ennreal_liminf (μ : X → Measure Ω) [hμ : ∀ p, IsProbabilityMeasure (μ p)]
    (hcont : ∀ g : Ω → ℝ, Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Continuous (fun p => ∫ x, g x ∂(μ p)))
    {xs : ℕ → X} {p : X} (hx : Tendsto xs atTop (𝓝 p))
    {w : Ω → ENNReal} (hw : LowerSemicontinuous w) :
    ∫⁻ x, w x ∂(μ p) ≤ atTop.liminf (fun k => ∫⁻ x, w x ∂(μ (xs k))) := by
  have hwm : Measurable w := hw.measurable
  let fm : ℕ → Ω → ℝ := fun m x => ENNReal.truncateToReal (m : ENNReal) (w x)
  have hfm_eq : ∀ m x, ENNReal.ofReal (fm m x) = min (m : ENNReal) (w x) := by
    intro m x
    simp only [fm, ENNReal.truncateToReal]
    exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top m) (min_le_left _ _))
  have hfm_lsc : ∀ m, LowerSemicontinuous (fm m) := fun m =>
    (ENNReal.continuous_truncateToReal (ENNReal.natCast_ne_top m)).comp_lowerSemicontinuous hw
      (ENNReal.monotone_truncateToReal (ENNReal.natCast_ne_top m))
  have hsup : ∀ x, w x = ⨆ m : ℕ, min (m : ENNReal) (w x) := by
    intro x
    rw [← iSup_inf_eq, ENNReal.iSup_natCast, top_inf_eq]
  have hint : ∫⁻ x, w x ∂(μ p) = ⨆ m : ℕ, ∫⁻ x, min (m : ENNReal) (w x) ∂(μ p) := by
    conv_lhs => rw [show w = fun x => ⨆ m : ℕ, min (m : ENNReal) (w x) from funext hsup]
    apply lintegral_iSup
    · intro m; exact measurable_const.min hwm
    · intro m n hmn x
      exact min_le_min_right _ (by exact_mod_cast hmn)
  rw [hint]
  refine iSup_le fun m => ?_
  have h1 := real_liminf μ hcont hx (hfm_lsc m) (fun x => ENNReal.toReal_nonneg)
  simp_rw [hfm_eq] at h1
  refine h1.trans (liminf_le_liminf (Eventually.of_forall fun k => ?_))
  exact lintegral_mono fun x => min_le_right _ _

lemma lsc_lintegral [FirstCountableTopology X] (μ : X → Measure Ω)
    [hμ : ∀ p, IsProbabilityMeasure (μ p)]
    (hcont : ∀ g : Ω → ℝ, Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Continuous (fun p => ∫ x, g x ∂(μ p)))
    {w : Ω → ENNReal} (hw : LowerSemicontinuous w) :
    LowerSemicontinuous (fun p => ∫⁻ x, w x ∂(μ p)) := by
  intro p y hy
  by_contra h
  rw [Filter.not_eventually] at h
  obtain ⟨xs, hxs, hle⟩ := exists_seq_forall_of_frequently h
  simp only [not_lt] at hle
  have h1 := ennreal_liminf μ hcont hxs hw
  have h2 : atTop.liminf (fun k => ∫⁻ x, w x ∂(μ (xs k))) ≤ y :=
    liminf_le_of_frequently_le' (Frequently.of_forall hle)
  exact absurd (h1.trans h2) (not_le.2 hy)

end MDPWk


open Filter Topology Set MeasureTheory

lemma wk_te (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]

lemma wk_usc_of_coe {X : Type*} [TopologicalSpace X] {h : X → ℝ} (C : ℝ)
    (H : UpperSemicontinuous (fun p => ((h p - C : ℝ) : EReal))) : UpperSemicontinuous h := by
  intro p y hy
  have := H p ((y - C : ℝ) : EReal) (EReal.coe_lt_coe_iff.2 (by linarith))
  exact this.mono fun q hq => by have := EReal.coe_lt_coe_iff.1 hq; linarith

lemma wk_fwd_bdd {E X : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
    [TopologicalSpace X] (b : E → ℝ)
    (Q : X → Measure E) [∀ p, IsProbabilityMeasure (Q p)]
    (hi : ∀ v : E → EReal, v ∈ IBbPlus b → UpperSemicontinuous v →
        UpperSemicontinuous (fun p => erealIntegral (Q p) v))
    (g : E → ℝ) (hg : Continuous g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) :
    UpperSemicontinuous (fun p => ∫ x, g x ∂(Q p)) := by
  have hgi : ∀ p, Integrable g (Q p) := fun p =>
    Integrable.of_bound hg.measurable.aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  let v : E → EReal := fun x => ((g x - C : ℝ) : EReal)
  have hvle : ∀ x, v x ≤ 0 := fun x => by
    have := le_abs_self (g x); have := hC x
    exact EReal.coe_nonpos.2 (by linarith)
  have hv : v ∈ IBbPlus b := by
    refine ⟨measurable_coe_real_ereal.comp (hg.measurable.sub_const C),
      fun x => EReal.coe_ne_top _, 0, le_rfl, fun x => ?_⟩
    rw [sup_eq_right.2 (hvle x)]; simp
  have hvu : UpperSemicontinuous v :=
    (continuous_coe_real_ereal.comp (hg.sub continuous_const)).upperSemicontinuous
  have H := hi v hv hvu
  apply wk_usc_of_coe C
  convert H using 1
  funext p
  unfold erealIntegral
  have h1 : (fun x => (v x ⊔ 0).toENNReal) = fun _ => 0 := by
    funext x; rw [sup_eq_right.2 (hvle x)]; exact EReal.toENNReal_zero
  have h2 : (fun x => ((-v x) ⊔ 0).toENNReal) = fun x => ENNReal.ofReal (C - g x) := by
    funext x
    have : -v x = ((C - g x : ℝ) : EReal) := by
      simp only [v]; rw [← EReal.coe_neg]; congr 1; ring
    rw [this, sup_eq_left.2 (EReal.coe_nonneg.2 (by
      have := le_abs_self (g x); have := hC x; linarith)), wk_te]
  rw [h1, h2, lintegral_zero]
  have h3 : ∫⁻ x, ENNReal.ofReal (C - g x) ∂(Q p) = ENNReal.ofReal (C - ∫ x, g x ∂(Q p)) := by
    have hint : Integrable (fun x => C - g x) (Q p) := (integrable_const C).sub (hgi p)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x => by
        have := le_abs_self (g x); have := hC x; show (0:ℝ) ≤ C - g x; linarith)]
    rw [integral_sub (integrable_const C) (hgi p)]
    simp
  rw [h3]
  have hnn : 0 ≤ C - ∫ x, g x ∂(Q p) := by
    have := norm_integral_le_of_norm_le_const (μ := Q p) (C := C)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
    simp only [probReal_univ, mul_one, Real.norm_eq_abs] at this
    have := le_abs_self (∫ x, g x ∂(Q p)); linarith
  rw [EReal.coe_ennreal_ofReal, max_eq_left hnn]
  simp only [EReal.coe_ennreal_zero, zero_add]
  rw [← EReal.coe_neg]; congr 1; ring

lemma wk_fwd_cont {E X : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
    [TopologicalSpace X] (b : E → ℝ)
    (Q : X → Measure E) [∀ p, IsProbabilityMeasure (Q p)]
    (hi : ∀ v : E → EReal, v ∈ IBbPlus b → UpperSemicontinuous v →
        UpperSemicontinuous (fun p => erealIntegral (Q p) v))
    (g : E → ℝ) (hg : Continuous g) (hC : ∃ C, ∀ x, |g x| ≤ C) :
    Continuous (fun p => ∫ x, g x ∂(Q p)) := by
  obtain ⟨C, hC⟩ := hC
  have hu := wk_fwd_bdd b Q hi g hg C hC
  have hu' := wk_fwd_bdd b Q hi (fun x => -g x) hg.neg C (fun x => by rw [abs_neg]; exact hC x)
  refine continuous_iff_lower_upperSemicontinuous.2 ⟨fun p y hy => ?_, hu⟩
  have := hu' p (-y) (by simp only [integral_neg]; linarith)
  exact this.mono fun q hq => by simp only [integral_neg] at hq; linarith



open Filter Topology Set MeasureTheory

lemma wk_int_b {E X : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
    (b : E → ℝ) (hb_nn : ∀ x, 0 ≤ b x) (hb_cont : Continuous b)
    (Q : X → Measure E) (hQb : ∀ p, ∫⁻ x', ENNReal.ofReal (b x') ∂(Q p) < ⊤) (p : X) :
    Integrable b (Q p) ∧ ∫⁻ x', ENNReal.ofReal (b x') ∂(Q p) = ENNReal.ofReal (∫ x, b x ∂(Q p)) := by
  have hI : Integrable b (Q p) := ⟨hb_cont.measurable.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hb_nn)).2 (hQb p)⟩
  exact ⟨hI, (ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hb_nn)).symm⟩

lemma wk_fwd_b {E X : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E]
    [TopologicalSpace X] [FirstCountableTopology X]
    (b : E → ℝ) (hb_nn : ∀ x, 0 ≤ b x) (hb_cont : Continuous b)
    (Q : X → Measure E) [∀ p, IsProbabilityMeasure (Q p)]
    (hQb : ∀ p, ∫⁻ x', ENNReal.ofReal (b x') ∂(Q p) < ⊤)
    (hi : ∀ v : E → EReal, v ∈ IBbPlus b → UpperSemicontinuous v →
        UpperSemicontinuous (fun p => erealIntegral (Q p) v)) :
    Continuous (fun p => ∫ x, b x ∂(Q p)) := by
  have hcont := fun g hg hC => wk_fwd_cont b Q hi g hg hC
  let v : E → EReal := fun x => ((b x : ℝ) : EReal)
  have hv : v ∈ IBbPlus b := by
    refine ⟨measurable_coe_real_ereal.comp hb_cont.measurable, fun x => EReal.coe_ne_top _, 1,
      zero_le_one, fun x => ?_⟩
    rw [sup_eq_left.2 (EReal.coe_nonneg.2 (hb_nn x)), one_mul]
  have hvu : UpperSemicontinuous v :=
    (continuous_coe_real_ereal.comp hb_cont).upperSemicontinuous
  have H := hi v hv hvu
  have hu : UpperSemicontinuous (fun p => ∫ x, b x ∂(Q p)) := by
    apply wk_usc_of_coe 0
    convert H using 1
    funext p
    unfold erealIntegral
    have h1 : (fun x => (v x ⊔ 0).toENNReal) = fun x => ENNReal.ofReal (b x) := by
      funext x; rw [sup_eq_left.2 (EReal.coe_nonneg.2 (hb_nn x))]; exact wk_te _
    have h2 : (fun x => ((-v x) ⊔ 0).toENNReal) = fun _ => 0 := by
      funext x
      rw [sup_eq_right.2 (by rw [EReal.neg_le, neg_zero]; exact EReal.coe_nonneg.2 (hb_nn x))]
      exact EReal.toENNReal_zero
    rw [h1, h2, lintegral_zero, (wk_int_b b hb_nn hb_cont Q hQb p).2,
      EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg hb_nn)]
    simp
  have hl : LowerSemicontinuous (fun p => ∫ x, b x ∂(Q p)) := by
    have hL := MDPWk.lsc_lintegral Q hcont
      (w := fun x => ENNReal.ofReal (b x)) (ENNReal.continuous_ofReal.comp hb_cont).lowerSemicontinuous
    intro p y hy
    rcases lt_or_ge y 0 with hy0 | hy0
    · exact Eventually.of_forall fun q => lt_of_lt_of_le hy0 (integral_nonneg hb_nn)
    · have h1 : ENNReal.ofReal y < ∫⁻ x, ENNReal.ofReal (b x) ∂(Q p) := by
        rw [(wk_int_b b hb_nn hb_cont Q hQb p).2]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hy0).2 hy
      exact (hL p _ h1).mono fun q hq => by
        have hq : ENNReal.ofReal y < ∫⁻ x, ENNReal.ofReal (b x) ∂(Q q) := hq
        rw [(wk_int_b b hb_nn hb_cont Q hQb q).2] at hq
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hy0).1 hq
  exact continuous_iff_lower_upperSemicontinuous.2 ⟨hl, hu⟩

lemma wk_bwd {E X : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E]
    [TopologicalSpace X] [FirstCountableTopology X]
    (b : E → ℝ) (hb_nn : ∀ x, 0 ≤ b x) (hb_cont : Continuous b)
    (Q : X → Measure E) [∀ p, IsProbabilityMeasure (Q p)]
    (hQb : ∀ p, ∫⁻ x', ENNReal.ofReal (b x') ∂(Q p) < ⊤)
    (hBc : Continuous (fun p => ∫ x, b x ∂(Q p)))
    (hcont : ∀ g : E → ℝ, Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Continuous (fun p => ∫ x, g x ∂(Q p)))
    (v : E → EReal) (hv : v ∈ IBbPlus b) (hvu : UpperSemicontinuous v) :
    UpperSemicontinuous (fun p => erealIntegral (Q p) v) := by
  obtain ⟨hvm, hvtop, c, hc, hvc⟩ := hv
  let w : E → ENNReal := fun x => ((((c * b x : ℝ)) : EReal) + -v x).toENNReal
  have hw_lsc : LowerSemicontinuous w := by
    have h1 : LowerSemicontinuous (fun x => (((c * b x : ℝ)) : EReal)) :=
      (continuous_coe_real_ereal.comp (continuous_const.mul hb_cont)).lowerSemicontinuous
    have h2 : LowerSemicontinuous (fun x => -v x) :=
      (continuous_neg (G := EReal)).comp_upperSemicontinuous_antitone hvu
        (fun a b h => EReal.neg_le_neg_iff.2 h)
    have h3 : LowerSemicontinuous (fun x => (((c * b x : ℝ)) : EReal) + -v x) := fun x =>
      LowerSemicontinuousAt.add' (h1 x) (h2 x)
        (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _)))
    exact EReal.continuous_toENNReal.comp_lowerSemicontinuous h3
      (fun a b h => EReal.toENNReal_le_toENNReal h)
  have hpt : ∀ x, (v x ⊔ 0).toENNReal + w x =
      ENNReal.ofReal (c * b x) + ((-v x) ⊔ 0).toENNReal := by
    intro x
    have hcb : 0 ≤ c * b x := mul_nonneg hc (hb_nn x)
    have h1 := hvc x
    have h2 := hvtop x
    simp only [w]
    generalize v x = t at h1 h2 ⊢
    induction t using EReal.rec with
    | bot => rw [EReal.neg_bot, EReal.coe_add_top]; simp
    | top => exact absurd rfl h2
    | coe t =>
      rw [← EReal.coe_neg, ← EReal.coe_add, wk_te]
      rcases le_total t 0 with ht | ht
      · rw [sup_eq_right.2 (EReal.coe_nonpos.2 ht),
          sup_eq_left.2 (EReal.coe_nonneg.2 (by linarith)), wk_te, EReal.toENNReal_zero,
          zero_add, ← ENNReal.ofReal_add hcb (by linarith)]
      · have htc : t ≤ c * b x := by
          have := le_trans (le_sup_left) h1
          exact EReal.coe_le_coe_iff.1 this
        rw [sup_eq_left.2 (EReal.coe_nonneg.2 ht),
          sup_eq_right.2 (EReal.coe_nonpos.2 (by linarith)), wk_te, EReal.toENNReal_zero,
          add_zero, ← ENNReal.ofReal_add ht (by linarith)]
        congr 1 <;> ring
  have hPm : Measurable (fun x => (v x ⊔ 0).toENNReal) :=
    (hvm.max measurable_const).ereal_toENNReal
  have hCm : Measurable (fun x => ENNReal.ofReal (c * b x)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hb_cont.measurable)
  have hsum : ∀ p, ∫⁻ x, (v x ⊔ 0).toENNReal ∂(Q p) + ∫⁻ x, w x ∂(Q p) =
      ∫⁻ x, ENNReal.ofReal (c * b x) ∂(Q p) + ∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂(Q p) := by
    intro p
    rw [← lintegral_add_left hPm, ← lintegral_add_left hCm]
    exact lintegral_congr hpt
  have hCB : ∀ p, ∫⁻ x, ENNReal.ofReal (c * b x) ∂(Q p) =
      ENNReal.ofReal (c * ∫ x, b x ∂(Q p)) := by
    intro p
    simp_rw [ENNReal.ofReal_mul hc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, (wk_int_b b hb_nn hb_cont Q hQb p).2]
  have hPle : ∀ p, ∫⁻ x, (v x ⊔ 0).toENNReal ∂(Q p) ≤ ∫⁻ x, ENNReal.ofReal (c * b x) ∂(Q p) :=
    fun p => lintegral_mono fun x => by
      have := EReal.toENNReal_le_toENNReal (hvc x); rwa [wk_te] at this
  have key : ∀ p, erealIntegral (Q p) v =
      ((c * ∫ x, b x ∂(Q p) : ℝ) : EReal) + -((∫⁻ x, w x ∂(Q p) : ENNReal) : EReal) := by
    intro p
    unfold erealIntegral
    have hs := hsum p
    rw [hCB p] at hs
    have hPle' := hPle p
    rw [hCB p] at hPle'
    have hPt : ∫⁻ x, (v x ⊔ 0).toENNReal ∂(Q p) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hPle'
    have hFnn : 0 ≤ c * ∫ x, b x ∂(Q p) := mul_nonneg hc (integral_nonneg hb_nn)
    by_cases hW : ∫⁻ x, w x ∂(Q p) = ⊤
    · have hN : ∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂(Q p) = ⊤ := by
        by_contra hN
        rw [hW, add_top] at hs
        exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hN⟩ hs.symm
      rw [hW, hN]
      simp
    · have hN : ∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂(Q p) ≠ ⊤ := by
        intro hN
        rw [hN, add_top] at hs
        exact ENNReal.add_ne_top.2 ⟨hPt, hW⟩ hs
      have hr := congrArg ENNReal.toReal hs
      rw [ENNReal.toReal_add hPt hW, ENNReal.toReal_add ENNReal.ofReal_ne_top hN,
        ENNReal.toReal_ofReal hFnn] at hr
      rw [← EReal.coe_ennreal_toReal hPt, ← EReal.coe_ennreal_toReal hN,
        ← EReal.coe_ennreal_toReal hW, ← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add,
        ← EReal.coe_add]
      congr 1
      linarith
  have hWl := MDPWk.lsc_lintegral Q hcont hw_lsc
  have h1 : UpperSemicontinuous (fun p => ((c * ∫ x, b x ∂(Q p) : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp (continuous_const.mul hBc)).upperSemicontinuous
  have h2 : UpperSemicontinuous (fun p => -((∫⁻ x, w x ∂(Q p) : ENNReal) : EReal)) :=
    (continuous_neg (G := EReal)).comp_lowerSemicontinuous_antitone
      (continuous_coe_ennreal_ereal.comp_lowerSemicontinuous hWl
        (fun a b h => EReal.coe_ennreal_le_coe_ennreal_iff.2 h))
      (fun a b h => EReal.neg_le_neg_iff.2 h)
  have h3 : UpperSemicontinuous (fun p => ((c * ∫ x, b x ∂(Q p) : ℝ) : EReal) +
      -((∫⁻ x, w x ∂(Q p) : ENNReal) : EReal)) := fun p =>
    UpperSemicontinuousAt.add' (h1 p) (h2 p)
      (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _)))
  convert h3 using 1
  funext p
  exact key p

theorem wk_core {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (hb_cont : Continuous b)
    (Q : Kernel (E × A) E) [∀ p, IsProbabilityMeasure (Q p)]
    (hQb : ∀ p, ∫⁻ x', ENNReal.ofReal (b x') ∂(Q p) < ⊤) :
    (∀ v : E → EReal, v ∈ IBbPlus b → UpperSemicontinuous v →
        UpperSemicontinuous (fun p : E × A => erealIntegral (Q p) v))
    ↔
    (Continuous (fun p : E × A => ∫ x', b x' ∂(Q p)) ∧
     ∀ v : E → ℝ, Continuous v → (∃ c, ∀ x, |v x| ≤ c) →
       Continuous (fun p : E × A => ∫ x', v x' ∂(Q p)) ∧
       ∃ c, ∀ p, |∫ x', v x' ∂(Q p)| ≤ c) := by
  constructor
  · intro hi
    refine ⟨wk_fwd_b b hb.hb_nonneg hb_cont (fun p => Q p) hQb hi, fun g hg hC => ⟨
      wk_fwd_cont b (fun p => Q p) hi g hg hC, ?_⟩⟩
    obtain ⟨C, hC⟩ := hC
    refine ⟨C, fun p => ?_⟩
    have := norm_integral_le_of_norm_le_const (μ := Q p) (C := C)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
    simpa [probReal_univ, Real.norm_eq_abs] using this
  · rintro ⟨hBc, hw⟩ v hv hvu
    exact wk_bwd b hb.hb_nonneg hb_cont (fun p => Q p) hQb hBc
      (fun g hg hC => (hw g hg hC).1) v hv hvu

end MDPFinance.Semicontinuous

open MDPFinance.Semicontinuous


theorem solution {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (hb_cont : Continuous b)
    (Q : Kernel (E × A) E) [∀ p, IsProbabilityMeasure (Q p)]
    (hQb : ∀ p, ∫⁻ x', ENNReal.ofReal (b x') ∂(Q p) < ⊤) :
    (∀ v : E → EReal, v ∈ IBbPlus b → UpperSemicontinuous v →
        UpperSemicontinuous (fun p : E × A => erealIntegral (Q p) v))
    ↔
    (Continuous (fun p : E × A => ∫ x', b x' ∂(Q p)) ∧
     ∀ v : E → ℝ, Continuous v → (∃ c, ∀ x, |v x| ≤ c) →
       Continuous (fun p : E × A => ∫ x', v x' ∂(Q p)) ∧
       ∃ c, ∀ p, |∫ x', v x' ∂(Q p)| ≤ c) := by
  exact wk_core M b cr cg αb hb hb_cont Q hQb
