-- Prove2me | solution 1 for ModelRiskOT.Duality.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T21:40:52.661219+00:00
-- url     : https://prove2.me/submissions/84ed2542-3186-4eb3-aa18-c4abe6e7cf15

/- Standalone exact original ModelRiskOT.Duality.theorem_1 proof.
All helper proofs are inlined; original Definitions are the only external
platform dependencies. The supporting geometry provenance is retained below. -/
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ModelRiskOT_Duality_primalValue
import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_ModelRiskOT_Duality_phiLam
import Definitions.Def_ModelRiskOT_Duality_dualFeasible
import Definitions.Def_ModelRiskOT_Duality_AssumptionA1
import Definitions.Def_ModelRiskOT_Duality_dualValue

set_option autoImplicit false

/- Source: Solutions/ModelRisk_ExtIntegral.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality

lemma extIntegral_mono {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → EReal) (hfg : f ≤ᵐ[μ] g) : extIntegral μ f ≤ extIntegral μ g := by
  apply EReal.sub_le_sub
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono_ae (hfg.mono fun _ h ↦ EReal.toENNReal_le_toENNReal h))
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono_ae (hfg.mono fun _ h ↦
        EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr h)))

lemma extIntegral_congr_ae {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → EReal) (hfg : f =ᵐ[μ] g) : extIntegral μ f = extIntegral μ g :=
  le_antisymm (extIntegral_mono μ f g hfg.le) (extIntegral_mono μ g f hfg.ge)

lemma extIntegral_eq_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ) :
    extIntegral μ (fun x ↦ (f x : EReal)) = (∫ x, f x ∂μ : ℝ) := by
  have hp : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm f).trans_lt hf.2).ne
  have hn : (∫⁻ x, ENNReal.ofReal (-f x) ∂μ) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm (fun x ↦ -f x)).trans_lt hf.neg.2).ne
  unfold extIntegral
  simp only [EReal.real_coe_toENNReal, ← EReal.coe_neg]
  rw [← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
    ← EReal.coe_sub, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]

lemma extIntegral_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (T : X → Y) (hT : Measurable T) (f : Y → EReal)
    (hf : AEMeasurable f (μ.map T)) :
    extIntegral (μ.map T) f = extIntegral μ (fun x ↦ f (T x)) := by
  unfold extIntegral
  rw [lintegral_map' (f := fun y ↦ (f y).toENNReal)
      (measurable_ereal_toENNReal.comp_aemeasurable hf) hT.aemeasurable,
    lintegral_map' (f := fun y ↦ (-f y).toENNReal)
      (measurable_ereal_toENNReal.comp_aemeasurable hf.neg) hT.aemeasurable]

lemma negativePart_finite_of_integrable_lower_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ) (φ : X → EReal)
    (hφ : ∀ᵐ x ∂μ, (f x : EReal) ≤ φ x) :
    (∫⁻ x, (-φ x).toENNReal ∂μ) ≠ ⊤ := by
  have hn : (∫⁻ x, ENNReal.ofReal (-f x) ∂μ) < ⊤ :=
    (lintegral_ofReal_le_lintegral_enorm (fun x ↦ -f x)).trans_lt hf.neg.2
  have hb : (∫⁻ x, (-φ x).toENNReal ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (-f x) ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [hφ] with x hx
    simpa only [← EReal.coe_neg, EReal.real_coe_toENNReal] using
      EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr hx)
  exact (hb.trans_lt hn).ne

end ModelRiskCodex

/- Source: Solutions/ModelRisk_SelectorPlan.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality

noncomputable def selectorPlan {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (v : S → S) : Measure (S × S) := μ.map (fun x ↦ (x, v x))

lemma selectorPlan_probability {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (v : S → S) (hv : Measurable v) :
    IsProbabilityMeasure (selectorPlan μ v) :=
  μ.isProbabilityMeasure_map (measurable_id.prodMk hv).aemeasurable

lemma selectorPlan_first_marginal {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (v : S → S) (hv : Measurable v) :
    (selectorPlan μ v).map Prod.fst = μ := by
  unfold selectorPlan
  change (μ.map (fun x ↦ (id x, v x))).map Prod.fst = μ
  rw [Measure.map_map measurable_fst (measurable_id.prodMk hv)]
  exact Measure.map_id'

lemma selectorPlan_cost {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (v : S → S) (hv : Measurable v) (c : S → S → ℝ)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2)) :
    (∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂selectorPlan μ v) =
      ∫⁻ x, ENNReal.ofReal (c x (v x)) ∂μ :=
  lintegral_map (ENNReal.measurable_ofReal.comp hc) (measurable_id.prodMk hv)

lemma selectorPlan_objective {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (v : S → S) (hv : Measurable v) (f : S → ℝ)
    (hf : Measurable f) (hfi : Integrable (fun x ↦ f (v x)) μ) :
    primalObj f (selectorPlan μ v) = (∫ x, f (v x) ∂μ : ℝ) := by
  unfold primalObj selectorPlan
  rw [extIntegral_map μ (fun x ↦ (x, v x)) (measurable_id.prodMk hv)
    (fun p : S × S ↦ (f p.2 : EReal))
    ((measurable_coe_real_ereal.comp (hf.comp measurable_snd)).aemeasurable)]
  exact extIntegral_eq_integral μ (fun x ↦ f (v x)) hfi

lemma selectorPlan_cost_toReal {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (v : S → S) (hv : Measurable v) (c : S → S → ℝ)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2))
    (hc0 : ∀ x y, 0 ≤ c x y) (hci : Integrable (fun x ↦ c x (v x)) μ) :
    (∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂selectorPlan μ v).toReal =
      ∫ x, c x (v x) ∂μ := by
  rw [selectorPlan_cost μ v hv c hc]
  exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x ↦ hc0 x (v x))
    hci.aestronglyMeasurable).symm

lemma selectorPlan_feasible {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (v : S → S) (hv : Measurable v)
    (c : S → S → ℝ) (hc : Measurable (fun p : S × S ↦ c p.1 p.2))
    (hc0 : ∀ x y, 0 ≤ c x y) (hci : Integrable (fun x ↦ c x (v x)) μ)
    (δ : ℝ) (hbudget : (∫ x, c x (v x) ∂μ) ≤ δ) :
    selectorPlan μ v ∈ primalFeasible c μ δ := by
  refine ⟨selectorPlan_probability μ v hv, selectorPlan_first_marginal μ v hv, ?_⟩
  rw [selectorPlan_cost μ v hv c hc]
  have hn : (∫⁻ x, ENNReal.ofReal (c x (v x)) ∂μ) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hci.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ hc0 x (v x))).mpr hci
  rw [← ENNReal.ofReal_toReal hn]
  apply ENNReal.ofReal_le_ofReal
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x ↦ hc0 x (v x)) hci.aestronglyMeasurable]
  exact hbudget

end ModelRiskCodex

/- Source: Solutions/ModelRisk_CouplingValues.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory

/-- Real cost/payoff pairs of probability couplings with the original first
marginal and finite integrable cost and payoff. -/
def finiteCouplingValues {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (c : S → S → ℝ) (f : S → ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ π : Measure (S × S), IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧
    Integrable (fun p ↦ c p.1 p.2) π ∧ Integrable (fun p ↦ f p.2) π ∧
    z = ((∫ p, c p.1 p.2 ∂π), (∫ p, f p.2 ∂π))}

lemma coupling_probability_mixture {Z : Type*} [MeasurableSpace Z]
    (π ρ : Measure Z) (hπ : IsProbabilityMeasure π) (hρ : IsProbabilityMeasure ρ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsProbabilityMeasure (ENNReal.ofReal a • π + ENNReal.ofReal b • ρ) := by
  let := hπ
  let := hρ
  constructor
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ha hb, hab]
  norm_num

lemma coupling_mixture_first_marginal {S : Type*} [MeasurableSpace S]
    (π ρ : Measure (S × S)) (μ : Measure S)
    (hπ : π.map Prod.fst = μ) (hρ : ρ.map Prod.fst = μ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (ENNReal.ofReal a • π + ENNReal.ofReal b • ρ).map Prod.fst = μ := by
  rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
    hπ, hρ, ← add_smul, ← ENNReal.ofReal_add ha hb, hab]
  simp

lemma coupling_mixture_integral {Z : Type*} [MeasurableSpace Z]
    (π ρ : Measure Z) (f : Z → ℝ) (hπ : Integrable f π) (hρ : Integrable f ρ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ z, f z ∂(ENNReal.ofReal a • π + ENNReal.ofReal b • ρ)) =
      a * (∫ z, f z ∂π) + b * (∫ z, f z ∂ρ) := by
  rw [integral_add_measure (hπ.smul_measure ENNReal.ofReal_ne_top)
    (hρ.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]

lemma finiteCouplingValues_convex {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (c : S → S → ℝ) (f : S → ℝ) : Convex ℝ (finiteCouplingValues μ c f) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨π, hπ, hπμ, hπc, hπf, rfl⟩
  rcases hy with ⟨ρ, hρ, hρμ, hρc, hρf, rfl⟩
  refine ⟨ENNReal.ofReal a • π + ENNReal.ofReal b • ρ,
    coupling_probability_mixture π ρ hπ hρ a b ha hb hab,
    coupling_mixture_first_marginal π ρ μ hπμ hρμ a b ha hb hab,
    (hπc.smul_measure ENNReal.ofReal_ne_top).add_measure
      (hρc.smul_measure ENNReal.ofReal_ne_top),
    (hπf.smul_measure ENNReal.ofReal_ne_top).add_measure
      (hρf.smul_measure ENNReal.ofReal_ne_top), ?_⟩
  rw [coupling_mixture_integral π ρ (fun p ↦ c p.1 p.2) hπc hρc a b ha hb,
    coupling_mixture_integral π ρ (fun p ↦ f p.2) hπf hρf a b ha hb]
  rfl

end ModelRiskCodex

/- Source: Solutions/ModelRisk_SupportingMultiplier.lean -/
/- Pure two-dimensional supporting geometry adapted from the previously
accepted local Wasserstein proof, Duality_CouplingValues.lean. The general
model-risk analytic/integral machinery is proved in this workspace. -/
set_option autoImplicit false
namespace ModelRiskCodex

lemma supporting_multiplier (C : Set (ℝ × ℝ)) (hC : Convex ℝ C)
    (δ V L : ℝ) (hδ : 0 < δ) (hbase : (0, L) ∈ C)
    (hbudget : ∀ z ∈ C, z.1 < δ → z.2 ≤ V) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ z ∈ C, z.2 ≤ V + γ * (z.1 - δ) := by
  let D : Set (ℝ × ℝ) := Set.Iio δ ×ˢ Set.Ioi V
  have hDconv : Convex ℝ D := (convex_Iio δ).prod (convex_Ioi V)
  have hDopen : IsOpen D := isOpen_Iio.prod isOpen_Ioi
  have hdisj : Disjoint D C := Set.disjoint_left.mpr (by
    intro z hzD hzC
    exact not_lt_of_ge (hbudget z hzC hzD.1) hzD.2)
  obtain ⟨f, k, hD, hCbound⟩ := geometric_hahn_banach_open hDconv hDopen hC hdisj
  let a := f (1, 0)
  let b := f (0, 1)
  have hf (x y : ℝ) : f (x, y) = a * x + b * y := by
    have he : (x, y) = x • (1, 0) + y • (0, 1) := by ext <;> simp
    rw [he, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    dsimp [a, b]
    ring
  have ha : 0 ≤ a := by
    by_contra ha
    have han : 0 < -a := neg_pos.mpr (lt_of_not_ge ha)
    let t := (|k - (a * δ + b * (V + 1))| + 1) / (-a)
    have ht : 0 < t := div_pos (by positivity) han
    have hm : (-a) * t = |k - (a * δ + b * (V + 1))| + 1 := by
      dsimp [t]
      exact mul_div_cancel₀ _ han.ne'
    have hd := hD (δ - t, V + 1) (show (δ - t, V + 1) ∈ D from ⟨by change δ - t < δ; linarith, by change V < V + 1; linarith⟩)
    rw [hf] at hd
    nlinarith [le_abs_self (k - (a * δ + b * (V + 1)))]
  have hb : b ≤ 0 := by
    by_contra hb
    have hbp : 0 < b := lt_of_not_ge hb
    let t := (|k - (a * (δ - 1) + b * V)| + 1) / b
    have ht : 0 < t := div_pos (by positivity) hbp
    have hm : b * t = |k - (a * (δ - 1) + b * V)| + 1 := by
      dsimp [t]
      exact mul_div_cancel₀ _ hbp.ne'
    have hd := hD (δ - 1, V + t) (show (δ - 1, V + t) ∈ D from ⟨by change δ - 1 < δ; linarith, by change V < V + t; linarith⟩)
    rw [hf] at hd
    nlinarith [le_abs_self (k - (a * (δ - 1) + b * V))]
  have hbneg : b < 0 := by
    by_contra hbneg
    have hbzero : b = 0 := le_antisymm hb (le_of_not_gt hbneg)
    have hd := hD (δ / 2, V + 1) (show (δ / 2, V + 1) ∈ D from ⟨by change δ / 2 < δ; linarith, by change V < V + 1; linarith⟩)
    have hc := hCbound (0, L) hbase
    rw [hf, hbzero] at hd hc
    nlinarith
  have hboundary : a * δ + b * V ≤ k := by
    by_contra hle
    have hgap : 0 < a * δ + b * V - k := sub_pos.mpr (lt_of_not_ge hle)
    obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_lt hgap (a - b)
    have hd := hD (δ - ε, V + ε) (show (δ - ε, V + ε) ∈ D from ⟨by change δ - ε < δ; linarith, by change V < V + ε; linarith⟩)
    rw [hf] at hd
    nlinarith
  refine ⟨a / (-b), div_nonneg ha (neg_nonneg.mpr hb), ?_⟩
  intro z hz
  have hc := hboundary.trans (hCbound z hz)
  have hzeta : (z.1, z.2) = z := Prod.mk.eta
  rw [← hzeta, hf] at hc
  have hn : 0 < -b := neg_pos.mpr hbneg
  have he : V + a / (-b) * (z.1 - δ) = (a * (z.1 - δ) + (-b) * V) / (-b) := by
    field_simp [ne_of_lt hbneg]
    ring
  rw [he]
  apply (le_div_iff₀ hn).mpr
  nlinarith

end ModelRiskCodex

/- Source: Solutions/ModelRisk_ExtIntegralGain.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality

lemma positive_negative_balance (a : ℝ) (b : EReal) (hab : (a : EReal) ≤ b) :
    b.toENNReal + ENNReal.ofReal (-a) =
      (b - (a : EReal)).toENNReal + ENNReal.ofReal a + (-b).toENNReal := by
  induction b using EReal.rec with
  | bot => exact ((EReal.bot_lt_coe a).not_ge hab).elim
  | top => simp
  | coe b =>
    have habr : a ≤ b := EReal.coe_le_coe_iff.mp hab
    simp only [← EReal.coe_sub, ← EReal.coe_neg, EReal.real_coe_toENNReal]
    by_cases ha : 0 ≤ a
    · have hb : 0 ≤ b := ha.trans habr
      rw [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr ha),
        ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hb), add_zero, add_zero,
        ← ENNReal.ofReal_add (sub_nonneg.mpr habr) ha, sub_add_cancel]
    · have ha0 : a ≤ 0 := (lt_of_not_ge ha).le
      by_cases hb : 0 ≤ b
      · rw [ENNReal.ofReal_of_nonpos ha0, ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hb),
          add_zero, add_zero, ← ENNReal.ofReal_add hb (neg_nonneg.mpr ha0)]
        congr 1
      · have hb0 : b ≤ 0 := (lt_of_not_ge hb).le
        rw [ENNReal.ofReal_of_nonpos ha0, ENNReal.ofReal_of_nonpos hb0, zero_add, add_zero,
          ← ENNReal.ofReal_add (sub_nonneg.mpr habr) (neg_nonneg.mpr hb0)]
        congr 1
        ring

lemma extIntegral_eq_nominal_add_gain {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ) (φ : X → EReal)
    (hφm : AEMeasurable φ μ) (hφ : ∀ᵐ x ∂μ, (f x : EReal) ≤ φ x) :
    extIntegral μ φ = ((∫ x, f x ∂μ : ℝ) : EReal) +
      ((∫⁻ x, (φ x - (f x : EReal)).toENNReal ∂μ : ENNReal) : EReal) := by
  let A : ENNReal := ∫⁻ x, ENNReal.ofReal (f x) ∂μ
  let B : ENNReal := ∫⁻ x, ENNReal.ofReal (-f x) ∂μ
  let C : ENNReal := ∫⁻ x, (φ x).toENNReal ∂μ
  let D : ENNReal := ∫⁻ x, (-φ x).toENNReal ∂μ
  let P : ENNReal := ∫⁻ x, (φ x - (f x : EReal)).toENNReal ∂μ
  have hA : A ≠ ⊤ := ((lintegral_ofReal_le_lintegral_enorm f).trans_lt hf.2).ne
  have hB : B ≠ ⊤ := ((lintegral_ofReal_le_lintegral_enorm (fun x ↦ -f x)).trans_lt hf.neg.2).ne
  have hD : D ≠ ⊤ := negativePart_finite_of_integrable_lower_bound μ f hf φ hφ
  have hpos : AEMeasurable (fun x ↦ (φ x).toENNReal) μ :=
    measurable_ereal_toENNReal.comp_aemeasurable hφm
  have hneg : AEMeasurable (fun x ↦ (-φ x).toENNReal) μ :=
    measurable_ereal_toENNReal.comp_aemeasurable hφm.neg
  have hgain : AEMeasurable (fun x ↦ (φ x - (f x : EReal)).toENNReal) μ :=
    measurable_ereal_toENNReal.comp_aemeasurable (hφm.sub hf.aemeasurable.coe_real_ereal)
  have he : C + B = P + A + D := by
    have hb := lintegral_congr_ae (hφ.mono fun x hx ↦ positive_negative_balance (f x) (φ x) hx)
    rw [lintegral_add_left' hpos,
      lintegral_add_right' (fun x ↦ (φ x - (f x : EReal)).toENNReal + ENNReal.ofReal (f x)) hneg,
      lintegral_add_left' hgain] at hb
    exact hb
  have hc := congrArg (fun z : ENNReal ↦ (z : EReal)) he
  simp only [EReal.coe_ennreal_add, ← EReal.coe_ennreal_toReal hA,
    ← EReal.coe_ennreal_toReal hB, ← EReal.coe_ennreal_toReal hD] at hc
  have hz := congrArg (fun z : EReal ↦ z + ((-B.toReal - D.toReal : ℝ) : EReal)) hc
  have hleft : (C : EReal) + (B.toReal : EReal) + ((-B.toReal - D.toReal : ℝ) : EReal) =
      (C : EReal) - (D.toReal : EReal) := by
    rw [add_assoc, ← EReal.coe_add]
    have heq : B.toReal + (-B.toReal - D.toReal) = -D.toReal := by ring
    rw [heq, EReal.coe_neg]
    rfl
  have hright : (P : EReal) + (A.toReal : EReal) + (D.toReal : EReal) +
      ((-B.toReal - D.toReal : ℝ) : EReal) =
      ((A.toReal - B.toReal : ℝ) : EReal) + (P : EReal) := by
    rw [add_assoc (P : EReal), add_assoc (P : EReal), ← EReal.coe_add, ← EReal.coe_add]
    have heq : A.toReal + D.toReal + (-B.toReal - D.toReal) = A.toReal - B.toReal := by ring
    rw [heq, add_comm]
  rw [hleft, hright] at hz
  have hnom : A.toReal - B.toReal = ∫ x, f x ∂μ :=
    (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf).symm
  rw [hnom] at hz
  change (C : EReal) - (D : EReal) = _
  rw [← EReal.coe_ennreal_toReal hD]
  exact hz

end ModelRiskCodex

/- Source: Solutions/ModelRisk_ExtIntegralShift.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality

lemma finite_shift_gain (φ : EReal) (a b : ℝ) :
    (φ + (b : EReal)) - ((a + b : ℝ) : EReal) = φ - (a : EReal) := by
  rw [EReal.coe_add, EReal.add_sub_add_comm (.inl (EReal.coe_ne_bot a))
    (.inl (EReal.coe_ne_top a)), ← EReal.coe_sub, sub_self, EReal.coe_zero, add_zero]

lemma extIntegral_add_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (φ : X → EReal) (hφm : AEMeasurable φ μ) (hφ : ∀ᵐ x ∂μ, (f x : EReal) ≤ φ x) :
    extIntegral μ (fun x ↦ φ x + (g x : EReal)) =
      extIntegral μ φ + ((∫ x, g x ∂μ : ℝ) : EReal) := by
  have hlow : ∀ᵐ x ∂μ, ((f x + g x : ℝ) : EReal) ≤ φ x + (g x : EReal) := by
    filter_upwards [hφ] with x hx
    rw [EReal.coe_add]
    exact add_le_add hx le_rfl
  rw [extIntegral_eq_nominal_add_gain μ (fun x ↦ f x + g x) (hf.add hg)
      (fun x ↦ φ x + (g x : EReal)) (hφm.add hg.aemeasurable.coe_real_ereal) hlow,
    extIntegral_eq_nominal_add_gain μ f hf φ hφm hφ]
  simp_rw [finite_shift_gain]
  rw [integral_add hf hg, EReal.coe_add]
  exact add_right_comm _ _ _

end ModelRiskCodex

/- Source: Solutions/ModelRisk_AnalyticHulls.lean -/
/- Supporting measure-theoretic lemmas for the unchanged general Polish-space
transport target. These do not prove strong duality or a selection theorem. -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory Set Filter Topology

theorem hull_sdiff_measurable_null {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {A B : Set X}
    (hB : MeasurableSet B) (hAB : A ⊆ B) : μ (toMeasurable μ A \ B) = 0 := by
  have he : toMeasurable μ A \ B = toMeasurable μ A \ (toMeasurable μ A ∩ B) := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff]
    tauto
  rw [he, measure_sdiff inter_subset_left
    ((measurableSet_toMeasurable μ A).inter hB).nullMeasurableSet
    (measure_ne_top μ _), measure_toMeasurable,
    Measure.measure_toMeasurable_inter hB (measure_ne_top μ A), inter_eq_left.mpr hAB,
    tsub_self]

theorem hull_sdiff_countable_union_null {X I : Type*} [MeasurableSpace X] [Countable I]
    (μ : Measure X) [IsFiniteMeasure μ] (A : Set X) (Achild : I → Set X)
    (hcover : A ⊆ ⋃ i, Achild i) :
    μ (toMeasurable μ A \ ⋃ i, toMeasurable μ (Achild i)) = 0 := by
  apply hull_sdiff_measurable_null μ
    (MeasurableSet.iUnion fun i ↦ measurableSet_toMeasurable μ (Achild i))
  exact hcover.trans (iUnion_mono fun i ↦ subset_toMeasurable μ (Achild i))

theorem hull_cylinder_children_null {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : (ℕ → ℕ) → X) (a : ℕ → ℕ) (n : ℕ) :
    μ (toMeasurable μ (f '' PiNat.cylinder a n) \
      ⋃ k : ℕ, toMeasurable μ (f '' PiNat.cylinder (Function.update a n k) (n + 1))) = 0 := by
  apply hull_sdiff_countable_union_null μ
  rw [← image_iUnion]
  have he : (⋃ k : ℕ, PiNat.cylinder (Function.update a n k) (n + 1)) = PiNat.cylinder a n :=
    PiNat.iUnion_cylinder_update a n
  rw [he]

theorem mem_all_closed_cylinder_images {X : Type*} [TopologicalSpace X] [T3Space X]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) (a : ℕ → ℕ) (x : X)
    (hx : ∀ n, x ∈ closure (f '' PiNat.cylinder a n)) : x = f a := by
  by_contra hne
  have hfa : f a ∈ ({x} : Set X)ᶜ := by simpa using Ne.symm hne
  obtain ⟨V, hVnhds, hVclosed, hVsub⟩ :=
    exists_mem_nhds_isClosed_subset (isOpen_compl_singleton.mem_nhds hfa)
  let : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hf.continuousAt.preimage_mem_nhds hVnhds)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < ε :=
    exists_pow_lt_of_lt_one hε (by norm_num)
  have hsubset : f '' PiNat.cylinder a n ⊆ V := by
    rw [image_subset_iff]
    intro b hb
    apply hball
    rw [Metric.mem_ball]
    exact (PiNat.mem_cylinder_iff_dist_le.mp hb).trans_lt hn
  have hxV : x ∈ V := (closure_minimal hsubset hVclosed) (hx n)
  simpa using hVsub hxV

end ModelRiskCodex

/- Source: Solutions/ModelRisk_BairePrefixes.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open Set MeasureTheory

abbrev BaireStem := Σ n : ℕ, Fin n → ℕ
def stemSeq (s : BaireStem) (i : ℕ) : ℕ :=
  if h : i < s.1 then s.2 ⟨i, h⟩ else 0
def stemChild (s : BaireStem) (k : ℕ) : BaireStem :=
  ⟨s.1 + 1, fun i ↦ if h : i.val < s.1 then s.2 ⟨i.val, h⟩ else k⟩
def stemCylinder (s : BaireStem) : Set (ℕ → ℕ) := PiNat.cylinder (stemSeq s) s.1
def emptyStem : BaireStem := ⟨0, fun i ↦ Fin.elim0 i⟩

@[simp] theorem stemChild_length (s : BaireStem) (k : ℕ) :
    (stemChild s k).1 = s.1 + 1 := rfl

theorem stemSeq_child_old (s : BaireStem) (k i : ℕ) (hi : i < s.1) :
    stemSeq (stemChild s k) i = stemSeq s i := by
  simp [stemSeq, stemChild, hi, Nat.lt_succ_of_lt hi]

theorem stemSeq_child_update (s : BaireStem) (k i : ℕ) (hi : i < s.1 + 1) :
    stemSeq (stemChild s k) i = Function.update (stemSeq s) s.1 k i := by
  by_cases h : i < s.1
  · simp [stemSeq, stemChild, h, hi, ne_of_lt h]
  · have he : i = s.1 := by omega
    subst i
    simp [stemSeq, stemChild]

theorem stemCylinder_child (s : BaireStem) (k : ℕ) :
    stemCylinder (stemChild s k) =
      PiNat.cylinder (Function.update (stemSeq s) s.1 k) (s.1 + 1) := by
  ext b
  simp only [stemCylinder, stemChild_length, PiNat.mem_cylinder_iff]
  constructor <;> intro h i hi
  · rw [← stemSeq_child_update s k i hi]
    exact h i hi
  · rw [stemSeq_child_update s k i hi]
    exact h i hi

theorem iUnion_stemCylinder_children (s : BaireStem) :
    (⋃ k : ℕ, stemCylinder (stemChild s k)) = stemCylinder s := by
  simp only [stemCylinder_child]
  exact PiNat.iUnion_cylinder_update (stemSeq s) s.1

@[simp] theorem stemCylinder_empty : stemCylinder emptyStem = Set.univ :=
  PiNat.cylinder_zero _

noncomputable def imageHull {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : (ℕ → ℕ) → X) (s : BaireStem) : Set X :=
  toMeasurable μ (f '' stemCylinder s)

theorem imageHull_children_null {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : (ℕ → ℕ) → X) (s : BaireStem) :
    μ (imageHull μ f s \ ⋃ k : ℕ, imageHull μ f (stemChild s k)) = 0 := by
  apply hull_sdiff_countable_union_null μ
  rw [← image_iUnion, iUnion_stemCylinder_children]

end ModelRiskCodex

/- Source: Solutions/ModelRisk_AnalyticNullMeasurable.lean -/
/- Finite-measure measurability of continuous Baire images, by countable
measurable hulls. Branch stabilization follows the pattern in Mathlib's
analytic separation proof (Polish/Basic, Apache-2.0). -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ModelRiskCodex
open MeasureTheory Set Filter Topology Function

def hullLoss {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : (ℕ → ℕ) → X) (s : BaireStem) : Set X :=
  (imageHull μ f s \ closure (f '' stemCylinder s)) ∪
    (imageHull μ f s \ ⋃ k : ℕ, imageHull μ f (stemChild s k))

def hullExceptional {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : (ℕ → ℕ) → X) : Set X := ⋃ s : BaireStem, hullLoss μ f s

theorem hullExceptional_null {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] (f : (ℕ → ℕ) → X) :
    μ (hullExceptional μ f) = 0 := by
  apply measure_iUnion_null
  intro s
  apply measure_union_null
  · exact hull_sdiff_measurable_null μ isClosed_closure.measurableSet subset_closure
  · exact imageHull_children_null μ f s

theorem mem_range_of_good_hull {X : Type*} [TopologicalSpace X] [T3Space X]
    [MeasurableSpace X] (μ : Measure X) (f : (ℕ → ℕ) → X) (hf : Continuous f)
    (x : X) (hx : x ∈ imageHull μ f emptyStem) (hgood : x ∉ hullExceptional μ f) :
    x ∈ Set.range f := by
  classical
  let A := {s : BaireStem // x ∈ imageHull μ f s}
  have hnext : ∀ p : A, ∃ k : ℕ, x ∈ imageHull μ f (stemChild p.val k) := by
    intro p
    by_contra h
    have hn : x ∉ ⋃ k : ℕ, imageHull μ f (stemChild p.val k) := by simpa using h
    exact hgood (mem_iUnion_of_mem p.val (Or.inr ⟨p.property, hn⟩))
  choose k hk using hnext
  let F : A → A := fun p ↦ ⟨stemChild p.val (k p), hk p⟩
  have hlen (p : A) : (F p).val.1 = p.val.1 + 1 := rfl
  have hold (p : A) (i : ℕ) (hi : i < p.val.1) :
      stemSeq (F p).val i = stemSeq p.val i := stemSeq_child_old p.val (k p) i hi
  let p0 : A := ⟨emptyStem, hx⟩
  let p : ℕ → A := fun n ↦ F^[n] p0
  have prec (n : ℕ) : p (n + 1) = F (p n) := by
    simp only [p, iterate_succ', Function.comp_apply]
  have plen : ∀ n, (p n).val.1 = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [prec, hlen, ih]
  have stable : ∀ i n, i + 1 ≤ n → stemSeq (p n).val i = stemSeq (p (i + 1)).val i := by
    intro i
    apply Nat.le_induction
    · rfl
    intro n hn ih
    rw [prec, hold (p n) i (by rw [plen]; omega), ih]
  let a : ℕ → ℕ := fun i ↦ stemSeq (p (i + 1)).val i
  have hcyl (n : ℕ) : stemCylinder (p n).val = PiNat.cylinder a n := by
    rw [stemCylinder, plen, ← PiNat.mem_cylinder_iff_eq, PiNat.mem_cylinder_iff]
    intro i hi
    exact stable i n (Nat.succ_le_of_lt hi)
  have hclosed (n : ℕ) : x ∈ closure (f '' stemCylinder (p n).val) := by
    by_contra h
    exact hgood (mem_iUnion_of_mem (p n).val (Or.inl ⟨(p n).property, h⟩))
  have heq : x = f a := mem_all_closed_cylinder_images f hf a x (fun n ↦ by
    rw [← hcyl n]
    exact hclosed n)
  exact ⟨a, heq.symm⟩

theorem continuous_baire_range_nullMeasurable {X : Type*} [TopologicalSpace X]
    [T3Space X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : (ℕ → ℕ) → X) (hf : Continuous f) :
    NullMeasurableSet (Set.range f) μ := by
  have hgood : ∀ᵐ x ∂μ, x ∉ hullExceptional μ f := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hullExceptional_null μ f
  have heq : imageHull μ f emptyStem =ᵐ[μ] Set.range f := by
    filter_upwards [hgood] with x hx
    apply propext
    change (x ∈ imageHull μ f emptyStem) ↔ (x ∈ Set.range f)
    constructor
    · exact fun h ↦ mem_range_of_good_hull μ f hf x h hx
    · intro h
      apply subset_toMeasurable μ (f '' stemCylinder emptyStem)
      simpa only [stemCylinder_empty, image_univ] using h
  exact (measurableSet_toMeasurable μ (f '' stemCylinder emptyStem)).nullMeasurableSet.congr heq

theorem analyticSet_nullMeasurable {X : Type*} [TopologicalSpace X]
    [T3Space X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {s : Set X} (hs : AnalyticSet s) :
    NullMeasurableSet s μ := by
  rw [AnalyticSet] at hs
  rcases hs with rfl | ⟨f, hf, rfl⟩
  · exact nullMeasurableSet_empty
  · exact continuous_baire_range_nullMeasurable μ f hf

theorem analyticSet_universallyMeasurable {X : Type*} [TopologicalSpace X]
    [T3Space X] [MeasurableSpace X] [BorelSpace X] {s : Set X} (hs : AnalyticSet s) :
    BertsekasShreve.AnalyticSelection.IsUniversallyMeasurable s := by
  intro μ hμ
  let := hμ
  exact analyticSet_nullMeasurable μ hs

end ModelRiskCodex

/- Source: Solutions/ModelRisk_EnvelopeMeasurability.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality Set Topology

theorem score_le_phiLam {S : Type*} (c : S → S → ℝ) (f : S → ℝ)
    (lam : ℝ) (x y : S) :
    ((f y - lam * c x y : ℝ) : EReal) ≤ phiLam c f lam x := by
  unfold phiLam phiLamOn
  exact le_iSup_of_le y (le_iSup_of_le (Set.mem_univ y) le_rfl)

theorem phiLam_real_superlevel_analytic {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (c : S → S → ℝ) (f : S → ℝ)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2)) (hf : Measurable f) (lam r : ℝ) :
    AnalyticSet (phiLam c f lam ⁻¹' Set.Ioi (r : EReal)) := by
  have hg : Measurable (fun p : S × S ↦ f p.2 - lam * c p.1 p.2) :=
    (hf.comp measurable_snd).sub (measurable_const.mul hc)
  have hs : MeasurableSet {p : S × S | r < f p.2 - lam * c p.1 p.2} :=
    measurableSet_lt measurable_const hg
  have he : phiLam c f lam ⁻¹' Set.Ioi (r : EReal) =
      Prod.fst '' {p : S × S | r < f p.2 - lam * c p.1 p.2} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor
    · intro h
      simp only [phiLam, phiLamOn, Set.mem_univ, iSup_true] at h
      obtain ⟨y, hy⟩ := lt_iSup_iff.mp h
      exact ⟨(x, y), EReal.coe_lt_coe_iff.mp hy, rfl⟩
    · rintro ⟨⟨z, y⟩, hy, rfl⟩
      exact (EReal.coe_lt_coe_iff.mpr hy).trans_le (score_le_phiLam c f lam z y)
  rw [he]
  exact hs.analyticSet.image_of_continuous continuous_fst

theorem phiLam_nullMeasurable {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    (c : S → S → ℝ) (f : S → ℝ)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2)) (hf : Measurable f) (lam : ℝ) :
    NullMeasurable (phiLam c f lam) μ := by
  have hm : @Measurable (NullMeasurableSpace S μ) EReal inferInstance inferInstance (phiLam c f lam) := by
    apply measurable_of_Ioi
    intro t
    change NullMeasurableSet (phiLam c f lam ⁻¹' Set.Ioi t) μ
    induction t using EReal.rec with
    | bot =>
      have he : phiLam c f lam ⁻¹' Set.Ioi ⊥ = Set.univ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
        exact (EReal.bot_lt_coe _).trans_le (score_le_phiLam c f lam x x)
      rw [he]
      exact nullMeasurableSet_univ
    | coe r =>
      exact analyticSet_nullMeasurable μ (phiLam_real_superlevel_analytic c f hc hf lam r)
    | top =>
      simp only [Set.Ioi_top, Set.preimage_empty]
      exact nullMeasurableSet_empty
  exact hm

theorem phiLam_universallyMeasurable {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (c : S → S → ℝ) (f : S → ℝ)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2)) (hf : Measurable f) (lam : ℝ) :
    IsUnivMeasurableEReal (phiLam c f lam) := by
  intro B hB μ hμ
  let := hμ
  exact phiLam_nullMeasurable μ c f hc hf lam hB

theorem canonical_dualFeasible {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (c : S → S → ℝ) (hc : AssumptionA1 c)
    (f : S → ℝ) (hf : UpperSemicontinuous f) (lam : ℝ) (hlam : 0 ≤ lam) :
    (lam, phiLam c f lam) ∈ dualFeasible c f Set.univ := by
  refine ⟨hlam, phiLam_universallyMeasurable c f hc.lsc.measurable hf.measurable lam, ?_⟩
  intro x hx y hy
  have h := add_le_add_right (score_le_phiLam c f lam x y) ((lam * c x y : ℝ) : EReal)
  have he : ((f y - lam * c x y : ℝ) : EReal) + ((lam * c x y : ℝ) : EReal) = (f y : EReal) := by
    rw [← EReal.coe_add]
    congr 1
    ring
  rw [add_comm ((lam * c x y : ℝ) : EReal), he] at h
  simpa only [Prod.fst, Prod.snd, add_comm] using h

end ModelRiskCodex

/- Source: Solutions/ModelRisk_BaselineBounds.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality

lemma nominal_le_phiLam {S : Type*} [TopologicalSpace S]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ) (lam : ℝ) (x : S) :
    (f x : EReal) ≤ phiLam c f lam x := by
  simpa only [(hc.eq_zero_iff x x).mpr rfl, mul_zero, sub_zero] using
    score_le_phiLam c f lam x x

lemma canonical_negativePart_finite {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    (μ : Measure S) (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ)
    (hfi : Integrable f μ) (lam : ℝ) :
    (∫⁻ x, (-phiLam c f lam x).toENNReal ∂μ) ≠ ⊤ :=
  negativePart_finite_of_integrable_lower_bound μ f hfi _
    (Filter.Eventually.of_forall (nominal_le_phiLam c hc f lam))

lemma nominal_le_dualFeasible_phi {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ) (lam : ℝ) (φ : S → EReal)
    (h : (lam, φ) ∈ dualFeasible c f Set.univ) (x : S) : (f x : EReal) ≤ φ x := by
  have hx := h.2.2 x (Set.mem_univ x) x (Set.mem_univ x)
  simpa only [Prod.fst, Prod.snd, (hc.eq_zero_iff x x).mpr rfl,
    mul_zero, EReal.coe_zero, add_zero] using hx

lemma nominal_le_dualObj {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    (μ : Measure S) (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ)
    (hfi : Integrable f μ) (δ : ℝ) (hδ : 0 ≤ δ) (lam : ℝ) (φ : S → EReal)
    (h : (lam, φ) ∈ dualFeasible c f Set.univ) :
    ((∫ x, f x ∂μ : ℝ) : EReal) ≤ dualObj μ δ lam φ := by
  have he := extIntegral_mono μ (fun x ↦ (f x : EReal)) φ
    (Filter.Eventually.of_forall (nominal_le_dualFeasible_phi c hc f lam φ h))
  rw [extIntegral_eq_integral μ f hfi] at he
  have h0 : (0 : EReal) ≤ ((lam * δ : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr (mul_nonneg h.1 hδ)
  exact he.trans (by simpa only [dualObj, add_zero, zero_add, add_comm] using add_le_add_right h0 (extIntegral μ φ))

lemma nominal_le_dualValue {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    (μ : Measure S) (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ)
    (hfi : Integrable f μ) (δ : ℝ) (hδ : 0 ≤ δ) :
    ((∫ x, f x ∂μ : ℝ) : EReal) ≤ dualValue c f μ δ := by
  apply le_iInf
  intro p
  apply le_iInf
  intro hp
  exact nominal_le_dualObj μ c hc f hfi δ hδ p.1 p.2 hp

lemma nominal_le_primalValue {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (hc : AssumptionA1 c)
    (f : S → ℝ) (hf : Measurable f) (hfi : Integrable f μ) (δ : ℝ) (hδ : 0 ≤ δ) :
    ((∫ x, f x ∂μ : ℝ) : EReal) ≤ primalValue c f μ δ := by
  have hz : (fun x : S ↦ c x (id x)) = fun _ ↦ (0 : ℝ) := by
    funext x
    exact (hc.eq_zero_iff x x).mpr rfl
  have hdiag : selectorPlan μ id ∈ primalFeasible c μ δ :=
    selectorPlan_feasible μ id measurable_id c hc.lsc.measurable hc.nonneg
      (by rw [hz]; exact integrable_const 0) δ (by simpa only [hz, integral_zero] using hδ)
  have he : primalObj f (selectorPlan μ id) = ((∫ x, f x ∂μ : ℝ) : EReal) :=
    selectorPlan_objective μ id measurable_id f hf hfi
  rw [← he]
  exact le_iSup_of_le (selectorPlan μ id) (le_iSup_of_le hdiag le_rfl)

end ModelRiskCodex

/- Source: Solutions/ModelRisk_WeakDuality.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality Filter

lemma dualFeasible_aemeasurable {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (f : S → ℝ)
    (lam : ℝ) (φ : S → EReal) (h : (lam, φ) ∈ dualFeasible c f Set.univ) :
    AEMeasurable φ μ := by
  have hm : NullMeasurable φ μ := by
    intro B hB
    exact h.2.1 B hB μ inferInstance
  exact hm.aemeasurable

lemma weak_duality_objective {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ)
    (_hf : UpperSemicontinuous f) (hfi : Integrable f μ) (δ : ℝ) (hδ : 0 ≤ δ)
    (π : Measure (S × S)) (hπ : π ∈ primalFeasible c μ δ)
    (lam : ℝ) (φ : S → EReal) (hD : (lam, φ) ∈ dualFeasible c f Set.univ) :
    primalObj f π ≤ dualObj μ δ lam φ := by
  obtain ⟨hprob, hfst, hcost⟩ := hπ
  let := hprob
  have hφmap : AEMeasurable φ (π.map Prod.fst) := by
    rw [hfst]
    exact dualFeasible_aemeasurable μ c f lam φ hD
  have hφπ : AEMeasurable (fun p : S × S ↦ φ p.1) π := hφmap.comp_measurable measurable_fst
  have hfmap : AEStronglyMeasurable f (π.map Prod.fst) := by
    rw [hfst]
    exact hfi.aestronglyMeasurable
  have hfirst : Integrable (fun p : S × S ↦ f p.1) π :=
    (integrable_map_measure hfmap measurable_fst.aemeasurable).mp (by rw [hfst]; exact hfi)
  have hc0 : ∀ᵐ p : S × S ∂π, 0 ≤ c p.1 p.2 :=
    Filter.Eventually.of_forall fun p ↦ hc.nonneg p.1 p.2
  have hcostfin : (∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π) ≠ ⊤ :=
    (hcost.trans_lt (by simp)).ne
  have hci : Integrable (fun p : S × S ↦ c p.1 p.2) π :=
    (lintegral_ofReal_ne_top_iff_integrable hc.lsc.measurable.aestronglyMeasurable hc0).mp hcostfin
  have hmean : (∫ p : S × S, c p.1 p.2 ∂π) ≤ δ := by
    have hr := (ENNReal.toReal_le_toReal hcostfin ENNReal.ofReal_ne_top).mpr hcost
    rw [ENNReal.toReal_ofReal hδ,
      ← integral_eq_lintegral_of_nonneg_ae hc0 hci.aestronglyMeasurable] at hr
    exact hr
  have hlow : ∀ᵐ p : S × S ∂π, (f p.1 : EReal) ≤ φ p.1 :=
    Filter.Eventually.of_forall fun p ↦ nominal_le_dualFeasible_phi c hc f lam φ hD p.1
  have hchange : extIntegral π (fun p : S × S ↦ φ p.1) = extIntegral μ φ := by
    rw [← extIntegral_map π Prod.fst measurable_fst φ hφmap, hfst]
  have he : extIntegral π (fun p : S × S ↦ φ p.1 + ((lam * c p.1 p.2 : ℝ) : EReal)) =
      extIntegral μ φ + ((lam * (∫ p : S × S, c p.1 p.2 ∂π) : ℝ) : EReal) := by
    rw [extIntegral_add_integrable π (fun p : S × S ↦ f p.1)
      (fun p : S × S ↦ lam * c p.1 p.2) hfirst (hci.const_mul lam)
      (fun p : S × S ↦ φ p.1) hφπ hlow, hchange, integral_const_mul]
  have hcover : primalObj f π ≤
      extIntegral π (fun p : S × S ↦ φ p.1 + ((lam * c p.1 p.2 : ℝ) : EReal)) :=
    extIntegral_mono π (fun p : S × S ↦ (f p.2 : EReal)) _
      (Filter.Eventually.of_forall fun p ↦ hD.2.2 p.1 (Set.mem_univ _) p.2 (Set.mem_univ _))
  rw [he] at hcover
  have hb : ((lam * (∫ p : S × S, c p.1 p.2 ∂π) : ℝ) : EReal) ≤ ((lam * δ : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left hmean hD.1)
  exact hcover.trans (by simpa only [dualObj, add_comm] using add_le_add (le_refl (extIntegral μ φ)) hb)

lemma weak_duality {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ)
    (hf : UpperSemicontinuous f) (hfi : Integrable f μ) (δ : ℝ) (hδ : 0 ≤ δ) :
    primalValue c f μ δ ≤ dualValue c f μ δ := by
  apply iSup_le
  intro π
  apply iSup_le
  intro hπ
  apply le_iInf
  intro p
  apply le_iInf
  intro hp
  exact weak_duality_objective μ c hc f hf hfi δ hδ π hπ p.1 p.2 hp

end ModelRiskCodex

/- Source: Solutions/ModelRisk_BoundedSelector.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory Set Filter

def selectorGain {S : Type*} (f : S → ℝ) (v : S → S) (x : S) : ℝ := f (v x) - f x

def selectorCutRegion {S : Type*} (c : S → S → ℝ) (f : S → ℝ) (v : S → S)
    (n : ℝ) : Set S := {x | 0 ≤ selectorGain f v x ∧ c x (v x) ≤ n ∧ selectorGain f v x ≤ n}

noncomputable def boundedSelector {S : Type*} (c : S → S → ℝ) (f : S → ℝ)
    (v : S → S) (n : ℝ) (x : S) : S := by
  classical
  exact if x ∈ selectorCutRegion c f v n then v x else x

lemma measurable_boundedSelector {S : Type*} [MeasurableSpace S]
    (c : S → S → ℝ) (f : S → ℝ) (v : S → S)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2)) (hf : Measurable f)
    (hv : Measurable v) (n : ℝ) : Measurable (boundedSelector c f v n) := by
  have hg : Measurable (selectorGain f v) := (hf.comp hv).sub hf
  have hs : MeasurableSet (selectorCutRegion c f v n) :=
    (measurableSet_le measurable_const hg).inter
      ((measurableSet_le (hc.comp (measurable_id.prodMk hv)) measurable_const).inter
        (measurableSet_le hg measurable_const))
  exact Measurable.ite hs hv measurable_id

lemma boundedSelector_quality {S : Type*} (c : S → S → ℝ) (f : S → ℝ) (v : S → S)
    (hc0 : ∀ x y, 0 ≤ c x y) (hcdiag : ∀ x, c x x = 0)
    (n : ℝ) (hn : 0 ≤ n) (x : S) :
    0 ≤ selectorGain f (boundedSelector c f v n) x ∧
      selectorGain f (boundedSelector c f v n) x ≤ n ∧
      0 ≤ c x (boundedSelector c f v n x) ∧ c x (boundedSelector c f v n x) ≤ n := by
  classical
  by_cases h : x ∈ selectorCutRegion c f v n
  · simp only [selectorGain, boundedSelector, if_pos h]
    exact ⟨h.1, h.2.2, hc0 x (v x), h.2.1⟩
  · simp only [boundedSelector, if_neg h, selectorGain, sub_self, hcdiag]
    exact ⟨le_rfl, hn, le_rfl, hn⟩

lemma boundedSelector_integrable_components {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] (c : S → S → ℝ) (f : S → ℝ) (v : S → S)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2)) (hf : Measurable f) (hv : Measurable v)
    (hc0 : ∀ x y, 0 ≤ c x y) (hcdiag : ∀ x, c x x = 0)
    (n : ℝ) (hn : 0 ≤ n) :
    Integrable (selectorGain f (boundedSelector c f v n)) μ ∧
      Integrable (fun x ↦ c x (boundedSelector c f v n x)) μ := by
  have hb := measurable_boundedSelector c f v hc hf hv n
  have hgi : Integrable (selectorGain f (boundedSelector c f v n)) μ := by
    apply (integrable_const n : Integrable (fun _ : S ↦ n) μ).mono'
      ((hf.comp hb).sub hf).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    change ‖selectorGain f (boundedSelector c f v n) x‖ ≤ n
    rw [Real.norm_eq_abs, abs_of_nonneg (boundedSelector_quality c f v hc0 hcdiag n hn x).1]
    exact (boundedSelector_quality c f v hc0 hcdiag n hn x).2.1
  have hci : Integrable (fun x ↦ c x (boundedSelector c f v n x)) μ := by
    apply (integrable_const n : Integrable (fun _ : S ↦ n) μ).mono'
      (hc.comp (measurable_id.prodMk hb)).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    change ‖c x (boundedSelector c f v n x)‖ ≤ n
    rw [Real.norm_eq_abs, abs_of_nonneg (boundedSelector_quality c f v hc0 hcdiag n hn x).2.2.1]
    exact (boundedSelector_quality c f v hc0 hcdiag n hn x).2.2.2
  exact ⟨hgi, hci⟩

lemma boundedSelector_payoff_integrable {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] (c : S → S → ℝ) (f : S → ℝ) (v : S → S)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2)) (hf : Measurable f) (hv : Measurable v)
    (hfi : Integrable f μ) (hc0 : ∀ x y, 0 ≤ c x y) (hcdiag : ∀ x, c x x = 0)
    (n : ℝ) (hn : 0 ≤ n) : Integrable (fun x ↦ f (boundedSelector c f v n x)) μ := by
  have hgi := (boundedSelector_integrable_components μ c f v hc hf hv hc0 hcdiag n hn).1
  have he : (fun x ↦ f (boundedSelector c f v n x)) =
      fun x ↦ f x + selectorGain f (boundedSelector c f v n) x := by
    funext x
    simp only [selectorGain]
    ring
  rw [he]
  exact hfi.add hgi

lemma boundedSelector_eventually_eq {S : Type*} (c : S → S → ℝ) (f : S → ℝ) (v : S → S)
    (x : S) (hgain : 0 ≤ selectorGain f v x) :
    ∀ᶠ n : ℕ in atTop, boundedSelector c f v n x = v x := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (max (c x (v x)) (selectorGain f v x))
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn ↦ ?_⟩
  have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hc : c x (v x) ≤ n := (le_max_left _ _).trans (hN.le.trans hcast)
  have hg : selectorGain f v x ≤ n := (le_max_right _ _).trans (hN.le.trans hcast)
  exact if_pos (show x ∈ selectorCutRegion c f v n from ⟨hgain, hc, hg⟩)

end ModelRiskCodex

/- Source: Solutions/ModelRisk_CouplingSupport.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality

lemma selector_mem_finiteCouplingValues {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (f : S → ℝ)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2)) (hf : Measurable f) (hfi : Integrable f μ)
    (w : S → S) (hw : Measurable w) (hg : Integrable (selectorGain f w) μ)
    (hci : Integrable (fun x ↦ c x (w x)) μ) :
    ((∫ x, c x (w x) ∂μ), (∫ x, f (w x) ∂μ)) ∈ finiteCouplingValues μ c f := by
  have hwi : Integrable (fun x ↦ f (w x)) μ := by
    have he : (fun x ↦ f (w x)) = fun x ↦ f x + selectorGain f w x := by
      funext x
      dsimp [selectorGain]
      ring
    rw [he]
    exact hfi.add hg
  let T : S → S × S := fun x ↦ (x, w x)
  have hT : Measurable T := measurable_id.prodMk hw
  refine ⟨selectorPlan μ w, selectorPlan_probability μ w hw,
    selectorPlan_first_marginal μ w hw,
    (integrable_map_measure hc.aestronglyMeasurable hT.aemeasurable).mpr hci,
    (integrable_map_measure (hf.comp measurable_snd).aestronglyMeasurable hT.aemeasurable).mpr hwi, ?_⟩
  change _ = ((∫ p : S × S, c p.1 p.2 ∂μ.map T), (∫ p : S × S, f p.2 ∂μ.map T))
  rw [integral_map hT.aemeasurable hc.aestronglyMeasurable,
    integral_map (f := fun p : S × S ↦ f p.2) hT.aemeasurable (hf.comp measurable_snd).aestronglyMeasurable]

lemma nominal_mem_finiteCouplingValues {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (f : S → ℝ)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2)) (hf : Measurable f) (hfi : Integrable f μ)
    (hcdiag : ∀ x, c x x = 0) :
    (0, ∫ x, f x ∂μ) ∈ finiteCouplingValues μ c f := by
  have hg : Integrable (selectorGain f (id : S → S)) μ := by
    change Integrable (fun x : S ↦ f x - f x) μ
    simpa only [sub_self] using (integrable_const (0 : ℝ) : Integrable (fun _ : S ↦ (0 : ℝ)) μ)
  have hci : Integrable (fun x ↦ c x (id x)) μ := by
    simpa only [id_eq, hcdiag] using
      (integrable_const (0 : ℝ) : Integrable (fun _ : S ↦ (0 : ℝ)) μ)
  simpa only [id_eq, hcdiag, integral_zero] using
    selector_mem_finiteCouplingValues μ c f hc hf hfi id measurable_id hg hci

lemma finiteCouplingValues_payoff_le_primal {S : Type*} [TopologicalSpace S]
    [MeasurableSpace S] (μ : Measure S) (c : S → S → ℝ) (hc : AssumptionA1 c)
    (f : S → ℝ) (δ : ℝ) (z : ℝ × ℝ) (hz : z ∈ finiteCouplingValues μ c f)
    (hbudget : z.1 ≤ δ) : (z.2 : EReal) ≤ primalValue c f μ δ := by
  rcases hz with ⟨π, hprob, hfst, hci, hfi, rfl⟩
  have hc0 : ∀ᵐ p : S × S ∂π, 0 ≤ c p.1 p.2 :=
    Filter.Eventually.of_forall fun p ↦ hc.nonneg p.1 p.2
  have hπ : π ∈ primalFeasible c μ δ := by
    refine ⟨hprob, hfst, ?_⟩
    rw [← ofReal_integral_eq_lintegral_ofReal hci hc0]
    exact ENNReal.ofReal_le_ofReal hbudget
  have ho : primalObj f π = ((∫ p : S × S, f p.2 ∂π : ℝ) : EReal) :=
    extIntegral_eq_integral π (fun p : S × S ↦ f p.2) hfi
  change ((∫ p : S × S, f p.2 ∂π : ℝ) : EReal) ≤ _
  rw [← ho]
  exact le_iSup_of_le π (le_iSup_of_le hπ le_rfl)

lemma finite_value_supporting_multiplier {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ)
    (hf : UpperSemicontinuous f) (hfi : Integrable f μ) (δ : ℝ) (hδ : 0 < δ)
    (V : ℝ) (hV : primalValue c f μ δ = (V : EReal)) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ z ∈ finiteCouplingValues μ c f,
      z.2 ≤ V + lam * (z.1 - δ) := by
  apply supporting_multiplier (finiteCouplingValues μ c f) (finiteCouplingValues_convex μ c f)
    δ V (∫ x, f x ∂μ) hδ
    (nominal_mem_finiteCouplingValues μ c f hc.lsc.measurable hf.measurable hfi
      (fun x ↦ (hc.eq_zero_iff x x).mpr rfl))
  intro z hz hbudget
  have h := finiteCouplingValues_payoff_le_primal μ c hc f δ z hz hbudget.le
  rw [hV] at h
  exact EReal.coe_le_coe_iff.mp h

end ModelRiskCodex

/- Source: Solutions/ModelRisk_BaireSelector.lean -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ModelRiskCodex
open MeasureTheory Set Filter Function Topology

private instance : MeasurableSingletonClass BaireStem where
  measurableSet_singleton s := by
    change MeasurableSet[⨅ n : ℕ, (inferInstance : MeasurableSpace (Fin n → ℕ)).map (Sigma.mk n)] {s}
    rw [MeasurableSpace.measurableSet_iInf]
    intro n
    exact (Set.to_countable ((Sigma.mk n) ⁻¹' {s})).measurableSet

private def childPredicate {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : (ℕ → ℕ) → X) (s : BaireStem) (x : X) (k : ℕ) : Prop :=
  x ∈ imageHull μ f (stemChild s k) ∨
    (k = 0 ∧ ¬ ∃ j : ℕ, x ∈ imageHull μ f (stemChild s j))

private theorem childPredicate_exists {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : (ℕ → ℕ) → X) (s : BaireStem) (x : X) :
    ∃ k, childPredicate μ f s x k := by
  classical
  by_cases h : ∃ k : ℕ, x ∈ imageHull μ f (stemChild s k)
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Or.inl hk⟩
  · exact ⟨0, Or.inr ⟨rfl, h⟩⟩

noncomputable def hullChildIndex {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : (ℕ → ℕ) → X) (s : BaireStem) (x : X) : ℕ := by
  classical
  exact Nat.find (childPredicate_exists μ f s x)

theorem measurable_hullChildIndex {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : (ℕ → ℕ) → X) (s : BaireStem) :
    Measurable (hullChildIndex μ f s) := by
  classical
  apply measurable_find
  intro k
  have hk : MeasurableSet (imageHull μ f (stemChild s k)) := measurableSet_toMeasurable _ _
  have hu : MeasurableSet (⋃ j : ℕ, imageHull μ f (stemChild s j)) :=
    MeasurableSet.iUnion (fun j ↦ measurableSet_toMeasurable _ _)
  by_cases h : k = 0
  · convert hk.union hu.compl using 1
    ext x
    simp [childPredicate, h]
  · simpa only [childPredicate, h, false_and, or_false, Set.ofPred_mem_eq] using hk

noncomputable def selectorStem {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : (ℕ → ℕ) → X) (x : X) : ℕ → BaireStem
  | 0 => emptyStem
  | n + 1 => stemChild (selectorStem μ f x n) (hullChildIndex μ f (selectorStem μ f x n) x)

theorem measurable_selectorStem {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : (ℕ → ℕ) → X) (n : ℕ) :
    Measurable (fun x ↦ selectorStem μ f x n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hm : Measurable (fun p : X × BaireStem ↦
        stemChild p.2 (hullChildIndex μ f p.2 p.1)) := by
      apply measurable_from_prod_countable_left
      intro s
      exact (measurable_of_countable (stemChild s)).comp (measurable_hullChildIndex μ f s)
    exact hm.comp (measurable_id.prodMk ih)

noncomputable def hullBaireSelector {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : (ℕ → ℕ) → X) (x : X) (i : ℕ) : ℕ :=
  stemSeq (selectorStem μ f x (i + 1)) i

theorem measurable_hullBaireSelector {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : (ℕ → ℕ) → X) : Measurable (hullBaireSelector μ f) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_of_countable (fun s : BaireStem ↦ stemSeq s i)).comp
    (measurable_selectorStem μ f (i + 1))

theorem hullBaireSelector_rightInverse {X : Type*} [TopologicalSpace X] [T3Space X]
    [MeasurableSpace X] (μ : Measure X) (f : (ℕ → ℕ) → X) (hf : Continuous f)
    (x : X) (hx : x ∈ imageHull μ f emptyStem) (hgood : x ∉ hullExceptional μ f) :
    f (hullBaireSelector μ f x) = x := by
  classical
  let p := selectorStem μ f x
  have hmem : ∀ n, x ∈ imageHull μ f (p n) := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih =>
      have hex : ∃ k : ℕ, x ∈ imageHull μ f (stemChild (p n) k) := by
        by_contra h
        have hn : x ∉ ⋃ k : ℕ, imageHull μ f (stemChild (p n) k) := by simpa using h
        exact hgood (mem_iUnion_of_mem (p n) (Or.inr ⟨ih, hn⟩))
      have hspec := Nat.find_spec (childPredicate_exists μ f (p n) x)
      rcases hspec with h | ⟨_, h⟩
      · exact h
      · exact (h hex).elim
  have plen : ∀ n, (p n).1 = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [p, selectorStem, stemChild_length] at *; exact congrArg Nat.succ ih
  have stable : ∀ i n, i + 1 ≤ n → stemSeq (p n) i = stemSeq (p (i + 1)) i := by
    intro i
    apply Nat.le_induction
    · rfl
    intro n hn ih
    change stemSeq (stemChild (p n) _) i = _
    rw [stemSeq_child_old (p n) _ i (by rw [plen]; omega), ih]
  have hcyl (n : ℕ) : stemCylinder (p n) = PiNat.cylinder (hullBaireSelector μ f x) n := by
    rw [stemCylinder, plen, ← PiNat.mem_cylinder_iff_eq, PiNat.mem_cylinder_iff]
    intro i hi
    exact stable i n (Nat.succ_le_of_lt hi)
  have hclosed (n : ℕ) : x ∈ closure (f '' stemCylinder (p n)) := by
    by_contra h
    exact hgood (mem_iUnion_of_mem (p n) (Or.inl ⟨hmem n, h⟩))
  exact (mem_all_closed_cylinder_images f hf (hullBaireSelector μ f x) x (fun n ↦ by
    rw [← hcyl n]
    exact hclosed n)).symm

theorem exists_measurable_baire_rightInverse {X : Type*} [TopologicalSpace X] [T3Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) :
    ∃ g : X → (ℕ → ℕ), Measurable g ∧ ∀ᵐ x ∂μ, x ∈ Set.range f → f (g x) = x := by
  refine ⟨hullBaireSelector μ f, measurable_hullBaireSelector μ f, ?_⟩
  have hgood : ∀ᵐ x ∂μ, x ∉ hullExceptional μ f := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hullExceptional_null μ f
  filter_upwards [hgood] with x hx hr
  apply hullBaireSelector_rightInverse μ f hf x _ hx
  apply subset_toMeasurable μ (f '' stemCylinder emptyStem)
  simpa only [stemCylinder_empty, image_univ] using hr

end ModelRiskCodex

/- Source: Solutions/ModelRisk_AnalyticRelationSelector.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory Set Filter Topology

/-- For a fixed finite Borel measure, an analytic relation admits a Borel
selector on almost every point of its projection. No global Borel selector
or continuity of the relation is asserted. -/
theorem exists_measurable_analytic_relation_selector
    {X Y : Type*} [TopologicalSpace X] [T3Space X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y]
    (μ : Measure X) [IsFiniteMeasure μ] {A : Set (X × Y)} (hA : AnalyticSet A) :
    ∃ v : X → Y, Measurable v ∧
      ∀ᵐ x ∂μ, x ∈ Prod.fst '' A → (x, v x) ∈ A := by
  classical
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨g, hg, rfl⟩
  · refine ⟨fun _ ↦ Classical.ofNonempty, measurable_const, ?_⟩
    exact Filter.Eventually.of_forall (by simp)
  · let f : (ℕ → ℕ) → X := fun a ↦ (g a).1
    have hf : Continuous f := continuous_fst.comp hg
    obtain ⟨a, ha, hright⟩ := exists_measurable_baire_rightInverse μ f hf
    refine ⟨fun x ↦ (g (a x)).2, (continuous_snd.comp hg).measurable.comp ha, ?_⟩
    filter_upwards [hright] with x hx hproj
    have hr : x ∈ Set.range f := by
      rcases hproj with ⟨_, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, rfl⟩
    have he : f (a x) = x := hx hr
    refine ⟨a x, ?_⟩
    apply Prod.ext
    · exact he
    · rfl

end ModelRiskCodex

/- Source: Solutions/ModelRisk_ScoreSelector.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory Set Filter Topology ModelRiskOT.Duality

/-- A Borel score selector above a measurable real threshold wherever that
threshold lies strictly below the canonical envelope, almost everywhere
for the specified probability measure. -/
theorem exists_measurable_score_selector {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → S → ℝ) (f : S → ℝ)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2)) (hf : Measurable f)
    (lam : ℝ) (q : S → ℝ) (hq : Measurable q) :
    ∃ v : S → S, Measurable v ∧
      ∀ᵐ x ∂μ, (q x : EReal) < phiLam c f lam x → q x < f (v x) - lam * c x (v x) := by
  let := nonempty_of_isProbabilityMeasure μ
  let A : Set (S × S) := {p | q p.1 < f p.2 - lam * c p.1 p.2}
  have hA : MeasurableSet A := measurableSet_lt (hq.comp measurable_fst)
    ((hf.comp measurable_snd).sub (measurable_const.mul hc))
  obtain ⟨v, hv, hsel⟩ := exists_measurable_analytic_relation_selector μ hA.analyticSet
  refine ⟨v, hv, ?_⟩
  filter_upwards [hsel] with x hx hlt
  have hproj : x ∈ Prod.fst '' A := by
    simp only [phiLam, phiLamOn, Set.mem_univ, iSup_true] at hlt
    obtain ⟨y, hy⟩ := lt_iSup_iff.mp hlt
    exact ⟨(x, y), EReal.coe_lt_coe_iff.mp hy, rfl⟩
  exact hx hproj

theorem exists_measurable_original_score_selector
    {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (hc : AssumptionA1 c)
    (f : S → ℝ) (hf : UpperSemicontinuous f) (lam : ℝ)
    (q : S → ℝ) (hq : Measurable q) :
    ∃ v : S → S, Measurable v ∧
      ∀ᵐ x ∂μ, (q x : EReal) < phiLam c f lam x → q x < f (v x) - lam * c x (v x) :=
  exists_measurable_score_selector μ c f hc.lsc.measurable hf.measurable lam q hq

end ModelRiskCodex

/- Source: Solutions/ModelRisk_SelectorPenaltyLimit.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory Set Filter
open scoped Classical

def selectorPenalty {S : Type*} (c : S → S → ℝ) (f : S → ℝ) (lam : ℝ)
    (v : S → S) (x : S) : ℝ := selectorGain f v x - lam * c x (v x)

lemma boundedSelector_penalty_apply {S : Type*} (c : S → S → ℝ) (f : S → ℝ)
    (lam : ℝ) (v : S → S) (hcdiag : ∀ x, c x x = 0) (n : ℝ) (x : S) :
    selectorPenalty c f lam (boundedSelector c f v n) x =
      if x ∈ selectorCutRegion c f v n then selectorPenalty c f lam v x else 0 := by
  classical
  by_cases h : x ∈ selectorCutRegion c f v n <;>
    simp [selectorPenalty, selectorGain, boundedSelector, h, hcdiag]

lemma boundedSelector_penalty_monotone {S : Type*} (c : S → S → ℝ) (f : S → ℝ)
    (lam : ℝ) (v : S → S) (hcdiag : ∀ x, c x x = 0) :
    Monotone (fun n : ℕ ↦ fun x ↦ ENNReal.ofReal (selectorPenalty c f lam
      (boundedSelector c f v n) x)) := by
  classical
  intro m n hmn x
  change ENNReal.ofReal (selectorPenalty c f lam (boundedSelector c f v m) x) ≤
    ENNReal.ofReal (selectorPenalty c f lam (boundedSelector c f v n) x)
  rw [boundedSelector_penalty_apply c f lam v hcdiag,
    boundedSelector_penalty_apply c f lam v hcdiag]
  by_cases hm : x ∈ selectorCutRegion c f v m
  · have hn : x ∈ selectorCutRegion c f v n :=
      ⟨hm.1, hm.2.1.trans (Nat.cast_le.mpr hmn), hm.2.2.trans (Nat.cast_le.mpr hmn)⟩
    simp only [if_pos hm, if_pos hn, le_refl]
  · rw [if_neg hm]
    simp only [ENNReal.ofReal_zero]
    exact zero_le

lemma boundedSelector_penalty_iSup {S : Type*} (c : S → S → ℝ) (f : S → ℝ)
    (lam : ℝ) (v : S → S) (hc0 : ∀ x y, 0 ≤ c x y) (hcdiag : ∀ x, c x x = 0)
    (hlam : 0 ≤ lam) (hpen : ∀ x, 0 ≤ selectorPenalty c f lam v x) (x : S) :
    (⨆ n : ℕ, ENNReal.ofReal (selectorPenalty c f lam (boundedSelector c f v n) x)) =
      ENNReal.ofReal (selectorPenalty c f lam v x) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro n
    rw [boundedSelector_penalty_apply c f lam v hcdiag]
    split_ifs <;> simp
  · have hgain : 0 ≤ selectorGain f v x := by
      have hc := mul_nonneg hlam (hc0 x (v x))
      have hp := hpen x
      dsimp [selectorPenalty] at hp
      linarith
    obtain ⟨N, hN⟩ := eventually_atTop.mp (boundedSelector_eventually_eq c f v x hgain)
    have he : selectorPenalty c f lam (boundedSelector c f v N) x =
        selectorPenalty c f lam v x := by
      simp only [selectorPenalty, selectorGain, hN N le_rfl]
    rw [← he]
    exact le_iSup (fun n : ℕ ↦ ENNReal.ofReal
      (selectorPenalty c f lam (boundedSelector c f v n) x)) N

lemma lintegral_selectorPenalty_eq_iSup_bounded {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (c : S → S → ℝ) (f : S → ℝ) (lam : ℝ) (v : S → S)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2)) (hf : Measurable f) (hv : Measurable v)
    (hc0 : ∀ x y, 0 ≤ c x y) (hcdiag : ∀ x, c x x = 0) (hlam : 0 ≤ lam)
    (hpen : ∀ x, 0 ≤ selectorPenalty c f lam v x) :
    (∫⁻ x, ENNReal.ofReal (selectorPenalty c f lam v x) ∂μ) =
      ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (selectorPenalty c f lam
        (boundedSelector c f v n) x) ∂μ := by
  have hm : ∀ n : ℕ, Measurable (fun x ↦ ENNReal.ofReal
      (selectorPenalty c f lam (boundedSelector c f v n) x)) := by
    intro n
    have hb := measurable_boundedSelector c f v hc hf hv n
    exact ENNReal.measurable_ofReal.comp
      (((hf.comp hb).sub hf).sub (measurable_const.mul (hc.comp (measurable_id.prodMk hb))))
  simp_rw [← boundedSelector_penalty_iSup c f lam v hc0 hcdiag hlam hpen]
  exact lintegral_iSup hm (boundedSelector_penalty_monotone c f lam v hcdiag)

end ModelRiskCodex

/- Source: Solutions/ModelRisk_SelectorIntegral.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality

lemma boundedSelectorPlan_objective {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] (c : S → S → ℝ) (f : S → ℝ) (v : S → S)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2)) (hf : Measurable f) (hv : Measurable v)
    (hfi : Integrable f μ) (hc0 : ∀ x y, 0 ≤ c x y) (hcdiag : ∀ x, c x x = 0)
    (n : ℝ) (hn : 0 ≤ n) :
    primalObj f (selectorPlan μ (boundedSelector c f v n)) =
      ((∫ x, f x ∂μ : ℝ) : EReal) +
        ((∫ x, selectorGain f (boundedSelector c f v n) x ∂μ : ℝ) : EReal) := by
  have hb := measurable_boundedSelector c f v hc hf hv n
  have hpay := boundedSelector_payoff_integrable μ c f v hc hf hv hfi hc0 hcdiag n hn
  have hg := (boundedSelector_integrable_components μ c f v hc hf hv hc0 hcdiag n hn).1
  rw [selectorPlan_objective μ _ hb f hf hpay, ← EReal.coe_add]
  congr 1
  have he : (fun x ↦ f (boundedSelector c f v n x)) =
      fun x ↦ f x + selectorGain f (boundedSelector c f v n) x := by
    funext x
    simp only [selectorGain]
    ring
  rw [he, integral_add hfi hg]

lemma integral_selectorPenalty {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (c : S → S → ℝ) (f : S → ℝ) (lam : ℝ) (v : S → S)
    (hg : Integrable (selectorGain f v) μ) (hc : Integrable (fun x ↦ c x (v x)) μ) :
    (∫ x, selectorPenalty c f lam v x ∂μ) =
      (∫ x, selectorGain f v x ∂μ) - lam * (∫ x, c x (v x) ∂μ) := by
  unfold selectorPenalty
  rw [integral_sub hg (hc.const_mul lam), integral_const_mul]

/-- A uniform supporting bound for integrable selectors controls the full
nonnegative selector penalty integral, by bounded diagonal truncation. -/
lemma selectorPenalty_lintegral_le_of_integrable_support {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] (c : S → S → ℝ) (f : S → ℝ) (lam : ℝ)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2)) (hf : Measurable f)
    (hc0 : ∀ x y, 0 ≤ c x y) (hcdiag : ∀ x, c x x = 0) (hlam : 0 ≤ lam)
    (α : ℝ)
    (hsupport : ∀ w : S → S, Measurable w → Integrable (selectorGain f w) μ →
      Integrable (fun x ↦ c x (w x)) μ →
      (∫ x, selectorGain f w x ∂μ) - lam * (∫ x, c x (w x) ∂μ) ≤ α)
    (v : S → S) (hv : Measurable v) (hpen : ∀ x, 0 ≤ selectorPenalty c f lam v x) :
    (∫⁻ x, ENNReal.ofReal (selectorPenalty c f lam v x) ∂μ) ≤ ENNReal.ofReal α := by
  rw [lintegral_selectorPenalty_eq_iSup_bounded μ c f lam v hc hf hv hc0 hcdiag hlam hpen]
  apply iSup_le
  intro n
  have hb := measurable_boundedSelector c f v hc hf hv n
  obtain ⟨hg, hci⟩ := boundedSelector_integrable_components μ c f v hc hf hv hc0 hcdiag n
    (Nat.cast_nonneg n)
  have hpi : Integrable (selectorPenalty c f lam (boundedSelector c f v n)) μ :=
    hg.sub (hci.const_mul lam)
  have hp0 : ∀ᵐ x ∂μ, 0 ≤ selectorPenalty c f lam (boundedSelector c f v n) x := by
    apply Filter.Eventually.of_forall
    intro x
    rw [boundedSelector_penalty_apply c f lam v hcdiag]
    split_ifs
    · exact hpen x
    · exact le_rfl
  rw [← ofReal_integral_eq_lintegral_ofReal hpi hp0]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_selectorPenalty μ c f lam _ hg hci]
  exact hsupport _ hb hg hci

end ModelRiskCodex

/- Source: Solutions/ModelRisk_ImprovingSelector.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality Set Filter

noncomputable def improvingSelector {S : Type*} (c : S → S → ℝ) (f : S → ℝ)
    (lam : ℝ) (v : S → S) (x : S) : S := by
  classical
  exact if 0 ≤ selectorPenalty c f lam v x then v x else x

lemma measurable_improvingSelector {S : Type*} [MeasurableSpace S]
    (c : S → S → ℝ) (f : S → ℝ) (lam : ℝ) (v : S → S)
    (hc : Measurable (fun p : S × S ↦ c p.1 p.2)) (hf : Measurable f) (hv : Measurable v) :
    Measurable (improvingSelector c f lam v) := by
  have hp : Measurable (selectorPenalty c f lam v) :=
    ((hf.comp hv).sub hf).sub (measurable_const.mul (hc.comp (measurable_id.prodMk hv)))
  exact Measurable.ite (measurableSet_le measurable_const hp) hv measurable_id

lemma improvingSelector_penalty {S : Type*} (c : S → S → ℝ) (f : S → ℝ)
    (lam : ℝ) (v : S → S) (hcdiag : ∀ x, c x x = 0) (x : S) :
    selectorPenalty c f lam (improvingSelector c f lam v) x =
      max (selectorPenalty c f lam v x) 0 := by
  classical
  by_cases h : 0 ≤ selectorPenalty c f lam v x
  · have hvx : improvingSelector c f lam v x = v x := if_pos h
    change f (improvingSelector c f lam v x) - f x -
      lam * c x (improvingSelector c f lam v x) = _
    rw [hvx]
    exact (max_eq_left h).symm
  · have hvx : improvingSelector c f lam v x = x := if_neg h
    change f (improvingSelector c f lam v x) - f x -
      lam * c x (improvingSelector c f lam v x) = _
    rw [hvx, hcdiag, sub_self, mul_zero, sub_zero]
    exact (max_eq_right (le_of_not_ge h)).symm

lemma exists_measurable_improving_score_selector
    {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (hc : AssumptionA1 c)
    (f : S → ℝ) (hf : UpperSemicontinuous f) (lam : ℝ) (q : S → ℝ) (hq : Measurable q) :
    ∃ w : S → S, Measurable w ∧ (∀ x, 0 ≤ selectorPenalty c f lam w x) ∧
      ∀ᵐ x ∂μ, (q x : EReal) < phiLam c f lam x →
        q x - f x < selectorPenalty c f lam w x := by
  obtain ⟨v, hv, hscore⟩ := exists_measurable_original_score_selector μ c hc f hf lam q hq
  have hd : ∀ x, c x x = 0 := fun x ↦ (hc.eq_zero_iff x x).mpr rfl
  refine ⟨improvingSelector c f lam v,
    measurable_improvingSelector c f lam v hc.lsc.measurable hf.measurable hv, ?_, ?_⟩
  · intro x
    rw [improvingSelector_penalty c f lam v hd]
    exact le_max_right _ _
  · filter_upwards [hscore] with x hx hqphi
    have h := hx hqphi
    have hp : q x - f x < selectorPenalty c f lam v x := by
      dsimp [selectorPenalty, selectorGain]
      linarith
    rw [improvingSelector_penalty c f lam v hd]
    exact hp.trans_le (le_max_left _ _)

end ModelRiskCodex

/- Source: Solutions/ModelRisk_CanonicalGain.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality Filter

noncomputable def canonicalGain {S : Type*} (c : S → S → ℝ) (f : S → ℝ) (lam : ℝ)
    (x : S) : ENNReal := (phiLam c f lam x - (f x : EReal)).toENNReal

lemma canonicalGain_aemeasurable {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ) (hf : UpperSemicontinuous f)
    (lam : ℝ) : AEMeasurable (canonicalGain c f lam) μ := by
  have hm := (phiLam_nullMeasurable μ c f hc.lsc.measurable hf.measurable lam).aemeasurable
  exact measurable_ereal_toENNReal.comp_aemeasurable
    (hm.sub hf.measurable.aemeasurable.coe_real_ereal)

lemma canonical_extIntegral_eq_nominal_add_gain {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ) (hf : UpperSemicontinuous f)
    (hfi : Integrable f μ) (lam : ℝ) :
    extIntegral μ (phiLam c f lam) = ((∫ x, f x ∂μ : ℝ) : EReal) +
      ((∫⁻ x, canonicalGain c f lam x ∂μ : ENNReal) : EReal) :=
  extIntegral_eq_nominal_add_gain μ f hfi _
    (phiLam_nullMeasurable μ c f hc.lsc.measurable hf.measurable lam).aemeasurable
    (Filter.Eventually.of_forall (nominal_le_phiLam c hc f lam))

lemma finite_gain_threshold_lt (a : ℝ) (φ : EReal) (hφ : (a : EReal) ≤ φ)
    (u : ENNReal) (hu : u ≠ ⊤) (hule : u ≤ (φ - (a : EReal)).toENNReal)
    (ε : ℝ) (hε : 0 < ε) : ((a + u.toReal - ε : ℝ) : EReal) < φ := by
  have hg0 : 0 ≤ φ - (a : EReal) :=
    (EReal.sub_nonneg (.inr (EReal.coe_ne_top a)) (.inr (EReal.coe_ne_bot a))).mpr hφ
  have hr : (u.toReal : EReal) ≤ φ - (a : EReal) := by
    rw [EReal.coe_ennreal_toReal hu, ← EReal.coe_toENNReal hg0]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hule
  have hs : (u.toReal : EReal) + (a : EReal) ≤ (φ - (a : EReal)) + (a : EReal) :=
    add_le_add hr le_rfl
  rw [EReal.sub_add_cancel] at hs
  have hs' : ((a + u.toReal : ℝ) : EReal) ≤ φ := by
    simpa only [← EReal.coe_add, add_comm] using hs
  exact (EReal.coe_lt_coe_iff.mpr (by linarith : a + u.toReal - ε < a + u.toReal)).trans_le hs'

lemma exists_capped_gain_selector {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ) (hf : UpperSemicontinuous f)
    (lam : ℝ) (P : S → ENNReal) (hPm : Measurable P)
    (hP : P =ᵐ[μ] canonicalGain c f lam) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ w : S → S, Measurable w ∧ (∀ x, 0 ≤ selectorPenalty c f lam w x) ∧
      ∀ᵐ x ∂μ, (min (P x) (n : ENNReal)).toReal - ε < selectorPenalty c f lam w x := by
  let q : S → ℝ := fun x ↦ f x + (min (P x) (n : ENNReal)).toReal - ε
  have hqm : Measurable q :=
    (hf.measurable.add (ENNReal.measurable_toReal.comp (hPm.min measurable_const))).sub measurable_const
  obtain ⟨w, hwm, hw0, hwq⟩ := exists_measurable_improving_score_selector μ c hc f hf lam q hqm
  refine ⟨w, hwm, hw0, ?_⟩
  filter_upwards [hP, hwq] with x hPx hx
  have hn : min (P x) (n : ENNReal) ≠ ⊤ :=
    (lt_of_le_of_lt (min_le_right _ _) (by simp)).ne
  have hle : min (P x) (n : ENNReal) ≤ (phiLam c f lam x - (f x : EReal)).toENNReal := by
    change min (P x) (n : ENNReal) ≤ canonicalGain c f lam x
    rw [← hPx]
    exact min_le_left _ _
  have hq : (q x : EReal) < phiLam c f lam x :=
    finite_gain_threshold_lt (f x) _ (nominal_le_phiLam c hc f lam x) _ hn hle ε hε
  have h := hx hq
  dsimp [q] at h
  linarith

end ModelRiskCodex

/- Source: Solutions/ModelRisk_GainIntegralSupport.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality Filter

lemma canonicalGain_lintegral_le_of_integrable_support
    {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (hc : AssumptionA1 c)
    (f : S → ℝ) (hf : UpperSemicontinuous f) (lam : ℝ) (hlam : 0 ≤ lam) (α : ℝ)
    (hsupport : ∀ w : S → S, Measurable w → Integrable (selectorGain f w) μ →
      Integrable (fun x ↦ c x (w x)) μ →
      (∫ x, selectorGain f w x ∂μ) - lam * (∫ x, c x (w x) ∂μ) ≤ α) :
    (∫⁻ x, canonicalGain c f lam x ∂μ) ≤ ENNReal.ofReal α := by
  have hd : ∀ x, c x x = 0 := fun x ↦ (hc.eq_zero_iff x x).mpr rfl
  have hg := canonicalGain_aemeasurable μ c hc f hf lam
  let P := hg.mk (canonicalGain c f lam)
  have hPm : Measurable P := hg.measurable_mk
  have hP : P =ᵐ[μ] canonicalGain c f lam := hg.ae_eq_mk.symm
  have hcap : ∀ n : ℕ, (∫⁻ x, min (P x) (n : ENNReal) ∂μ) ≤ ENNReal.ofReal α := by
    intro n
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨w, hwm, hw0, hquality⟩ := exists_capped_gain_selector μ c hc f hf lam P hPm hP n ε hεr
    have hwbound := selectorPenalty_lintegral_le_of_integrable_support μ c f lam hc.lsc.measurable
      hf.measurable hc.nonneg hd hlam α hsupport w hwm hw0
    have hpoint : ∀ᵐ x ∂μ, min (P x) (n : ENNReal) ≤
        ENNReal.ofReal (selectorPenalty c f lam w x) + (ε : ENNReal) := by
      filter_upwards [hquality] with x hx
      have hn : min (P x) (n : ENNReal) ≠ ⊤ :=
        (lt_of_le_of_lt (min_le_right _ _) (by simp)).ne
      rw [← ENNReal.ofReal_toReal hn]
      have hr : (min (P x) (n : ENNReal)).toReal ≤ selectorPenalty c f lam w x + (ε : ℝ) := by
        linarith
      calc
        ENNReal.ofReal (min (P x) (n : ENNReal)).toReal ≤
            ENNReal.ofReal (selectorPenalty c f lam w x + (ε : ℝ)) := ENNReal.ofReal_le_ofReal hr
        _ = ENNReal.ofReal (selectorPenalty c f lam w x) + (ε : ENNReal) := by
          rw [ENNReal.ofReal_add (hw0 x) ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    calc
      (∫⁻ x, min (P x) (n : ENNReal) ∂μ) ≤
          ∫⁻ x, ENNReal.ofReal (selectorPenalty c f lam w x) + (ε : ENNReal) ∂μ :=
        lintegral_mono_ae hpoint
      _ = (∫⁻ x, ENNReal.ofReal (selectorPenalty c f lam w x) ∂μ) + (ε : ENNReal) := by
        rw [lintegral_add_right _ measurable_const]
        simp
      _ ≤ ENNReal.ofReal α + (ε : ENNReal) := add_le_add hwbound le_rfl
  have he : P = fun x ↦ ⨆ n : ℕ, min (P x) (n : ENNReal) := by
    funext x
    rw [← inf_iSup_eq, ENNReal.iSup_natCast]
    simp
  rw [← lintegral_congr_ae hP, he, lintegral_iSup (fun n ↦ hPm.min measurable_const)]
  · exact iSup_le hcap
  · intro m n hmn x
    exact min_le_min_left _ (Nat.cast_le.mpr hmn)

lemma canonical_extIntegral_le_of_integrable_support
    {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (hc : AssumptionA1 c)
    (f : S → ℝ) (hf : UpperSemicontinuous f) (hfi : Integrable f μ)
    (lam : ℝ) (hlam : 0 ≤ lam) (α : ℝ)
    (hsupport : ∀ w : S → S, Measurable w → Integrable (selectorGain f w) μ →
      Integrable (fun x ↦ c x (w x)) μ →
      (∫ x, selectorGain f w x ∂μ) - lam * (∫ x, c x (w x) ∂μ) ≤ α) :
    extIntegral μ (phiLam c f lam) ≤ ((∫ x, f x ∂μ : ℝ) : EReal) + (α : EReal) := by
  rw [canonical_extIntegral_eq_nominal_add_gain μ c hc f hf hfi lam]
  have h := canonicalGain_lintegral_le_of_integrable_support μ c hc f hf lam hlam α hsupport
  have hd : ∀ x, c x x = 0 := fun x ↦ (hc.eq_zero_iff x x).mpr rfl
  have hα : 0 ≤ α := by
    have hgId : Integrable (selectorGain f (id : S → S)) μ := by
      change Integrable (fun x : S ↦ f (id x) - f x) μ
      simpa only [id_eq, sub_self] using
        (integrable_const (0 : ℝ) : Integrable (fun _ : S ↦ (0 : ℝ)) μ)
    have hcId : Integrable (fun x ↦ c x (id x)) μ := by
      simpa only [id_eq, hd] using (integrable_const (0 : ℝ) : Integrable (fun _ : S ↦ (0 : ℝ)) μ)
    simpa only [selectorGain, id_eq, sub_self, hd, integral_zero, mul_zero, sub_zero] using
      hsupport id measurable_id hgId hcId
  have hcoe : ((∫⁻ x, canonicalGain c f lam x ∂μ : ENNReal) : EReal) ≤ (α : EReal) := by
    have hc' := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
    have heα : ((ENNReal.ofReal α : ENNReal) : EReal) = (α : EReal) := by
      simpa only [EReal.real_coe_toENNReal] using
        (EReal.coe_toENNReal (show (0 : EReal) ≤ (α : EReal) from EReal.coe_le_coe_iff.mpr hα))
    exact hc'.trans_eq heα
  exact add_le_add le_rfl hcoe

end ModelRiskCodex

/- Source: Solutions/ModelRisk_ZeroMultiplier.lean -/
/- Canonical zero-multiplier feasibility and the infinite dual-value branch.
The finite strong-duality and optimizer branches remain to be proved. -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality BertsekasShreve.AnalyticSelection

theorem phiLam_zero {S : Type*} (c : S → S → ℝ) (f : S → ℝ) :
    phiLam c f 0 = fun _ ↦ ⨆ y : S, (f y : EReal) := by
  funext x
  simp [phiLam, phiLamOn]

theorem univMeasurable_const {S : Type*} [MeasurableSpace S] (a : EReal) :
    IsUnivMeasurableEReal (fun _ : S ↦ a) := by
  intro B hB μ hμ
  exact (measurable_const hB).nullMeasurableSet

theorem zero_phi_dualFeasible {S : Type*} [MeasurableSpace S]
    (c : S → S → ℝ) (f : S → ℝ) :
    (0, phiLam c f 0) ∈ dualFeasible c f Set.univ := by
  refine ⟨le_rfl, ?_, ?_⟩
  · rw [phiLam_zero]
    exact univMeasurable_const _
  · intro x hx y hy
    simp only [zero_mul, EReal.coe_zero, add_zero]
    rw [phiLam_zero]
    exact le_iSup (fun y : S ↦ (f y : EReal)) y

theorem dual_optimizer_of_top {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (c : S → S → ℝ) (f : S → ℝ) (δ : ℝ)
    (htop : dualValue c f μ δ = ⊤) :
    ∃ lam : ℝ, 0 ≤ lam ∧ (lam, phiLam c f lam) ∈ dualFeasible c f Set.univ ∧
      dualObj μ δ lam (phiLam c f lam) = dualValue c f μ δ := by
  have hfeas := zero_phi_dualFeasible c f
  refine ⟨0, le_rfl, hfeas, ?_⟩
  have h : dualValue c f μ δ ≤ dualObj μ δ 0 (phiLam c f 0) :=
    iInf_le_of_le (0, phiLam c f 0) (iInf_le_of_le hfeas le_rfl)
  rw [htop] at h ⊢
  exact top_unique h

end ModelRiskCodex

/- Source: Solutions/ModelRisk_StrongDuality.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality

private lemma integral_selected_eq_nominal_add_gain {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (f : S → ℝ) (w : S → S) (hfi : Integrable f μ)
    (hg : Integrable (selectorGain f w) μ) :
    (∫ x, f (w x) ∂μ) = (∫ x, f x ∂μ) + (∫ x, selectorGain f w x ∂μ) := by
  have he : (fun x ↦ f (w x)) = fun x ↦ f x + selectorGain f w x := by
    funext x
    dsimp [selectorGain]
    ring
  rw [he, integral_add hfi hg]

lemma finite_value_dual_optimizer {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ)
    (hf : UpperSemicontinuous f) (hfi : Integrable f μ) (δ : ℝ) (hδ : 0 < δ)
    (V : ℝ) (hV : primalValue c f μ δ = (V : EReal)) :
    ∃ lam : ℝ, 0 ≤ lam ∧ (lam, phiLam c f lam) ∈ dualFeasible c f Set.univ ∧
      dualObj μ δ lam (phiLam c f lam) = primalValue c f μ δ := by
  obtain ⟨lam, hlam, hsupport⟩ := finite_value_supporting_multiplier μ c hc f hf hfi δ hδ V hV
  let α := V - lam * δ - (∫ x, f x ∂μ)
  have hsel : ∀ w : S → S, Measurable w → Integrable (selectorGain f w) μ →
      Integrable (fun x ↦ c x (w x)) μ →
      (∫ x, selectorGain f w x ∂μ) - lam * (∫ x, c x (w x) ∂μ) ≤ α := by
    intro w hw hg hci
    have hpoint := selector_mem_finiteCouplingValues μ c f hc.lsc.measurable hf.measurable hfi w hw hg hci
    have h := hsupport _ hpoint
    change (∫ x, f (w x) ∂μ) ≤ V + lam * ((∫ x, c x (w x) ∂μ) - δ) at h
    rw [integral_selected_eq_nominal_add_gain μ f w hfi hg] at h
    dsimp [α]
    linarith
  have henvelope := canonical_extIntegral_le_of_integrable_support μ c hc f hf hfi lam hlam α hsel
  have hD := canonical_dualFeasible c hc f hf lam hlam
  have hupper : dualObj μ δ lam (phiLam c f lam) ≤ primalValue c f μ δ := by
    rw [hV]
    calc
      dualObj μ δ lam (phiLam c f lam) ≤ ((lam * δ : ℝ) : EReal) +
          (((∫ x, f x ∂μ : ℝ) : EReal) + (α : EReal)) := add_le_add le_rfl henvelope
      _ = (V : EReal) := by
        rw [← EReal.coe_add, ← EReal.coe_add]
        congr 1
        dsimp [α]
        ring
  have hlower : primalValue c f μ δ ≤ dualObj μ δ lam (phiLam c f lam) :=
    (weak_duality μ c hc f hf hfi δ hδ.le).trans
      (iInf_le_of_le (lam, phiLam c f lam) (iInf_le_of_le hD le_rfl))
  exact ⟨lam, hlam, hD, le_antisymm hupper hlower⟩

lemma finite_strong_duality_optimizer {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ)
    (hf : UpperSemicontinuous f) (hfi : Integrable f μ) (δ : ℝ) (hδ : 0 < δ)
    (V : ℝ) (hV : primalValue c f μ δ = (V : EReal)) :
    primalValue c f μ δ = dualValue c f μ δ ∧
      (∃ lam : ℝ, 0 ≤ lam ∧ (lam, phiLam c f lam) ∈ dualFeasible c f Set.univ ∧
        dualObj μ δ lam (phiLam c f lam) = dualValue c f μ δ) := by
  obtain ⟨lam, hlam, hD, hObj⟩ := finite_value_dual_optimizer μ c hc f hf hfi δ hδ V hV
  have hupper : dualValue c f μ δ ≤ primalValue c f μ δ := by
    rw [← hObj]
    exact iInf_le_of_le (lam, phiLam c f lam) (iInf_le_of_le hD le_rfl)
  have he := le_antisymm (weak_duality μ c hc f hf hfi δ hδ.le) hupper
  refine ⟨he, lam, hlam, hD, ?_⟩
  exact hObj.trans he

/-- The first two conjuncts of the original theorem, at its complete scope.
The complementary-slackness conjuncts remain to be proved. -/
lemma strong_duality_optimizer {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ)
    (hf : UpperSemicontinuous f) (hfi : Integrable f μ) (δ : ℝ) (hδ : 0 < δ) :
    primalValue c f μ δ = dualValue c f μ δ ∧
      (∃ lam : ℝ, 0 ≤ lam ∧ (lam, phiLam c f lam) ∈ dualFeasible c f Set.univ ∧
        dualObj μ δ lam (phiLam c f lam) = dualValue c f μ δ) := by
  by_cases htop : primalValue c f μ δ = ⊤
  · have hjtop : dualValue c f μ δ = ⊤ :=
      top_unique (by rw [← htop]; exact weak_duality μ c hc f hf hfi δ hδ.le)
    refine ⟨by rw [htop, hjtop], dual_optimizer_of_top μ c f δ hjtop⟩
  · have hbot : primalValue c f μ δ ≠ ⊥ := by
      intro h
      have hl := nominal_le_primalValue μ c hc f hf.measurable hfi δ hδ.le
      rw [h] at hl
      exact (EReal.bot_lt_coe (∫ x, f x ∂μ)).not_ge hl
    exact finite_strong_duality_optimizer μ c hc f hf hfi δ hδ
      (primalValue c f μ δ).toReal (EReal.coe_toReal htop hbot).symm

end ModelRiskCodex

/- Source: Solutions/ModelRisk_DualCover.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality Filter

lemma dual_cover_integral {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ) (hfi : Integrable f μ)
    (δ : ℝ) (π : Measure (S × S)) (hπ : π ∈ primalFeasible c μ δ)
    (lam : ℝ) (φ : S → EReal) (hD : (lam, φ) ∈ dualFeasible c f Set.univ) :
    Integrable (fun p : S × S ↦ c p.1 p.2) π ∧
      extIntegral π (fun p : S × S ↦ φ p.1 + ((lam * c p.1 p.2 : ℝ) : EReal)) =
        extIntegral μ φ +
          ((lam * (∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π).toReal : ℝ) : EReal) := by
  obtain ⟨hprob, hfst, hcost⟩ := hπ
  let := hprob
  have hφmap : AEMeasurable φ (π.map Prod.fst) := by
    rw [hfst]
    exact dualFeasible_aemeasurable μ c f lam φ hD
  have hφπ : AEMeasurable (fun p : S × S ↦ φ p.1) π := hφmap.comp_measurable measurable_fst
  have hfmap : AEStronglyMeasurable f (π.map Prod.fst) := by
    rw [hfst]
    exact hfi.aestronglyMeasurable
  have hfirst : Integrable (fun p : S × S ↦ f p.1) π :=
    (integrable_map_measure hfmap measurable_fst.aemeasurable).mp (by rw [hfst]; exact hfi)
  have hc0 : ∀ᵐ p : S × S ∂π, 0 ≤ c p.1 p.2 :=
    Filter.Eventually.of_forall fun p ↦ hc.nonneg p.1 p.2
  have hcostfin : (∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π) ≠ ⊤ :=
    (hcost.trans_lt (by simp)).ne
  have hci : Integrable (fun p : S × S ↦ c p.1 p.2) π :=
    (lintegral_ofReal_ne_top_iff_integrable hc.lsc.measurable.aestronglyMeasurable hc0).mp hcostfin
  have hlow : ∀ᵐ p : S × S ∂π, (f p.1 : EReal) ≤ φ p.1 :=
    Filter.Eventually.of_forall fun p ↦ nominal_le_dualFeasible_phi c hc f lam φ hD p.1
  have hchange : extIntegral π (fun p : S × S ↦ φ p.1) = extIntegral μ φ := by
    rw [← extIntegral_map π Prod.fst measurable_fst φ hφmap, hfst]
  have he : extIntegral π (fun p : S × S ↦ φ p.1 + ((lam * c p.1 p.2 : ℝ) : EReal)) =
      extIntegral μ φ + ((lam * (∫ p : S × S, c p.1 p.2 ∂π) : ℝ) : EReal) := by
    rw [extIntegral_add_integrable π (fun p : S × S ↦ f p.1)
      (fun p : S × S ↦ lam * c p.1 p.2) hfirst (hci.const_mul lam)
      (fun p : S × S ↦ φ p.1) hφπ hlow, hchange, integral_const_mul]
  have hcostReal : (∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π).toReal =
      ∫ p : S × S, c p.1 p.2 ∂π :=
    (integral_eq_lintegral_of_nonneg_ae hc0 hci.aestronglyMeasurable).symm
  refine ⟨hci, ?_⟩
  rw [hcostReal]
  exact he

end ModelRiskCodex

/- Source: Solutions/ModelRisk_SlacknessIf.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality Filter

lemma slackness_objective_eq {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ) (hfi : Integrable f μ)
    (δ : ℝ) (π : Measure (S × S)) (hπ : π ∈ primalFeasible c μ δ)
    (lam : ℝ) (hD : (lam, phiLam c f lam) ∈ dualFeasible c f Set.univ)
    (hscore : ∀ᵐ p ∂π, ((f p.2 - lam * c p.1 p.2 : ℝ) : EReal) = phiLam c f lam p.1)
    (hbudget : lam * ((∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π).toReal - δ) = 0) :
    primalObj f π = dualObj μ δ lam (phiLam c f lam) := by
  have hae : (fun p : S × S ↦ (f p.2 : EReal)) =ᵐ[π]
      (fun p : S × S ↦ phiLam c f lam p.1 + ((lam * c p.1 p.2 : ℝ) : EReal)) := by
    filter_upwards [hscore] with p hp
    have he : (f p.2 : EReal) =
        ((f p.2 - lam * c p.1 p.2 : ℝ) : EReal) + ((lam * c p.1 p.2 : ℝ) : EReal) := by
      rw [← EReal.coe_add]
      congr 1
      ring
    rw [hp] at he
    exact he
  have hcost : lam * (∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π).toReal = lam * δ := by
    nlinarith
  have h := extIntegral_congr_ae π _ _ hae
  rw [(dual_cover_integral μ c hc f hfi δ π hπ lam (phiLam c f lam) hD).2, hcost] at h
  simpa only [primalObj, dualObj, add_comm] using h

lemma complementary_slackness_if {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ)
    (hf : UpperSemicontinuous f) (hfi : Integrable f μ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ π ∈ primalFeasible c μ δ, ∀ lam : ℝ,
      (lam, phiLam c f lam) ∈ dualFeasible c f Set.univ →
      ((∀ᵐ p ∂π, ((f p.2 - lam * c p.1 p.2 : ℝ) : EReal) = phiLam c f lam p.1) ∧
        lam * ((∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π).toReal - δ) = 0) →
      (primalObj f π = primalValue c f μ δ ∧
        dualObj μ δ lam (phiLam c f lam) = dualValue c f μ δ ∧
        primalObj f π = dualObj μ δ lam (phiLam c f lam)) := by
  intro π hπ lam hD hslack
  have he := slackness_objective_eq μ c hc f hfi δ π hπ lam hD hslack.1 hslack.2
  have hP : primalObj f π ≤ primalValue c f μ δ :=
    le_iSup_of_le π (le_iSup_of_le hπ le_rfl)
  have hJ : dualValue c f μ δ ≤ dualObj μ δ lam (phiLam c f lam) :=
    iInf_le_of_le (lam, phiLam c f lam) (iInf_le_of_le hD le_rfl)
  have hW := weak_duality μ c hc f hf hfi δ hδ.le
  refine ⟨le_antisymm hP ?_, le_antisymm ?_ hJ, he⟩
  · rw [he]
    exact hW.trans hJ
  · rw [← he]
    exact hP.trans hW

end ModelRiskCodex

/- Source: Solutions/ModelRisk_ExtIntegralStrict.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality Filter

lemma extIntegral_parts_finite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (φ : X → EReal) (hT : extIntegral μ φ ≠ ⊤) (hB : extIntegral μ φ ≠ ⊥) :
    (∫⁻ x, (φ x).toENNReal ∂μ) ≠ ⊤ ∧ (∫⁻ x, (-φ x).toENNReal ∂μ) ≠ ⊤ := by
  have hn : (∫⁻ x, (-φ x).toENNReal ∂μ) ≠ ⊤ := by
    intro h
    apply hB
    unfold extIntegral
    rw [h, EReal.coe_ennreal_top, EReal.sub_top]
  refine ⟨?_, hn⟩
  intro h
  apply hT
  unfold extIntegral
  rw [h, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hn, EReal.top_sub_coe]

lemma ereal_positive_negative_reconstruct (x : EReal) :
    ((x.toENNReal : ENNReal) : EReal) - (((-x).toENNReal : ENNReal) : EReal) = x := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe x =>
    by_cases hx : 0 ≤ x
    · rw [EReal.real_coe_toENNReal, ← EReal.coe_neg, EReal.real_coe_toENNReal,
        ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hx), EReal.coe_ennreal_zero, sub_zero]
      exact EReal.coe_toENNReal (EReal.coe_le_coe_iff.mpr hx)
    · have hx' : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hx)
      rw [EReal.real_coe_toENNReal, ← EReal.coe_neg, EReal.real_coe_toENNReal,
        ENNReal.ofReal_of_nonpos (le_of_not_ge hx), EReal.coe_ennreal_zero, zero_sub]
      rw [← EReal.real_coe_toENNReal, EReal.coe_toENNReal (EReal.coe_le_coe_iff.mpr hx'),
        EReal.coe_neg, neg_neg]

lemma ae_eq_of_extIntegral_eq_finite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (φ ψ : X → EReal) (hφ : AEMeasurable φ μ) (hψ : AEMeasurable ψ μ)
    (hle : φ ≤ᵐ[μ] ψ) (he : extIntegral μ φ = extIntegral μ ψ)
    (hT : extIntegral μ ψ ≠ ⊤) (hB : extIntegral μ ψ ≠ ⊥) : φ =ᵐ[μ] ψ := by
  let A : ENNReal := ∫⁻ x, (φ x).toENNReal ∂μ
  let B : ENNReal := ∫⁻ x, (-φ x).toENNReal ∂μ
  let C : ENNReal := ∫⁻ x, (ψ x).toENNReal ∂μ
  let D : ENNReal := ∫⁻ x, (-ψ x).toENNReal ∂μ
  obtain ⟨hA, hB'⟩ := extIntegral_parts_finite μ φ (he ▸ hT) (he ▸ hB)
  obtain ⟨hC, hD⟩ := extIntegral_parts_finite μ ψ hT hB
  have hp : (fun x ↦ (φ x).toENNReal) ≤ᵐ[μ] (fun x ↦ (ψ x).toENNReal) :=
    hle.mono fun _ h ↦ EReal.toENNReal_le_toENNReal h
  have hn : (fun x ↦ (-ψ x).toENNReal) ≤ᵐ[μ] (fun x ↦ (-φ x).toENNReal) :=
    hle.mono fun _ h ↦ EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr h)
  have hAC : A ≤ C := lintegral_mono_ae hp
  have hDB : D ≤ B := lintegral_mono_ae hn
  have hrAC := (ENNReal.toReal_le_toReal hA hC).mpr hAC
  have hrDB := (ENNReal.toReal_le_toReal hD hB').mpr hDB
  have he' : (A : EReal) - (B : EReal) = (C : EReal) - (D : EReal) := he
  rw [← EReal.coe_ennreal_toReal hA, ← EReal.coe_ennreal_toReal hB',
    ← EReal.coe_ennreal_toReal hC, ← EReal.coe_ennreal_toReal hD,
    ← EReal.coe_sub, ← EReal.coe_sub] at he'
  have hr := EReal.coe_eq_coe_iff.mp he'
  have hCA : C ≤ A := (ENNReal.toReal_le_toReal hC hA).mp (by linarith)
  have hBD : B ≤ D := (ENNReal.toReal_le_toReal hB' hD).mp (by linarith)
  have haePos := ae_eq_of_ae_le_of_lintegral_le hp hA
    (measurable_ereal_toENNReal.comp_aemeasurable hψ) hCA
  have haeNeg := ae_eq_of_ae_le_of_lintegral_le hn hD
    (measurable_ereal_toENNReal.comp_aemeasurable hφ.neg) hBD
  filter_upwards [haePos, haeNeg] with x hx hy
  rw [← ereal_positive_negative_reconstruct (φ x),
    ← ereal_positive_negative_reconstruct (ψ x), hx, hy]

end ModelRiskCodex

/- Source: Solutions/ModelRisk_SlacknessOnlyIf.lean -/
set_option autoImplicit false
namespace ModelRiskCodex
open MeasureTheory ModelRiskOT.Duality Filter

lemma complementary_slackness_only_if {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ)
    (hf : UpperSemicontinuous f) (hfi : Integrable f μ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ π ∈ primalFeasible c μ δ, ∀ lam : ℝ,
      (lam, phiLam c f lam) ∈ dualFeasible c f Set.univ →
      dualObj μ δ lam (phiLam c f lam) ≠ ⊤ →
      (primalObj f π = primalValue c f μ δ ∧
        dualObj μ δ lam (phiLam c f lam) = dualValue c f μ δ ∧
        primalObj f π = dualObj μ δ lam (phiLam c f lam)) →
      ((∀ᵐ p ∂π, ((f p.2 - lam * c p.1 p.2 : ℝ) : EReal) = phiLam c f lam p.1) ∧
        lam * ((∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π).toReal - δ) = 0) := by
  intro π hπ lam hD hJtop hOpt
  let φ := phiLam c f lam
  let F : S × S → EReal := fun p ↦ (f p.2 : EReal)
  let G : S × S → EReal := fun p ↦ φ p.1 + ((lam * c p.1 p.2 : ℝ) : EReal)
  have hfst := hπ.2.1
  have hφmap : AEMeasurable φ (π.map Prod.fst) := by
    rw [hfst]
    exact dualFeasible_aemeasurable μ c f lam φ hD
  have hFm : AEMeasurable F π := (hf.measurable.comp measurable_snd).aemeasurable.coe_real_ereal
  have hGm : AEMeasurable G π := (hφmap.comp_measurable measurable_fst).add
    (measurable_const.mul hc.lsc.measurable).aemeasurable.coe_real_ereal
  have hle : F ≤ᵐ[π] G := Filter.Eventually.of_forall fun p ↦
    hD.2.2 p.1 (Set.mem_univ _) p.2 (Set.mem_univ _)
  have hcover := (dual_cover_integral μ c hc f hfi δ π hπ lam φ hD).2
  have hcostfin : (∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π) ≠ ⊤ :=
    (hπ.2.2.trans_lt (by simp)).ne
  have hmean : (∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π).toReal ≤ δ := by
    have h := (ENNReal.toReal_le_toReal hcostfin ENNReal.ofReal_ne_top).mpr hπ.2.2
    simpa only [ENNReal.toReal_ofReal hδ.le] using h
  have hGJ : extIntegral π G ≤ dualObj μ δ lam φ := by
    rw [hcover]
    have hb : ((lam * (∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π).toReal : ℝ) : EReal) ≤
        ((lam * δ : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left hmean hD.1)
    simpa only [dualObj, add_comm] using add_le_add (le_refl (extIntegral μ φ)) hb
  have hFG : extIntegral π F ≤ extIntegral π G := extIntegral_mono π F G hle
  have hObj : extIntegral π F = dualObj μ δ lam φ := hOpt.2.2
  have hGJeq : extIntegral π G = dualObj μ δ lam φ :=
    le_antisymm hGJ (hObj.symm.le.trans hFG)
  have hFGeq : extIntegral π F = extIntegral π G := hObj.trans hGJeq.symm
  have hJbot : dualObj μ δ lam φ ≠ ⊥ := ne_of_gt
    ((EReal.bot_lt_coe (∫ x, f x ∂μ)).trans_le
      (nominal_le_dualObj μ c hc f hfi δ hδ.le lam φ hD))
  have hGeq : F =ᵐ[π] G := ae_eq_of_extIntegral_eq_finite π F G hFm hGm hle hFGeq
    (by rw [hGJeq]; exact hJtop) (by rw [hGJeq]; exact hJbot)
  refine ⟨?_, ?_⟩
  · filter_upwards [hGeq] with p hp
    have he := congrArg (fun z : EReal ↦ z - ((lam * c p.1 p.2 : ℝ) : EReal)) hp
    change (f p.2 : EReal) - ((lam * c p.1 p.2 : ℝ) : EReal) =
      (φ p.1 + ((lam * c p.1 p.2 : ℝ) : EReal)) - ((lam * c p.1 p.2 : ℝ) : EReal) at he
    rw [EReal.add_sub_cancel_right] at he
    simpa only [← EReal.coe_sub] using he
  · have hφT : extIntegral μ φ ≠ ⊤ :=
      (EReal.add_ne_top_iff_ne_top_right (EReal.coe_ne_bot (lam * δ))
        (EReal.coe_ne_top (lam * δ))).mp hJtop
    have hφB : extIntegral μ φ ≠ ⊥ := (EReal.add_ne_bot_iff.mp hJbot).2
    have hφreal : extIntegral μ φ = ((extIntegral μ φ).toReal : EReal) :=
      (EReal.coe_toReal hφT hφB).symm
    rw [hcover] at hGJeq
    change extIntegral μ φ + ((lam * (∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π).toReal : ℝ) : EReal) =
      ((lam * δ : ℝ) : EReal) + extIntegral μ φ at hGJeq
    rw [hφreal, ← EReal.coe_add, ← EReal.coe_add] at hGJeq
    have hr := EReal.coe_eq_coe_iff.mp hGJeq
    nlinarith

end ModelRiskCodex

/- Source: Solutions/Sol_ModelRiskOT_Duality_theorem_1.lean -/
set_option autoImplicit false
open MeasureTheory ModelRiskOT.Duality

theorem solution {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (hc : AssumptionA1 c)
    (f : S → ℝ) (hf_usc : UpperSemicontinuous f) (hf_int : Integrable f μ)
    (δ : ℝ) (hδ : 0 < δ) :
    primalValue c f μ δ = dualValue c f μ δ ∧
    (∃ lam : ℝ, 0 ≤ lam ∧ (lam, phiLam c f lam) ∈ dualFeasible c f Set.univ ∧
      dualObj μ δ lam (phiLam c f lam) = dualValue c f μ δ) ∧
    (∀ π ∈ primalFeasible c μ δ, ∀ lam : ℝ, (lam, phiLam c f lam) ∈ dualFeasible c f Set.univ →
      ((∀ᵐ p ∂π, ((f p.2 - lam * c p.1 p.2 : ℝ) : EReal) = phiLam c f lam p.1) ∧
        lam * ((∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π).toReal - δ) = 0) →
      (primalObj f π = primalValue c f μ δ ∧
        dualObj μ δ lam (phiLam c f lam) = dualValue c f μ δ ∧
        primalObj f π = dualObj μ δ lam (phiLam c f lam))) ∧
    (∀ π ∈ primalFeasible c μ δ, ∀ lam : ℝ, (lam, phiLam c f lam) ∈ dualFeasible c f Set.univ →
      dualObj μ δ lam (phiLam c f lam) ≠ ⊤ →
      (primalObj f π = primalValue c f μ δ ∧
        dualObj μ δ lam (phiLam c f lam) = dualValue c f μ δ ∧
        primalObj f π = dualObj μ δ lam (phiLam c f lam)) →
      ((∀ᵐ p ∂π, ((f p.2 - lam * c p.1 p.2 : ℝ) : EReal) = phiLam c f lam p.1) ∧
        lam * ((∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π).toReal - δ) = 0)) := by
  obtain ⟨hstrong, hoptimizer⟩ := ModelRiskCodex.strong_duality_optimizer μ c hc f hf_usc hf_int δ hδ
  exact ⟨hstrong, hoptimizer,
    ModelRiskCodex.complementary_slackness_if μ c hc f hf_usc hf_int δ hδ,
    ModelRiskCodex.complementary_slackness_only_if μ c hc f hf_usc hf_int δ hδ⟩


#print axioms solution
