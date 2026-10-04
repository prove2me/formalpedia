-- Prove2me | solution 1 for NumStochOpt.Bounds.eq_2_32_2_34_edmundson_madansky_one_dim
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T20:43:45.959117+00:00
-- url     : https://prove2.me/submissions/8488c786-a037-44c6-a403-10e04ca2c283

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_EdmundsonMadansky

set_option autoImplicit false

open MeasureTheory

namespace EMda547d52

lemma chord {a b : ℝ} (hab : a < b) {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Set.Icc a b) φ)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    φ x ≤ (b - x) / (b - a) * φ a + (x - a) / (b - a) * φ b := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have h1 : 0 ≤ (b - x) / (b - a) := div_nonneg (by linarith [hx.2]) hba.le
  have h2 : 0 ≤ (x - a) / (b - a) := div_nonneg (by linarith [hx.1]) hba.le
  have h3 : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp; ring
  have key := hφ.2 ha hb h1 h2 h3
  have hxe : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
    field_simp; ring
  simp only [smul_eq_mul] at key
  rw [hxe] at key
  exact key

lemma chord_le_abs {a b : ℝ} (hab : a < b) {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Set.Icc a b) φ)
    {x : ℝ} (hx : x ∈ Set.Icc a b) : φ x ≤ |φ a| + |φ b| := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have h1 : 0 ≤ (b - x) / (b - a) := div_nonneg (by linarith [hx.2]) hba.le
  have h2 : 0 ≤ (x - a) / (b - a) := div_nonneg (by linarith [hx.1]) hba.le
  have h3 : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp; ring
  have e1 : (b - x) / (b - a) * φ a ≤ (b - x) / (b - a) * |φ a| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) h1
  have e2 : (x - a) / (b - a) * φ b ≤ (x - a) / (b - a) * |φ b| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) h2
  have e3 : (b - x) / (b - a) ≤ 1 := by linarith
  have e4 : (x - a) / (b - a) ≤ 1 := by linarith
  have e5 : (b - x) / (b - a) * |φ a| ≤ |φ a| := by
    have := mul_le_mul_of_nonneg_right e3 (abs_nonneg (φ a)); linarith
  have e6 : (x - a) / (b - a) * |φ b| ≤ |φ b| := by
    have := mul_le_mul_of_nonneg_right e4 (abs_nonneg (φ b)); linarith
  linarith [chord hab hφ hx]

lemma abs_bound {a b : ℝ} (hab : a < b) {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Set.Icc a b) φ)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |φ x| ≤ 2 * |φ ((a + b) / 2)| + 2 * (|φ a| + |φ b|) := by
  have hy : a + b - x ∈ Set.Icc a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hup := chord_le_abs hab hφ hx
  have hup' := chord_le_abs hab hφ hy
  have key := hφ.2 hx hy (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  have hm : (1/2 : ℝ) • x + (1/2 : ℝ) • (a + b - x) = (a + b) / 2 := by
    simp only [smul_eq_mul]; ring
  rw [hm] at key
  simp only [smul_eq_mul] at key
  have hmabs := neg_abs_le (φ ((a + b) / 2))
  rw [abs_le]
  constructor
  · nlinarith [abs_nonneg (φ a), abs_nonneg (φ b)]
  · nlinarith [abs_nonneg (φ a), abs_nonneg (φ b), abs_nonneg (φ ((a + b) / 2))]

/-- A measurable function agreeing with `φ` on `[a, b]`. -/
lemma exists_measurable_eqOn {a b : ℝ} (hab : a < b) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ (Set.Icc a b) φ) :
    ∃ g : ℝ → ℝ, Measurable g ∧ Set.EqOn g φ (Set.Icc a b) := by
  classical
  have hc : ContinuousOn φ (Set.Ioo a b) := by
    have := hφ.continuousOn_interior
    rwa [interior_Icc] at this
  let ψ : ℝ → ℝ := (Set.Ioo a b).piecewise φ (fun _ => 0)
  have hψ : Measurable ψ :=
    ContinuousOn.measurable_piecewise hc continuousOn_const measurableSet_Ioo
  let h : ℝ → ℝ := fun x => if x = a then φ a else if x = b then φ b else 0
  have hh : Measurable h :=
    Measurable.ite (measurableSet_singleton a) measurable_const
      (Measurable.ite (measurableSet_singleton b) measurable_const measurable_const)
  refine ⟨fun x => ψ x + h x, hψ.add hh, ?_⟩
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hxa | hax
  · subst hxa
    have : a ∉ Set.Ioo a b := fun h' => lt_irrefl _ h'.1
    simp [ψ, h, this]
  rcases eq_or_lt_of_le hx.2 with hxb | hxb
  · subst hxb
    have : x ∉ Set.Ioo a x := fun h' => lt_irrefl _ h'.2
    simp [ψ, h, this, hax.ne']
  · have : x ∈ Set.Ioo a b := ⟨hax, hxb⟩
    simp [ψ, h, this, hax.ne', hxb.ne]

end EMda547d52

open MeasureTheory NumStochOpt.Bounds in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : Ω → ℝ) (hξ : AEMeasurable ξ P)
    (a b : ℝ) (hab : a < b) (hsupp : ∀ᵐ ω ∂P, ξ ω ∈ Set.Icc a b)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Set.Icc a b) φ) :
    ∫ ω, φ (ξ ω) ∂P ≤
      emProb a b (∫ ω, ξ ω ∂P) false * φ a + emProb a b (∫ ω, ξ ω ∂P) true * φ b := by
  have hba : 0 < b - a := sub_pos.mpr hab
  obtain ⟨g, hg, hgφ⟩ := EMda547d52.exists_measurable_eqOn hab hφ
  have hmeas : AEStronglyMeasurable (fun ω => φ (ξ ω)) P := by
    refine (hg.comp_aemeasurable hξ).aestronglyMeasurable.congr ?_
    filter_upwards [hsupp] with ω hω
    exact hgφ hω
  have hint : Integrable (fun ω => φ (ξ ω)) P := by
    refine Integrable.of_bound hmeas (2 * |φ ((a + b) / 2)| + 2 * (|φ a| + |φ b|)) ?_
    filter_upwards [hsupp] with ω hω
    rw [Real.norm_eq_abs]
    exact EMda547d52.abs_bound hab hφ hω
  have hξint : Integrable ξ P := by
    refine Integrable.of_bound hξ.aestronglyMeasurable (|a| + |b|) ?_
    filter_upwards [hsupp] with ω hω
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le a, abs_nonneg b, hω.1]
    · linarith [le_abs_self b, abs_nonneg a, hω.2]
  set α : ℝ := (b * φ a - a * φ b) / (b - a)
  set β : ℝ := (φ b - φ a) / (b - a)
  have hle : ∀ᵐ ω ∂P, φ (ξ ω) ≤ α + β * ξ ω := by
    filter_upwards [hsupp] with ω hω
    have := EMda547d52.chord hab hφ hω
    have e : (b - ξ ω) / (b - a) * φ a + (ξ ω - a) / (b - a) * φ b = α + β * ξ ω := by
      simp only [α, β]; field_simp; ring
    linarith
  have hRint : Integrable (fun ω => α + β * ξ ω) P :=
    (integrable_const α).add (hξint.const_mul β)
  have h1 := integral_mono_ae hint hRint hle
  have h2 : ∫ ω, (α + β * ξ ω) ∂P = α + β * ∫ ω, ξ ω ∂P := by
    rw [integral_add (integrable_const α) (hξint.const_mul β), integral_const,
      integral_const_mul]
    simp
  rw [h2] at h1
  refine h1.trans (le_of_eq ?_)
  simp only [emProb, α, β, if_true, if_false, Bool.false_eq_true]
  field_simp
  ring
