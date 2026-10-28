-- Prove2me | solution 1 for MomentProblem.exists_dual_of_slater
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T05:16:52.647992+00:00
-- url     : https://prove2.me/submissions/34335d2b-b816-4828-8b92-387523efd857

import Mathlib
import Theorems.Thm_Lagrange_exists_multiplier

-- carved verbatim out of submission 3c55ced4-4944-4de2-ba43-8110d2682db1, lines 3556-3637

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma aux1_linear_pi {α : Type*} [Fintype α] [DecidableEq α] (L : (α → ℝ) →ₗ[ℝ] ℝ) (p : α → ℝ) :
    L p = ∑ i, p i * L (Pi.single i 1) := by
  rw [LinearMap.pi_apply_eq_sum_univ L p]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

end

section
open MeasureTheory Matrix
open scoped ENNReal

theorem aux_integrable_mix {X : Type*} [MeasurableSpace X] {μ₁ μ₂ : Measure X} {h : X → ℝ}
    (h1 : Integrable h μ₁) (h2 : Integrable h μ₂) (t : ℝ) :
    Integrable h (ENNReal.ofReal t • μ₁ + ENNReal.ofReal (1 - t) • μ₂) :=
  (h1.smul_measure ENNReal.ofReal_ne_top).add_measure (h2.smul_measure ENNReal.ofReal_ne_top)

theorem aux_integral_mix {X : Type*} [MeasurableSpace X] {μ₁ μ₂ : Measure X} {h : X → ℝ}
    (h1 : Integrable h μ₁) (h2 : Integrable h μ₂) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ x, h x ∂(ENNReal.ofReal t • μ₁ + ENNReal.ofReal (1 - t) • μ₂) =
      t * ∫ x, h x ∂μ₁ + (1 - t) * ∫ x, h x ∂μ₂ := by
  rw [integral_add_measure (h1.smul_measure ENNReal.ofReal_ne_top)
    (h2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal ht0, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

theorem aux_isFinite_dirac {X : Type*} [MeasurableSpace X] (t : ℝ) (x : X) :
    IsFiniteMeasure (ENNReal.ofReal t • Measure.dirac x) := by
  constructor
  simp only [Measure.coe_smul, Pi.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.ofReal_lt_top

theorem aux_isFinite_mix {X : Type*} [MeasurableSpace X] {μ₁ μ₂ : Measure X}
    (h1 : IsFiniteMeasure μ₁) (h2 : IsFiniteMeasure μ₂) (t : ℝ) :
    IsFiniteMeasure (ENNReal.ofReal t • μ₁ + ENNReal.ofReal (1 - t) • μ₂) := by
  constructor
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

theorem aux_lin_nonpos {α c s : ℝ} (h : ∀ R : ℝ, 0 ≤ R → α + R * c ≤ s) : c ≤ 0 := by
  by_contra hc
  push Not at hc
  have h1 := h ((|s - α| + 1) / c) (by positivity)
  rw [div_mul_cancel₀ _ hc.ne'] at h1
  linarith [le_abs_self (s - α)]

end

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem Module.Dual.exists_dotProduct_eq {n : Type*} [Fintype n] [DecidableEq n]
    (φ : Module.Dual ℝ (n → ℝ)) : ∃ u : n → ℝ, ∀ v, φ v = u ⬝ᵥ v := by
  refine ⟨fun i => φ (Pi.single i 1), fun v => ?_⟩
  rw [aux1_linear_pi φ v, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end

section
open MeasureTheory Matrix
open scoped ENNReal

theorem solution {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]
    (T : Set X) (hT : MeasurableSet T) (φ : X → ι → ℝ) (hφ : ∀ i, Measurable fun x => φ x i)
    (g : X → ℝ) (hg : Measurable g) (B : Set (ι → ℝ)) (hB : Convex ℝ B) (p : ℝ)
    (hp : ∀ μ : Measure X, IsFiniteMeasure μ → μ Tᶜ = 0 →
      (∀ i, Integrable (fun x => φ x i) μ) → Integrable g μ →
      (fun i => ∫ x, φ x i ∂μ) ∈ B → ∫ x, g x ∂μ ≤ p)
    (hslater : (0 : ι → ℝ) ∈ interior {u | ∃ μ : Measure X, IsFiniteMeasure μ ∧ μ Tᶜ = 0 ∧
      (∀ i, Integrable (fun x => φ x i) μ) ∧ Integrable g μ ∧
      ∃ s ∈ B, (fun i => ∫ x, φ x i ∂μ) - s = u}) :
    ∃ η : ι → ℝ, (∀ x ∈ T, g x ≤ η ⬝ᵥ φ x) ∧ ∀ s ∈ B, η ⬝ᵥ s ≤ p := by
  classical
  let S : Set (Measure X × (ι → ℝ)) := {z | IsFiniteMeasure z.1 ∧ z.1 Tᶜ = 0 ∧
      (∀ i, Integrable (fun x => φ x i) z.1) ∧ Integrable g z.1 ∧ z.2 ∈ B}
  let f : Measure X × (ι → ℝ) → ℝ := fun z => ∫ x, g x ∂z.1
  let G : Measure X × (ι → ℝ) → (ι → ℝ) := fun z => (fun i => ∫ x, φ x i ∂z.1) - z.2
  have hcvx : ∀ z₁ ∈ S, ∀ z₂ ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ z ∈ S,
      G z - (t • G z₁ + (1 - t) • G z₂) ∈ (⊥ : PointedCone ℝ (ι → ℝ)) ∧
        t * f z₁ + (1 - t) * f z₂ ≤ f z := by
    rintro ⟨μ₁, s₁⟩ ⟨hf1, hT1, hφ1, hg1, hs1⟩ ⟨μ₂, s₂⟩ ⟨hf2, hT2, hφ2, hg2, hs2⟩ t ht0 ht1
    refine ⟨(ENNReal.ofReal t • μ₁ + ENNReal.ofReal (1 - t) • μ₂, t • s₁ + (1 - t) • s₂),
      ⟨aux_isFinite_mix hf1 hf2 t, ?_, fun i => aux_integrable_mix (hφ1 i) (hφ2 i) t,
        aux_integrable_mix hg1 hg2 t, hB hs1 hs2 ht0 (by linarith) (by ring)⟩, ?_, ?_⟩
    · simp [hT1, hT2]
    · rw [Submodule.mem_bot]
      funext i
      simp only [G, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [aux_integral_mix (hφ1 i) (hφ2 i) ht0 ht1]
      ring
    · simp only [f]
      rw [aux_integral_mix hg1 hg2 ht0 ht1]
  have hset : {u | ∃ z ∈ S, G z - u ∈ (⊥ : PointedCone ℝ (ι → ℝ))} =
      {u | ∃ μ : Measure X, IsFiniteMeasure μ ∧ μ Tᶜ = 0 ∧
        (∀ i, Integrable (fun x => φ x i) μ) ∧ Integrable g μ ∧
        ∃ s ∈ B, (fun i => ∫ x, φ x i ∂μ) - s = u} := by
    ext u
    simp only [Set.mem_setOf_eq, Submodule.mem_bot, sub_eq_zero]
    constructor
    · rintro ⟨⟨μ, s⟩, ⟨h1, h2, h3, h4, h5⟩, h⟩
      exact ⟨μ, h1, h2, h3, h4, s, h5, h⟩
    · rintro ⟨μ, h1, h2, h3, h4, s, h5, h⟩
      exact ⟨⟨μ, s⟩, ⟨h1, h2, h3, h4, h5⟩, h⟩
  have hp' : ∀ z ∈ S, G z ∈ (⊥ : PointedCone ℝ (ι → ℝ)) → f z ≤ p := by
    rintro ⟨μ, s⟩ ⟨h1, h2, h3, h4, h5⟩ hG
    rw [Submodule.mem_bot, sub_eq_zero] at hG
    exact hp μ h1 h2 h3 h4 (by simp only at hG; rw [hG]; exact h5)
  obtain ⟨y, -, hy⟩ := Lagrange.exists_multiplier S f G ⊥ hcvx (hset ▸ hslater) p hp'
  obtain ⟨η', hη'⟩ := Module.Dual.exists_dotProduct_eq y
  obtain ⟨μ₀, -, -, -, -, s₀, hs₀, -⟩ := interior_subset hslater
  refine ⟨-η', fun x hx => ?_, fun s hs => ?_⟩
  · have key : ∀ R : ℝ, 0 ≤ R → -(η' ⬝ᵥ s₀) + R * (g x + η' ⬝ᵥ φ x) ≤ p := by
      intro R hR
      have hT0 : (ENNReal.ofReal R • Measure.dirac x) Tᶜ = 0 := by
        simp [Measure.dirac_apply' _ hT.compl, hx]
      have hint : ∀ h : X → ℝ, Measurable h → Integrable h (ENNReal.ofReal R • Measure.dirac x) :=
        fun h hh => (integrable_dirac' hh.stronglyMeasurable enorm_lt_top).smul_measure
          ENNReal.ofReal_ne_top
      have hval : ∀ h : X → ℝ, Measurable h →
          ∫ x', h x' ∂(ENNReal.ofReal R • Measure.dirac x) = R * h x := by
        intro h hh
        rw [integral_smul_measure, integral_dirac' _ _ hh.stronglyMeasurable,
          ENNReal.toReal_ofReal hR, smul_eq_mul]
      have hz : (ENNReal.ofReal R • Measure.dirac x, s₀) ∈ S :=
        ⟨aux_isFinite_dirac R x, hT0, fun i => hint _ (hφ i), hint g hg, hs₀⟩
      have h1 := hy _ hz
      simp only [f, G, hη'] at h1
      rw [hval g hg] at h1
      have e : (fun i => ∫ x', φ x' i ∂(ENNReal.ofReal R • Measure.dirac x)) = R • φ x := by
        funext i; rw [hval _ (hφ i)]; rfl
      rw [e, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h1
      linarith
    have := aux_lin_nonpos key
    rw [neg_dotProduct]
    linarith
  · have hz : ((0 : Measure X), s) ∈ S :=
      ⟨inferInstance, by simp, fun i => integrable_zero_measure, integrable_zero_measure, hs⟩
    have h1 := hy _ hz
    simp only [f, G, hη', integral_zero_measure] at h1
    rw [neg_dotProduct]
    have e : (fun _ : ι => (0 : ℝ)) - s = -s := by funext i; simp
    rw [e, dotProduct_neg] at h1
    linarith

end
