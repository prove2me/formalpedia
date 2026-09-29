-- Prove2me | solution 1 for MeasureTheory.Measure.map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/928ebb3b-cd93-5ac7-9bd4-14d9f9e92f20

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace GramTransport

open Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def ψ {n : ℕ} (e : Fin n → V) : (Fin n → ℝ) →ₗ[ℝ] V := Fintype.linearCombination ℝ e

theorem ψ_apply {n : ℕ} (e : Fin n → V) (a : Fin n → ℝ) : ψ e a = ∑ i, a i • e i := by
  simp [ψ, Fintype.linearCombination_apply]

theorem ψ_coe {n : ℕ} (e : Fin n → V) : (ψ e : (Fin n → ℝ) → V) = fun a => ∑ i, a i • e i := by
  funext a; exact ψ_apply e a

def gram (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e : Fin n → V) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => B (e i) (e j)

theorem ψ_eq_comp {n : ℕ} (e e' : Fin n → V) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ j, e' j = ∑ i, P i j • e i) : ψ e' = ψ e ∘ₗ Matrix.toLin' P := by
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, Matrix.toLin'_apply, ψ_apply, ψ_apply]
  simp_rw [hP, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem gram_eq_of_comp (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e e' : Fin n → V) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ j, e' j = ∑ i, P i j • e i) : gram B e' = Pᵀ * gram B e * P := by
  ext j k
  simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [hP j, hP k]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun l _ => ?_
  ring

def G (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e : Fin n → V) : ENNReal := ENNReal.ofReal (Real.sqrt |(gram B e).det|)

theorem G_eq_of_comp (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e e' : Fin n → V) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ j, e' j = ∑ i, P i j • e i) : G B e' = ENNReal.ofReal |P.det| * G B e := by
  rw [G, G, gram_eq_of_comp B e e' P hP, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show P.det * (gram B e).det * P.det = P.det ^ 2 * (gram B e).det by ring, abs_mul, abs_pow,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (abs_nonneg _), ENNReal.ofReal_mul (abs_nonneg _)]

section Topology

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem continuous_ψ {n : ℕ} (e : Fin n → V) : Continuous (ψ e) := by
  rw [ψ_coe]
  exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const

theorem measurable_ψ {n : ℕ} (e : Fin n → V) : Measurable (ψ e) := (continuous_ψ e).measurable

theorem G_smul_map_eq_of_comp (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n : ℕ} (e e' : Fin n → V) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ j, e' j = ∑ i, P i j • e i) (hdet : P.det ≠ 0) :
    G B e' • Measure.map (ψ e') volume = G B e • Measure.map (ψ e) volume := by
  classical
  rw [ψ_eq_comp e e' P hP, LinearMap.coe_comp, ← Measure.map_map (measurable_ψ e) (Matrix.toLin' P |>.continuous_of_finiteDimensional).measurable,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, Measure.map_smul, smul_smul]
  congr 1
  rw [G_eq_of_comp B e e' P hP, mul_assoc, mul_comm (G B e), ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _),
    abs_inv, mul_inv_cancel₀ (abs_ne_zero.2 hdet), ENNReal.ofReal_one, one_mul]

end Topology

theorem withDensity_map_of_measurableEmbedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) (μ : Measure α) (g : β → ENNReal) :
    (Measure.map f μ).withDensity g = Measure.map f (μ.withDensity (g ∘ f)) := by
  ext s hs
  rw [withDensity_apply _ hs, hf.restrict_map, hf.lintegral_map, hf.map_apply,
    withDensity_apply _ (hf.measurable hs)]
  simp only [Function.comp_apply]

end GramTransport

end

open GramTransport in
theorem solution
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Φ : V ≃ₗ[ℝ] V) (hΦ : ∀ x y : V, B (Φ x) (Φ y) = B x y)
    {n₁ n₂ : ℕ} (e₁ : Fin n₁ → V) (e₂ : Fin n₂ → V)
    (h₁ : LinearIndependent ℝ e₁) (h₂ : LinearIndependent ℝ e₂)
    (hspan : (Submodule.span ℝ (Set.range e₂)).map (Φ : V →ₗ[ℝ] V) = Submodule.span ℝ (Set.range e₁))
    (ρ : V → ENNReal) (hρm : Measurable ρ) (hρ : ∀ x : V, ρ (Φ x) = ρ x) :
    Measure.map Φ
        (((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ => B (e₂ i) (e₂ j)).det|)) •
            Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity ρ) =
      ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ => B (e₁ i) (e₁ j)).det|)) •
          Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity ρ := by
  classical

  have hn : n₁ = n₂ := by
    have h2' : Module.finrank ℝ (Submodule.span ℝ (Set.range e₂)) = n₂ := by
      rw [finrank_span_eq_card h₂, Fintype.card_fin]
    have h1' : Module.finrank ℝ (Submodule.span ℝ (Set.range e₁)) = n₁ := by
      rw [finrank_span_eq_card h₁, Fintype.card_fin]
    have := LinearEquiv.finrank_map_eq Φ (Submodule.span ℝ (Set.range e₂))
    rw [hspan, h1', h2'] at this
    exact this
  subst hn

  set f : Fin n₁ → V := fun i => Φ (e₂ i) with hf
  have hfli : LinearIndependent ℝ f := by
    have := h₂.map' (Φ : V →ₗ[ℝ] V) (LinearMap.ker_eq_bot.2 Φ.injective)
    exact this
  have hfspan : Submodule.span ℝ (Set.range f) = Submodule.span ℝ (Set.range e₁) := by
    rw [← hspan, Submodule.map_span]
    congr 1
    ext v
    simp [hf, Set.mem_range, Set.mem_image]

  set W : Submodule ℝ V := Submodule.span ℝ (Set.range e₁) with hW
  set b₁ : Module.Basis (Fin n₁) ℝ W := Module.Basis.span h₁ with hb₁
  have hfmem : ∀ j, f j ∈ W := fun j => by
    rw [← hfspan]; exact Submodule.subset_span (Set.mem_range_self j)
  set P : Matrix (Fin n₁) (Fin n₁) ℝ := fun i j => b₁.repr ⟨f j, hfmem j⟩ i with hP
  have hPf : ∀ j, f j = ∑ i, P i j • e₁ i := by
    intro j
    have h := b₁.sum_repr ⟨f j, hfmem j⟩
    have h' := congrArg (fun w : W => (w : V)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    rw [← h']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb₁, Module.Basis.coe_span_apply]

  have hψf : Function.Injective (ψ f) :=
    (linearIndependent_iff_injective_fintypeLinearCombination).1 hfli
  have hdet : P.det ≠ 0 := by
    have hinj : Function.Injective P.mulVec := by
      intro a b hab
      apply hψf
      have := ψ_eq_comp e₁ f P hPf
      rw [this, LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, hab]
    have hu : IsUnit P := Matrix.mulVec_injective_iff_isUnit.1 hinj
    exact ((Matrix.isUnit_iff_isUnit_det P).1 hu).ne_zero

  have hGf : G B f = G B e₂ := by
    simp only [G, gram, hf, hΦ]
  have hψΦ : (Φ : V → V) ∘ (fun a : Fin n₁ → ℝ => ∑ i, a i • e₂ i) = ψ f := by
    funext a
    rw [ψ_coe]
    simp only [Function.comp_apply, map_sum, map_smul, hf]
  have hΦemb : MeasurableEmbedding (Φ : V → V) :=
    (Φ.toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
  have hΦmeas : Measurable (Φ : V → V) := hΦemb.measurable
  have hρΦ : ρ ∘ (Φ : V → V) = ρ := funext hρ

  have key : G B f • Measure.map (ψ f) volume = G B e₁ • Measure.map (ψ e₁) volume :=
    G_smul_map_eq_of_comp B e₁ f P hPf hdet
  rw [show (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) = (ψ e₁ : (Fin n₁ → ℝ) → V) from (ψ_coe e₁).symm]
  change Measure.map Φ ((G B e₂ • Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₂ i) volume).withDensity ρ) =
    (G B e₁ • Measure.map (ψ e₁) volume).withDensity ρ
  rw [← key, withDensity_smul_measure, withDensity_smul_measure, Measure.map_smul, ← hGf]
  congr 1
  have hm2 : Measurable (fun a : Fin n₁ → ℝ => ∑ i, a i • e₂ i) := by rw [← ψ_coe]; exact measurable_ψ e₂
  calc Measure.map Φ ((Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₂ i) volume).withDensity ρ)
      = Measure.map Φ ((Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₂ i) volume).withDensity (ρ ∘ Φ)) := by
        rw [hρΦ]
    _ = (Measure.map Φ (Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₂ i) volume)).withDensity ρ :=
        (withDensity_map_of_measurableEmbedding hΦemb _ ρ).symm
    _ = (Measure.map (ψ f) volume).withDensity ρ := by rw [Measure.map_map hΦmeas hm2, hψΦ]

end S_MeasureTheory_Measure_map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq
end P2MW
export P2MW.S_MeasureTheory_Measure_map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq (solution)
