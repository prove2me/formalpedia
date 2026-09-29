-- Prove2me | solution 1 for MeasureTheory.Measure.exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/be1059c8-cdb3-5909-943a-4b65a4bed0d8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "MeasureTheory P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq.MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter Function"
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace MeasureTheory
p2m_export "MeasureTheory" "lintegral_zero_measure Measure MeasurePreserving setLIntegral_mono Measure.restrict_smul lintegral_congr measure_lt_top measurePreserving_piFinSuccAbove Measure.measure_prod_null Measure.comap measure_union_null_iff lintegral_eq_zero_iff measure_union_null Measure.restrict_eq_self_of_ae_mem Measure.map Measure.map_apply measure_preimage_mul Measure.addHaar_image_linearMap withDensity_apply Measure.map_linearMap_addHaar_eq_smul_addHaar Measure.prod_swap measure_biUnion_null_iff measure_mono_null map_mul_left_eq_self lintegral_smul_measure Measure.restrict_univ setLIntegral_const ae_iff lintegral_const_mul' measure_empty Measure.restrict_eq_zero extend setLIntegral_map measure_diff_null"
namespace UnitGroupHaar
p2m_open "MeasureTheory"

section Algebra

variable {M : Type*} [Ring M] [Algebra ℝ M] [FiniteDimensional ℝ M]

theorem isUnit_of_isUnit_lmul {x : M} (h : IsUnit (Algebra.lmul ℝ M x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h

  set T : M →ₗ[ℝ] M := ((u⁻¹ : (M →ₗ[ℝ] M)ˣ) : M →ₗ[ℝ] M) with hT
  have hTL : ∀ y, T (x * y) = y := by
    intro y
    have h1 := congrArg (fun f : (M →ₗ[ℝ] M)ˣ => (f : M →ₗ[ℝ] M) y) (inv_mul_cancel u)
    simp only [Units.val_mul, Units.val_one, Module.End.mul_apply, Module.End.one_apply, hu] at h1

    have h2 : (Algebra.lmul ℝ M x) y = x * y := rfl
    rw [h2] at h1
    exact h1
  have hLT : ∀ y, x * T y = y := by
    intro y
    have h1 := congrArg (fun f : (M →ₗ[ℝ] M)ˣ => (f : M →ₗ[ℝ] M) y) (mul_inv_cancel u)
    simp only [Units.val_mul, Units.val_one, Module.End.mul_apply, Module.End.one_apply, hu] at h1
    have h2 : ∀ z, (Algebra.lmul ℝ M x) z = x * z := fun z => rfl
    rw [h2] at h1
    exact h1
  have hright : ∀ y z, T (y * z) = T y * z := by
    intro y z
    have h1 : x * (T y * z) = y * z := by rw [← mul_assoc, hLT]
    calc T (y * z) = T (x * (T y * z)) := by rw [h1]
      _ = T y * z := hTL _
  refine ⟨⟨x, T 1, hLT 1, ?_⟩, rfl⟩
  calc T 1 * x = T (1 * x) := (hright 1 x).symm
    _ = T (x * 1) := by rw [one_mul, mul_one]
    _ = 1 := hTL 1

theorem isUnit_iff_norm_ne_zero (x : M) : IsUnit x ↔ Algebra.norm ℝ x ≠ 0 := by
  constructor
  · intro hx h0
    have := (Algebra.norm ℝ (S := M)).map_mul x
    obtain ⟨u, rfl⟩ := hx
    have h1 : Algebra.norm ℝ ((u : M) * (u⁻¹ : Mˣ)) = 1 := by rw [Units.mul_inv, map_one]
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro h
    have h' : IsUnit (LinearMap.det (Algebra.lmul ℝ M x)) := by
      rw [← Algebra.norm_apply]; exact isUnit_iff_ne_zero.2 h
    exact isUnit_of_isUnit_lmul ((LinearMap.isUnit_iff_isUnit_det _).2 h')

theorem finite_setOf_not_isUnit_add (Y : M) : {t : ℝ | ¬ IsUnit (t • (1 : M) + Y)}.Finite := by
  have hfin : (spectrum ℝ (Algebra.lmul ℝ M (-Y))).Finite := Module.End.finite_spectrum _
  refine hfin.subset fun t ht => ?_
  rw [Set.mem_setOf_eq] at ht
  rw [spectrum.mem_iff]
  intro hu
  apply ht
  have : (algebraMap ℝ (Module.End ℝ M) t - Algebra.lmul ℝ M (-Y)) = Algebra.lmul ℝ M (t • (1 : M) + Y) := by
    rw [map_add, map_neg, sub_neg_eq_add, map_smul, map_one, Algebra.algebraMap_eq_smul_one]
  rw [this] at hu
  exact isUnit_of_isUnit_lmul hu

variable [TopologicalSpace M] [IsTopologicalRing M] [ContinuousSMul ℝ M] [T2Space M]

def coordHomeo {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ M) : M ≃ₜ (ι → ℝ) where
  toEquiv := b.equivFun.toEquiv
  continuous_toFun := b.equivFun.toLinearMap.continuous_of_finiteDimensional
  continuous_invFun := b.equivFun.symm.toLinearMap.continuous_of_finiteDimensional

scoped instance (priority := 100) secondCountable_of_finiteDimensional : SecondCountableTopology M :=
  (coordHomeo (Module.finBasis ℝ M)).secondCountableTopology

theorem polishSpace_of_finiteDimensional : PolishSpace M :=
  (coordHomeo (Module.finBasis ℝ M)).isClosedEmbedding.polishSpace

theorem continuous_norm : Continuous (Algebra.norm ℝ : M → ℝ) := by
  classical
  set b := Module.finBasis ℝ M
  have h : (Algebra.norm ℝ : M → ℝ) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h]
  have hc : Continuous fun x : M => Algebra.leftMulMatrix b x :=
    (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional
  exact hc.matrix_det

theorem isClosed_setOf_not_isUnit : IsClosed {x : M | ¬ IsUnit x} := by
  have : {x : M | ¬ IsUnit x} = (Algebra.norm ℝ : M → ℝ) ⁻¹' {0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, isUnit_iff_norm_ne_zero, not_not]
  rw [this]
  exact isClosed_singleton.preimage continuous_norm

end Algebra

section Setting

variable {M : Type*} [Ring M] [Algebra ℝ M] [FiniteDimensional ℝ M]
  [TopologicalSpace M] [IsTopologicalRing M] [ContinuousSMul ℝ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]
  (A : Subalgebra ℝ M) (Γ : Subgroup Mˣ) (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A)
  {n : ℕ} (e : Fin n → M) (hli : LinearIndependent ℝ e)
  (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A)

def ψ : (Fin n → ℝ) →ₗ[ℝ] M := Fintype.linearCombination ℝ e

theorem ψ_apply (c : Fin n → ℝ) : ψ e c = ∑ i, c i • e i := rfl

theorem continuous_ψ : Continuous (ψ e) := by
  have : (ψ e : (Fin n → ℝ) → M) = fun c => ∑ i, c i • e i := funext (ψ_apply e)
  rw [this]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

theorem measurable_ψ : Measurable (ψ e) := (continuous_ψ e).measurable

include hli in
theorem injective_ψ : Function.Injective (ψ e) := hli.fintypeLinearCombination_injective

include hsp in
theorem range_ψ : Set.range (ψ e) = (A : Set M) := by
  have h := Fintype.range_linearCombination ℝ e
  have h' : (LinearMap.range (ψ e) : Set M) = (Submodule.span ℝ (Set.range e) : Set M) := by
    rw [ψ, h]
  rw [LinearMap.coe_range] at h'
  rw [h', hsp]
  rfl

include hsp in
theorem ψ_mem (c : Fin n → ℝ) : ψ e c ∈ A := by
  have : ψ e c ∈ Set.range (ψ e) := ⟨c, rfl⟩
  rw [range_ψ A e hsp] at this
  exact this

include hsp in
theorem mem_e (i : Fin n) : e i ∈ A := by
  have : e i ∈ (Submodule.span ℝ (Set.range e) : Set M) := Submodule.subset_span ⟨i, rfl⟩
  rw [hsp] at this
  exact this

def bA : Module.Basis (Fin n) ℝ A :=
  Module.Basis.mk (v := fun i => (⟨e i, mem_e A e hsp i⟩ : A))
    (by
      have : (A.val.toLinearMap) ∘ (fun i => (⟨e i, mem_e A e hsp i⟩ : A)) = e := by
        funext i; rfl
      refine LinearIndependent.of_comp A.val.toLinearMap ?_
      rw [this]; exact hli)
    (by
      rintro ⟨x, hx⟩ -
      have hx' : x ∈ (Submodule.span ℝ (Set.range e) : Set M) := by rw [hsp]; exact hx
      obtain ⟨c, rfl⟩ : x ∈ Set.range (ψ e) := by rw [range_ψ A e hsp]; exact hx
      have : (⟨ψ e c, hx⟩ : A) = ∑ i, c i • (⟨e i, mem_e A e hsp i⟩ : A) := by
        apply Subtype.ext
        simp only [ψ_apply]
        rw [show ((∑ i, c i • (⟨e i, mem_e A e hsp i⟩ : A) : A) : M) = ∑ i, ((c i • (⟨e i, mem_e A e hsp i⟩ : A) : A) : M)
          from AddSubmonoidClass.coe_finset_sum _ _]
        rfl
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem bA_apply (i : Fin n) : ((bA A e hli hsp i : A) : M) = e i := by
  rw [bA, Module.Basis.mk_apply]

theorem coe_equivFun_symm (c : Fin n → ℝ) : (((bA A e hli hsp).equivFun.symm c : A) : M) = ψ e c := by
  rw [Module.Basis.equivFun_symm_apply, ψ_apply, AddSubmonoidClass.coe_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subalgebra.coe_smul, bA_apply]

theorem equivFun_ψ (c : Fin n → ℝ) : (bA A e hli hsp).equivFun ⟨ψ e c, ψ_mem A e hsp c⟩ = c := by
  have : (⟨ψ e c, ψ_mem A e hsp c⟩ : A) = (bA A e hli hsp).equivFun.symm c :=
    Subtype.ext (coe_equivFun_symm A e hli hsp c).symm
  rw [this, LinearEquiv.apply_symm_apply]

theorem ψ_mulVec_of_left {g : M} {P : Matrix (Fin n) (Fin n) ℝ} (hP : ∀ j, g * e j = ∑ i, P i j • e i)
    (c : Fin n → ℝ) : ψ e (Matrix.mulVec P c) = g * ψ e c := by
  simp only [ψ_apply, Matrix.mulVec, dotProduct]
  calc ∑ i, (∑ j, P i j * c j) • e i = ∑ j, c j • ∑ i, P i j • e i := by
        simp only [Finset.sum_smul, Finset.smul_sum, smul_smul, mul_comm (c _)]
        rw [Finset.sum_comm]
    _ = ∑ j, c j • (g * e j) := by simp only [hP]
    _ = g * ∑ j, c j • e j := by simp only [Finset.mul_sum, mul_smul_comm]

theorem ψ_mulVec_of_right {g : M} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : ∀ j, e j * g = ∑ i, Q i j • e i)
    (c : Fin n → ℝ) : ψ e (Matrix.mulVec Q c) = ψ e c * g := by
  simp only [ψ_apply, Matrix.mulVec, dotProduct]
  calc ∑ i, (∑ j, Q i j * c j) • e i = ∑ j, c j • ∑ i, Q i j • e i := by
        simp only [Finset.sum_smul, Finset.smul_sum, smul_smul, mul_comm (c _)]
        rw [Finset.sum_comm]
    _ = ∑ j, c j • (e j * g) := by simp only [hQ]
    _ = (∑ j, c j • e j) * g := by simp only [Finset.sum_mul, smul_mul_assoc]

end Setting

section Invariance

variable {M : Type*} [Ring M] [Algebra ℝ M] [FiniteDimensional ℝ M]
  [TopologicalSpace M] [IsTopologicalRing M] [ContinuousSMul ℝ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]
  {n : ℕ} (e : Fin n → M) (χ : M →* ℝ)

def dens : M → ℝ≥0∞ := fun x => (ENNReal.ofReal |χ x|)⁻¹

theorem measurable_dens (hχ : Continuous χ) : Measurable (dens χ) := by
  have h1 : Measurable fun x : M => ENNReal.ofReal |χ x| :=
    ENNReal.measurable_ofReal.comp ((continuous_abs.comp hχ).measurable)
  exact h1.inv

def ν : Measure M := (Measure.map (ψ e) volume).withDensity (dens χ)

theorem ν_apply (hχ : Continuous χ) {S : Set M} (hS : MeasurableSet S) :
    ν e χ S = ∫⁻ c in (ψ e) ⁻¹' S, dens χ (ψ e c) ∂volume := by
  rw [ν, withDensity_apply _ hS, setLIntegral_map hS (measurable_dens χ hχ) (measurable_ψ e)]

theorem dens_pos (x : M) : 0 < dens χ x := by
  simp only [dens, ENNReal.inv_pos]
  exact ENNReal.ofReal_ne_top

theorem dens_mul_of_ne_zero {g : M} (hg : χ g ≠ 0) (x : M) :
    dens χ (g * x) = (ENNReal.ofReal |χ g|)⁻¹ * dens χ x := by
  simp only [dens]
  rw [map_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.mul_inv (Or.inl ((ENNReal.ofReal_pos.2 (abs_pos.2 hg)).ne')) (Or.inl ENNReal.ofReal_ne_top)]

theorem dens_mul_of_ne_zero' {g : M} (hg : χ g ≠ 0) (x : M) :
    dens χ (x * g) = (ENNReal.ofReal |χ g|)⁻¹ * dens χ x := by
  simp only [dens]
  rw [map_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inr ((ENNReal.ofReal_pos.2 (abs_pos.2 hg)).ne')), mul_comm]

theorem ν_preimage_eq (hχ : Continuous χ) (φ : M → M) (hφ : Measurable φ) (Λ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hdet : LinearMap.det Λ ≠ 0) (hΛ : ∀ c, ψ e (Λ c) = φ (ψ e c))
    (hdens : ∀ x, dens χ (φ x) = (ENNReal.ofReal |LinearMap.det Λ|)⁻¹ * dens χ x)
    {S : Set M} (hS : MeasurableSet S) : ν e χ (φ ⁻¹' S) = ν e χ S := by
  have hSφ : MeasurableSet (φ ⁻¹' S) := hφ hS
  rw [ν_apply e χ hχ hSφ, ν_apply e χ hχ hS]

  have hpre : (ψ e) ⁻¹' (φ ⁻¹' S) = Λ ⁻¹' ((ψ e) ⁻¹' S) := by
    ext c
    simp only [Set.mem_preimage, hΛ]
  rw [hpre]
  set F : (Fin n → ℝ) → ℝ≥0∞ := fun c => dens χ (ψ e c) with hF
  have hFm : Measurable F := (measurable_dens χ hχ).comp (measurable_ψ e)
  set k : ℝ≥0∞ := ENNReal.ofReal |LinearMap.det Λ| with hk
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.2 (abs_pos.2 hdet)).ne'
  have hktop : k ≠ ⊤ := ENNReal.ofReal_ne_top

  have hFΛ : ∀ c, F c = k * F (Λ c) := by
    intro c
    simp only [hF]
    rw [hΛ, hdens, ← mul_assoc, ENNReal.mul_inv_cancel hk0 hktop, one_mul]
  have hΛm : Measurable Λ := Λ.continuous_of_finiteDimensional.measurable
  have hT : MeasurableSet ((ψ e) ⁻¹' S) := measurable_ψ e hS
  calc ∫⁻ c in Λ ⁻¹' ((ψ e) ⁻¹' S), F c ∂volume
      = ∫⁻ c in Λ ⁻¹' ((ψ e) ⁻¹' S), k * F (Λ c) ∂volume := by
        refine lintegral_congr fun c => hFΛ c
    _ = k * ∫⁻ c in Λ ⁻¹' ((ψ e) ⁻¹' S), F (Λ c) ∂volume := by
        rw [lintegral_const_mul' k _ hktop]
    _ = k * ∫⁻ y in (ψ e) ⁻¹' S, F y ∂(Measure.map Λ volume) := by
        rw [setLIntegral_map hT hFm hΛm]
    _ = k * ∫⁻ y in (ψ e) ⁻¹' S, F y ∂(ENNReal.ofReal |(LinearMap.det Λ)⁻¹| • (volume : Measure (Fin n → ℝ))) := by
        rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet]
    _ = k * (ENNReal.ofReal |(LinearMap.det Λ)⁻¹| * ∫⁻ y in (ψ e) ⁻¹' S, F y ∂volume) := by
        rw [Measure.restrict_smul, lintegral_smul_measure]
        rfl
    _ = ∫⁻ y in (ψ e) ⁻¹' S, F y ∂volume := by
        rw [← mul_assoc, hk, abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.2 hdet), ENNReal.mul_inv_cancel hk0 hktop,
          one_mul]

variable (A : Subalgebra ℝ M) (Γ : Subgroup Mˣ) (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A)

theorem chi_ne_zero (g : Mˣ) : χ g ≠ 0 := by
  intro h
  have : χ ((g : M) * (g⁻¹ : Mˣ)) = 1 := by rw [Units.mul_inv, map_one]
  rw [map_mul, h, zero_mul] at this
  exact zero_ne_one this

theorem ν_preimage_mul_left (hχ : Continuous χ)
    (hli : LinearIndependent ℝ e) (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A)
    (hleft : ∀ g : Mˣ, g ∈ Γ → ∃ P : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, (g : M) * e j = ∑ i, P i j • e i) ∧ |P.det| = |χ g|)
    {g : Mˣ} (hg : g ∈ Γ) {S : Set M} (hS : MeasurableSet S) :
    ν e χ ((fun x : M => (g : M) * x) ⁻¹' S) = ν e χ S := by
  have hχg : χ g ≠ 0 := chi_ne_zero χ g
  obtain ⟨P, hP, hl⟩ := hleft g hg
  have hdetP : P.det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hl
    exact hχg (abs_eq_zero.1 hl.symm)
  refine ν_preimage_eq e χ hχ (fun x : M => (g : M) * x) (measurable_const_mul _) (Matrix.toLin' P)
    (by rwa [LinearMap.det_toLin']) (fun c => ?_) (fun x => ?_) hS
  · rw [Matrix.toLin'_apply]; exact ψ_mulVec_of_left e hP c
  · rw [LinearMap.det_toLin', hl]
    exact dens_mul_of_ne_zero χ hχg x

theorem ν_preimage_mul_right (hχ : Continuous χ)
    (hli : LinearIndependent ℝ e) (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A)
    (hright : ∀ g : Mˣ, g ∈ Γ → ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, e j * (g : M) = ∑ i, Q i j • e i) ∧ |Q.det| = |χ g|)
    {g : Mˣ} (hg : g ∈ Γ) {S : Set M} (hS : MeasurableSet S) :
    ν e χ ((fun x : M => x * (g : M)) ⁻¹' S) = ν e χ S := by
  have hχg : χ g ≠ 0 := chi_ne_zero χ g
  obtain ⟨Q, hQ, hr⟩ := hright g hg
  have hdetQ : Q.det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hr
    exact hχg (abs_eq_zero.1 hr.symm)
  refine ν_preimage_eq e χ hχ (fun x : M => x * (g : M)) (measurable_mul_const _) (Matrix.toLin' Q)
    (by rwa [LinearMap.det_toLin']) (fun c => ?_) (fun x => ?_) hS
  · rw [Matrix.toLin'_apply]; exact ψ_mulVec_of_right e hQ c
  · rw [LinearMap.det_toLin', hr]
    exact dens_mul_of_ne_zero' χ hχg x

end Invariance

section NullNonUnits

variable {M : Type*} [Ring M] [Algebra ℝ M] [FiniteDimensional ℝ M]
  [TopologicalSpace M] [IsTopologicalRing M] [ContinuousSMul ℝ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]

theorem prod_null_of_smul_one {m : ℕ} (θ : (ℝ × (Fin m → ℝ)) →ₗ[ℝ] M) (hθ : ∀ t : ℝ, θ (t, 0) = t • (1 : M)) :
    ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) {p | ¬ IsUnit (θ p)} = 0 := by
  have hθc : Continuous θ := θ.continuous_of_finiteDimensional
  have hmeas : MeasurableSet {p : ℝ × (Fin m → ℝ) | ¬ IsUnit (θ p)} :=
    (isClosed_setOf_not_isUnit.preimage hθc).measurableSet

  have hswap : ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) =
      Measure.map Prod.swap ((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)) :=
    (Measure.prod_swap).symm
  rw [hswap, Measure.map_apply measurable_swap hmeas]
  rw [Measure.measure_prod_null (measurable_swap hmeas)]
  refine Filter.Eventually.of_forall fun c => ?_

  show (volume : Measure ℝ) (Prod.mk c ⁻¹' (Prod.swap ⁻¹' {p : ℝ × (Fin m → ℝ) | ¬ IsUnit (θ p)})) = 0
  have hsec : Prod.mk c ⁻¹' (Prod.swap ⁻¹' {p : ℝ × (Fin m → ℝ) | ¬ IsUnit (θ p)}) =
      {t : ℝ | ¬ IsUnit (t • (1 : M) + θ (0, c))} := by
    ext t
    simp only [Set.mem_preimage, Prod.swap_prod_mk, Set.mem_setOf_eq]
    have : θ (t, c) = t • (1 : M) + θ (0, c) := by
      rw [← hθ t, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
    rw [this]
  rw [hsec]
  exact (finite_setOf_not_isUnit_add (θ (0, c))).measure_zero _

variable {n : ℕ} (e : Fin n → M) (A : Subalgebra ℝ M)

theorem volume_setOf_not_isUnit_ψ
    (hli : LinearIndependent ℝ e) (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A) :
    (volume : Measure (Fin n → ℝ)) {c | ¬ IsUnit (ψ e c)} = 0 := by
  classical

  obtain ⟨w, hw⟩ : (1 : M) ∈ Set.range (ψ e) := by rw [range_ψ A e hsp]; exact A.one_mem
  rcases subsingleton_or_nontrivial M with hM | hM
  ·
    have : {c : Fin n → ℝ | ¬ IsUnit (ψ e c)} = ∅ := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact isUnit_of_subsingleton _
    rw [this, measure_empty]

  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw
    exact zero_ne_one hw
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exact absurd (Subsingleton.elim w 0) hw0
    · exact ⟨n - 1, by omega⟩

  have hwli : LinearIndepOn ℝ id ({w} : Set (Fin (m + 1) → ℝ)) := LinearIndepOn.singleton (v := id) hw0

  obtain ⟨b, hb0⟩ : ∃ b : Module.Basis (Fin (m + 1)) ℝ (Fin (m + 1) → ℝ), b 0 = w := by

    let s : Set (Fin (m + 1) → ℝ) := hwli.extend (Set.subset_univ _)
    let bs : Module.Basis s ℝ (Fin (m + 1) → ℝ) := Module.Basis.extend hwli
    have hws : w ∈ s := Module.Basis.subset_extend hwli (Set.mem_singleton w)
    haveI : Fintype s := Fintype.ofFinite s
    have hcard : Fintype.card s = m + 1 := by
      have := Module.finrank_eq_card_basis bs
      rw [Module.finrank_fin_fun] at this
      exact this.symm

    obtain ⟨σ, hσ⟩ : ∃ σ : Fin (m + 1) ≃ s, σ 0 = ⟨w, hws⟩ := by
      obtain ⟨σ₀⟩ : Nonempty (Fin (m + 1) ≃ s) :=
        ⟨Fintype.equivOfCardEq (by rw [hcard, Fintype.card_fin])⟩
      refine ⟨(Equiv.swap 0 (σ₀.symm ⟨w, hws⟩)).trans σ₀, ?_⟩
      simp
    refine ⟨bs.reindex σ.symm, ?_⟩
    have h1 : (bs.reindex σ.symm) 0 = bs (σ 0) := by
      rw [Module.Basis.reindex_apply, Equiv.symm_symm]
    rw [h1, hσ]
    exact Module.Basis.extend_apply_self hwli _

  set T : (Fin (m + 1) → ℝ) ≃ₗ[ℝ] (Fin (m + 1) → ℝ) := b.equivFun.symm with hT
  have hT0 : ∀ t : ℝ, T (Pi.single 0 t) = t • w := by
    intro t
    rw [hT, Module.Basis.equivFun_symm_apply, Fin.sum_univ_succ, hb0]
    simp [Pi.single_apply, Fin.succ_ne_zero]

  set Φ : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) := MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 with hΦ
  have hΦmp : MeasurePreserving Φ (volume : Measure (Fin (m + 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) := by
    have := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => (volume : Measure ℝ)) 0
    rw [hΦ]
    convert this using 1
    rfl
    rfl
    rfl

  set ΦL : (ℝ × (Fin m → ℝ)) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
    { toFun := fun p => Φ.symm p
      map_add' := fun p q => by
        rw [hΦ]
        ext j
        refine Fin.cases ?_ (fun j => ?_) j <;>
          simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_apply_same,
            Fin.insertNth_apply_succAbove]
      map_smul' := fun r p => by
        rw [hΦ]
        ext j
        refine Fin.cases ?_ (fun j => ?_) j <;>
          simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_apply_same,
            Fin.insertNth_apply_succAbove] } with hΦL
  have hΦL_apply : ∀ p, ΦL p = Φ.symm p := fun p => rfl
  have hΦL0 : ∀ t : ℝ, ΦL (t, 0) = Pi.single 0 t := by
    intro t
    rw [hΦL_apply, hΦ]
    ext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_apply_same]
    · simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_apply_succAbove, Pi.single_apply,
        Fin.succ_ne_zero]
  set θ : (ℝ × (Fin m → ℝ)) →ₗ[ℝ] M := (ψ e) ∘ₗ (T : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) ∘ₗ ΦL with hθ
  have hθ1 : ∀ t : ℝ, θ (t, 0) = t • (1 : M) := by
    intro t
    simp only [hθ, LinearMap.comp_apply, LinearEquiv.coe_coe, hΦL0, hT0, map_smul, hw]
  have hnull := prod_null_of_smul_one θ hθ1

  have hset : {c : Fin (m + 1) → ℝ | ¬ IsUnit (ψ e c)} =
      (T : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) '' (Φ ⁻¹' {p | ¬ IsUnit (θ p)}) := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_preimage]
    constructor
    · intro hc
      refine ⟨T.symm c, ?_, by simp⟩
      simp only [hθ, LinearMap.comp_apply, LinearEquiv.coe_coe, hΦL_apply, MeasurableEquiv.symm_apply_apply,
        LinearEquiv.apply_symm_apply]
      exact hc
    · rintro ⟨c', hc', rfl⟩
      simp only [hθ, LinearMap.comp_apply, LinearEquiv.coe_coe, hΦL_apply, MeasurableEquiv.symm_apply_apply] at hc'
      simpa using hc'
  rw [hset, Measure.addHaar_image_linearMap, hΦmp.measure_preimage]
  · rw [hnull, mul_zero]
  · exact ((isClosed_setOf_not_isUnit.preimage θ.continuous_of_finiteDimensional).measurableSet).nullMeasurableSet

end NullNonUnits

section Haar

variable {M : Type*} [Ring M] [Algebra ℝ M] [FiniteDimensional ℝ M]
  [TopologicalSpace M] [IsTopologicalRing M] [ContinuousSMul ℝ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]
  (A : Subalgebra ℝ M) (Γ : Subgroup Mˣ)
  {n : ℕ} (e : Fin n → M) (χ : M →* ℝ)

scoped instance (priority := 10000) instMeasurableSpaceΓ : MeasurableSpace Γ := borel Γ
scoped instance instBorelSpaceΓ : BorelSpace Γ := ⟨rfl⟩

theorem polishSpace_units : PolishSpace Mˣ := by
  haveI : PolishSpace M := polishSpace_of_finiteDimensional
  haveI : PolishSpace Mᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.polishSpace
  exact Units.isClosedEmbedding_embedProduct.polishSpace

theorem isClosed_A : IsClosed ((A : Set M)) :=
  (Subalgebra.toSubmodule A).closed_of_finiteDimensional

theorem isClosed_Γ (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A) : IsClosed ((Γ : Set Mˣ)) := by
  have : (Γ : Set Mˣ) = ((↑) : Mˣ → M) ⁻¹' (A : Set M) := by
    ext g; exact hΓ g
  rw [this]
  exact (isClosed_A A).preimage Units.continuous_val

theorem polishSpace_Γ (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A) : PolishSpace Γ := by
  haveI := polishSpace_units (M := M)
  exact (isClosed_Γ A Γ hΓ).polishSpace

scoped instance secondCountable_units : SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance secondCountable_Γ : SecondCountableTopology Γ :=
  (Topology.IsInducing.subtypeVal).secondCountableTopology

def incl : Γ → M := fun t => ((t : Mˣ) : M)

theorem continuous_incl : Continuous (incl Γ) := Units.continuous_val.comp continuous_subtype_val

theorem injective_incl : Function.Injective (incl Γ) := fun s t h =>
  Subtype.ext (Units.ext h)

theorem measurableEmbedding_incl (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A) : MeasurableEmbedding (incl Γ) := by
  haveI := polishSpace_Γ A Γ hΓ
  exact (continuous_incl Γ).measurableEmbedding (injective_incl Γ)

theorem range_incl (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A) :
    Set.range (incl Γ) = (A : Set M) \ {x | ¬ IsUnit x} := by
  ext x
  simp only [Set.mem_range, Set.mem_diff, Set.mem_setOf_eq, not_not, SetLike.mem_coe]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(hΓ _).1 t.2, Units.isUnit _⟩
  · rintro ⟨hx, u, rfl⟩
    exact ⟨⟨u, (hΓ u).2 hx⟩, rfl⟩

def τ : Measure Γ := Measure.comap (incl Γ) (ν e χ)

theorem τ_apply (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A) (S : Set Γ) : τ Γ e χ S = ν e χ (incl Γ '' S) :=
  (measurableEmbedding_incl A Γ hΓ).comap_apply _ S

theorem ν_nonunits (hli : LinearIndependent ℝ e) (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A) :
    ν e χ ((A : Set M) ∩ {x | ¬ IsUnit x}) = 0 := by
  have hmeas : MeasurableSet ((A : Set M) ∩ {x | ¬ IsUnit x}) :=
    ((isClosed_A A).inter isClosed_setOf_not_isUnit).measurableSet
  rw [ν, withDensity_apply _ hmeas]
  have h0 : (Measure.map (ψ e) volume) ((A : Set M) ∩ {x | ¬ IsUnit x}) = 0 := by
    rw [Measure.map_apply (measurable_ψ e) hmeas]
    have : (ψ e) ⁻¹' ((A : Set M) ∩ {x | ¬ IsUnit x}) ⊆ {c | ¬ IsUnit (ψ e c)} := fun c hc => hc.2
    exact measure_mono_null this (volume_setOf_not_isUnit_ψ e A hli hsp)
  rw [Measure.restrict_eq_zero.2 h0, lintegral_zero_measure]

theorem ν_compl_A (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A) : ν e χ ((A : Set M)ᶜ) = 0 := by
  rw [ν, withDensity_apply _ (isClosed_A A).measurableSet.compl]
  have h0 : (Measure.map (ψ e) volume) ((A : Set M)ᶜ) = 0 := by
    rw [Measure.map_apply (measurable_ψ e) (isClosed_A A).measurableSet.compl]
    have : (ψ e) ⁻¹' ((A : Set M)ᶜ) = ∅ := by
      ext c
      simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false, not_not]
      exact ψ_mem A e hsp c
    rw [this, measure_empty]
  rw [Measure.restrict_eq_zero.2 h0, lintegral_zero_measure]

theorem ν_compl_range (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A)
    (hli : LinearIndependent ℝ e) (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A) :
    ν e χ ((Set.range (incl Γ))ᶜ) = 0 := by
  rw [range_incl A Γ hΓ]
  have : ((A : Set M) \ {x | ¬ IsUnit x})ᶜ ⊆ (A : Set M)ᶜ ∪ ((A : Set M) ∩ {x | ¬ IsUnit x}) := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_setOf_eq, not_and, not_not] at hx
    by_cases hA : x ∈ (A : Set M)
    · exact Or.inr ⟨hA, hx hA⟩
    · exact Or.inl hA
  refine measure_mono_null this ?_
  rw [measure_union_null_iff]
  exact ⟨ν_compl_A A e χ hsp, ν_nonunits A e χ hli hsp⟩

theorem map_τ (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A)
    (hli : LinearIndependent ℝ e) (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A) :
    Measure.map (incl Γ) (τ Γ e χ) = ν e χ := by
  rw [τ, (measurableEmbedding_incl A Γ hΓ).map_comap]
  exact Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]
    exact ν_compl_range A Γ e χ hΓ hli hsp)

theorem τ_isMulLeftInvariant (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A) (hχ : Continuous χ)
    (hli : LinearIndependent ℝ e) (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A)
    (hleft : ∀ g : Mˣ, g ∈ Γ → ∃ P : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, (g : M) * e j = ∑ i, P i j • e i) ∧ |P.det| = |χ g|) :
    (τ Γ e χ).IsMulLeftInvariant := by
  refine ⟨fun t => ?_⟩
  ext S hS
  rw [Measure.map_apply (measurable_const_mul t) hS, τ_apply A Γ e χ hΓ, τ_apply A Γ e χ hΓ]
  have himg : incl Γ '' ((fun s => t * s) ⁻¹' S) = (fun x : M => ((t : Mˣ) : M) * x) ⁻¹' (incl Γ '' S) := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, incl]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨t * s, hs, by simp⟩
    · rintro ⟨s', hs', hx⟩
      refine ⟨t⁻¹ * s', by simpa using hs', ?_⟩
      have h1 : ((↑(t⁻¹ * s' : Γ) : Mˣ) : M) = ((↑(t⁻¹ : Γ) : Mˣ) : M) * ((s' : Mˣ) : M) := by simp
      rw [h1, hx]
      simp [← mul_assoc]
  rw [himg]
  exact ν_preimage_mul_left e χ A Γ hχ hli hsp hleft t.2 ((measurableEmbedding_incl A Γ hΓ).measurableSet_image' hS)

theorem τ_isMulRightInvariant (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A) (hχ : Continuous χ)
    (hli : LinearIndependent ℝ e) (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A)
    (hright : ∀ g : Mˣ, g ∈ Γ → ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, e j * (g : M) = ∑ i, Q i j • e i) ∧ |Q.det| = |χ g|) :
    (τ Γ e χ).IsMulRightInvariant := by
  refine ⟨fun t => ?_⟩
  ext S hS
  rw [Measure.map_apply (measurable_mul_const t) hS, τ_apply A Γ e χ hΓ, τ_apply A Γ e χ hΓ]
  have himg : incl Γ '' ((fun s => s * t) ⁻¹' S) = (fun x : M => x * ((t : Mˣ) : M)) ⁻¹' (incl Γ '' S) := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, incl]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s * t, hs, by simp⟩
    · rintro ⟨s', hs', hx⟩
      refine ⟨s' * t⁻¹, by simpa using hs', ?_⟩
      have h1 : ((↑(s' * t⁻¹ : Γ) : Mˣ) : M) = ((s' : Mˣ) : M) * ((↑(t⁻¹ : Γ) : Mˣ) : M) := by simp
      rw [h1, hx]
      simp [mul_assoc]
  rw [himg]
  exact ν_preimage_mul_right e χ A Γ hχ hli hsp hright t.2 ((measurableEmbedding_incl A Γ hΓ).measurableSet_image' hS)

theorem isClosedEmbedding_ψ (hli : LinearIndependent ℝ e)
    (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A) : IsClosedEmbedding (ψ e) := by
  have hcont : Continuous (ψ e) := continuous_ψ e
  haveI : IsTopologicalAddGroup A := inferInstanceAs (IsTopologicalAddGroup (Subalgebra.toSubmodule A))
  haveI : ContinuousSMul ℝ A := inferInstanceAs (ContinuousSMul ℝ (Subalgebra.toSubmodule A))
  haveI : FiniteDimensional ℝ A := inferInstanceAs (FiniteDimensional ℝ (Subalgebra.toSubmodule A))
  let φ : A →ₗ[ℝ] (Fin n → ℝ) := (bA A e hli hsp).equivFun.toLinearMap
  have hφ : Continuous φ := φ.continuous_of_finiteDimensional
  have hleftinv : ∀ c, φ ⟨ψ e c, ψ_mem A e hsp c⟩ = c := fun c => equivFun_ψ A e hli hsp c
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap hcont (injective_ψ e hli) ?_
  intro F hF
  have h1 : ψ e '' F = ((↑) : A → M) '' (φ ⁻¹' F) := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨ψ e c, ψ_mem A e hsp c⟩, by rw [hleftinv]; exact hc, rfl⟩
    · rintro ⟨⟨y, hy⟩, h, rfl⟩
      refine ⟨φ ⟨y, hy⟩, h, ?_⟩
      have := coe_equivFun_symm A e hli hsp (φ ⟨y, hy⟩)
      rw [show φ ⟨y, hy⟩ = (bA A e hli hsp).equivFun ⟨y, hy⟩ from rfl, LinearEquiv.symm_apply_apply] at this
      exact this.symm
  rw [h1]
  exact ((isClosed_A A).isClosedEmbedding_subtypeVal).isClosedMap _ (hF.preimage hφ)

theorem τ_lt_top_of_isCompact (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A) (hχ : Continuous χ)
    (hli : LinearIndependent ℝ e) (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A)
    {C : Set Γ} (hC : IsCompact C) : τ Γ e χ C < ⊤ := by
  rw [τ_apply A Γ e χ hΓ]
  have hCM : IsCompact (incl Γ '' C) := hC.image (continuous_incl Γ)
  rcases (incl Γ '' C).eq_empty_or_nonempty with h0 | hne
  · rw [h0, measure_empty]; exact ENNReal.zero_lt_top

  obtain ⟨x₀, hx₀, hmin⟩ := hCM.exists_isMinOn hne (continuous_abs.comp hχ).continuousOn
  have hpos : 0 < |χ x₀| := by
    obtain ⟨t, -, rfl⟩ := hx₀
    exact abs_pos.2 (chi_ne_zero χ _)
  set K : ℝ≥0∞ := (ENNReal.ofReal |χ x₀|)⁻¹ with hK
  have hKtop : K ≠ ⊤ := ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hpos).ne'
  have hbound : ∀ x ∈ incl Γ '' C, dens χ x ≤ K := by
    intro x hx
    simp only [dens, hK]
    exact ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal (hmin hx))
  have hle : ν e χ (incl Γ '' C) ≤ K * (Measure.map (ψ e) volume) (incl Γ '' C) := by
    rw [ν, withDensity_apply _ hCM.measurableSet]
    calc ∫⁻ x in incl Γ '' C, dens χ x ∂(Measure.map (ψ e) volume)
        ≤ ∫⁻ x in incl Γ '' C, K ∂(Measure.map (ψ e) volume) :=
          setLIntegral_mono measurable_const fun x hx => hbound x hx
      _ = K * (Measure.map (ψ e) volume) (incl Γ '' C) := setLIntegral_const _ _
  refine lt_of_le_of_lt hle (ENNReal.mul_lt_top hKtop.lt_top ?_)
  rw [Measure.map_apply (measurable_ψ e) hCM.measurableSet]
  exact ((isClosedEmbedding_ψ A e hli hsp).isCompact_preimage hCM).measure_lt_top

theorem τ_pos_of_isOpen (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A) (hχ : Continuous χ)
    (hli : LinearIndependent ℝ e) (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A)
    (hleft : ∀ g : Mˣ, g ∈ Γ → ∃ P : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, (g : M) * e j = ∑ i, P i j • e i) ∧ |P.det| = |χ g|)
    {U : Set Γ} (hU : IsOpen U) (hne : U.Nonempty) : τ Γ e χ U ≠ 0 := by
  intro hU0
  haveI := τ_isMulLeftInvariant A Γ e χ hΓ hχ hli hsp hleft
  obtain ⟨s₀, hs₀⟩ := hne

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun g : Γ => (fun s => g * s) ⁻¹' U)
    fun g => hU.preimage (continuous_const_mul g)
  have hcov : (⋃ g : Γ, (fun s => g * s) ⁻¹' U) = Set.univ := by
    refine Set.eq_univ_of_forall fun t => Set.mem_iUnion.2 ⟨s₀ * t⁻¹, ?_⟩
    show s₀ * t⁻¹ * t ∈ U
    simpa using hs₀
  have huniv : τ Γ e χ Set.univ = 0 := by
    rw [← hcov, ← hTU]
    refine (measure_biUnion_null_iff hTc).2 fun g _ => ?_
    rw [measure_preimage_mul]
    exact hU0

  rw [τ_apply A Γ e χ hΓ, Set.image_univ, range_incl A Γ hΓ] at huniv
  have hN : ν e χ {x : M | ¬ IsUnit x} = 0 := by
    have hsub : {x : M | ¬ IsUnit x} ⊆ ((A : Set M) ∩ {x | ¬ IsUnit x}) ∪ (A : Set M)ᶜ := by
      intro x hx
      by_cases hA : x ∈ (A : Set M)
      · exact Or.inl ⟨hA, hx⟩
      · exact Or.inr hA
    exact measure_mono_null hsub (measure_union_null (ν_nonunits A e χ hli hsp) (ν_compl_A A e χ hsp))
  have hdiff : ν e χ ((A : Set M) \ {x | ¬ IsUnit x}) = ν e χ (A : Set M) := measure_diff_null hN
  rw [hdiff, ν_apply e χ hχ (isClosed_A A).measurableSet] at huniv
  have hpre : (ψ e) ⁻¹' (A : Set M) = Set.univ := by
    ext c; simpa using ψ_mem A e hsp c
  rw [hpre, Measure.restrict_univ] at huniv
  have hm : Measurable fun c => dens χ (ψ e c) := (measurable_dens χ hχ).comp (measurable_ψ e)
  rw [lintegral_eq_zero_iff hm] at huniv

  have hvol : (volume : Measure (Fin n → ℝ)) Set.univ ≠ 0 :=
    (measure_pos_of_nonempty_interior (μ := volume) (by rw [interior_univ]; exact Set.univ_nonempty)).ne'
  have h2 : (volume : Measure (Fin n → ℝ)) {c | (fun c => dens χ (ψ e c)) c ≠ (0 : (Fin n → ℝ) → ℝ≥0∞) c} = 0 :=
    ae_iff.1 huniv
  have hall : {c : Fin n → ℝ | (fun c => dens χ (ψ e c)) c ≠ (0 : (Fin n → ℝ) → ℝ≥0∞) c} = Set.univ := by
    refine Set.eq_univ_of_forall fun c => ?_
    exact (dens_pos χ (ψ e c)).ne'
  rw [hall] at h2
  exact hvol h2

theorem isHaarMeasure_τ (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A) (hχ : Continuous χ)
    (hli : LinearIndependent ℝ e) (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A)
    (hleft : ∀ g : Mˣ, g ∈ Γ → ∃ P : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, (g : M) * e j = ∑ i, P i j • e i) ∧ |P.det| = |χ g|)
    (hright : ∀ g : Mˣ, g ∈ Γ → ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, e j * (g : M) = ∑ i, Q i j • e i) ∧ |Q.det| = |χ g|) :
    (τ Γ e χ).IsHaarMeasure where
  lt_top_of_isCompact := fun C hC => τ_lt_top_of_isCompact A Γ e χ hΓ hχ hli hsp hC
  map_mul_left_eq_self := (τ_isMulLeftInvariant A Γ e χ hΓ hχ hli hsp hleft).map_mul_left_eq_self
  open_pos := fun U hU hne => τ_pos_of_isOpen A Γ e χ hΓ hχ hli hsp hleft hU hne

end Haar

end MeasureTheory.UnitGroupHaar
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq.MeasureTheory P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq.MeasureTheory.UnitGroupHaar"
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq.MeasureTheory"

end
p2m_reactivate "P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq.MeasureTheory P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq.MeasureTheory.UnitGroupHaar"

open _root_.MeasureTheory _root_.P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq.MeasureTheory MeasureTheory.UnitGroupHaar in
theorem solution
    {M : Type*} [Ring M] [Algebra ℝ M] [FiniteDimensional ℝ M]
    [TopologicalSpace M] [IsTopologicalRing M] [ContinuousSMul ℝ M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    (A : Subalgebra ℝ M) (Γ : Subgroup Mˣ) (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A)
    (n : ℕ) (e : Fin n → M) (hli : LinearIndependent ℝ e)
    (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A)
    (χ : M →* ℝ) (hχ : Continuous χ)
    (hleft : ∀ g : Mˣ, g ∈ Γ → ∃ P : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, (g : M) * e j = ∑ i, P i j • e i) ∧ |P.det| = |χ g|)
    (hright : ∀ g : Mˣ, g ∈ Γ → ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, e j * (g : M) = ∑ i, Q i j • e i) ∧ |Q.det| = |χ g|) :
    letI : MeasurableSpace Γ := borel Γ
    ∃ τ : Measure Γ, τ.IsHaarMeasure ∧ τ.IsMulRightInvariant ∧
      Measure.map (fun t : Γ => ((t : Mˣ) : M)) τ =
        (Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume).withDensity
          fun x => (ENNReal.ofReal |χ x|)⁻¹ := by
  refine ⟨τ Γ e χ, isHaarMeasure_τ A Γ e χ hΓ hχ hli hsp hleft hright,
    τ_isMulRightInvariant A Γ e χ hΓ hχ hli hsp hright, ?_⟩
  have h := map_τ A Γ e χ hΓ hli hsp
  have hψ : (ψ e : (Fin n → ℝ) → M) = fun c => ∑ i, c i • e i := funext (ψ_apply e)
  show Measure.map (incl Γ) (τ Γ e χ) = _
  rw [h, ν, hψ]
  rfl

end S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq
end P2MW
export P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq (solution)
