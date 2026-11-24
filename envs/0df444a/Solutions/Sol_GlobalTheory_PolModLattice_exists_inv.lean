-- Prove2me | solution 1 for GlobalTheory.PolModLattice.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:42:35.729801+00:00
-- url     : https://prove2.me/submissions/dcb4ca74-e36f-4a20-9da2-b03dee3b4fb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
import Theorems.Thm_GlobalTheory_PolModLattice_real_of_bar
import Theorems.Thm_GlobalTheory_PolModLattice_formSpan_le_imag
import Theorems.Thm_GlobalTheory_PolModLattice_exists_imag_int
import Theorems.Thm_GlobalTheory_PolModLattice_isIntegral_formSpan
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
open GlobalTheory GlobalTheory.PolModLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open scoped nonZeroDivisors
namespace GlobalTheory.PolModLattice
theorem _root_.solution (L : Submodule (OF E) E)
    (hL : ∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) :
    ∃ J : Submodule (OF E) E, formSpan L * J = 1 ∧ ∀ j ∈ J, bar j = -j := by
  obtain ⟨N, hN0, hNL, hNi⟩ := hL
  obtain ⟨δ, hδ0, hδb⟩ := exists_imag_int (E := E)
  let K := maximalRealSubfield E
  let f : K →ₐ[OF E] E := IsScalarTower.toAlgHom (OF E) K E
  let g : K →ₗ[OF E] E := (LinearMap.mulRight (OF E) (δ : E)).comp f.toLinearMap
  let IK : Submodule (OF E) K := (formSpan L).comap g
  have hg : ∀ a : K, g a = (a : E) * δ := fun a => rfl

  have hsplit : formSpan L = IK.map f.toLinearMap * Submodule.span (OF E) {(δ : E)} := by
    apply le_antisymm
    · intro w hw
      have hwi : bar w = -w := formSpan_le_imag L hw
      have hr : bar (w / δ) = w / δ := by
        simp only [bar, map_div₀] at hwi hδb ⊢
        rw [hwi, hδb, neg_div_neg_eq]
      obtain ⟨a, ha⟩ := real_of_bar hr
      have haI : a ∈ IK := by
        show g a ∈ formSpan L
        rw [hg, ha, div_mul_cancel₀ _ hδ0]
        exact hw
      have : w = f a * δ := by
        show w = (a : E) * δ
        rw [ha, div_mul_cancel₀ _ hδ0]
      rw [this]
      exact Submodule.mul_mem_mul ⟨a, haI, rfl⟩ (Submodule.mem_span_singleton_self _)
    · refine Submodule.mul_le.2 fun u hu s hs => ?_
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
      rw [mul_smul_comm]
      exact (formSpan L).smul_mem c ha

  have hδ2 : bar ((δ : E) * δ) = (δ : E) * δ := by
    simp only [bar, map_mul] at hδb ⊢; rw [hδb]; ring
  obtain ⟨d, hd⟩ : ∃ d : OF E, algebraMap (OF E) E d = (δ : E) * δ := by
    obtain ⟨d, hd⟩ := (IsCMField.RingOfIntegers.complexConj_eq_self_iff E (δ * δ)).1 (by
      push_cast; exact hδ2)
    exact ⟨d, by rw [hd]; push_cast; rfl⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd
    exact mul_self_ne_zero.2 hδ0 hd.symm
  have hfrac : IsFractional (OF E)⁰ IK := by
    refine ⟨(N : OF E) ^ 2 * d, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hN0.ne')) hd0), ?_⟩
    intro a ha
    have h1 := isIntegral_formSpan L N hNi _ ha
    rw [hg] at h1
    have h2 : IsIntegral ℤ (f (((N : OF E) ^ 2 * d) • a)) := by
      have e : f (((N : OF E) ^ 2 * d) • a) = (N : E) ^ 2 * ((a : E) * δ) * δ := by
        rw [Algebra.smul_def, map_mul, AlgHom.commutes, map_mul, map_pow, map_natCast, hd]
        change (N : E) ^ 2 * (δ * δ) * (a : E) = _
        ring
      rw [e]
      exact h1.mul δ.2
    have h3 : IsIntegral ℤ (((N : OF E) ^ 2 * d) • a) :=
      (isIntegral_algHom_iff (f.restrictScalars ℤ) f.toRingHom.injective).1 h2
    exact ⟨⟨_, h3⟩, rfl⟩
  let 𝔦 : FractionalIdeal (OF E)⁰ K := ⟨IK, hfrac⟩
  have h𝔦 : 𝔦 ≠ 0 := by
    intro h
    have hm : (-(N : K) ^ 2 - (N : K) ^ 2 : K) ∈ IK := by
      show g _ ∈ formSpan L
      have hx := hNL 1
      have hy : (N : E) * (δ : E) ∈ L := hNL δ
      rw [map_one, mul_one] at hx
      have hmem : altForm (N : E) ((N : E) * (δ : E)) ∈ formSpan L := Submodule.subset_span ⟨_, hx, _, hy, rfl⟩
      convert hmem using 1
      rw [hg]
      simp only [altForm, bar, map_mul, map_natCast] at hδb ⊢
      rw [hδb]
      push_cast
      ring
    have : (-(N : K) ^ 2 - (N : K) ^ 2 : K) ∈ (𝔦 : Submodule (OF E) K) := hm
    rw [h, FractionalIdeal.coe_zero, Submodule.mem_bot] at this
    have hN : (N : K) ≠ 0 := by exact_mod_cast hN0.ne'
    rw [show (-(N : K) ^ 2 - (N : K) ^ 2 : K) = -2 * (N : K) ^ 2 by ring] at this
    exact (mul_ne_zero (by norm_num) (pow_ne_zero 2 hN)) this
  have hmul : IK * ((𝔦⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K) = 1 := by
    rw [show IK = (𝔦 : Submodule (OF E) K) from rfl, ← FractionalIdeal.coe_mul, mul_inv_cancel₀ h𝔦,
      FractionalIdeal.coe_one]
  refine ⟨((𝔦⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K).map f.toLinearMap *
    Submodule.span (OF E) {(δ : E)⁻¹}, ?_, ?_⟩
  · rw [hsplit, mul_mul_mul_comm, ← Submodule.map_mul, hmul, Submodule.map_one,
      Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hδ0, ← Submodule.one_eq_span, mul_one]
  · intro j hj
    have hle : ((𝔦⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K).map f.toLinearMap *
        Submodule.span (OF E) {(δ : E)⁻¹} ≤ imagPart E := by
      refine Submodule.mul_le.2 fun u hu s hs => ?_
      obtain ⟨a, -, rfl⟩ := hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
      show bar _ = -_
      rw [mul_smul_comm, bar_smul]
      simp only [bar, map_mul, map_inv₀] at hδb ⊢
      rw [hδb]
      have : IsCMField.complexConj E (f.toLinearMap a) = f.toLinearMap a := IsCMField.complexConj_apply_eq_self E a
      rw [this, inv_neg, mul_neg, smul_neg]
    exact hle hj
end GlobalTheory.PolModLattice
