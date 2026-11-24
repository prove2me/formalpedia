-- Prove2me | solution 1 for GlobalTheory.NoetherPrimitive.exists_primitive_element_discriminant_multiple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:32:37.296444+00:00
-- url     : https://prove2.me/submissions/cfe35ebd-02ad-425c-a3a7-b713bdb1f5c5

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsPrimitiveElementDiscriminantMultiple
import Theorems.Thm_GlobalTheory_NoetherPrimitive_exists_map_eq_C_mul
import Theorems.Thm_GlobalTheory_NoetherPrimitive_exists_C_mem_span
import Theorems.Thm_GlobalTheory_NoetherPrimitive_exists_common_denominator
import Theorems.Thm_GlobalTheory_CommonDenominatorForFinset_exists_common_denominator


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherPrimitive
open Polynomial
open scoped nonZeroDivisors
namespace GlobalTheory.NoetherPrimitive
theorem _root_.solution (R A K L : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra A L]
    [IsFractionRing A L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R A L] :
    ∃ (a : A) (q : R), q ≠ 0 ∧ C q ∈ Ideal.span {minpoly R a, (minpoly R a).derivative} ∧
      ∀ b : A, ∃ r : R[X], algebraMap R A q * b = aeval a r := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A R⁰) L := inferInstance
  haveI : Module.Finite K L := Module.Finite.of_isLocalization R A R⁰
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  obtain ⟨⟨a, ⟨_, t, ht, rfl⟩⟩, hat⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid A R⁰) α
  have ht' : algebraMap R K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (nonZeroDivisors.ne_zero ht)
  have hat' : α = algebraMap K L (algebraMap R K t)⁻¹ * algebraMap A L a := by
    simp only at hat
    rw [← hat, ← IsScalarTower.algebraMap_apply R A L, IsScalarTower.algebraMap_apply R K L,
      mul_left_comm, ← map_mul, inv_mul_cancel₀ ht', map_one, mul_one]
  have hint : IsIntegral R a := Algebra.IsIntegral.isIntegral a
  have htop : Algebra.adjoin K {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α), hα, IntermediateField.top_toSubalgebra]
  obtain ⟨q₁, hq₁, h₁⟩ := exists_common_denominator (R := R) a fun b => by
    have hb : algebraMap A L b ∈ Algebra.adjoin K {α} := htop ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    obtain ⟨f, hf⟩ := hb
    obtain ⟨s, hs, g, hg⟩ := exists_map_eq_C_mul (R := R) (f.comp (C (algebraMap R K t)⁻¹ * X))
    refine ⟨s, hs, g, IsFractionRing.injective A L ?_⟩
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap K, hg, map_mul, map_mul, aeval_C,
      aeval_comp, map_mul, aeval_C, aeval_X, ← hat', ← hf, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
    rfl
  obtain ⟨q₂, hq₂, h₂⟩ := exists_C_mem_span (K := K) (minpoly R a) (by
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L hint]
    exact Algebra.IsSeparable.isSeparable K _)
  refine ⟨a, q₂ * q₁, mul_ne_zero hq₂ hq₁, ?_, fun b => ?_⟩
  · rw [C_mul]; exact Ideal.mul_mem_right _ _ h₂
  · obtain ⟨r, hr⟩ := h₁ b
    exact ⟨C q₂ * r, by rw [map_mul, map_mul, aeval_C, mul_assoc, hr]⟩
end GlobalTheory.NoetherPrimitive
