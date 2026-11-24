-- Prove2me | solution 1 for GlobalTheory.TraceSpread.exists_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:39:00.178121+00:00
-- url     : https://prove2.me/submissions/360f495a-bd50-4660-b63f-16a0a393e939

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmTypeEigenMultiplicityOfDensePrimes
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.TraceSpread
variable {E : Type} [Field E] [NumberField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] in
private lemma ringOfIntegers_ringHom_injective' {K : Type} [Field K] [CharZero K]
    (τ : 𝓞 E →+* K) : Function.Injective τ := by
  refine (injective_iff_map_eq_zero τ).mpr fun a ha => ?_
  by_contra hne
  have haE : (a : E) ≠ 0 := by
    intro h; exact hne (RingOfIntegers.coe_injective (h.trans (map_zero (algebraMap (𝓞 E) E)).symm))
  obtain ⟨z, hz, h⟩ := exists_integral_multiples ℤ ℚ ({(a : E)⁻¹} : Finset E)
  let c : 𝓞 E := ⟨z • (a : E)⁻¹, h _ (Finset.mem_singleton_self _)⟩
  have hzc : (z : 𝓞 E) = a * c := by
    apply RingOfIntegers.coe_injective
    show ((z : 𝓞 E) : E) = (a : E) * (z • (a : E)⁻¹)
    rw [zsmul_eq_mul, mul_left_comm, mul_inv_cancel₀ haE, _root_.mul_one]
    simp
  have : τ (z : 𝓞 E) = 0 := by rw [hzc, map_mul, ha, zero_mul]
  rw [map_intCast] at this
  exact hz (Int.cast_eq_zero.mp this)
variable [IsCMField E]
end GlobalTheory.TraceSpread
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TraceSpread
variable {E : Type} [Field E] [NumberField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.TraceSpread
namespace _root_.GlobalTheory.TraceSpread
theorem _root_.solution {K : Type} [Field K] [CharZero K]
    (τ : 𝓞 E →+* K) :
    ∃ φ : E →+* K, φ.comp (algebraMap (𝓞 E) E) = τ := by
  refine ⟨IsFractionRing.lift (ringOfIntegers_ringHom_injective' τ), ?_⟩
  ext a
  exact IsFractionRing.lift_algebraMap (ringOfIntegers_ringHom_injective' τ) a
end _root_.GlobalTheory.TraceSpread
end GlobalTheory.TraceSpread
