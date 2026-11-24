-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HT.LatBasic.eigProj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:34:37.264967+00:00
-- url     : https://prove2.me/submissions/3e1fb145-91c7-4c2c-b8bc-49dba42e98ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_LatNormGrLatNeZeroOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_mem_eigSp
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_expand_dual
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_repr_eq_trace
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open Module NumberField
open GlobalTheory.CompanionTheory.Ar.HT.LatBasic
open TensorProduct
variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CompanionTheory.Ar.HT.LatBasic
theorem _root_.solution (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (x : V) :
    eigProj ρ σ x ∈ eigSp ρ σ := by
  classical
  haveI : CharZero K := (RingHom.charZero_iff σ.injective).1 inferInstance
  rw [mem_eigSp]
  intro a
  set b := RingOfIntegers.basis E
  have e1 : ∀ k, ρ a (ρ (b k) x) =
      ∑ j, σ ((Algebra.trace ℚ E (dualInt E j * (a : E) * integralBasis E k) : ℚ) : E) •
        ρ (b j) x := by
    intro k
    rw [← Module.End.mul_apply, ← map_mul, ← b.sum_repr (a * b k), map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := repr_eq_trace (a * b k) j
    rw [map_zsmul, mul_assoc, integralBasis_apply]
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul (algebraMap (𝓞 E) E)] at this
    rw [RingOfIntegers.coe_eq_algebraMap, ← this]
    simp [Int.cast_smul_eq_zsmul, b]
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  change ∑ k, σ (dualInt E k) • ρ a (ρ (b k) x) = _
  simp only [e1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← map_mul, mul_comm (a : E), expand_dual (dualInt E j * (a : E)), map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← expand_dual, ← map_mul, Rat.smul_def, mul_comm]
end GlobalTheory.CompanionTheory.Ar.HT.LatBasic
