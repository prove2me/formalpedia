-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HT.LatBasic.eigProj_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:32:24.161217+00:00
-- url     : https://prove2.me/submissions/5219ddb8-e444-40cf-b506-b80cc998ef8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_LatNormGrLatNeZeroOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_mem_eigSp
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
theorem _root_.solution {ρ : 𝓞 E →+* Module.End K V} {σ : E →+* K} {x : V} (hx : x ∈ eigSp ρ σ) :
    eigProj ρ σ x = x := by
  rw [mem_eigSp] at hx
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul]
  rw [← Finset.sum_smul]
  have : ∑ k, σ (dualInt E k) * σ ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    rw [← map_one σ, ← sum_dualInt_mul, map_sum]
    simp
  rw [this, one_smul]
end GlobalTheory.CompanionTheory.Ar.HT.LatBasic
