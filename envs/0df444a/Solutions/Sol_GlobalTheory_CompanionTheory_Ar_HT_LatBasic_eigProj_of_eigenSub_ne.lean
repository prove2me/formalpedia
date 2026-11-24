-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HT.LatBasic.eigProj_of_eigenSub_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:49:53.291604+00:00
-- url     : https://prove2.me/submissions/0436318a-94e2-4a9b-897d-89ecd1594bea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_LatNormGrLatNeZeroOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_mem_eigSp
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_eigProj_mem
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
theorem _root_.solution {ρ : 𝓞 E →+* Module.End K V} {σ : E →+* K} {χ : 𝓞 E →+* K}
    (h : σ.comp (algebraMap (𝓞 E) E) ≠ χ) {x : V} (hx : x ∈ GlobalTheory.EigenSplit.eigenSub ρ χ) :
    eigProj ρ σ x = 0 := by
  have h1 := eigProj_mem ρ σ x
  have h2 : eigProj ρ σ x ∈ GlobalTheory.EigenSplit.eigenSub ρ χ := by
    simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply,
      GlobalTheory.EigenSplit.mem_eigenSub.1 hx]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hx)
  by_contra hne
  refine h (RingHom.ext fun a => ?_)
  exact smul_left_injective K hne
    ((mem_eigSp.1 h1 a).symm.trans (GlobalTheory.EigenSplit.mem_eigenSub.1 h2 a))
end GlobalTheory.CompanionTheory.Ar.HT.LatBasic
