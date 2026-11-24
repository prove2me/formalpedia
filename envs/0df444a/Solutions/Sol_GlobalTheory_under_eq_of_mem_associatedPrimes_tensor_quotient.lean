-- Prove2me | solution 1 for GlobalTheory.under_eq_of_mem_associatedPrimes_tensor_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:53.711985+00:00
-- url     : https://prove2.me/submissions/6763a91c-c2d4-4ec6-be20-e122908496bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Theorems.Thm_GlobalTheory_under_mem_associatedPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]
variable [Module B M] [IsScalarTower A B M] [Module.Flat A M]
namespace GlobalTheory
theorem _root_.solution (p : Ideal A) [hp : p.IsPrime]
    {q : Ideal B} (hq : q ∈ associatedPrimes B (M ⊗[A] (A ⧸ p))) : q.under A = p := by
  obtain ⟨hq', x, hx⟩ := under_mem_associatedPrimes (A := A) hq
  have key : ∀ a : A, a • x = LinearMap.lTensor M (a • LinearMap.id) x := fun a ↦ by
    rw [LinearMap.lTensor_smul, LinearMap.lTensor_id, LinearMap.smul_apply, LinearMap.id_apply]
  refine le_antisymm (fun a ha ↦ ?_) (fun a ha ↦ ?_)
  · by_contra hap
    rw [hx] at ha
    obtain ⟨n, hn⟩ := ha
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, key] at hn
    have hinj : Function.Injective (a ^ n • LinearMap.id : (A ⧸ p) →ₗ[A] (A ⧸ p)) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      rw [LinearMap.smul_apply, LinearMap.id_apply, Algebra.smul_def, mul_eq_zero,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hz
      exact hz.resolve_left fun h ↦ hap (hp.mem_of_pow_mem n h)
    have hx0 : x = 0 := Module.Flat.lTensor_preserves_injective_linearMap _ hinj
      (hn.trans (map_zero _).symm)
    exact hq'.ne_top (by simp [hx, hx0])
  · rw [hx]
    refine Ideal.le_radical ?_
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, key]
    have : (a • LinearMap.id : (A ⧸ p) →ₗ[A] (A ⧸ p)) = 0 := by
      refine LinearMap.ext fun z ↦ ?_
      simp [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem.2 ha]
    simp [this]
end GlobalTheory
