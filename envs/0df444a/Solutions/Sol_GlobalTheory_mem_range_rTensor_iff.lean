-- Prove2me | solution 1 for GlobalTheory.mem_range_rTensor_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:50.051795+00:00
-- url     : https://prove2.me/submissions/e337a4f6-bbdf-47b6-9375-1666005dde2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_isTorsionFree_of_isLocalizedModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable {K}
variable (p : Ideal A) [p.IsPrime] (B : Type*) [CommRing B] [Algebra A B]
  [IsLocalization.AtPrime B p] [Algebra B K] [IsScalarTower A B K]
namespace GlobalTheory
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module A M] (v : K ⊗[A] M) :
    v ∈ LinearMap.range ((IsScalarTower.toAlgHom A B K).toLinearMap.rTensor M) ↔
      ∃ s, s ∉ p ∧ s • v ∈ LinearMap.range (TensorProduct.mk A K M 1) := by
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨⟨m, s⟩, e⟩ := IsLocalizedModule.surj p.primeCompl (TensorProduct.mk A B M 1) w
    refine ⟨s, s.2, m, ?_⟩
    rw [← map_smul]
    change _ = LinearMap.rTensor M _ (s • w)
    rw [e]
    simp
  · rintro ⟨s, hs, m, e⟩
    have := isTorsionFree_of_isLocalizedModule (TensorProduct.mk A K M 1)
    have hs0 : s ≠ 0 := fun h => hs (h ▸ p.zero_mem)
    refine ⟨IsLocalization.mk' B (1 : A) (⟨s, hs⟩ : p.primeCompl) ⊗ₜ m,
      smul_right_injective _ hs0 ?_⟩
    simp only
    rw [← e, ← map_smul, TensorProduct.smul_tmul', Algebra.smul_def,
      IsLocalization.mk'_spec' B (1 : A) (⟨s, hs⟩ : p.primeCompl)]
    simp
end GlobalTheory
