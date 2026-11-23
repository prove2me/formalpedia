-- Prove2me | solution 1 for GlobalTheory.BaseChangeComponents.isLocalization_incl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:10.290859+00:00
-- url     : https://prove2.me/submissions/37c392f2-9983-484c-b642-5486524fd730

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegrallyClosedQuotientOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsNoetherianRingTensor
import Theorems.Thm_GlobalTheory_BaseChangeComponents_incl_tmul
import Theorems.Thm_GlobalTheory_BaseChangeComponents_incl_injective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BaseChangeComponents.incl_tmul

set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.BaseChangeComponents
variable {K Ω : Type} (F : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
namespace GlobalTheory.BaseChangeComponents
theorem _root_.solution (R : Subalgebra K Ω)
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) :
    @IsLocalization _ _ (denoms F R) (F ⊗[K] Ω) _ (incl F R).toAlgebra :=
  by
    letI := (incl F R).toAlgebra
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.1 hy
      have hr0 : (r : Ω) ≠ 0 := by
        have := nonZeroDivisors.ne_zero hr
        simpa using this
      have hval : algebraMap (F ⊗[K] R) (F ⊗[K] Ω)
          (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := R) r) =
            Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω) (r : Ω) := by
        show incl F R ((1 : F) ⊗ₜ r) = (1 : F) ⊗ₜ (r : Ω)
        exact incl_tmul F R 1 r
      rw [hval]
      exact (IsUnit.mk0 _ hr0).map _
    · intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨(0, 1), by simp⟩
      | tmul a w =>
        obtain ⟨c, hc, b, hb, hb0, hw⟩ := hR w
        have hbR : (⟨b, hb⟩ : R) ∈ nonZeroDivisors R :=
          mem_nonZeroDivisors_of_ne_zero (fun h => hb0 (congrArg Subtype.val h))
        refine ⟨(a ⊗ₜ ⟨c, hc⟩, ⟨(1 : F) ⊗ₜ ⟨b, hb⟩, Submonoid.mem_map_of_mem _ hbR⟩), ?_⟩
        show (a ⊗ₜ w) * incl F R ((1 : F) ⊗ₜ ⟨b, hb⟩) = incl F R (a ⊗ₜ ⟨c, hc⟩)
        rw [incl_tmul, incl_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        exact congrArg _ hw
      | add x y hx hy =>
        obtain ⟨⟨x₁, s₁⟩, h₁⟩ := hx
        obtain ⟨⟨x₂, s₂⟩, h₂⟩ := hy
        refine ⟨(x₁ * s₂ + x₂ * s₁, s₁ * s₂), ?_⟩
        simp only [Submonoid.coe_mul, map_mul, map_add] at h₁ h₂ ⊢
        linear_combination (algebraMap (F ⊗[K] R) (F ⊗[K] Ω) s₂) * h₁ +
          (algebraMap (F ⊗[K] R) (F ⊗[K] Ω) s₁) * h₂
    · intro x y h
      exact ⟨1, congrArg _ (incl_injective F R h)⟩
end GlobalTheory.BaseChangeComponents
