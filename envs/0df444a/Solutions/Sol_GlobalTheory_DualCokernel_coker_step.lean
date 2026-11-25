-- Prove2me | solution 1 for GlobalTheory.DualCokernel.coker_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:25:38.936273+00:00
-- url     : https://prove2.me/submissions/470cf8df-5235-4629-b860-029a2e636553

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Theorems.Thm_GlobalTheory_DualCokernel_extZero_coker
import Theorems.Thm_GlobalTheory_DualCokernel_eq_zero_of_extZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R]
variable [IsLocalRing R]
variable [IsNoetherianRing R]
namespace GlobalTheory.DualCokernel
theorem _root_.solution (ϖ : R) (hϖ : ϖ ∈ maximalIdeal R) {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module R D₀] [AddCommGroup D₁] [Module R D₁] [AddCommGroup D₂] [Module R D₂]
    [Module.Finite R D₁] (β : D₂ →ₗ[R] D₁) (α : D₁ →ₗ[R] D₀) (hαβ : ∀ x, α (β x) = 0)
    (hD₀ : IsSMulRegular D₀ ϖ) (n : ℕ) (hE₀ : ∀ j < n + 1, ExtZero (R := R) D₀ j)
    (hQ : IsSMulRegular (D₁ ⧸ LinearMap.range β) ϖ)
    (hE : ∀ j < n + 2, ExtZero (R := R) (D₁ ⧸ LinearMap.range β) j)
    (h₁ : ∀ p : Ideal R, p.IsPrime → ϖ ∈ p → p ≠ maximalIdeal R →
      ∃ s, s ∉ p ∧ ∀ x, α x = 0 → s • x ∈ LinearMap.range β)
    (h₀ : ∀ p : Ideal R, p.IsPrime → ϖ ∈ p → p ≠ maximalIdeal R →
      ∃ s, s ∉ p ∧ ∀ x, ϖ • x ∈ LinearMap.range α → s • x ∈ LinearMap.range α) :
    IsSMulRegular (D₀ ⧸ LinearMap.range α) ϖ ∧
      ∀ j < n + 1, ExtZero (R := R) (D₀ ⧸ LinearMap.range α) j := by
  let μ : (D₁ ⧸ LinearMap.range β) →ₗ[R] (D₁ ⧸ LinearMap.range β) := ϖ • LinearMap.id
  have hμ : ExtZero (R := R) ((D₁ ⧸ LinearMap.range β) ⧸ LinearMap.range μ) 0 :=
    extZero_coker μ _ hQ (Submodule.mkQ_surjective _) μ.exact_map_mkQ_range 0
      (hE 1 (by omega)) (hE 0 (by omega))
  have hker : LinearMap.ker α ≤ LinearMap.range β := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R)
      (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _) fun x hx => ?_
    have h1 := eq_zero_of_extZero hμ
      ((LinearMap.range μ).mkQ ((LinearMap.range β).mkQ x)) fun p hp hm => by
        by_cases hϖp : ϖ ∈ p
        · obtain ⟨s, hs, hs'⟩ := h₁ p hp hϖp hm
          refine ⟨s, hs, ?_⟩
          rw [← map_smul, ← map_smul, Submodule.mkQ_apply (LinearMap.range β),
            (Submodule.Quotient.mk_eq_zero _).2 (hs' x hx), map_zero]
        · refine ⟨ϖ, hϖp, ?_⟩
          rw [← map_smul]
          exact (Submodule.Quotient.mk_eq_zero _).2 ⟨_, rfl⟩
    obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).1 h1
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨y, hy⟩ : ϖ • z - x ∈ LinearMap.range β := (Submodule.Quotient.eq _).1 hz
    have hz0 : α z = 0 := by
      have := hαβ y
      rw [hy, map_sub, LinearMap.mem_ker.mp hx, sub_zero, map_smul] at this
      exact hD₀ (this.trans (smul_zero ϖ).symm)
    have : x = -β y + ϖ • z := by rw [hy]; abel
    rw [this]
    exact Submodule.add_mem_sup (neg_mem ⟨y, rfl⟩) (Submodule.smul_mem_smul hϖ hz0)
  have hle : LinearMap.range β ≤ LinearMap.ker α := by
    rintro _ ⟨y, rfl⟩
    exact hαβ y
  have hE' : ∀ j < n + 1, ExtZero (R := R) (D₀ ⧸ LinearMap.range α) j := fun j hj =>
    extZero_coker ((LinearMap.range β).liftQ α hle) (LinearMap.range α).mkQ
      (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ hker))
      (Submodule.mkQ_surjective _)
      (by rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_liftQ]) j
      (hE _ (by omega)) (hE₀ j hj)
  refine ⟨IsSMulRegular.of_right_eq_zero_of_smul fun x hx => ?_, hE'⟩
  refine eq_zero_of_extZero (hE' 0 (by omega)) x fun p hp hm => ?_
  by_cases hϖp : ϖ ∈ p
  · obtain ⟨s, hs, hs'⟩ := h₀ p hp hϖp hm
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    exact ⟨s, hs, (Submodule.Quotient.mk_eq_zero _).2
      (hs' x ((Submodule.Quotient.mk_eq_zero _).1 hx))⟩
  · exact ⟨ϖ, hϖp, hx⟩
end GlobalTheory.DualCokernel
