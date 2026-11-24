-- Prove2me | solution 1 for GlobalTheory.ValConjClosure.isClosed_apply_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:29.800222+00:00
-- url     : https://prove2.me/submissions/15685092-132b-48dd-813f-f999c6f8db07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsTopWTopWOfExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsGaloisConjValuationSubringSameTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsConjOverPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
open GlobalTheory GlobalTheory.ValConjClosure
namespace GlobalTheory.ValConjClosure
theorem _root_.solution {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsIntegral F Ω]
    (x : Ω) (T : Set Ω) : IsClosed {σ : Ω ≃ₐ[F] Ω | σ x ∈ T} := by
  let E := IntermediateField.adjoin F ({x} : Set Ω)
  haveI : FiniteDimensional F E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) x)
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' (E.fixingSubgroup : Set (Ω ≃ₐ[F] Ω)), ?_,
    E.fixingSubgroup_isOpen.preimage (continuous_mul_left σ⁻¹), ?_⟩
  · intro τ hτ hT
    apply hσ
    have hfix : (σ⁻¹ * τ) x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x
      (IntermediateField.mem_adjoin_simple_self F x)
    have hinv : ∀ y, σ (σ⁻¹ y) = y := fun y => by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [AlgEquiv.mul_apply] at hfix
    have he : τ x = σ x :=
      calc τ x = σ (σ⁻¹ (τ x)) := (hinv _).symm
        _ = σ x := by rw [hfix]
    change σ x ∈ T
    rw [← he]
    exact hT
  · show σ⁻¹ * σ ∈ E.fixingSubgroup
    rw [inv_mul_cancel]
    exact E.fixingSubgroup.one_mem
end GlobalTheory.ValConjClosure
