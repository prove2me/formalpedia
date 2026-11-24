-- Prove2me | solution 1 for GlobalTheory.existsUnique_algEquiv_of_compatible_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:07:17.660014+00:00
-- url     : https://prove2.me/submissions/7a610cb3-99e9-43dd-bf80-a0bc9cb0c5f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Theorems.Thm_GlobalTheory_eq_of_forall_one_tmul_quotient_eq
import Theorems.Thm_GlobalTheory_existsUnique_algHom_of_compatible_tensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct
variable {R : Type*} [CommRing R] (I : Ideal R)
variable [IsNoetherianRing R] [IsAdicComplete I R]
variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
namespace GlobalTheory
theorem _root_.solution [Module.Finite R A] [Module.Finite R B]
    (f : ∀ n : ℕ, (R ⧸ I ^ n) ⊗[R] A ≃ₐ[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)
    (hf : ∀ n x, adicTensorTransition I B n (f (n + 1) x) = f n (adicTensorTransition I A n x)) :
    ∃! g : A ≃ₐ[R] B, ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := by
  obtain ⟨g, hg, hu⟩ := existsUnique_algHom_of_compatible_tensor I (fun n ↦ (f n).toAlgHom) hf
  obtain ⟨g', hg', -⟩ := existsUnique_algHom_of_compatible_tensor I
    (fun n ↦ (f n).symm.toAlgHom) fun n x ↦ by
      apply (f n).injective
      simp [← hf]
  have hA : g'.comp g = .id _ _ := AlgHom.ext fun a ↦
    eq_of_forall_one_tmul_quotient_eq I fun n ↦ by simp [hg, hg']
  have hB : g.comp g' = .id _ _ := AlgHom.ext fun a ↦
    eq_of_forall_one_tmul_quotient_eq I fun n ↦ by simp [hg, hg']
  exact ⟨.ofAlgHom g g' hB hA, hg,
    fun e he ↦ AlgEquiv.coe_algHom_injective (hu e.toAlgHom he)⟩
end GlobalTheory
