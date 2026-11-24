-- Prove2me | solution 1 for GlobalTheory.existsUnique_bialgHom_of_compatible_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:07:19.281845+00:00
-- url     : https://prove2.me/submissions/b6767f89-4e25-4f52-9d68-222afb225534

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Theorems.Thm_GlobalTheory_eq_of_forall_one_tmul_quotient_eq
import Theorems.Thm_GlobalTheory_existsUnique_algHom_of_compatible_tensor
import Theorems.Thm_GlobalTheory_comul_one_tmul_eq_distribBaseChange

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
variable {A B : Type*} [Ring A] [Ring B] [Bialgebra R A] [Bialgebra R B]
namespace GlobalTheory
theorem _root_.solution [Module.Finite R B]
    (f : ∀ n : ℕ, (R ⧸ I ^ n) ⊗[R] A →ₐc[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)
    (hf : ∀ n x, adicTensorTransition I B n (f (n + 1) x) = f n (adicTensorTransition I A n x)) :
    ∃! g : A →ₐc[R] B, ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := by
  obtain ⟨g, hg, hu⟩ := existsUnique_algHom_of_compatible_tensor I (A := A) (B := B)
    (fun n ↦ (f n : (R ⧸ I ^ n) ⊗[R] A →ₐ[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)) hf
  replace hg : ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := hg
  refine ⟨.ofAlgHom g ?_ ?_, hg, fun g' hg' ↦ BialgHom.ext fun a ↦ congr($(hu g' hg') a)⟩
  · refine AlgHom.ext fun a ↦ eq_of_forall_one_tmul_quotient_eq I fun n ↦ ?_
    have := CoalgHomClass.counit_comp_apply (f n) (1 ⊗ₜ a)
    rw [← hg, TensorProduct.counit_tmul, TensorProduct.counit_tmul] at this
    apply (TensorProduct.rid R _).injective
    simpa using this
  · refine AlgHom.ext fun a ↦ eq_of_forall_one_tmul_quotient_eq I fun n ↦ ?_
    have := CoalgHomClass.map_comp_comul_apply (f n) (1 ⊗ₜ a)
    rw [← hg, comul_one_tmul_eq_distribBaseChange, comul_one_tmul_eq_distribBaseChange] at this
    apply (AlgebraTensorModule.distribBaseChange R (R ⧸ I ^ n) B B).injective
    simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
    rw [← this]
    induction (Coalgebra.comul a : A ⊗[R] A) with
    | zero => simp
    | tmul x y => simp [hg]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
end GlobalTheory
