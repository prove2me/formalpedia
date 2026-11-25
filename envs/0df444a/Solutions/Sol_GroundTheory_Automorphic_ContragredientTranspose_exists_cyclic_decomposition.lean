-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.exists_cyclic_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:09.309907+00:00
-- url     : https://prove2.me/submissions/951a1793-761f-4d1e-a0d8-52e73334f507

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_charpoly_smul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
universe u
variable {F : Type u} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (A : Matrix (Fin n) (Fin n) F) :
    ∃ (ι : Type u) (_ : Fintype ι) (q : ι → F[X]), (∀ i, q i ≠ 0) ∧ (∀ i, q i ∣ A.charpoly) ∧
      Nonempty (Module.AEval' (Matrix.toLin' A) ≃ₗ[F[X]] DirectSum ι fun i => F[X] ⧸ F[X] ∙ q i) := by
  classical
  have htors : Module.IsTorsion F[X] (Module.AEval' (Matrix.toLin' A)) :=
    Module.AEval.isTorsion_of_finiteDimensional F (Fin n → F) (Matrix.toLin' A)
  obtain ⟨ι, hι, p, hp, e, ⟨E⟩⟩ := Module.equiv_directSum_of_isTorsion htors
  refine ⟨ι, hι, fun i => p i ^ e i, fun i => pow_ne_zero _ (hp i).ne_zero, fun i => ?_, ⟨E⟩⟩
  set x : DirectSum ι fun i => F[X] ⧸ F[X] ∙ p i ^ e i :=
    DirectSum.of (fun i => F[X] ⧸ F[X] ∙ p i ^ e i) i (Submodule.Quotient.mk 1)
  have h0 : A.charpoly • x = 0 := by
    have := charpoly_smul_eq_zero A (E.symm x)
    rwa [← map_smul, LinearEquiv.map_eq_zero_iff] at this
  rw [← DirectSum.of_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one] at h0
  have h1 := DirectSum.of_injective (β := fun i => F[X] ⧸ F[X] ∙ p i ^ e i) i
    (h0.trans (map_zero _).symm)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 ((Submodule.Quotient.mk_eq_zero _).1 h1)
  exact ⟨c, by rw [← hc, smul_eq_mul, mul_comm]⟩
end GroundTheory.Automorphic.ContragredientTranspose
