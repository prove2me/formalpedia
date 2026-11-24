-- Prove2me | solution 1 for GlobalTheory.TopForm.exists_algHom_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:28:15.865797+00:00
-- url     : https://prove2.me/submissions/51cd823c-6eea-447a-b7ef-d571d7acef09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
namespace GlobalTheory.TopForm
theorem _root_.solution {φ : M →ₗ[A] N} (hφ : IsBaseChange B φ) :
    ∃ F : ExteriorAlgebra B N →ₐ[B] B ⊗[A] ExteriorAlgebra A M,
      ∀ m, F (ExteriorAlgebra.ι B (φ m)) = 1 ⊗ₜ ExteriorAlgebra.ι A m := by
  let f : N →ₗ[B] B ⊗[A] ExteriorAlgebra A M :=
    hφ.lift ((TensorProduct.mk A B _ 1).comp (ExteriorAlgebra.ι A))
  have hf (m : M) : f (φ m) = 1 ⊗ₜ ExteriorAlgebra.ι A m := hφ.lift_eq _ m
  have anti (n n' : N) : f n * f n' + f n' * f n = 0 := by
    induction n using hφ.inductionOn with
    | zero => simp
    | smul s n h => rw [map_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, h, smul_zero]
    | add a b ha hb => rw [map_add, add_mul, mul_add, add_add_add_comm, ha, hb, add_zero]
    | tmul m =>
      induction n' using hφ.inductionOn with
      | zero => simp
      | smul s n h => rw [map_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, h, smul_zero]
      | add a b ha hb => rw [map_add, add_mul, mul_add, add_add_add_comm, ha, hb, add_zero]
      | tmul m' =>
        rw [hf, hf, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          ← TensorProduct.tmul_add, ExteriorAlgebra.ι_add_mul_swap, TensorProduct.tmul_zero]
  have sq (n : N) : f n * f n = 0 := by
    induction n using hφ.inductionOn with
    | zero => simp
    | smul s n h => rw [map_smul, smul_mul_assoc, mul_smul_comm, h, smul_zero, smul_zero]
    | add a b ha hb =>
      rw [map_add, add_mul, mul_add, mul_add, ha, hb, zero_add, add_zero, anti]
    | tmul m =>
      rw [hf, Algebra.TensorProduct.tmul_mul_tmul, ExteriorAlgebra.ι_sq_zero,
        TensorProduct.tmul_zero]
  exact ⟨ExteriorAlgebra.lift B ⟨f, sq⟩, fun m => by rw [ExteriorAlgebra.lift_ι_apply, hf]⟩
end GlobalTheory.TopForm
