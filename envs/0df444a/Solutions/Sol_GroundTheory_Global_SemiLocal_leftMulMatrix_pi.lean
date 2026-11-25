-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.leftMulMatrix_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:29:35.311802+00:00
-- url     : https://prove2.me/submissions/4b8a8123-cf12-4648-9b03-04ddd93c991e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Matrix
noncomputable section
open GroundTheory.Global.SemiLocal
variable {R : Type*} [Field R] {ι : Type*} [Fintype ι] {S : ι → Type*} [∀ i, CommRing (S i)]
  [∀ i, Algebra R (S i)] [∀ i, Module.Finite R (S i)]
omit [∀ i, Module.Finite R (S i)]
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    [∀ i, DecidableEq (κ i)] (b : ∀ i, Basis (κ i) R (S i)) (x : ∀ i, S i) :
    Algebra.leftMulMatrix (Pi.basis b) x =
      blockDiagonal' fun i ↦ Algebra.leftMulMatrix (b i) (x i) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Algebra.leftMulMatrix_eq_repr_mul, blockDiagonal'_apply', Pi.basis_repr, Pi.basis_apply]
  by_cases h : i = j
  · subst h
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  · simp [h]
end GroundTheory.Global.SemiLocal
