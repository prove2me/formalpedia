-- Prove2me | solution 1 for GlobalTheory.EigenSplit.det_sq_eq_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:52:28.362267+00:00
-- url     : https://prove2.me/submissions/e3f46739-208d-4d60-8221-5b884585d2d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul

set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
namespace GlobalTheory.EigenSplit
theorem _root_.solution {O : Type*} [CommRing O] (σ : ι → O →+* R)
    (b b' : Module.Basis ι ℤ O) :
    (Matrix.of fun i j => σ i (b j)).det ^ 2 = (Matrix.of fun i j => σ i (b' j)).det ^ 2 := by
  have h1 : (Matrix.of fun i j => σ i (b' j))
      = (Matrix.of fun i j => σ i (b j)) * (b.toMatrix b').map (Int.castRingHom R) := by
    ext i j
    conv_lhs => rw [Matrix.of_apply, ← b.sum_toMatrix_smul_self b' j]
    simp [Matrix.mul_apply, mul_comm]
  have h2 : (b.toMatrix b').det ^ 2 = 1 := by
    have hu : IsUnit (b.toMatrix b').det := by
      rw [← Module.Basis.det_apply]; exact b.isUnit_det b'
    rcases Int.isUnit_iff.1 hu with h | h <;> simp [h]
  rw [h1, Matrix.det_mul, mul_pow, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_pow, h2]
  simp
end GlobalTheory.EigenSplit
