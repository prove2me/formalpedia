-- Prove2me | solution 1 for GlobalTheory.DiscrJacobian.der_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:27:42.862115+00:00
-- url     : https://prove2.me/submissions/b5291dfe-d996-4e10-9a64-3b94e46c4ba0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
import Theorems.Thm_GlobalTheory_DiscrJacobian_mu_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_der_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DiscrJacobian.mu_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.der_tmul

set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscrJacobian
open scoped TensorProduct
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B]
open scoped TensorProduct
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B]
namespace GlobalTheory.DiscrJacobian
namespace _root_.GlobalTheory.DiscrJacobian
theorem _root_.solution (D : Derivation R S S) (y z : S ⊗[R] B) :
    _root_.GlobalTheory.DiscrJacobian.der D (y * z) =
      _root_.GlobalTheory.DiscrJacobian.mu R S B y * _root_.GlobalTheory.DiscrJacobian.der D z +
        _root_.GlobalTheory.DiscrJacobian.mu R S B z * _root_.GlobalTheory.DiscrJacobian.der D y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => rw [add_mul, map_add, hy, hy', map_add, map_add]; ring
  | tmul s w =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => rw [mul_add, map_add, hz, hz', map_add, map_add]; ring
    | tmul t v =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [_root_.GlobalTheory.DiscrJacobian.der_tmul, _root_.GlobalTheory.DiscrJacobian.mu_tmul,
        Derivation.leibniz, smul_eq_mul, map_add, map_mul]
      ring
end _root_.GlobalTheory.DiscrJacobian
end GlobalTheory.DiscrJacobian
