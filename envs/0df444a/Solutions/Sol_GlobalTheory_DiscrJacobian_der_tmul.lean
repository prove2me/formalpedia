-- Prove2me | solution 1 for GlobalTheory.DiscrJacobian.der_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:22.136973+00:00
-- url     : https://prove2.me/submissions/3425e096-811f-45b0-a9c1-839d77c47575

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
import Theorems.Thm_GlobalTheory_DiscrJacobian_mu_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DiscrJacobian.mu_tmul

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
theorem _root_.solution (D : Derivation R S S) (s : S) (w : B) :
    _root_.GlobalTheory.DiscrJacobian.der D (s ⊗ₜ[R] w) = algebraMap S B (D s) * w := by
  simp [_root_.GlobalTheory.DiscrJacobian.der]
end _root_.GlobalTheory.DiscrJacobian
end GlobalTheory.DiscrJacobian
