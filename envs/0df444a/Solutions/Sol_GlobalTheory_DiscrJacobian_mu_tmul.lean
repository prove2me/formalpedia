-- Prove2me | solution 1 for GlobalTheory.DiscrJacobian.mu_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:47.502855+00:00
-- url     : https://prove2.me/submissions/1ff4e22f-0f16-4373-b6eb-4296b85b23c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (s : S) (w : B) :
    _root_.GlobalTheory.DiscrJacobian.mu R S B (s ⊗ₜ w) = algebraMap S B s * w := by
  simp [_root_.GlobalTheory.DiscrJacobian.mu]
end _root_.GlobalTheory.DiscrJacobian
end GlobalTheory.DiscrJacobian
