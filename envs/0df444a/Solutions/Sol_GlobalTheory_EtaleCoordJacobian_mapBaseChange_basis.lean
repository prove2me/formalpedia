-- Prove2me | solution 1 for GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:11.133798+00:00
-- url     : https://prove2.me/submissions/537a68fc-3c63-4ffa-a6c3-9957205ebbf8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KaehlerDifferential TensorProduct
open GlobalTheory GlobalTheory.EtaleCoordJacobian
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B]
open KaehlerDifferential TensorProduct
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B]
namespace GlobalTheory.EtaleCoordJacobian
namespace _root_.GlobalTheory.EtaleCoordJacobian
theorem _root_.solution (i : I) :
    mapBaseChange R (MvPolynomial I R) B (((mvPolynomialBasis R I).baseChange B) i) =
      D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i)) := by
  rw [Module.Basis.baseChange_apply, mvPolynomialBasis_apply, mapBaseChange_tmul, one_smul,
    map_D]
end _root_.GlobalTheory.EtaleCoordJacobian
end GlobalTheory.EtaleCoordJacobian
