-- Prove2me | solution 1 for GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:14.801852+00:00
-- url     : https://prove2.me/submissions/d82b0521-fe17-4f54-8346-f41e0f7344c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Theorems.Thm_GlobalTheory_EtaleCoordJacobian_mapBaseChange_basis

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
theorem _root_.solution [Finite I] [Algebra.Etale (MvPolynomial I R) B] :
    (∃ b : Module.Basis I B Ω[B⁄R],
      ∀ i, b i = D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i))) ∧
      Algebra.Smooth R B := by
  haveI : Algebra.Smooth R (MvPolynomial I R) := Algebra.Smooth.mk
  refine ⟨⟨((mvPolynomialBasis R I).baseChange B).map
    (tensorKaehlerEquivOfFormallyEtale R (MvPolynomial I R) B), fun i => ?_⟩,
    Algebra.Smooth.comp R (MvPolynomial I R) B⟩
  rw [Module.Basis.map_apply, ← _root_.GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis]
  rfl
end _root_.GlobalTheory.EtaleCoordJacobian
end GlobalTheory.EtaleCoordJacobian
