-- Prove2me | solution 1 for GlobalTheory.EtaleCoordJacobian.etale_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:40.323835+00:00
-- url     : https://prove2.me/submissions/ad0480c6-ca41-4507-9105-ee4caebbf90a

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
theorem _root_.solution [Finite I] [Algebra.Smooth R B]
    (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i))) :
    Algebra.Etale (MvPolynomial I R) B := by
  set bc := (mvPolynomialBasis R I).baseChange B
  have hmap : mapBaseChange R (MvPolynomial I R) B = (bc.equiv b (Equiv.refl I)).toLinearMap :=
    bc.ext fun i => by
      rw [_root_.GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
        Equiv.refl_apply, hb]
  have hinj : Function.Injective (mapBaseChange R (MvPolynomial I R) B) := by
    rw [hmap]; exact (bc.equiv b (Equiv.refl I)).injective
  have hsurj : Function.Surjective (mapBaseChange R (MvPolynomial I R) B) := by
    rw [hmap]; exact (bc.equiv b (Equiv.refl I)).surjective
  have hΩ : Subsingleton Ω[B⁄MvPolynomial I R] := by
    refine ⟨fun x y => ?_⟩
    have hx : ∀ z : Ω[B⁄MvPolynomial I R], z = 0 := fun z => by
      obtain ⟨w, rfl⟩ := map_surjective R (MvPolynomial I R) B z
      obtain ⟨v, rfl⟩ := hsurj w
      exact (exact_mapBaseChange_map R (MvPolynomial I R) B).apply_apply_eq_zero v
    rw [hx x, hx y]
  have hH : Subsingleton (Algebra.H1Cotangent (MvPolynomial I R) B) := by
    haveI : Subsingleton (Algebra.H1Cotangent R B) :=
      Algebra.FormallySmooth.subsingleton_h1Cotangent
    refine ⟨fun x y => ?_⟩
    have hx : ∀ z : Algebra.H1Cotangent (MvPolynomial I R) B, z = 0 := fun z => by
      have h1 : Algebra.H1Cotangent.δ R (MvPolynomial I R) B z = 0 :=
        hinj (((Algebra.H1Cotangent.exact_δ_mapBaseChange R _ B).apply_apply_eq_zero z).trans
          (map_zero _).symm)
      obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R (MvPolynomial I R) B z).mp h1
      rw [Subsingleton.elim w 0, map_zero]
    rw [hx x, hx y]
  haveI : Algebra.FormallyEtale (MvPolynomial I R) B := Algebra.FormallyEtale.mk hΩ hH
  haveI : Algebra.FinitePresentation (MvPolynomial I R) B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ B
  exact Algebra.Etale.mk
end _root_.GlobalTheory.EtaleCoordJacobian
end GlobalTheory.EtaleCoordJacobian
