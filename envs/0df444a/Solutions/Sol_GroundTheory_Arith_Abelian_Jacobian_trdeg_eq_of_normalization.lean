-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_normalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:30.212486+00:00
-- url     : https://prove2.me/submissions/19909d37-1515-4109-9266-3dffa05a96c2

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian GroundTheory.Arith.Abelian.Jacobian
open Algebra Cardinal
universe u
variable (k : Type u) [Field k] {A : Type u} [CommRing A] [Algebra k A]
namespace GroundTheory.Arith.Abelian.Jacobian
theorem _root_.solution [IsDomain A] {s : ℕ} (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinj : Function.Injective g) (hint : g.IsIntegral) : trdeg k A = s := by
  let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have _ : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have _ : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun x => hint x⟩
  have _ : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have h := trdeg_add_eq k (MvPolynomial (Fin s) k) (A := A)
  rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero (R := MvPolynomial (Fin s) k) (A := A)] at h
  simpa using h.symm
end GroundTheory.Arith.Abelian.Jacobian
