-- Prove2me | solution 1 for JacPoisson.isUnit_det_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:03:30.176172+00:00
-- url     : https://prove2.me/submissions/9895cc2b-3bde-47e5-af73-912e8b28f41d

module
public import Definitions.Def_JacPoisson_Defs
public import Definitions.Def_JacPoisson_Main
public import Theorems.Thm_JacPoisson_poissonBracket_eq_mul
public import Theorems.Thm_JacPoisson_jacobian_id

set_option autoImplicit false
@[expose] public section
public section
open JacPoisson
open MvPolynomial Matrix JacobianConjecture
variable {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
namespace JacPoisson
theorem _root_.solution (F : RegularFunction R (l ⊕ l) (l ⊕ l))
    (hF : ∀ v w, poissonBracket (F v) (F w) = poissonBracket (X v) (X w)) :
    IsUnit F.Jacobian.det := by
  have hΩ : F.Jacobianᵀ * (-Matrix.J l (MvPolynomial (l ⊕ l) R)) * F.Jacobian =
      -Matrix.J l (MvPolynomial (l ⊕ l) R) := by
    refine Matrix.ext fun v w => ?_
    have h := hF v w
    rw [poissonBracket_eq_mul, show (X v : MvPolynomial (l ⊕ l) R) =
      RegularFunction.id R (l ⊕ l) v from rfl, show (X w : MvPolynomial (l ⊕ l) R) =
      RegularFunction.id R (l ⊕ l) w from rfl, poissonBracket_eq_mul, jacobian_id] at h
    simpa using h
  have hmem : F.Jacobian ∈ symplecticGroup l (MvPolynomial (l ⊕ l) R) := by
    rw [SymplecticGroup.mem_iff']
    simpa [Matrix.mul_neg, Matrix.neg_mul] using hΩ
  exact SymplecticGroup.symplectic_det hmem
end JacPoisson
