-- Prove2me | solution 1 for MvPolynomial.RegularFunction.comp_aeval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:40:56.296054+00:00
-- url     : https://prove2.me/submissions/5c07b5db-8456-48b1-bc56-411512f0cdb1

module
public import Mathlib
public import Definitions.Def_JacPoisson_Defs

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
variable {k : Type*} [CommRing k]
variable {σ τ ι : Type*}
open MvPolynomial.RegularFunction
namespace MvPolynomial.RegularFunction
theorem _root_.solution
    {σ τ ι : Type*}
    (F : RegularFunction k σ τ) (G : RegularFunction k τ ι)
    (a : σ → k) : (F.comp G).aeval a = G.aeval (F.aeval a) := by
  ext i
  rw [aeval, comp, MvPolynomial.aeval_bind₁, ←aeval]
  rfl
end MvPolynomial.RegularFunction
