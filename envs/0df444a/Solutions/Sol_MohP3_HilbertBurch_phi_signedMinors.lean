-- Prove2me | solution 1 for MohP3.HilbertBurch.phi_signedMinors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:38:43.48684+00:00
-- url     : https://prove2.me/submissions/17cdbda8-d53a-4ce9-babb-5bcbf929c96f

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_phi_minors
public import Theorems.Thm_MohP3_HilbertBurch_rowMap_apply
attribute [local simp] MohP3.HilbertBurch.rowMap_apply

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
open MvPolynomial
variable {A : Type*} [CommRing A]
namespace MohP3.HilbertBurch
theorem _root_.solution (x y z : A) (i : Fin 4) :
    (-1) ^ (i : ℕ) * maximalMinor (phi x y z) i = 6 * fvec x y z i := by
  rw [phi_minors]
  fin_cases i <;> simp [fvec]
  ring
end MohP3.HilbertBurch
