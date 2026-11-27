-- Prove2me | solution 1 for MohP3.HilbertBurch.fvec_vecMul_phi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:38:43.962742+00:00
-- url     : https://prove2.me/submissions/c4348148-3bf0-460d-a496-e3dcdff9c98e

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_phi_relations

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
theorem _root_.solution (x y z : A) : fvec x y z ᵥ* phi x y z = 0 := phi_relations x y z
end MohP3.HilbertBurch
