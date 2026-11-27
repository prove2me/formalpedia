-- Prove2me | solution 1 for MohP3.HilbertBurch.phi_exact_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:42:03.299491+00:00
-- url     : https://prove2.me/submissions/5b374a5c-a15f-42c1-af80-42230b81a5c8

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_exact_of_signedMinors
public import Theorems.Thm_MohP3_HilbertBurch_mem_span_of_monic_mul
public import Theorems.Thm_MohP3_HilbertBurch_phi_signedMinors
public import Theorems.Thm_MohP3_HilbertBurch_fvec_vecMul_phi
public import Theorems.Thm_MohP3_HilbertBurch_f1_mem_span
public import Theorems.Thm_MohP3_HilbertBurch_g_mem
public import Theorems.Thm_MohP3_HilbertBurch_xEquiv_f1
public import Theorems.Thm_MohP3_HilbertBurch_g_eq_symm
public import Theorems.Thm_MohP3_HilbertBurch_three_g_ne_zero
public import Theorems.Thm_MohP3_HilbertBurch_six_isUnit

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
open MvPolynomial
variable {A : Type*} [CommRing A]
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.HilbertBurch
theorem _root_.solution :
    Function.Injective (Matrix.mulVecLin (phi (X 0) (X 1) (X 2) : Matrix (Fin 4) (Fin 3)
        (MvPolynomial (Fin 3) k))) ∧
      LinearMap.range (Matrix.mulVecLin (phi (X 0) (X 1) (X 2) : Matrix (Fin 4) (Fin 3)
        (MvPolynomial (Fin 3) k))) = LinearMap.ker (rowMap (fvec (X 0) (X 1) (X 2))) := by
  refine exact_of_signedMinors _ _ 6 (six_isUnit k) (phi_signedMinors _ _ _)
    (fvec_vecMul_phi _ _ _) _ _ (g_mem _ _ _) (f1_mem_span _ _ _) (three_g_ne_zero k) ?_
  intro u hu
  rw [g_eq_symm] at hu ⊢
  exact mem_span_of_monic_mul _ _ _ (xEquiv_f1 k) hu
end MohP3.HilbertBurch
