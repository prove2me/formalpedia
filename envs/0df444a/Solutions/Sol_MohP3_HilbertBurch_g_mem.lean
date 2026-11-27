-- Prove2me | solution 1 for MohP3.HilbertBurch.g_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:41:17.385533+00:00
-- url     : https://prove2.me/submissions/a476cff6-334b-4349-8666-e7177323193b

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_g_certificate
public import Theorems.Thm_MohP3_HilbertBurch_f1_mem_span
public import Theorems.Thm_MohP3_HilbertBurch_f2_mem_span
public import Theorems.Thm_MohP3_HilbertBurch_f4_mem_span

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
theorem _root_.solution (x y z : A) : 3 * (y ^ 5 - z ^ 4) ∈ Ideal.span (Set.range (fvec x y z)) := by
  rw [g_certificate]
  exact sub_mem (sub_mem (Ideal.mul_mem_left _ _ (f1_mem_span x y z))
    (Ideal.mul_mem_left _ _ (f2_mem_span x y z))) (Ideal.mul_mem_left _ _ (f4_mem_span x y z))
end MohP3.HilbertBurch
