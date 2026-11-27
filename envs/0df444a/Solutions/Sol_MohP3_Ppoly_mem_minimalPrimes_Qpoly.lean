-- Prove2me | solution 1 for MohP3.Ppoly_mem_minimalPrimes_Qpoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:38:19.000924+00:00
-- url     : https://prove2.me/submissions/4badd4b7-7853-4dca-be96-ec7296eb6f23

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
public import Theorems.Thm_MohP3_Ppoly_isPrime
public import Theorems.Thm_MohP3_global_radical_k
public import Theorems.Thm_MohP3_mem_minimalPrimes_of_radical_eq


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3
theorem _root_.solution : Ppoly k ∈ (Qpoly k).minimalPrimes :=
  mem_minimalPrimes_of_radical_eq (Ppoly_isPrime k) (global_radical_k k)
end MohP3
