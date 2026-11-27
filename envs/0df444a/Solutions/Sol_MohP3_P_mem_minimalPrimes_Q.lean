-- Prove2me | solution 1 for MohP3.P_mem_minimalPrimes_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:32:14.914859+00:00
-- url     : https://prove2.me/submissions/c30aaae5-922f-49ec-bd24-dc4a17830004

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
public import Theorems.Thm_MohP3_P_isPrime
public import Theorems.Thm_MohP3_mem_minimalPrimes_of_radical_eq
public import Theorems.Thm_MohP3_radical_Q


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : P ∈ Q.minimalPrimes :=
  mem_minimalPrimes_of_radical_eq P_isPrime radical_Q
end MohP3
