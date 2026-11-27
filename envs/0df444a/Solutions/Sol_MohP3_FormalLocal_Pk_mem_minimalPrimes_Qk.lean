-- Prove2me | solution 1 for MohP3.FormalLocal.Pk_mem_minimalPrimes_Qk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:40:51.471123+00:00
-- url     : https://prove2.me/submissions/c65043e0-a965-46ad-9c20-fd6a757cfe4b

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Theorems.Thm_MohP3_FormalLocal_Pk_isPrime
public import Theorems.Thm_MohP3_FormalLocal_radical_Qk_eq_Pk
public import Theorems.Thm_MohP3_mem_minimalPrimes_of_radical_eq


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : Pk k ∈ (Qk k).minimalPrimes :=
  mem_minimalPrimes_of_radical_eq (Pk_isPrime k) (radical_Qk_eq_Pk k)
end MohP3.FormalLocal
