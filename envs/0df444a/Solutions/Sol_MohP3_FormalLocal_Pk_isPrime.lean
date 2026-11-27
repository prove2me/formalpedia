-- Prove2me | solution 1 for MohP3.FormalLocal.Pk_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:38:51.171003+00:00
-- url     : https://prove2.me/submissions/9aa9cdf6-0112-4630-b828-b443e0139a37

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Theorems.Thm_MohP3_FormalLocal_ker_psi
public import Theorems.Thm_MohP3_FormalLocal_ker_psi_isPrime


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : (Pk k).IsPrime := ker_psi k ▸ ker_psi_isPrime k
end MohP3.FormalLocal
