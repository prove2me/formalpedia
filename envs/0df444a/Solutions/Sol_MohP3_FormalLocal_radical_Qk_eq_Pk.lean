-- Prove2me | solution 1 for MohP3.FormalLocal.radical_Qk_eq_Pk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:38:53.04501+00:00
-- url     : https://prove2.me/submissions/902301ae-7161-41da-87d0-5e9b58dbc21c

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Theorems.Thm_MohP3_FormalLocal_formalLocal_radical_Qk
public import Theorems.Thm_MohP3_FormalLocal_ker_psi


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : (Qk k).radical = Pk k := by
  rw [formalLocal_radical_Qk, ker_psi]
end MohP3.FormalLocal
