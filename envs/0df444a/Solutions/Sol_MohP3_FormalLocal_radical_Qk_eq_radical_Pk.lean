-- Prove2me | solution 1 for MohP3.FormalLocal.radical_Qk_eq_radical_Pk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:13:42.044262+00:00
-- url     : https://prove2.me/submissions/81d3b091-37d8-4321-be2d-299e92316fdc

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
public import Theorems.Thm_MohP3_Gen_radical_Q_eq_radical_P


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : (Qk k).radical = (Pk k).radical :=
  Gen.radical_Q_eq_radical_P _ _ _
end MohP3.FormalLocal
