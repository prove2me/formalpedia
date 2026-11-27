-- Prove2me | solution 1 for MohP3.FormalLocal.Pk_sq_le_Qk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:46:25.447807+00:00
-- url     : https://prove2.me/submissions/9ad63448-96e6-429f-9a35-987517343c98

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
public import Theorems.Thm_MohP3_Gen_P_sq_le_Q


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : Pk k ^ 2 ≤ Qk k := Gen.P_sq_le_Q _ _ _
end MohP3.FormalLocal
