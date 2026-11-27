-- Prove2me | solution 1 for MohP3.FormalLocal.Qk_le_Pk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:46:24.931642+00:00
-- url     : https://prove2.me/submissions/788d83ed-1674-4694-9b45-a9a9c5e3db20

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
public import Theorems.Thm_MohP3_Gen_Q_le_P


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : Qk k ≤ Pk k := Gen.Q_le_P _ _ _
end MohP3.FormalLocal
