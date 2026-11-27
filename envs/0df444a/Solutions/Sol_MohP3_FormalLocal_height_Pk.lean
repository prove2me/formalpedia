-- Prove2me | solution 1 for MohP3.FormalLocal.height_Pk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:44:22.139832+00:00
-- url     : https://prove2.me/submissions/67e4b3db-4312-4b96-a6bd-4ab225a7dc18

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Theorems.Thm_MohP3_FormalLocal_height_Pk_le_two
public import Theorems.Thm_MohP3_FormalLocal_two_le_height_Pk

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : (Pk k).height = 2 :=
  le_antisymm (height_Pk_le_two k) (two_le_height_Pk k)
end MohP3.FormalLocal
