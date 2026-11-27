-- Prove2me | solution 1 for MohP3.FormalLocal.Psurfk_lt_Pk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:40:30.560121+00:00
-- url     : https://prove2.me/submissions/eaf035a9-6a23-4f5d-98d1-fc2903be0416

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Theorems.Thm_MohP3_FormalLocal_Psurfk_le_Pk
public import Theorems.Thm_MohP3_FormalLocal_f4S_notMem_Psurfk
public import Theorems.Thm_MohP3_Gen_f4_mem


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : Psurfk k < Pk k :=
  lt_of_le_of_ne (Psurfk_le_Pk k)
    (fun h => f4S_notMem_Psurfk k (h ▸ Gen.f4_mem (xs k) (ys k) (zs k)))
end MohP3.FormalLocal
