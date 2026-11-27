-- Prove2me | solution 1 for MohP3.FormalLocal.bot_lt_Psurfk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:35:53.241326+00:00
-- url     : https://prove2.me/submissions/034f9e8c-a7f8-4817-b35b-cc1733279504

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Theorems.Thm_MohP3_FormalLocal_Psurfk_ne_bot

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : (⊥ : Ideal (Sk k)) < Psurfk k :=
  lt_of_le_of_ne bot_le (Ne.symm (Psurfk_ne_bot k))
end MohP3.FormalLocal
