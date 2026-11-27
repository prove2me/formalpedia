-- Prove2me | solution 1 for MohP3.FormalLocal.mem_Psurfk_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:30:10.099454+00:00
-- url     : https://prove2.me/submissions/53b69bc2-82b9-461c-bb3b-d9831b23f59d

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution {g : Sk k} : g ∈ Psurfk k ↔ sigmaS k g = 0 := Iff.rfl
end MohP3.FormalLocal
