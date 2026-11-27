-- Prove2me | solution 1 for MohP3.FormalLocal.Psurfk_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:34:21.990342+00:00
-- url     : https://prove2.me/submissions/b710254a-cc64-48bc-bee8-b2ff4ef15fe6

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
theorem _root_.solution : (Psurfk k).IsPrime := RingHom.ker_isPrime (sigmaS k)
end MohP3.FormalLocal
