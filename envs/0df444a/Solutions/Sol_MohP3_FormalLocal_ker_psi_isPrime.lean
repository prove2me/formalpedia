-- Prove2me | solution 1 for MohP3.FormalLocal.ker_psi_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:09.372824+00:00
-- url     : https://prove2.me/submissions/8814c31e-768d-4116-9eac-4c27a6ec5c18

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : (RingHom.ker (psi k)).IsPrime := RingHom.ker_isPrime (psi k)
end MohP3.FormalLocal
