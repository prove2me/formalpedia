-- Prove2me | solution 1 for MohP3.PsurfK_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:35:11.770493+00:00
-- url     : https://prove2.me/submissions/51487f1c-a0fb-4da3-9840-808190b92f77

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution : (PsurfK k).IsPrime := RingHom.ker_isPrime (sigmaK k)
end MohP3
