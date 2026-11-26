-- Prove2me | solution 1 for MohP3.mem_PsurfK_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:21.564752+00:00
-- url     : https://prove2.me/submissions/ca448ee5-b6aa-4aec-8618-a5ebf913c57e

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
theorem _root_.solution {g : Rk k} : g ∈ PsurfK k ↔ sigmaK k g = 0 := Iff.rfl
end MohP3
