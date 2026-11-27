-- Prove2me | solution 1 for MohP3.bot_lt_PsurfK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:37:06.221144+00:00
-- url     : https://prove2.me/submissions/2a904e21-e1d8-40ba-9b68-04f37fa6e731

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
public import Theorems.Thm_MohP3_PsurfK_ne_bot

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution : (⊥ : Ideal (Rk k)) < PsurfK k :=
  lt_of_le_of_ne bot_le (Ne.symm (PsurfK_ne_bot k))
end MohP3
