-- Prove2me | solution 1 for MohP3.height_Ppoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:41:26.898686+00:00
-- url     : https://prove2.me/submissions/7808d466-fc54-4c64-8ad9-18fae5ae7876

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
public import Theorems.Thm_MohP3_height_Ppoly_le_two
public import Theorems.Thm_MohP3_two_le_height_Ppoly

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3
theorem _root_.solution : (Ppoly k).height = 2 :=
  le_antisymm (height_Ppoly_le_two k) (two_le_height_Ppoly k)
end MohP3
