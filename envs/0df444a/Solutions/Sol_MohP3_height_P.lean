-- Prove2me | solution 1 for MohP3.height_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:37:39.572185+00:00
-- url     : https://prove2.me/submissions/687033ca-40c3-4f7b-b5c1-a9fae60e7c6e

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
public import Theorems.Thm_MohP3_height_P_le_two
public import Theorems.Thm_MohP3_two_le_height_P

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : P.height = 2 := le_antisymm height_P_le_two two_le_height_P
end MohP3
