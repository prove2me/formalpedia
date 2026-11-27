-- Prove2me | solution 1 for MohP3.bot_lt_Psurf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:33:19.794163+00:00
-- url     : https://prove2.me/submissions/14a64bf2-b2f9-4c62-9c7d-c6ad5d36d80d

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
public import Theorems.Thm_MohP3_Psurf_ne_bot

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : (⊥ : Ideal R) < Psurf :=
  lt_of_le_of_ne bot_le (Ne.symm Psurf_ne_bot)
end MohP3
