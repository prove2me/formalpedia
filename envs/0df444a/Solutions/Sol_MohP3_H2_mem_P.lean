-- Prove2me | solution 1 for MohP3.H2_mem_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:46:09.175581+00:00
-- url     : https://prove2.me/submissions/739ca0c6-889b-4ef8-81d1-44f3b20dd5fb

module
public import Definitions.Def_MohP3_Defs
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_Certificate
public import Theorems.Thm_MohP3_Gen_H2_mem_P


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : H2 ∈ P := Gen.H2_mem_P x y z
end MohP3
