-- Prove2me | solution 1 for MohP3.H1_mem_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:45:48.364973+00:00
-- url     : https://prove2.me/submissions/1fff8ecd-6381-4533-a47f-803f0ba90829

module
public import Definitions.Def_MohP3_Defs
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_Certificate
public import Theorems.Thm_MohP3_Gen_H1_mem_P


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : H1 ∈ P := Gen.H1_mem_P x y z
end MohP3
