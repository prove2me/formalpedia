-- Prove2me | solution 1 for MohP3.P_radical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:24:08.900001+00:00
-- url     : https://prove2.me/submissions/232c5e98-fd70-432a-9fd5-625ab40d1644

module
public import Definitions.Def_MohP3_Kernel
public import Definitions.Def_MohP3_Global
public import Theorems.Thm_MohP3_P_isPrime

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : P.radical = P := P_isPrime.radical
end MohP3
