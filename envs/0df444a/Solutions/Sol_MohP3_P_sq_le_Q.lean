-- Prove2me | solution 1 for MohP3.P_sq_le_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:13:07.587717+00:00
-- url     : https://prove2.me/submissions/090d267a-3d8d-4026-9b00-35cdf8dabfa7

module
public import Definitions.Def_MohP3_Defs
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_Certificate
public import Theorems.Thm_MohP3_Gen_P_sq_le_Q


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : P ^ 2 ≤ Q := Gen.P_sq_le_Q x y z
end MohP3
