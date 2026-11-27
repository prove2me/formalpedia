-- Prove2me | solution 1 for MohP3.radical_Q_eq_radical_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:46:18.59546+00:00
-- url     : https://prove2.me/submissions/d6b5992d-137b-4c23-badf-aca1f5ff88e4

module
public import Definitions.Def_MohP3_Defs
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_Certificate
public import Theorems.Thm_MohP3_Gen_radical_Q_eq_radical_P


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : Q.radical = P.radical := Gen.radical_Q_eq_radical_P x y z
end MohP3
