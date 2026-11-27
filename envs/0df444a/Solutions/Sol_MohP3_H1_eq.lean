-- Prove2me | solution 1 for MohP3.H1_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:45:22.153233+00:00
-- url     : https://prove2.me/submissions/115bc90f-6f0e-42b7-a1e3-5d10302fae44

module
public import Definitions.Def_MohP3_Defs
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_Certificate
public import Theorems.Thm_MohP3_Gen_H1_eq


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : H1 = (-24*x)*f1 + ell*f3 + 81*f4 := Gen.H1_eq x y z
end MohP3
