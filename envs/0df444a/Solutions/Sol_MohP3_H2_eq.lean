-- Prove2me | solution 1 for MohP3.H2_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:45:26.180538+00:00
-- url     : https://prove2.me/submissions/c1bdc195-1e36-4e21-b400-26dc1cb3f5d3

module
public import Definitions.Def_MohP3_Defs
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_Certificate
public import Theorems.Thm_MohP3_Gen_H2_eq


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : H2 = (-12*y)*f1 + (27*x)*f2 + kappa*f3 := Gen.H2_eq x y z
end MohP3
