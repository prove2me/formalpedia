-- Prove2me | solution 1 for MohP3.Summary.hilbertBurch_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:49:13.564229+00:00
-- url     : https://prove2.me/submissions/1817b6f8-7857-485b-b260-71fbf2c7ea34

module
public import Definitions.Def_MohP3_Defs
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Independence
public import Definitions.Def_MohP3_Closure
public import Definitions.Def_MohP3_Kernel
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Definitions.Def_MohP3_HeightK
public import Definitions.Def_MohP3_HilbertBurch
public import Definitions.Def_MohP3
public import Theorems.Thm_MohP3_HilbertBurch_hilbertBurch_exact


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3 MohP3.Summary
open MohP3.HilbertBurch
namespace MohP3.Summary
theorem _root_.solution (k : Type*) [Field k] [CharZero k] :
    Function.Injective (phiMap k) ∧
      Function.Exact (phiMap k) (genMap k) ∧
      Function.Exact (genMap k) (Ideal.Quotient.mkₐ k (J k)) ∧
      Function.Surjective (Ideal.Quotient.mkₐ k (J k)) :=
  MohP3.HilbertBurch.hilbertBurch_exact k
end MohP3.Summary
