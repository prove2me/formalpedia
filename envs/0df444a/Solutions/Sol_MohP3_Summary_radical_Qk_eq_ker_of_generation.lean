-- Prove2me | solution 1 for MohP3.Summary.radical_Qk_eq_ker_of_generation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:50:01.290371+00:00
-- url     : https://prove2.me/submissions/f1108631-723c-4d84-b4b1-6044c958af35

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
public import Theorems.Thm_MohP3_FormalLocal_radical_Qk_eq_ker_of_generation


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3 MohP3.Summary
open MohP3.FormalLocal
namespace MohP3.Summary
theorem _root_.solution (k : Type*) [Field k] [CharZero k]
    (hgen : Generation k) : (Qk k).radical = RingHom.ker (psi k) :=
  MohP3.FormalLocal.radical_Qk_eq_ker_of_generation k hgen
end MohP3.Summary
