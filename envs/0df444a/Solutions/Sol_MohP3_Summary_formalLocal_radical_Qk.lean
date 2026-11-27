-- Prove2me | solution 1 for MohP3.Summary.formalLocal_radical_Qk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:50:27.783798+00:00
-- url     : https://prove2.me/submissions/e78c415d-0c2c-4951-b60c-e92cd2fd2e95

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
public import Theorems.Thm_MohP3_FormalLocal_formalLocal_radical_Qk


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3 MohP3.Summary
open MohP3.FormalLocal
namespace MohP3.Summary
theorem _root_.solution (k : Type*) [Field k] [CharZero k] :
    (Qk k).radical = RingHom.ker (psi k) :=
  MohP3.FormalLocal.formalLocal_radical_Qk k
end MohP3.Summary
