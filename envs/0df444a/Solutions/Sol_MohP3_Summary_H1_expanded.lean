-- Prove2me | solution 1 for MohP3.Summary.H1_expanded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:47:43.897806+00:00
-- url     : https://prove2.me/submissions/8eabb821-7977-46f2-a15e-d84653a6c28b

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
public import Theorems.Thm_MohP3_Gen_H1_expanded
public import Theorems.Thm_MohP3_H1_expanded


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3 MohP3.Summary
namespace MohP3.Summary
theorem _root_.solution : H1 =
    128*x^7*y*z^3 - 272*x^6*y^3*z^2 - 128*x^5*y^5*z^6
    + 120*x^5*y^5*z - 24*x^5 + 16*x^4*y^7*z^5
    + 208*x^4*y^2*z^4 + 40*x^3*y^9*z^4 - 394*x^3*y^4*z^3
    - 144*x^2*y^6*z^7 + 291*x^2*y^6*z^2 + 177*x^2*y*z
    + 90*x*y^8*z^6 + 144*x*y^3*z^5 - 234*x*y^3
    + 81*y^10*z^5 - 162*y^5*z^4 + 81*z^3 :=
  MohP3.H1_expanded
end MohP3.Summary
