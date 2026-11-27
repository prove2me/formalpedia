-- Prove2me | solution 1 for MohP3.Summary.Q_le_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:48:34.028932+00:00
-- url     : https://prove2.me/submissions/78d6b753-d5bb-445f-96ee-0bdcc9c452c0

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
public import Theorems.Thm_MohP3_Gen_Q_le_P
public import Theorems.Thm_MohP3_Q_le_P


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3 MohP3.Summary
namespace MohP3.Summary
theorem _root_.solution : Q ≤ P := MohP3.Q_le_P
end MohP3.Summary
