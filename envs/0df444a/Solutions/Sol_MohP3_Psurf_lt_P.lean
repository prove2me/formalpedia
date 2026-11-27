-- Prove2me | solution 1 for MohP3.Psurf_lt_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:34:49.868719+00:00
-- url     : https://prove2.me/submissions/60eca292-62af-4149-98b1-aed3371b8094

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
public import Theorems.Thm_MohP3_Psurf_le_P
public import Theorems.Thm_MohP3_f4_notMem_Psurf
public import Theorems.Thm_MohP3_Gen_f4_mem
public import Theorems.Thm_MohP3_f4_mem


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : Psurf < P :=
  lt_of_le_of_ne Psurf_le_P (fun h => f4_notMem_Psurf (h ▸ f4_mem))
end MohP3
