-- Prove2me | solution 1 for MetricCodes.Hamming.exists_codeNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/b714a3d4-2f36-4dc7-8506-7fd1202a2cd4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_mem_validCodes
import Theorems.Thm_MetricCodes_Hamming_validCodes_nonempty

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution (n d : ℕ) :
    ∃ C : Finset (BinaryWord n),
      MetricCodes.IsBinaryCode d C ∧ C.card = codeNumber n d := by
  obtain ⟨C, hC, hmax⟩ :=
    Finset.exists_mem_eq_sup (validCodes n d)
      (validCodes_nonempty n d) (fun C => C.card)
  exact ⟨C, (mem_validCodes C).1 hC, hmax.symm⟩
end MetricCodes.Hamming
