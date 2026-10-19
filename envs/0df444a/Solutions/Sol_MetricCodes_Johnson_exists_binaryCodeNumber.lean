-- Prove2me | solution 1 for MetricCodes.Johnson.exists_binaryCodeNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/29e63792-605c-4153-8bac-97c690d180ef

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_binaryCodeFamily_nonempty

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution (n d : ℕ) :
    ∃ C : Finset (BinaryWord n),
      IsBinaryCode d C ∧ C.card = binaryCodeNumber n d := by
  obtain ⟨C, hC, hmax⟩ :=
    Finset.exists_mem_eq_sup (binaryCodeFamily n d)
      (binaryCodeFamily_nonempty n d) (fun C => C.card)
  exact ⟨C, (mem_binaryCodeFamily C).mp hC, hmax.symm⟩
end MetricCodes.Johnson
