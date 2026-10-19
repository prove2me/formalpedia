-- Prove2me | solution 1 for MetricCodes.Johnson.exists_shellCodeNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/41c694e8-6e60-48b0-98ec-1a926f62577a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_shellCodeFamily_nonempty

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution (n w d : ℕ) :
    ∃ C : Finset (BinaryWord n),
      C ⊆ weightShell n w ∧ IsBinaryCode d C ∧
        C.card = shellCodeNumber n w d := by
  obtain ⟨C, hC, hmax⟩ :=
    Finset.exists_mem_eq_sup (shellCodeFamily n w d)
      (shellCodeFamily_nonempty n w d) (fun C => C.card)
  obtain ⟨hweight, hdistance⟩ := (mem_shellCodeFamily C).mp hC
  exact ⟨C, hweight, hdistance, hmax.symm⟩
end MetricCodes.Johnson
