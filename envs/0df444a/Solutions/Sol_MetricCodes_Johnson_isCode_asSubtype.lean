-- Prove2me | solution 1 for MetricCodes.Johnson.isCode_asSubtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/405f4e8c-d96b-4f06-84e2-94986518f584

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_words_asSubtype

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {n w d : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w)
    (hC : IsBinaryCode d C) :
    IsCode d (asSubtype C hweight) := by
  unfold IsCode
  rw [words_asSubtype]
  exact hC
end MetricCodes.Johnson
