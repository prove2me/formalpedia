-- Prove2me | solution 1 for MetricCodes.Hamming.codeNumber_real_le_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/feab1ad9-1bb5-4ff8-a7e6-04ed72993634

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_exists_codeNumber

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {n d : ℕ} {B : ℝ}
    (h : ∀ C : Finset (BinaryWord n),
      MetricCodes.IsBinaryCode d C → (C.card : ℝ) ≤ B) :
    (codeNumber n d : ℝ) ≤ B := by
  obtain ⟨C, hC, hmax⟩ := exists_codeNumber n d
  simpa [hmax] using h C hC
end MetricCodes.Hamming
