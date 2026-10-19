-- Prove2me | solution 1 for MetricCodes.translateLocalizedCode_subset_weightShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/0306d976-7fcf-4259-8e34-d2f80aaf8a9a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n w : ℕ}
    (C : Finset (BinaryWord n)) (z : BinaryWord n) :
    translateLocalizedCode C z w ⊆ weightShell n w := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact (mem_weightShell _).mpr ((mem_localizedCode C z x).mp hx).2
end MetricCodes
