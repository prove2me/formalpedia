-- Prove2me | solution 1 for MetricCodes.translateLocalizedCode_isBinaryCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/d01c20ed-55f4-488b-9a38-221863793de6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_hammingDist_binaryTranslate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n d w : ℕ}
    (C : Finset (BinaryWord n)) (z : BinaryWord n)
    (hC : IsBinaryCode d C) :
    IsBinaryCode d (translateLocalizedCode C z w) := by
  intro x hx y hy hxy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  rw [hammingDist_binaryTranslate]
  apply hC ((mem_localizedCode C z u).mp hu).1
    ((mem_localizedCode C z v).mp hv).1
  intro huv
  exact hxy (congrArg (binaryTranslate z) huv)
end MetricCodes
