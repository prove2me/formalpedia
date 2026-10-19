-- Prove2me | solution 1 for MetricCodes.hammingSphere_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/f971e6fb-e50f-4bc3-a4c9-099e99377946

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_binaryWeight_binaryTranslate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n : ℕ} (x : BinaryWord n) (r : ℕ) :
    hammingSphere x r = (weightShell n r).image (binaryTranslate x) := by
  ext y
  constructor
  · intro hy
    have hd : hammingDist x y = r := (mem_hammingSphere x y).mp hy
    refine Finset.mem_image.mpr
      ⟨binaryTranslate x y, (mem_weightShell _).mpr ?_,
        binaryTranslate_involutive x y⟩
    simpa [binaryWeight_binaryTranslate] using hd
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    apply (mem_hammingSphere _ _).mpr
    rw [← binaryWeight_binaryTranslate, binaryTranslate_involutive]
    exact (mem_weightShell _).mp hz
end MetricCodes
