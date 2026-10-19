-- Prove2me | solution 1 for MetricCodes.weightShell_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/62f5e993-6140-44d7-951a-72a8d6d358d9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution (n w : ℕ) :
    weightShell n w =
      ((Finset.univ : Finset (Fin n)).powersetCard w).image wordOfSupport := by
  ext x
  constructor
  · intro hx
    have hw : binaryWeight x = w := (mem_weightShell x).mp hx
    refine Finset.mem_image.mpr
      ⟨wordSupport x, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩,
        wordOfSupport_wordSupport x⟩
    simpa [binaryWeight_eq_card_wordSupport] using hw
  · intro hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_weightShell _).mpr
    rw [binaryWeight_eq_card_wordSupport, wordSupport_wordOfSupport]
    exact (Finset.mem_powersetCard.mp hs).2
end MetricCodes
