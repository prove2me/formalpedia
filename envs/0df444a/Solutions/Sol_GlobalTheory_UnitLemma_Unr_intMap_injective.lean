-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.intMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:29.815911+00:00
-- url     : https://prove2.me/submissions/c2636487-7cf7-4d41-9d7c-a34cc51f4763

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtension
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_intMap_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (hU : IsUnrExt K K' d φ) : Function.Injective (intMap hU) := by
  intro a b h
  apply IsFractionRing.injective K.O K.E
  apply φ.injective
  rw [← intMap_spec hU, ← intMap_spec hU, h]
end GlobalTheory.UnitLemma.Unr
