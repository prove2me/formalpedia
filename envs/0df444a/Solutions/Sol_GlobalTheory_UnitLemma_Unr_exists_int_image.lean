-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.exists_int_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:06.391939+00:00
-- url     : https://prove2.me/submissions/7cf9d2ff-c694-4c30-8b7f-02ff0c4aaa6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_mem_range_of_val_nonneg
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_algebraMap_nonneg

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
open GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (a : K.O) :
    ∃ b : K'.O, algebraMap K'.O K'.E b = φ (algebraMap K.O K.E a) := by
  apply mem_range_of_val_nonneg
  rw [hU.2.2.1]
  exact val_algebraMap_nonneg K a
end GlobalTheory.UnitLemma.Unr
