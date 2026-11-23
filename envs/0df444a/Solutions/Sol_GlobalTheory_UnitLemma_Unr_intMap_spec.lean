-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.intMap_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:25.598939+00:00
-- url     : https://prove2.me/submissions/20ad89ce-0331-466a-973c-6920d0bf9708

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtension
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_int_image


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
theorem _root_.solution (hU : IsUnrExt K K' d φ) (a : K.O) :
    algebraMap K'.O K'.E (intMap hU a) = φ (algebraMap K.O K.E a) :=
  Classical.choose_spec (exists_int_image hU a)
end GlobalTheory.UnitLemma.Unr
