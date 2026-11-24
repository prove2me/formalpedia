-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.exists_trace_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:33.64606+00:00
-- url     : https://prove2.me/submissions/cc611478-74c5-4f65-b26f-7f799465eb5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtension
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_trace_unit_of_span
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_int_basis_of_unr


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
theorem _root_.solution (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) :
    ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧
      @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a :=
  exists_trace_unit_of_span K K' d φ hU (exists_int_basis_of_unr K K' d φ hU)
end GlobalTheory.UnitLemma.Unr
