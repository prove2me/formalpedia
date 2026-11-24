-- Prove2me | solution 1 for GlobalTheory.T.exists_integer_spanning_family_of_unramifiedExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:21:09.119731+00:00
-- url     : https://prove2.me/submissions/a504dfdc-32ef-429c-9d95-684ec69e9e4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExtStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_int_basis_of_unr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O, algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i) := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr | exact GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr | (intros; apply GlobalTheory.UnitLemma.Unr.exists_int_basis_of_unr <;> assumption)
end _root_.GlobalTheory.T
