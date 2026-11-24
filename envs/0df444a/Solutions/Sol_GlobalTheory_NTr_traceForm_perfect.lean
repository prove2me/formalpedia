-- Prove2me | solution 1 for GlobalTheory.NTr.traceForm_perfect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:44:33.594604+00:00
-- url     : https://prove2.me/submissions/cb525237-bc84-4a75-bc5f-bb8285f48dd8

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect
import Theorems.Thm_GlobalTheory_NTr_trace_eq
import Theorems.Thm_GlobalTheory_NTr_exists_half
import Theorems.Thm_GlobalTheory_NTr_small_of_trace_small

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NTr
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
namespace GlobalTheory.NTr
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) ∧ (∃ e : E, ‖e‖ ≤ 1 ∧ e + star e = 1) ∧ ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ‖Algebra.trace F E (e * y)‖ < 1) → ‖y‖ < 1 :=
  fun F E _ _ _ _ _ => ⟨trace_eq, exists_half F, small_of_trace_small⟩
end GlobalTheory.NTr
