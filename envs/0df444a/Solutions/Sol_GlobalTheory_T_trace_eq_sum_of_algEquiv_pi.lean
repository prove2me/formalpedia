-- Prove2me | solution 1 for GlobalTheory.T.trace_eq_sum_of_algEquiv_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:32.044241+00:00
-- url     : https://prove2.me/submissions/bd0deb20-1f69-4388-bd49-a9e13d4407cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceEqSumCoordsOfAlgEquiv
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceEqSumCoordsOfAlgEquivStatement
import Theorems.Thm_GlobalTheory_trace_eq_sum_coords_of_algEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F K : Type} [Field F] [CommRing K] [Algebra F K] (r : ℕ) (e : K ≃ₐ[F] (Fin r → F)) (k : K), Algebra.trace F K k = ∑ i, e k i := by
  first | exact @GlobalTheory.trace_eq_sum_coords_of_algEquiv | exact GlobalTheory.trace_eq_sum_coords_of_algEquiv | (intros; apply GlobalTheory.trace_eq_sum_coords_of_algEquiv <;> assumption)
end _root_.GlobalTheory.T
