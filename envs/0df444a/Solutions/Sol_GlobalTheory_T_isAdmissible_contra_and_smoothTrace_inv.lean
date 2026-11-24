-- Prove2me | solution 1 for GlobalTheory.T.isAdmissible_contra_and_smoothTrace_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:29:08.83317+00:00
-- url     : https://prove2.me/submissions/b488991d-43c3-4f30-97e5-a72f708147a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContraAdmissibleTrace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContraAdmissibleTraceStatement
import Theorems.Thm_GlobalTheory_SmGL_ContraTrace_contra_admissible_trace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → IsAdmissible (contra π) ∧ ∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace (contra π) μ f = smoothTrace π μ (fun g => f g⁻¹) := by
  first | exact @GlobalTheory.SmGL.ContraTrace.contra_admissible_trace | exact GlobalTheory.SmGL.ContraTrace.contra_admissible_trace | (intros; apply GlobalTheory.SmGL.ContraTrace.contra_admissible_trace <;> assumption)
end _root_.GlobalTheory.T
