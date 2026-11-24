-- Prove2me | solution 1 for GlobalTheory.T.nonempty_equiv_of_smoothTrace_eq_admissible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:55.407822+00:00
-- url     : https://prove2.me/submissions/62c6a565-ef96-4930-9b44-07eb56c073da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonemptyEquivOfSmoothTraceEqAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonemptyEquivOfSmoothTraceEqAdmissibleStatement
import Theorems.Thm_GlobalTheory_CharIndep_nonempty_equiv_of_smoothTrace_eq


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
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G W), IsAdmissible π → IsAdmissible π' → π.IsIrreducible → π'.IsIrreducible → (∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace π μ f = smoothTrace π' μ f) → Nonempty (π.Equiv π') := by
  first | exact @GlobalTheory.CharIndep.nonempty_equiv_of_smoothTrace_eq | exact GlobalTheory.CharIndep.nonempty_equiv_of_smoothTrace_eq | (intros; apply GlobalTheory.CharIndep.nonempty_equiv_of_smoothTrace_eq <;> assumption)
end _root_.GlobalTheory.T
