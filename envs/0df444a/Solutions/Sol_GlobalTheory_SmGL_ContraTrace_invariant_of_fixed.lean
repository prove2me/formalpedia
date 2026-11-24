-- Prove2me | solution 1 for GlobalTheory.SmGL.ContraTrace.invariant_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:40:21.356029+00:00
-- url     : https://prove2.me/submissions/21250f62-1f4a-46b7-8f69-0a499132970d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContraAdmissibleTrace
import Theorems.Thm_GlobalTheory_OpTrace_mem_fixed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.ContraTrace
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.SmGL.ContraTrace
theorem _root_.solution {π : Representation ℂ G V} {K : Subgroup G} (l : fixed (contra π) K)
    (h : G) (hh : h ∈ K) (w : V) : (l.1 : Module.Dual ℂ V) (π h w) = (l.1 : Module.Dual ℂ V) w := by
  have h1 := mem_fixed.1 l.2 h⁻¹ (inv_mem hh)
  conv_rhs => rw [← h1]
  rw [contra_apply, inv_inv]
end GlobalTheory.SmGL.ContraTrace
