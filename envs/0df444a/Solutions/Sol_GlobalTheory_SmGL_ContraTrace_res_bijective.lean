-- Prove2me | solution 1 for GlobalTheory.SmGL.ContraTrace.res_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:55:58.232493+00:00
-- url     : https://prove2.me/submissions/55748d4b-7b92-45d2-9a3e-e104f87a2177

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContraAdmissibleTrace
import Theorems.Thm_GlobalTheory_SmGL_ContraTrace_invariant_of_fixed
import Theorems.Thm_GlobalTheory_OpTrace_mem_fixed
import Theorems.Thm_GlobalTheory_SmGL_DualAverage_exists_invariant_form
import Theorems.Thm_GlobalTheory_SmGL_IndDual_dual_ext
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


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
theorem _root_.solution [T2Space G] {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) : Function.Bijective (res π K) := by
  constructor
  · intro l l' h
    refine Subtype.ext (Subtype.ext ?_)
    exact IndDual.dual_ext hπ hK (invariant_of_fixed l) (invariant_of_fixed l')
      fun w hw => LinearMap.congr_fun h ⟨w, hw⟩
  · intro m
    obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend m
    obtain ⟨l, h1, h2⟩ := DualAverage.exists_invariant_form G V π hπ K hK l₀
    have h3 : ∀ g ∈ K, π.dual g l = l := fun g hg => LinearMap.ext fun w => h1 g⁻¹ (inv_mem hg) w
    refine ⟨⟨⟨l, mem_smoothPart_of_nhds (Filter.mem_of_superset (ho.mem_nhds (one_mem K)) h3)⟩,
      mem_fixed.2 fun g hg => Subtype.ext (h3 g hg)⟩, LinearMap.ext fun w => ?_⟩
    exact (h2 _ (mem_fixed.1 w.2)).trans (LinearMap.congr_fun hl₀ w)
end GlobalTheory.SmGL.ContraTrace
