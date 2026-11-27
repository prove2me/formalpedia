-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.isCompactOperator_restrict_integrated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:44:19.57193+00:00
-- url     : https://prove2.me/submissions/673a286d-bf95-4f4a-a5ac-df3cbfb9f033

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_MultiplicityOne_OpenSubgroupRep
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_comp_integrated_of_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_subtypeL_mem_intertwiners


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology Function
open GroundTheory GroundTheory.Automorphic
noncomputable section
namespace GroundTheory.Automorphic
namespace UnitaryRep
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (μ : Measure G) {V : Submodule ℂ H} [CompleteSpace V]
    (hV : IsClosed (V : Set H)) (hinv : π.IsInvariant V) (g : G →₁[μ] ℂ)
    (h : IsCompactOperator (π.integrated μ g)) :
    IsCompactOperator ((π.restrict V hinv).integrated μ g) := by
  have e := UnitaryRep.comp_integrated_of_mem_intertwiners (π.restrict V hinv) μ
    (UnitaryRep.subtypeL_mem_intertwiners π V hinv) g
  have hc : IsCompactOperator (V.subtypeL ∘L (π.restrict V hinv).integrated μ g) := by
    rw [e]
    exact h.comp_clm _
  have hmem : ∀ v, (fun v => (V.subtypeL ∘L (π.restrict V hinv).integrated μ g) v) v ∈ V :=
    fun v => ((π.restrict V hinv).integrated μ g v).2
  have hfun : (((π.restrict V hinv).integrated μ g : V →L[ℂ] V) : V → V) =
      Set.codRestrict (fun v => (V.subtypeL ∘L (π.restrict V hinv).integrated μ g) v) V hmem :=
    funext fun v => Subtype.ext rfl
  rw [hfun]
  exact hc.codRestrict hmem hV
end UnitaryRep
end GroundTheory.Automorphic
