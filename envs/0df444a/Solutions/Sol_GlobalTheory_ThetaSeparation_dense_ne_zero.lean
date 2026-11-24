-- Prove2me | solution 1 for GlobalTheory.ThetaSeparation.dense_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:41:26.8658+00:00
-- url     : https://prove2.me/submissions/9046cfe2-ce60-4c3f-b749-177c4d8167db

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesPoints
import Theorems.Thm_GlobalTheory_SCV_eqOn_of_eqOn_open


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaSeparation
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory.ThetaSeparation
namespace _root_.GlobalTheory.ThetaSeparation
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {f : E → ℂ} (hf : Differentiable ℂ f) (h0 : ∃ x, f x ≠ 0) :
    Dense {x | f x ≠ 0} := by
  by_contra hd
  obtain ⟨x₀, hx₀⟩ := h0
  rw [dense_iff_inter_open] at hd
  simp only [not_forall] at hd
  obtain ⟨U, hUo, hUne, hU⟩ := hd
  have hEq : Set.EqOn f (fun _ => (0 : ℂ)) Set.univ :=
    _root_.GlobalTheory.SCV.eqOn_of_eqOn_open (g := fun _ => (0 : ℂ)) isOpen_univ isPreconnected_univ
      hf.differentiableOn (differentiableOn_const 0) hUo hUne (Set.subset_univ _)
      (fun y hy => by
        by_contra hne
        exact hU ⟨y, hy, hne⟩)
  exact hx₀ (hEq (Set.mem_univ x₀))
end _root_.GlobalTheory.ThetaSeparation
end GlobalTheory.ThetaSeparation
