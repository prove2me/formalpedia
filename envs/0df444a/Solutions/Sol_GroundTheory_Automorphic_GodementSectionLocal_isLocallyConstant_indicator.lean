-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.isLocallyConstant_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:45.579133+00:00
-- url     : https://prove2.me/submissions/f6499705-c3c9-4db4-ad2a-a02f94b67fb3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open GroundTheory.LocalField
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
omit [MeasurableSpace F] [BorelSpace F]
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClopen S)
    {f : X → ℂ} (hf : IsLocallyConstant f) : IsLocallyConstant (S.indicator f) := by
  rw [IsLocallyConstant.iff_exists_open] at hf ⊢
  intro x
  obtain ⟨V, hV, hxV, hfV⟩ := hf x
  by_cases hx : x ∈ S
  · refine ⟨V ∩ S, hV.inter hS.isOpen, ⟨hxV, hx⟩, fun y hy ↦ ?_⟩
    rw [Set.indicator_of_mem hy.2, Set.indicator_of_mem hx, hfV y hy.1]
  · refine ⟨V ∩ Sᶜ, hV.inter hS.compl.isOpen, ⟨hxV, hx⟩, fun y hy ↦ ?_⟩
    rw [Set.indicator_of_notMem hy.2, Set.indicator_of_notMem hx]
end GroundTheory.Automorphic.GodementSectionLocal
