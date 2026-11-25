-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.withDensity_map_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:10.423199+00:00
-- url     : https://prove2.me/submissions/636ab663-428e-4134-9e31-9d44c794343d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJParabolicFubini

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory Measure Topology Set
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α]
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]
variable {β : Fin n → α}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y)
    (ν : Measure X) {f : Y → ℝ≥0∞} (hf : Measurable f) :
    (map e ν).withDensity f = map e (ν.withDensity (f ∘ e)) := by
  ext S hS
  rw [withDensity_apply _ hS, map_apply e.measurable hS, withDensity_apply _ (e.measurable hS),
    setLIntegral_map hS hf e.measurable]
  rfl
end GroundTheory.Automorphic.GodementJacquet
