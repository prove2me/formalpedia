-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.mem_lieLevi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:52.749098+00:00
-- url     : https://prove2.me/submissions/19a453bb-24eb-4e22-86f8-99c0c57566e6

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
variable (F n) (β : Fin n → α)
variable {F n β}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution {A : Matrix (Fin n) (Fin n) F} :
    A ∈ lieLevi F n β ↔ ∀ i j, β i ≠ β j → A i j = 0 :=
  Iff.rfl
end GroundTheory.Automorphic.GodementJacquet
