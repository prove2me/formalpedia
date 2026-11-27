-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.mem_lieParabolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:44:38.640097+00:00
-- url     : https://prove2.me/submissions/13352638-99bb-431b-8077-ff478b2b941e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel Iwasawa
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution {A : Matrix (Fin n) (Fin n) F} :
    A ∈ lieParabolic F n β ↔ A.BlockTriangular β :=
  Iff.rfl
end GroundTheory.Automorphic.Measures
