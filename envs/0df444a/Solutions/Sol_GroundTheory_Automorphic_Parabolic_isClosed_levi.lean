-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isClosed_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:23:21.920603+00:00
-- url     : https://prove2.me/submissions/fead11eb-d90a-44c2-b4d0-ac70a8fac634

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution : IsClosed (levi F n β : Set (GL (Fin n) F)) := by
  rw [levi, Subgroup.coe_inf]
  exact (Measures.isClosed_blockUpper F n β).inter
    (Measures.isClosed_blockUpper F n (OrderDual.toDual ∘ β))
end GroundTheory.Automorphic.Parabolic
