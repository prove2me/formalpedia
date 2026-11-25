-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.jacquetMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:22.227832+00:00
-- url     : https://prove2.me/submissions/9fc58adb-fc23-4434-b23a-242d6e8dc38d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic

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
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) F) V)
variable {π} {V' : Type*} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ (GL (Fin n) F) V'}
  {V'' : Type*} [AddCommGroup V''] [Module ℂ V''] {π'' : Representation ℂ (GL (Fin n) F) V''}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (f : Representation.IntertwiningMap π π') (v : V) :
    jacquetMap F n β f (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ (f v) := rfl
end GroundTheory.Automorphic.Parabolic
