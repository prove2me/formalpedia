-- Prove2me | solution 1 for GlobalTheory.isIso_of_isIntegralHom_of_isIso_stalkMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:49.448798+00:00
-- url     : https://prove2.me/submissions/280604fd-b420-4bf5-923f-8c32cff5d5f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Theorems.Thm_GlobalTheory_isIso_fromNormalization_of_birational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
open GlobalTheory
universe u
variable {X Y : Scheme.{u}}
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
variable {X Y : Scheme.{u}}
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (f : X ⟶ Y) [IsIntegralHom f]
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f := by
  haveI := _root_.GlobalTheory.isIso_fromNormalization_of_birational f hY
  rw [← f.toNormalization_fromNormalization]
  infer_instance
end _root_.GlobalTheory
end GlobalTheory
