-- Prove2me | solution 1 for GlobalTheory.isFractionRing_stalk_of_eq_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:35.479637+00:00
-- url     : https://prove2.me/submissions/6a48e38d-4839-40c6-bdd5-fc6415dc3c26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational

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
theorem _root_.solution [IsIntegral Y] {U : Y.Opens} (hU : IsAffineOpen U)
    (y : Y) (hyU : y ∈ U) (hy : y = genericPoint Y) :
    letI := Y.presheaf.algebra_section_stalk (U := U) ⟨y, hyU⟩
    IsFractionRing Γ(Y, U) (Y.presheaf.stalk y) := by
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  subst hy
  exact functionField_isFractionRing_of_isAffineOpen Y U hU
end _root_.GlobalTheory
end GlobalTheory
