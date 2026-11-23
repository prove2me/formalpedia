-- Prove2me | solution 1 for GlobalTheory.range_subset_opens_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:55.175501+00:00
-- url     : https://prove2.me/submissions/098d6790-1214-43fd-a24d-a5c2514614d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S)
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {B : CommRingCat.{u}} [IsLocalRing B] (s : Spec B ⟶ S)
    {U : S.Opens} (h : s (closedPoint B) ∈ U) : Set.range s ⊆ U := by
  rintro _ ⟨y, rfl⟩
  exact ((specializes_closedPoint y).map s.base.hom.continuous).mem_open U.isOpen h
end _root_.GlobalTheory
end GlobalTheory
