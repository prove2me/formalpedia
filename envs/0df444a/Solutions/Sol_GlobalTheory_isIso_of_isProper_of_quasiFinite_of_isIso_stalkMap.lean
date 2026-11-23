-- Prove2me | solution 1 for GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:26.029145+00:00
-- url     : https://prove2.me/submissions/b4272b5a-d832-43cb-9b1a-b0a922a8cf23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Theorems.Thm_GlobalTheory_isOpenImmersion_of_quasiFinite_of_isIso_stalkMap

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
theorem _root_.solution (f : X ⟶ Y) [IsProper f]
    [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y] [IsDominant f]
    [IsIso (f.stalkMap (genericPoint X))]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f := by
  haveI := _root_.GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap f hY
  haveI : Epi f.base := by
    rw [TopCat.epi_iff_surjective, ← Set.range_eq_univ]
    refine IsClopen.eq_univ ⟨f.isClosedMap.isClosed_range, f.isOpenEmbedding.isOpen_range⟩ ?_
    exact Set.range_nonempty _
  exact IsOpenImmersion.isIso f
end _root_.GlobalTheory
end GlobalTheory
