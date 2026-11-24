-- Prove2me | solution 1 for GlobalTheory.exists_isAffineOpen_le_of_isQProjOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:42:40.45528+00:00
-- url     : https://prove2.me/submissions/2da7afa7-be47-4d3f-bd89-e19e183de43e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsAffineOpenLeOfIsQProjOver
import Theorems.Thm_GlobalTheory_FiniteSubsetsInAffineOpens_of_isQProjOver
import Theorems.Thm_GlobalTheory_OrbitsInAffineOpens_of_isQProjOver


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s →
      ∀ (F : Set X) (U : X.Opens), F.Finite → F ⊆ U →
        ∃ V : X.Opens, IsAffineOpen V ∧ F ⊆ V ∧ V ≤ U := by
  intro R _ X s hs F U hF hFU
  haveI := FiniteSubsetsInAffineOpens.of_isQProjOver hs
  exact FiniteSubsetsInAffineOpens.exists_isAffineOpen_le hF U hFU
end GlobalTheory
