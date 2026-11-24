-- Prove2me | solution 1 for GlobalTheory.exists_notMem_of_ncard_lt_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:45:48.999052+00:00
-- url     : https://prove2.me/submissions/fc12f7fe-6750-4c5c-a7db-708a2a1c6458

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPairAvoidingSmallSets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {H : Type} [Finite H] (S : Set H)
    (h : S.ncard < Nat.card H) : ∃ x : H, x ∉ S := by
  by_contra hx
  have hS : S = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    by_contra hx'
    exact hx ⟨x, hx'⟩
  rw [hS, Set.ncard_univ] at h
  exact lt_irrefl _ h
end GlobalTheory
