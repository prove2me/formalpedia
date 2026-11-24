-- Prove2me | solution 1 for GlobalTheory.OpenSubgroupScheme.mem_range_iff_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:21:20.167588+00:00
-- url     : https://prove2.me/submissions/9a50a6f8-5a08-428c-bddb-a6ba70be03bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIsoOfIsOpenImmersionOfGeometricallyConnected

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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.OpenSubgroupScheme
variable {K : Type} [Field K] {Ga G : Over (Spec (CommRingCat.of K))}
namespace GlobalTheory.OpenSubgroupScheme
theorem _root_.solution (p : Ga ⟶ G) [IsOpenImmersion p.left] (x : 𝟙_ _ ⟶ G) :
    x.left (IsLocalRing.closedPoint K) ∈ Set.range p.left ↔ ∃ a : 𝟙_ _ ⟶ Ga, a ≫ p = x := by
  constructor
  · intro h
    have hr : Set.range x.left ⊆ Set.range p.left := by
      rintro _ ⟨z, rfl⟩
      have : z = IsLocalRing.closedPoint K :=
        Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _
      rw [this]; exact h
    refine ⟨Over.homMk (IsOpenImmersion.lift p.left x.left hr) ?_, ?_⟩
    · rw [← Over.w p, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w x
    · ext1
      simp
  · rintro ⟨a, rfl⟩
    exact ⟨a.left (IsLocalRing.closedPoint K), rfl⟩
end GlobalTheory.OpenSubgroupScheme
