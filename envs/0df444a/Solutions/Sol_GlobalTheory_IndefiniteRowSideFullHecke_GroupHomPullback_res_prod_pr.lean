-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.res_prod_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:39:40.485743+00:00
-- url     : https://prove2.me/submissions/db1a7ff8-7638-47b1-ba40-a6d2851cc0c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_GroupHomPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
variable {X X' Y Y' : Scheme.{u}}
variable {K : Type u} [Fintype K]
namespace GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) {U : K → X.Opens} {V W : Y.Opens}
    (h : ∀ k, V ≤ φ k ⁻¹ᵁ U k) (h' : W ≤ V) (a : ∀ k, Γ(X, U k)ˣ) :
    res h' (∏ k, pr (φ k) (h k) (a k) ^ ε k) = ∏ k, pr (φ k) (h'.trans (h k)) (a k) ^ ε k := by
  simp only [map_prod, map_zpow, res_pr]
end GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback
