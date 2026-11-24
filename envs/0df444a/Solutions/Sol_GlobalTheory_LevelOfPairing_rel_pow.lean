-- Prove2me | solution 1 for GlobalTheory.LevelOfPairing.rel_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:41:30.957086+00:00
-- url     : https://prove2.me/submissions/6130d89c-0606-4b5e-8116-ec714b7ea883

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsLevelStructureOfWeilPairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.LevelOfPairing
variable {G U : Type} [Group G] [CommGroup U] {R : G → G → U → Prop} {M : ℕ}
namespace GlobalTheory.LevelOfPairing
theorem _root_.solution (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {x y : G} {c : U}
    (h₁ : R 1 y 1) (h : R x y c) (a : ℕ) : R (x ^ a) y (c ^ a) := by
  induction a with
  | zero => simpa using h₁
  | succ a ih => rw [pow_succ, pow_succ]; exact hm _ _ _ _ _ ih h
end GlobalTheory.LevelOfPairing
