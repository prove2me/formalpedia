-- Prove2me | solution 1 for GlobalTheory.LevelOfPairing.rel_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:41:29.5678+00:00
-- url     : https://prove2.me/submissions/2c3f498a-cf1a-4cc8-9836-7d19bada2e41

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
theorem _root_.solution (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, R x y c)
    (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {y : G} (hy : y ^ M = 1) :
    R 1 y 1 := by
  obtain ⟨c, hc, hc'⟩ := hu 1 y (one_pow _) hy
  have h := hm _ _ _ _ _ hc hc
  rw [_root_.mul_one] at h
  have e : c * c = c := hc' _ h
  have : c = 1 := by simpa using e
  exact this ▸ hc
end GlobalTheory.LevelOfPairing
