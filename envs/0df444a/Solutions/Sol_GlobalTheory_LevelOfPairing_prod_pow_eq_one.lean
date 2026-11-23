-- Prove2me | solution 1 for GlobalTheory.LevelOfPairing.prod_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:19.502869+00:00
-- url     : https://prove2.me/submissions/82212146-e7f2-4992-8d91-647af1704fdf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsLevelStructureOfWeilPairing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


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
theorem _root_.solution (cm : ∀ a b : G, Commute a b) {n : ℕ} (y : Fin n → G) (hy : ∀ i, y i ^ M = 1)
    (a : Fin n → ℕ) : (List.ofFn fun i => y i ^ a i).prod ^ M = 1 := by
  refine List.prod_induction (fun y => y ^ M = 1) (fun x y hx hy => ?_) (one_pow _) fun z hz => ?_
  · rw [(cm x y).mul_pow, hx, hy, _root_.mul_one]
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hz
    rw [← pow_mul, Nat.mul_comm, pow_mul, hy, one_pow]
end GlobalTheory.LevelOfPairing
