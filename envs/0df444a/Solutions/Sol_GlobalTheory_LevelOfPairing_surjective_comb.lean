-- Prove2me | solution 1 for GlobalTheory.LevelOfPairing.surjective_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:21.579875+00:00
-- url     : https://prove2.me/submissions/357b4913-c4a7-4143-9508-4220b29e234b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsLevelStructureOfWeilPairing
import Theorems.Thm_GlobalTheory_LevelOfPairing_prod_pow_eq_one
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
theorem _root_.solution (cm : ∀ a b : G, Commute a b) (hM : M ≠ 0) {n : ℕ} (y : Fin n → G)
    (hy : ∀ i, y i ^ M = 1) (hcard : Nat.card {x : G // x ^ M = 1} = M ^ n)
    (hinj : ∀ c c' : Fin n → Fin M,
      (List.ofFn fun i => y i ^ (c i : ℕ)).prod = (List.ofFn fun i => y i ^ (c' i : ℕ)).prod → c = c')
    (z : G) (hz : z ^ M = 1) : ∃ c : Fin n → Fin M, (List.ofFn fun i => y i ^ (c i : ℕ)).prod = z := by
  let f : (Fin n → Fin M) → {x : G // x ^ M = 1} := fun c => ⟨_, prod_pow_eq_one cm y hy fun i => (c i : ℕ)⟩
  have : Finite {x : G // x ^ M = 1} := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hM)
  have hb : Function.Bijective f := by
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨fun c c' h => hinj c c' (congrArg Subtype.val h), by rw [hcard]; simp⟩
  obtain ⟨c, hc⟩ := hb.2 ⟨z, hz⟩
  exact ⟨c, congrArg Subtype.val hc⟩
end GlobalTheory.LevelOfPairing
