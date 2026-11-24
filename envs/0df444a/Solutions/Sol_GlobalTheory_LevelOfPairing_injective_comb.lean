-- Prove2me | solution 1 for GlobalTheory.LevelOfPairing.injective_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:59:24.66995+00:00
-- url     : https://prove2.me/submissions/a5f9aa32-eb38-43c6-9437-cdc937c51500

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsLevelStructureOfWeilPairing
import Theorems.Thm_GlobalTheory_LevelOfPairing_prod_pow_eq_one
import Theorems.Thm_GlobalTheory_LevelOfPairing_rel_one
import Theorems.Thm_GlobalTheory_LevelOfPairing_rel_pow
import Theorems.Thm_GlobalTheory_LevelOfPairing_rel_prod
import Theorems.Thm_GlobalTheory_LevelOfPairing_exists_column
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
theorem _root_.solution (cm : ∀ a b : G, Commute a b)
    (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, R x y c)
    (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {ζ : U} (hζ : IsPrimitiveRoot ζ M)
    {g : ℕ} (y : Fin (2 * g) → G) (hy : ∀ i, y i ^ M = 1) (hp : ∀ i j, R (y i) (y j) (ζ ^ stdSymp g i j))
    (c c' : Fin (2 * g) → Fin M)
    (e : (List.ofFn fun i => y i ^ (c i : ℕ)).prod = (List.ofFn fun i => y i ^ (c' i : ℕ)).prod) : c = c' := by
  funext i
  obtain ⟨j, hj, hj'⟩ := exists_column g i
  have h₁ := rel_one hu hm (hy j)
  have key : ∀ a : Fin (2 * g) → Fin M,
      R (List.ofFn fun i => y i ^ (a i : ℕ)).prod (y j) ((ζ ^ stdSymp g i j) ^ (a i : ℕ)) := fun a => by
    have h := rel_prod hm h₁ (fun i => y i ^ (a i : ℕ)) (fun i => (ζ ^ stdSymp g i j) ^ (a i : ℕ))
      fun i => rel_pow hm h₁ (hp i j) _
    rwa [Finset.prod_eq_single i (fun b _ hb => by rw [hj' b hb, zpow_zero, one_pow])
      (fun h => absurd (Finset.mem_univ _) h)] at h
  have k₁ := key c
  rw [e] at k₁
  have q := (hu _ _ (prod_pow_eq_one cm y hy _) (hy j)).unique k₁ (key c')
  have hζ' : IsPrimitiveRoot (ζ ^ stdSymp g i j) M := by
    rcases hj with hj | hj
    · rwa [hj, zpow_one]
    · rw [hj, zpow_neg, zpow_one]; exact hζ.inv
  exact Fin.ext (hζ'.pow_inj (c i).2 (c' i).2 q)
end GlobalTheory.LevelOfPairing
