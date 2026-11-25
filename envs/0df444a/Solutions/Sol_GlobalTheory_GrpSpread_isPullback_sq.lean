-- Prove2me | solution 1 for GlobalTheory.GrpSpread.isPullback_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:26:44.750248+00:00
-- url     : https://prove2.me/submissions/09fa7771-e3a6-4ac3-8752-3e833eb1534a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToFgSubalgebra
import Theorems.Thm_GlobalTheory_GrpSpread_isSquare_sq
import Theorems.Thm_GlobalTheory_GrpSpread_sq_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.GrpSpread
open GrpDense
variable {Z U : Scheme.{0}} {j : U ⟶ Z}
variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}
namespace GlobalTheory.GrpSpread
theorem _root_.solution (hA : IsPullback φ A.hom G.hom j) :
    IsPullback (sq hA.w) (A ⊗ A).hom (G ⊗ G).hom j := by
  have hs := isSquare_sq hA.w
  have comm : sq hA.w ≫ (G ⊗ G).hom = (A ⊗ A).hom ≫ j := by
    rw [← Over.w (fst G G), ← Category.assoc, hs.1, Category.assoc, hA.w, ← Category.assoc,
      Over.w (fst A A)]
  let u : ∀ (s : PullbackCone (G ⊗ G).hom j) (p : G ⊗ G ⟶ G), s.pt ⟶ A.left := fun s p =>
    hA.lift (s.fst ≫ p.left) s.snd (by rw [Category.assoc, Over.w p, s.condition])
  let L : ∀ s : PullbackCone (G ⊗ G).hom j, s.pt ⟶ (A ⊗ A).left := fun s =>
    (lift (Over.homMk (u s (fst G G)) (hA.lift_snd _ _ _) : Over.mk s.snd ⟶ A)
      (Over.homMk (u s (snd G G)) (hA.lift_snd _ _ _) : Over.mk s.snd ⟶ A)).left
  have L1 : ∀ s, L s ≫ (fst A A).left = u s (fst G G) := fun s => by
    simp only [L]
    rw [← Over.comp_left, lift_fst]
    rfl
  have L2 : ∀ s, L s ≫ (snd A A).left = u s (snd G G) := fun s => by
    simp only [L]
    rw [← Over.comp_left, lift_snd]
    rfl
  have fl : ∀ s : PullbackCone (G ⊗ G).hom j, L s ≫ sq hA.w = s.fst := fun s => by
    apply sq_ext
    · rw [Category.assoc, hs.1, ← Category.assoc, L1]
      exact hA.lift_fst _ _ _
    · rw [Category.assoc, hs.2, ← Category.assoc, L2]
      exact hA.lift_fst _ _ _
  have fr : ∀ s : PullbackCone (G ⊗ G).hom j, L s ≫ (A ⊗ A).hom = s.snd := fun s => by
    rw [← Over.w (fst A A), ← Category.assoc, L1]
    exact hA.lift_snd _ _ _
  have un : ∀ (s : PullbackCone (G ⊗ G).hom j) (m : s.pt ⟶ (A ⊗ A).left),
      m ≫ sq hA.w = s.fst → m ≫ (A ⊗ A).hom = s.snd → m = L s := fun s m h1 h2 => by
    apply sq_ext
    · rw [L1]
      apply hA.hom_ext
      · rw [hA.lift_fst, Category.assoc, ← hs.1, ← Category.assoc, h1]
      · rw [hA.lift_snd, Category.assoc, Over.w (fst A A), h2]
    · rw [L2]
      apply hA.hom_ext
      · rw [hA.lift_fst, Category.assoc, ← hs.2, ← Category.assoc, h1]
      · rw [hA.lift_snd, Category.assoc, Over.w (snd A A), h2]
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk comm L fl fr un)
end GlobalTheory.GrpSpread
