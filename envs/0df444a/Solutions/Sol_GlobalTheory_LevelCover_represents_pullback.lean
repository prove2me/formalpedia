-- Prove2me | solution 1 for GlobalTheory.LevelCover.represents_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:46.812919+00:00
-- url     : https://prove2.me/submissions/dae7ee97-f8d3-4c2b-9b4c-a722104b6408

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFiniteEtaleSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevelCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l l₂ : Level H}
namespace GlobalTheory.LevelCover
theorem _root_.solution (hC : ObjCompSt) (Xo : Moduli D l) {B : Type} [CommRing B] {b : Base l B} (j : KA l →+* B)
    (hR : ∀ (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsReduced S →
      ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f))
    {s : pullback Xo.s (spMap j) ⟶ Sp B} (hs : s = pullback.snd _ _) (o : Obj D l b s)
    (mo : ObjMap o Xo.univ (pullback.fst _ _)) : Represents o := by
  subst hs
  intro S s' o' hS
  obtain ⟨g, ⟨hg, ⟨u⟩⟩, huniq⟩ := hR S s' o' hS
  have hl : pullback.lift g s' hg ≫ pullback.fst _ _ = g := pullback.lift_fst _ _ _
  refine ⟨pullback.lift g s' hg, ⟨pullback.lift_snd _ _ _, ?_⟩, ?_⟩
  · obtain ⟨u', -⟩ := ((hC E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 _ (pullback.lift g s' hg) mo).2
      (hl.symm ▸ u)
    exact ⟨u'⟩
  · rintro f ⟨hf, ⟨v⟩⟩
    apply pullback.hom_ext
    · rw [hl]
      obtain ⟨v', -⟩ := ((hC E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 _ f mo).1 v
      exact huniq _ ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, hf], ⟨v'⟩⟩
    · rw [hf, pullback.lift_snd]
end GlobalTheory.LevelCover
