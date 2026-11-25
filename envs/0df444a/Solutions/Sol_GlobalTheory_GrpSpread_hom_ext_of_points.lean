-- Prove2me | solution 1 for GlobalTheory.GrpSpread.hom_ext_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:59:19.416505+00:00
-- url     : https://prove2.me/submissions/63ae5b36-8caa-4ca5-82b2-53a234948747

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToFgSubalgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
namespace GlobalTheory.GrpSpread
theorem _root_.solution (j : U ⟶ Z) [QuasiCompact j] [IsSchemeTheoreticallyDominant j] {X Y : Over Z}
    [Flat X.hom] [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have hsd : IsSchemeTheoreticallyDominant (pullback.fst X.hom j) := inferInstance
  let t : Over.mk ((Over.mk (pullback.snd X.hom j) : Over U).hom ≫ j) ⟶ X :=
    Over.homMk (pullback.fst X.hom j) pullback.condition
  have ht : t ≫ f = t ≫ g := h _ t
  have hdom : IsSchemeTheoreticallyDominant
      ((equalizer.lift t ht).left ≫ (equalizer.ι f g).left) := by
    rw [← Over.comp_left, equalizer.lift_ι]
    exact hsd
  have hker : (equalizer.ι f g).left.ker = ⊥ :=
    le_bot_iff.mp ((Scheme.Hom.le_ker_comp _ _).trans hdom.ker_eq_bot.le)
  have : IsIso (equalizer.ι f g).left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  ext1
  rw [← cancel_epi (equalizer.ι f g).left, ← Over.comp_left, ← Over.comp_left, equalizer.condition]
end GlobalTheory.GrpSpread
