-- Prove2me | solution 1 for GlobalTheory.TwistTranslate.exists_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:42:25.506852+00:00
-- url     : https://prove2.me/submissions/4d9ce4ef-2b3a-4611-819a-4a77dd047fc9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TwistedPowTranslate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionDivision_exists_section


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
open GlobalTheory GlobalTheory.TwistTranslate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
variable {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)
namespace GlobalTheory.TwistTranslate
theorem _root_.solution [IsAlgClosed K] (r : ℕ) [IsFinite (mulA P.A r).left] [Surjective (mulA P.A r).left]
    (c : Over.mk t ⟶ P.A) : ∃ d : Over.mk t ⟶ P.A, d ^ r = c := by
  obtain ⟨u, hu⟩ := H1.SectionDivision.exists_section (k := K) (pullback.snd (mulA P.A r).left c.left)
  have hb' : (u ≫ pullback.fst (mulA P.A r).left c.left) ≫ (mulA P.A r).left = c.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu]; exact Category.id_comp _
  have hw : (u ≫ pullback.fst (mulA P.A r).left c.left) ≫ P.A.hom = (Over.mk t).hom := by
    rw [← Over.w (mulA P.A r), ← Category.assoc, hb']; exact Over.w c
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Over.mk t ⟶ P.A, b ^ r = b ≫ mulA P.A r := fun b =>
    (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 P.A) r b).symm
  rw [e]
  exact Over.OverMorphism.ext hb'
end GlobalTheory.TwistTranslate
