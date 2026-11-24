-- Prove2me | solution 1 for GlobalTheory.TwistZero.hom_base_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:42:26.399247+00:00
-- url     : https://prove2.me/submissions/245c4297-7fdf-47fc-82d4-41e6a5aa45be

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_TorsionZeroCountTwist

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
  ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistZero
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
namespace GlobalTheory.TwistZero
theorem _root_.solution {T : Over S} (f g : T ⟶ baseOver S) : f = g := by
  apply Over.OverMorphism.ext
  have h1 := Over.w f
  have h2 := Over.w g
  simp only [Over.mk_hom, Over.mk_left] at h1 h2
  exact (Category.comp_id _).symm.trans (h1.trans (h2.symm.trans (Category.comp_id _)))
end GlobalTheory.TwistZero
