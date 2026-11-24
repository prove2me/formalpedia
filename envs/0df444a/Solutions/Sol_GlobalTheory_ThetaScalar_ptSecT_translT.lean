-- Prove2me | solution 1 for GlobalTheory.ThetaScalar.ptSecT_translT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:46:23.271511+00:00
-- url     : https://prove2.me/submissions/217ca4d6-aed2-445d-83e6-47ec13f2e6a9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaScalar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
namespace GlobalTheory.ThetaScalar
theorem _root_.solution {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (x d : T ⟶ A) :
    ptSecT A x ≫ translT A d = ptSecT A (d * x) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT, ptSecT]
  · rw [Category.assoc, translT, lift_snd, ptSecT, ptSecT, lift_snd]
    show lift (𝟙 T) x ≫ ((fst T A ≫ d) * snd T A) = _
    rw [MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst, Category.id_comp]
end GlobalTheory.ThetaScalar
