-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.isPullback_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:50:04.96626+00:00
-- url     : https://prove2.me/submissions/e4f5fc83-8a98-4deb-8b90-c91f8244fa9d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoefficientFieldBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange
theorem _root_.solution {l : Level H} {X : Scheme.{0}} (str : X ⟶ Sp (KA l)) {F₀ : IntermediateField ℚ ℂ}
    (h : IsCoeffField l F₀) : IsPullback (baseChangeFst str h) (baseChangeStr str h) str (spMap h.incl) :=
  IsPullback.of_hasPullback _ _
end GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange
