-- Prove2me | solution 1 for GlobalTheory.KeyPBScale.resG_constFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:07:18.491794+00:00
-- url     : https://prove2.me/submissions/38daa312-750d-4118-8c5f-8cf759a997d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PwIsoIsGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DualNumberRingHomExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_LieCombBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LieBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyPBScale
namespace GlobalTheory.KeyPBScale
theorem _root_.solution {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a :=
  KeyVia.res_appLE (φ := p) (U := ⊤) (fun _ _ => trivial) h _
end GlobalTheory.KeyPBScale
