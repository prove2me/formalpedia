-- Prove2me | solution 1 for GlobalTheory.KeyPBScale.appLE_constFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:07:15.044794+00:00
-- url     : https://prove2.me/submissions/7b55d15e-2160-4a21-abec-c69cf7496d19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PwIsoIsGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DualNumberRingHomExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_LieCombBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LieBaseChange
import Theorems.Thm_GlobalTheory_KeyVia_appLE_cst


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
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {X Y : Scheme.{0}} {φ : Y ⟶ X}
    (p : X ⟶ Sp R) (p' : Y ⟶ Sp R') (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U)
    (a : R) : (φ.appLE U V h).hom (constFn p U a) = constFn p' V (f a) :=
  KeyVia.appLE_cst f p p' hφ h a
end GlobalTheory.KeyPBScale
