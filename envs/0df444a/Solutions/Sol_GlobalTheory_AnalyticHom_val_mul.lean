-- Prove2me | solution 1 for GlobalTheory.AnalyticHom.val_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:57:45.137217+00:00
-- url     : https://prove2.me/submissions/5325f0ae-63fb-4499-b565-84a58e3f6fad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsHomOfLinearScalingHermForm
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.AnalyticHom
open CubeValues SymmetricSemicharacter ComplexPoints AffinePointValues
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)
namespace GlobalTheory.AnalyticHom
theorem _root_.solution {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f f' : Γ(X, U)) :
    valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  obtain ⟨e, he⟩ := (valueRules X x).2.1 U h
  simp only [he, map_mul]
end GlobalTheory.AnalyticHom
