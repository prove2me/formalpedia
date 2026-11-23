-- Prove2me | solution 1 for GlobalTheory.KS.VertFib.ringVal_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:45.394797+00:00
-- url     : https://prove2.me/submissions/92b7179f-f27b-4a98-92ba-e9f71338724d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationOfFibreOfKillsBase

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.VertFib
namespace GlobalTheory.KS.VertFib
theorem _root_.solution {A : Type} [CommRing A] {X : Scheme.{0}} {v v' : Sp A ⟶ X} (e : v = v') (W : X.Opens)
    (h : ⊤ ≤ v ⁻¹ᵁ W) (h' : ⊤ ≤ v' ⁻¹ᵁ W) (f : Γ(X, W)) : ringVal v W h f = ringVal v' W h' f := by
  subst e; rfl
end GlobalTheory.KS.VertFib
