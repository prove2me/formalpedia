-- Prove2me | solution 1 for GlobalTheory.KS.VertFib.ringVal_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:28:28.787706+00:00
-- url     : https://prove2.me/submissions/bba58873-1202-4340-9fcd-e56a8134b3f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationOfFibreOfKillsBase
import Theorems.Thm_GlobalTheory_KS_VertFib_ringVal_appLE

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
theorem _root_.solution {A : Type} [CommRing A] {X Y : Scheme.{0}} (v : Sp A ⟶ Y) (m : Y ⟶ X) (W : X.Opens)
    (h : ⊤ ≤ v ⁻¹ᵁ (m ⁻¹ᵁ W)) (h' : ⊤ ≤ (v ≫ m) ⁻¹ᵁ W) (f : Γ(X, W)) :
    ringVal v (m ⁻¹ᵁ W) h ((m.app W).hom f) = ringVal (v ≫ m) W h' f := by
  rw [Scheme.Hom.app_eq_appLE]
  exact ringVal_appLE v m W _ _ h h' f
end GlobalTheory.KS.VertFib
