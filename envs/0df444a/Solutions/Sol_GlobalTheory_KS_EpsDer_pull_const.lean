-- Prove2me | solution 1 for GlobalTheory.KS.EpsDer.pull_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:45:10.046537+00:00
-- url     : https://prove2.me/submissions/e9a651ce-aa88-4a5c-8bd4-8b45281ec9e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationOfDualNumberThickening
import Theorems.Thm_GlobalTheory_KS_EpsDer_pull_pull
import Theorems.Thm_GlobalTheory_KS_EpsDer_pull_congr
import Theorems.Thm_GlobalTheory_KS_EpsDer_spec_pull_inv

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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EpsDer
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.KS.EpsDer
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (φ : Y ⟶ X) (p : X ⟶ Sp R)
    (p' : Y ⟶ Sp R') (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (r : R) :
    (φ.appLE U V h).hom (constFn p U r) = constFn p' V (f r) := by
  unfold constFn
  rw [pull_pull φ p (φ ≫ p) rfl (U := ⊤) (V := U) (W := V) (by simp) h (by simp),
    pull_congr hφ (U := ⊤) (V := V) (by simp) (by simp),
    ← pull_pull p' (spMap f) (p' ≫ spMap f) rfl (U := ⊤) (V := ⊤) (W := V) (by simp) (by simp) (by simp),
    spec_pull_inv f (by simp)]
end GlobalTheory.KS.EpsDer
