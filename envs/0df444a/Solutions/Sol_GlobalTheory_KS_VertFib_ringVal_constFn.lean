-- Prove2me | solution 1 for GlobalTheory.KS.VertFib.ringVal_constFn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:21.533813+00:00
-- url     : https://prove2.me/submissions/e8e3f27a-e448-489a-99ef-47f44a1d2094

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationOfFibreOfKillsBase
import Theorems.Thm_GlobalTheory_KS_VertFib_ringVal_appLE
import Theorems.Thm_GlobalTheory_KS_VertFib_ringVal_spMap
import Theorems.Thm_GlobalTheory_KS_VertFib_ringVal_congr

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
theorem _root_.solution {A R : Type} [CommRing A] [CommRing R] {X : Scheme.{0}} (v : Sp A ⟶ X) (p : X ⟶ Sp R)
    (φ : R →+* A) (hv : v ≫ p = spMap φ) (h : ⊤ ≤ v ⁻¹ᵁ ⊤) (r : R) :
    ringVal v ⊤ h (constFn p ⊤ r) = φ r := by
  refine (ringVal_appLE v p ⊤ ⊤ le_top h le_top _).trans ?_
  refine (ringVal_congr hv ⊤ _ le_top _).trans ((ringVal_spMap φ _ _).trans ?_)
  congr 1
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id_apply r
end GlobalTheory.KS.VertFib
