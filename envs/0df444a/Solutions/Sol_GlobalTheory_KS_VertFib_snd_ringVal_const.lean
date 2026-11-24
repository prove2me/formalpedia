-- Prove2me | solution 1 for GlobalTheory.KS.VertFib.snd_ringVal_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:28:29.544404+00:00
-- url     : https://prove2.me/submissions/8e395c06-ae13-4e7e-867f-612db12bd95e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationOfFibreOfKillsBase
import Theorems.Thm_GlobalTheory_KS_VertFib_epsPt_epsStr
import Theorems.Thm_GlobalTheory_KS_VertFib_top_le_epsPt
import Theorems.Thm_GlobalTheory_KS_VertFib_ringVal_appLE
import Theorems.Thm_GlobalTheory_KS_VertFib_ringVal_spMap

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
theorem _root_.solution {X : Scheme.{0}} (z : Sp ℂ ⟶ X) (W : X.Opens) (h : ⊤ ≤ (epsStr ≫ z) ⁻¹ᵁ W) (f : Γ(X, W)) :
    TrivSqZeroExt.snd (ringVal (epsStr ≫ z) W h f) = 0 := by
  have hz : ⊤ ≤ z ⁻¹ᵁ W := by
    have := top_le_epsPt _ W h
    rwa [← Category.assoc, epsPt_epsStr, Category.id_comp] at this
  exact congrArg TrivSqZeroExt.snd
    ((ringVal_appLE epsStr z W ⊤ hz le_top h f).symm.trans (ringVal_spMap _ _ _))
end GlobalTheory.KS.VertFib
