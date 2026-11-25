-- Prove2me | solution 1 for GlobalTheory.T.exists_goodUniformisation_kodairaSpencer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:48:42.458807+00:00
-- url     : https://prove2.me/submissions/5e2a1ea3-e5f4-4346-a3d4-53508eea9949

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGoodUniformisationKodairaSpencer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGoodUniformisationKodairaSpencerStatement
import Theorems.Thm_GlobalTheory_KSInh_exists_goodU_ksRel


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
namespace _root_.GlobalTheory.T
theorem _root_.solution : ThetaUnifAV → ∀ P₀ : Out.PolAV (Sp ℂ), ∃ (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ ∧ ∀ w : Fin P₀.g → ℂ, KSRel u P₀.A.hom (𝟙 _) (fun _ => 0) 0 (fun z W f => fderiv ℂ (fn u (𝟙 _) W f) z w) := by
  first | exact @GlobalTheory.KSInh.exists_goodU_ksRel | exact GlobalTheory.KSInh.exists_goodU_ksRel | (intros; apply GlobalTheory.KSInh.exists_goodU_ksRel <;> assumption)
end _root_.GlobalTheory.T
