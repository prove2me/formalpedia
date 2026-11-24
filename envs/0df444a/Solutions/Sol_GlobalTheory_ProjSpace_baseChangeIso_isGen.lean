-- Prove2me | solution 1 for GlobalTheory.ProjSpace.baseChangeIso_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:45:00.470507+00:00
-- url     : https://prove2.me/submissions/7fa7e494-b923-41cd-b3fb-275edd57e04f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Theorems.Thm_GlobalTheory_ProjSpace_inv_ratioUnit
import Theorems.Thm_GlobalTheory_ProjSpace_res_ratioUnit
import Theorems.Thm_GlobalTheory_ProjSpace_ratioUnit_mul_ratioUnit
import Theorems.Thm_GlobalTheory_ProjSpace_O1_g_eq_ratioUnit_chart_inf
import Theorems.Thm_GlobalTheory_ProjSpace_gradedMap_apply
import Theorems.Thm_GlobalTheory_ProjSpace_pullback_O1_transition_eq_blockUnit
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.Qcqs.appLinearBase_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply


attribute [local simp] GlobalTheory.ProjSpace.gradedMap_apply

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace
variable (R : Type) [CommRing R] (N : ℕ)
variable {R N}
variable (R N)
variable {R N}
variable (R N)
variable {R} {R' : Type} [CommRing R'] (φ : R →+* R')
namespace GlobalTheory.ProjSpace
theorem _root_.solution : (baseChangeIso N φ).IsGen := by
  rintro ⟨i, j⟩ ⟨i', j'⟩
  simp only [LB.div, O1_g_eq_ratioUnit_chart_inf, baseChangeIso]
  erw [pullback_O1_transition_eq_blockUnit, res_ratioUnit, res_ratioUnit, res_ratioUnit, res_ratioUnit]
  erw [inv_ratioUnit, mul_right_comm, ratioUnit_mul_ratioUnit, ratioUnit_mul_ratioUnit]
end GlobalTheory.ProjSpace
