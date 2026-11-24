-- Prove2me | solution 1 for GlobalTheory.ProjSpace.formOn_chart_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:48:09.908604+00:00
-- url     : https://prove2.me/submissions/4faa7b31-d811-414d-a438-970d85f66ac1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
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
namespace GlobalTheory.ProjSpace
theorem _root_.solution (i : Fin (N + 1)) {n : ℕ} {f g : MvPolynomial (Fin (N + 1)) R}
    (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n) :
    formOn (chart R N i) i le_rfl n f hf = formOn (chart R N i) i le_rfl n g hg ↔ f = g := by
  refine ⟨fun h => ?_, fun h => by subst h; rfl⟩
  rw [← chartAlgEquiv_dehom, ← chartAlgEquiv_dehom] at h
  have h1 := congrArg (fun p => (polyToAway R N i p).val) ((chartAlgEquiv R N i).injective h)
  simp only [polyToAway_dehom R N i n f (by simpa using hf), polyToAway_dehom R N i n g (by simpa using hg),
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at h1
  obtain ⟨⟨_, m, rfl⟩, h1⟩ := h1
  exact ((isRegular_X (n := i)).pow n).left (((isRegular_X (n := i)).pow m).left h1)
end GlobalTheory.ProjSpace
