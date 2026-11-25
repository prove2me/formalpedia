-- Prove2me | solution 1 for GlobalTheory.ProjSpace.baseChange_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:10:14.74025+00:00
-- url     : https://prove2.me/submissions/a43fa220-7f25-4587-98f5-b7184a2deeef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Theorems.Thm_GlobalTheory_ProjSpace_gradedMap_apply
import Theorems.Thm_P2M_GlobalTheory_ProjSpace_chart__baseChange_4f839b0b071b
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
theorem _root_.solution : baseChange N (RingHom.id R) = 𝟙 (PSpace R N) := by
  refine (chartCover R N).hom_ext _ _ fun (i : Fin (N + 1)) => ?_
  refine (chartι_baseChange N (RingHom.id R) i).trans ?_
  have : (MvPolynomial.map (RingHom.id R) : MvPolynomial {j // j ≠ i} R →+* _) = RingHom.id _ :=
    RingHom.ext map_id
  rw [this]
  exact (congrArg (· ≫ _) (Spec.map_id _)).trans ((Category.id_comp _).trans (Category.comp_id _).symm)
end GlobalTheory.ProjSpace
