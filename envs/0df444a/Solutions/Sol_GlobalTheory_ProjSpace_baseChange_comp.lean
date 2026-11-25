-- Prove2me | solution 1 for GlobalTheory.ProjSpace.baseChange_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:09:04.178894+00:00
-- url     : https://prove2.me/submissions/5d22f210-1932-4252-9526-5a352716d424

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
theorem _root_.solution {R'' : Type} [CommRing R''] (ψ : R' →+* R'') :
    baseChange N (ψ.comp φ) = baseChange N ψ ≫ baseChange N φ := by
  refine (chartCover R'' N).hom_ext _ _ fun (i : Fin (N + 1)) => ?_
  change chartι R'' N i ≫ _ = chartι R'' N i ≫ _
  rw [chartι_baseChange, ← Category.assoc, chartι_baseChange, Category.assoc, chartι_baseChange,
    ← Spec.map_comp_assoc]
  have : (MvPolynomial.map (ψ.comp φ) : MvPolynomial {j // j ≠ i} R →+* _) =
      (MvPolynomial.map ψ).comp (MvPolynomial.map φ) := RingHom.ext fun p => (map_map φ ψ p).symm
  rw [this]
  rfl
end GlobalTheory.ProjSpace
