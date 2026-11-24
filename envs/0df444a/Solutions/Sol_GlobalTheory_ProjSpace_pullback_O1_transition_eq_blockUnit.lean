-- Prove2me | solution 1 for GlobalTheory.ProjSpace.pullback_O1_transition_eq_blockUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:31:13.395994+00:00
-- url     : https://prove2.me/submissions/d03486dd-de8c-4d61-9ab4-dee47fbc0ec3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Theorems.Thm_GlobalTheory_ProjSpace_pullU_baseChange_ratioUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (i j : PUnit → Fin (N + 1)) :
    ((O1 R N).pull (baseChange N φ)).g i j =
      ratioUnit (((O1 R N).pull (baseChange N φ)).U i ⊓ ((O1 R N).pull (baseChange N φ)).U j)
        (i PUnit.unit) (j PUnit.unit) (inf_le_left.trans (pull_O1_chart N φ i).le)
        (inf_le_right.trans (pull_O1_chart N φ j).le) :=
  (linComb_punit_g (O1 R N) (baseChange N φ) 1 i j).trans ((zpow_one _).trans
    (congrArg (res _) (pullU_baseChange_ratioUnit φ inf_le_left inf_le_right)))
end GlobalTheory.ProjSpace
