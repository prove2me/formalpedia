-- Prove2me | solution 1 for GlobalTheory.ProjSpace.baseChangeIso_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:08:59.120893+00:00
-- url     : https://prove2.me/submissions/788ffeb2-9cae-4d45-96e0-fc11d917a72b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Theorems.Thm_GlobalTheory_ProjSpace_baseChange_app_ratioOn

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
theorem _root_.solution (k i : Fin (N + 1)) (j : PUnit → Fin (N + 1)) :
    resG _ (inf_le_left : (O1 R' N).U i ⊓ ((O1 R N).pull (baseChange N φ)).U j ≤ _) ((coord R' N k).f i) =
      ((baseChangeIso N φ).s (i, j)).val *
        resG _ (inf_le_right.trans (LB.wchart_le (O1 R N) (fun _ => baseChange N φ) j PUnit.unit))
          (((baseChange N φ).app ((O1 R N).U (j PUnit.unit))).hom ((coord R N k).f (j PUnit.unit))) := by
  have e := baseChange_app_ratioOn φ (le_refl (chart R N (j PUnit.unit))) k
  exact (ratioOn_mul_ratioOn (hi := inf_le_left)
    (hj := inf_le_right.trans (pull_O1_chart N φ j).le)).symm.trans (congrArg (_ * resG _ _ ·) e.symm)
end GlobalTheory.ProjSpace
