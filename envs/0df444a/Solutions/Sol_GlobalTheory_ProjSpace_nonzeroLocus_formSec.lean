-- Prove2me | solution 1 for GlobalTheory.ProjSpace.nonzeroLocus_formSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:14:33.669656+00:00
-- url     : https://prove2.me/submissions/14709856-b2f1-4f3d-87bf-1a61c20c51a6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Theorems.Thm_GlobalTheory_ProjSpace_basicOpen_formOn
import Theorems.Thm_GlobalTheory_ProjSpace_On_isLB

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
namespace GlobalTheory.ProjSpace
theorem _root_.solution (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) :
    nonzeroLocus (formSec n f hf) = Proj.basicOpen (grading R N) f := by
  have e : ∀ j, (PSpace R N).basicOpen ((formSec n f hf).f j) =
      (On R N n).U j ⊓ Proj.basicOpen (grading R N) f := fun j =>
    basicOpen_formOn (hi := (On_U R N n j).le) hf
  refine (iSup_congr e).trans ((iSup_inf_eq _ _).symm.trans ?_)
  exact (congrArg (· ⊓ _) (On_isLB R N n).cover).trans (top_inf_eq _)
end GlobalTheory.ProjSpace
