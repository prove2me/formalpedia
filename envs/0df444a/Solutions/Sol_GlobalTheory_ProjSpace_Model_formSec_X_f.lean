-- Prove2me | solution 1 for GlobalTheory.ProjSpace.Model.formSec_X_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:08:25.81499+00:00
-- url     : https://prove2.me/submissions/58f29ae2-3a79-42c0-beb3-2b1c4704773d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsFormOfEqRatioPowMul
import Theorems.Thm_GlobalTheory_ProjSpace_formOn_X


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
open GlobalTheory.ProjFrac
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace GlobalTheory.ProjSpace.Model
variable {R : Type} [CommRing R] {N : ℕ}
namespace GlobalTheory.ProjSpace.Model
theorem _root_.solution (k : Fin (N + 1)) (j : PUnit → Fin (N + 1)) :
    (formSec 1 (X k) (isHomogeneous_X R k)).f j =
      resG _ (On_U R N 1 j).le ((coord R N k).f (j PUnit.unit)) :=
  formOn_X (hi := (On_U R N 1 j).le)
end GlobalTheory.ProjSpace.Model
