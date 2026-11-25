-- Prove2me | solution 1 for GlobalTheory.ProjSpace.Model.isEmpty_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:08:29.442535+00:00
-- url     : https://prove2.me/submissions/34653e26-f1ed-4a83-90e0-51e59537d22c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsFormOfEqRatioPowMul

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
theorem _root_.solution [Subsingleton R] : IsEmpty (PSpace R N) :=
  ⟨fun x => x.isPrime.ne_top (Subsingleton.elim _ _)⟩
end GlobalTheory.ProjSpace.Model
