-- Prove2me | solution 1 for GlobalTheory.EisBL.NilAlg.tau_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:39.609859+00:00
-- url     : https://prove2.me/submissions/9125fa88-1b6a-4e24-9db8-685bc361d685

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.EisBL.NilAlg
theorem _root_.solution (c : B →+* B) (J K X Y : Matrix n n B) : tau c J K (X + Y) = tau c J K X + tau c J K Y := by
  unfold tau
  rw [show (X + Y).map c = X.map c + Y.map c from map_add c.mapMatrix X Y, Matrix.mul_add, Matrix.add_mul,
    transpose_add, neg_add]
end GlobalTheory.EisBL.NilAlg
