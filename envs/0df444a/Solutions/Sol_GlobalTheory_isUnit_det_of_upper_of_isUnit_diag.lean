-- Prove2me | solution 1 for GlobalTheory.isUnit_det_of_upper_of_isUnit_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:31.188103+00:00
-- url     : https://prove2.me/submissions/0e5d13cb-69a5-4249-9593-ffc0156c5a5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsLowerMulUpperOfLeadingMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
variable {R : Type} [CommRing R]
namespace GlobalTheory
theorem _root_.solution {r : ℕ} (b : Matrix (Fin r) (Fin r) R)
    (hb : b.BlockTriangular id) (hu : ∀ i, IsUnit (b i i)) : IsUnit b.det := by
  rw [Matrix.det_of_upperTriangular hb]
  exact IsUnit.prod_iff.2 fun i _ => hu i
end GlobalTheory
