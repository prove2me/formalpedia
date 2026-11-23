-- Prove2me | solution 1 for GlobalTheory.det_eq_one_of_lower_unitriangular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:12.06984+00:00
-- url     : https://prove2.me/submissions/6d1dcd62-16ce-431c-b93b-e67590512263

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
theorem _root_.solution {r : ℕ} (l : Matrix (Fin r) (Fin r) R)
    (h0 : ∀ i j : Fin r, i < j → l i j = 0) (h1 : ∀ i, l i i = 1) : l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular l (fun i j h => h0 i j h)]
  simp [h1]
end GlobalTheory
