-- Prove2me | solution 1 for GlobalTheory.map_transpose_mul_rev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:29:31.096828+00:00
-- url     : https://prove2.me/submissions/aa9dbd29-6cd0-42e0-9413-ef02632b78d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitaryStabiliserOrthogonalSummand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] (s : R →+* R) {l m n : Type} [Fintype m]
    (A : Matrix l m R) (B : Matrix m n R) :
    ((A * B).map s)ᵀ = (B.map s)ᵀ * (A.map s)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]
end GlobalTheory
