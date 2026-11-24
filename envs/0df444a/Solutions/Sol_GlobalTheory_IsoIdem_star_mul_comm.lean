-- Prove2me | solution 1 for GlobalTheory.IsoIdem.star_mul_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:14.771867+00:00
-- url     : https://prove2.me/submissions/97fb5328-6343-4b0c-93a9-fca4cd0b1a6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsotropicIdempotentCentralizerHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.IsoIdem
namespace GlobalTheory.IsoIdem
theorem _root_.solution {E : Type} [Field E] [StarRing E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (hA : A.IsHermitian) (y : Matrix (Fin r) (Fin r) E) (hy : y * A = A * y) :
    star y * A = A * star y := by
  have hA' : star A = A := hA
  have := congrArg star hy
  rw [star_mul, star_mul, hA'] at this
  exact this.symm
end GlobalTheory.IsoIdem
