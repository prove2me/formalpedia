-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.det_blk_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:33:40.247521+00:00
-- url     : https://prove2.me/submissions/68fcf8ca-2564-4fc5-91db-72f6d9bef858

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_blk_mul

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
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
open Classical
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution (s : Set ι) (p : GL ι R) {q : GL ι R} (hq : q ∈ stab R s) :
    (((p * q : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det =
      ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det *
        ((q : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det := by
  rw [Units.val_mul, blk_mul s _ _ fun r hr c hc => (hq r hr c hc).1, Matrix.det_mul]
end GlobalTheory.CompanionTheory.RgEis
