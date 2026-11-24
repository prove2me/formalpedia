-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.bdet_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:32:21.101983+00:00
-- url     : https://prove2.me/submissions/06cc953a-397c-4474-9cca-bb66cdffe26e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_isUnit_det_blk

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
theorem _root_.solution (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) :
    ((bdet s p : Rˣ) : R) = ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det := by
  rw [bdet, dif_pos (isUnit_det_blk s hp), IsUnit.unit_spec]
end GlobalTheory.CompanionTheory.RgEis
