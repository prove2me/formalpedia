-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.isUnit_det_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:15:43.873779+00:00
-- url     : https://prove2.me/submissions/8d5cce92-c96c-4517-bc46-1976e46b5229

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_det_blk_mul_inv

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
    IsUnit ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det :=
  IsUnit.of_mul_eq_one _ (det_blk_mul_inv s hp)
end GlobalTheory.CompanionTheory.RgEis
