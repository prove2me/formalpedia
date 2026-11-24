-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.bdet_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:19.860283+00:00
-- url     : https://prove2.me/submissions/c2f68cff-bab0-4bb3-9481-72516d026079

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_det_blk_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdet_val

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
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution (s : Set ι) {p q : GL ι R} (hp : p ∈ stab R s) (hq : q ∈ stab R s) :
    bdet s (p * q) = bdet s p * bdet s q := by
  classical
  apply Units.ext
  rw [Units.val_mul, bdet_val s (mul_mem hp hq), bdet_val s hp, bdet_val s hq]
  exact det_blk_mul s p hq
end GlobalTheory.CompanionTheory.RgEis
