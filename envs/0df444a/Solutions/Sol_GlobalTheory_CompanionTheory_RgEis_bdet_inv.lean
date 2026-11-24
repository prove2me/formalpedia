-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.bdet_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:48.232827+00:00
-- url     : https://prove2.me/submissions/612c35e9-282c-469c-aee6-7282081b789f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_det_blk_mul_inv
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
theorem _root_.solution (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s) : (bdet s p)⁻¹ = bdet s p⁻¹ := by
  classical
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  apply Units.ext
  rw [Units.val_mul, bdet_val s hp, bdet_val s (inv_mem hp), Units.val_one]
  exact det_blk_mul_inv s hp
end GlobalTheory.CompanionTheory.RgEis
