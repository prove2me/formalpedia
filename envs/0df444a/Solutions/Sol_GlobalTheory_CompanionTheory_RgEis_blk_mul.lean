-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.blk_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:17:30.694798+00:00
-- url     : https://prove2.me/submissions/3693ae44-4e32-48fa-a94e-913b06bec31d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_sum_eq_sum_set

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
theorem _root_.solution {S : Type} [CommRing S] (s : Set ι) [Fintype s] (x y : Matrix ι ι S)
    (hy : ∀ r, r ∉ s → ∀ c ∈ s, y r c = 0) :
    (x * y).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) =
      x.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) *
        y.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) := by
  ext r c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  exact sum_eq_sum_set s _ fun m hm => by rw [hy m hm c c.2, mul_zero]
end GlobalTheory.CompanionTheory.RgEis
