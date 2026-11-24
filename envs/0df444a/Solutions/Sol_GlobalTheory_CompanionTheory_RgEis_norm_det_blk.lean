-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.norm_det_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:19.956043+00:00
-- url     : https://prove2.me/submissions/44433dab-b4aa-469d-864d-8322e6f2ab59

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
variable {E : Type} [Field E]
open Classical
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution (M : Matrix ι ι ℂ) (hM : M ∈ Matrix.unitaryGroup ι ℂ) (s : Set ι)
    (h0 : ∀ r, r ∉ s → ∀ c ∈ s, M r c = 0) :
    ‖(M.submatrix (Subtype.val : s → ι) Subtype.val).det‖ = 1 := by
  have h1 : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.1 hM
  have h2 : ((star M * M).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det = 1 := by
    rw [h1, Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]
  rw [blk_mul s _ _ h0, Matrix.det_mul, Matrix.star_eq_conjTranspose, ← Matrix.conjTranspose_submatrix,
    Matrix.det_conjTranspose] at h2
  have h3 : ‖(M.submatrix (Subtype.val : s → ι) Subtype.val).det‖ ^ 2 = 1 := by
    have := congrArg norm h2
    rw [norm_mul, norm_star, norm_one] at this
    rw [sq]; exact this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
end GlobalTheory.CompanionTheory.RgEis
