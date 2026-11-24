-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.bdet_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:10:10.856007+00:00
-- url     : https://prove2.me/submissions/16a022a1-0572-4064-8490-e3f2a13aa2e6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] {s : Set ι} {s' : Set κ} {g : GL ι R} {g' : GL κ R}
    (h : ∀ [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s'],
      ((g : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det =
      ((g' : Matrix κ κ R).submatrix (Subtype.val : s' → κ) Subtype.val).det) : bdet s g = bdet s' g' := by
  classical
  unfold bdet
  by_cases h1 : IsUnit ((g : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det
  · have h2 : IsUnit ((g' : Matrix κ κ R).submatrix (Subtype.val : s' → κ) Subtype.val).det := by
      rw [← h]; exact h1
    rw [dif_pos h1, dif_pos h2]
    exact Units.ext (by simpa using h)
  · have h2 : ¬ IsUnit ((g' : Matrix κ κ R).submatrix (Subtype.val : s' → κ) Subtype.val).det := by
      rw [← h]; exact h1
    rw [dif_neg h1, dif_neg h2]
end GlobalTheory.CompanionTheory.Plucker
