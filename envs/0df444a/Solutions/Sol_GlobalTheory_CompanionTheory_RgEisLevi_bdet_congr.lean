-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.bdet_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:10:46.721172+00:00
-- url     : https://prove2.me/submissions/7b8f0925-c53e-4a0d-a25b-2c4f26e35aa4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
open Classical
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (s : Set κ) (t : Set κ')
    (e : s ≃ t) (g : GL κ' R) (m : GL κ R)
    (h : ∀ a b : s, (g : Matrix κ' κ' R) (e a).1 (e b).1 = (m : Matrix κ κ R) a.1 b.1) : bdet t g = bdet s m := by
  have hdet : ((g : Matrix κ' κ' R).submatrix (Subtype.val : t → κ') Subtype.val).det =
      ((m : Matrix κ κ R).submatrix (Subtype.val : s → κ) Subtype.val).det := by
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext a b
    exact h a b
  unfold bdet
  simp only [hdet]
end GlobalTheory.CompanionTheory.RgEisLevi
