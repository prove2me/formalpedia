-- Prove2me | solution 1 for GlobalTheory.MinorNorm.det_cons_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:30:29.792568+00:00
-- url     : https://prove2.me/submissions/1c71dccc-d75e-4448-881e-7bb3359beba6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {R : Type} [CommRing R] [Algebra ℂ R]
namespace GlobalTheory.MinorNorm
theorem _root_.solution {m : ℕ} (M : Fin m → Fin (m + 1) → R) (t : Fin m) :
    (Matrix.of (Fin.cons (M t) M : Fin (m + 1) → Fin (m + 1) → R)).det = 0 :=
  det_zero_of_row_eq (i := 0) (j := t.succ) (Fin.succ_ne_zero t).symm rfl
end GlobalTheory.MinorNorm
