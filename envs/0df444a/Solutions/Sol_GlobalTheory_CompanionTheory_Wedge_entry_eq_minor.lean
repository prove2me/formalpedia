-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.entry_eq_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:53:24.744691+00:00
-- url     : https://prove2.me/submissions/461987f1-8172-4e81-b9c3-a0e4328a49d2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {K ι ι' κ κ' : Type} [NormedField K]
namespace GlobalTheory.CompanionTheory.Wedge
theorem _root_.solution [Fintype κ] [DecidableEq κ] (D : Matrix ι κ K) (s : κ → ι)
    (hD : D.submatrix s id = 1) (i : ι) (k : κ) :
    D i k = (D.submatrix (Function.update s k i) id).det := by
  have h : D.submatrix (Function.update s k i) id = (1 : Matrix κ κ K).updateRow k (D i) := by
    ext a b
    by_cases hak : a = k
    · subst hak
      simp
    · have := congrFun (congrFun hD a) b
      simpa [Function.update_of_ne hak, updateRow_ne hak] using this
  rw [h, ← det_transpose, ← updateCol_transpose, transpose_one, ← cramer_apply, cramer_one]
  rfl
end GlobalTheory.CompanionTheory.Wedge
