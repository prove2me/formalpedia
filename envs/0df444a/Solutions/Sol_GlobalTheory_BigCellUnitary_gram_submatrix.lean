-- Prove2me | solution 1 for GlobalTheory.BigCellUnitary.gram_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:26:06.604925+00:00
-- url     : https://prove2.me/submissions/64a2a310-2d6a-46e7-adb0-c60609c5fe62

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BigCellMemUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
noncomputable section
open GlobalTheory
open GlobalTheory.BigCellUnitary
namespace GlobalTheory.BigCellUnitary
theorem _root_.solution (k r : ℕ) :
    (Hpk k r).submatrix (pos k r) (pos k r) =
      fromBlocks (fromBlocks 0 1 1 0) 0 0 (Hb k) := by
  ext ((a | a) | a) ((b | b) | b) <;>
    have ha := a.isLt <;> have hb := b.isLt <;>
    simp only [pos, eI, esI, wI, Hpk, Hb, Sum.elim_inl, Sum.elim_inr, submatrix_apply,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.one_apply, diagonal_apply, Fin.ext_iff, Fin.val_last] <;>
    split_ifs <;> first | rfl | (exfalso; omega) | contradiction | (exfalso; simp_all; done) |
      (rename_i h1 h2
       first
        | exact (if_pos h2).trans (by rw [if_pos (by omega), if_pos (by omega)])
        | exact (if_neg h2).trans (by rw [if_pos (by omega), if_neg (by omega)]))
end GlobalTheory.BigCellUnitary
