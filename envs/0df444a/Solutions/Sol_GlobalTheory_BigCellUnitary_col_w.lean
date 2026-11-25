-- Prove2me | solution 1 for GlobalTheory.BigCellUnitary.col_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:26:47.939066+00:00
-- url     : https://prove2.me/submissions/cefbf930-ca75-4299-a75a-dc61effcfc27

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
theorem _root_.solution (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i : Fin (2 * r + k + 1)) (b : Fin (k + 1)) :
    bigCell k r c μ i (wI k r b) =
      if hi : r ≤ i.val ∧ i.val ≤ r + k then μ ⟨i.val - r, by omega⟩ b else 0 := by
  have hb := b.isLt
  have hv : (wI k r b).val = r + b.val := rfl
  unfold bigCell
  rw [dif_neg (by omega), dif_pos (by omega)]
  split_ifs
  · congr 1
    apply Fin.ext
    show (wI k r b).val - r = b.val
    omega
  · rfl
end GlobalTheory.BigCellUnitary
