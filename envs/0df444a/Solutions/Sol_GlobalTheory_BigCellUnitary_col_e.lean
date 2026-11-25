-- Prove2me | solution 1 for GlobalTheory.BigCellUnitary.col_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:26:37.565962+00:00
-- url     : https://prove2.me/submissions/4715b936-1c7a-4bff-afad-91128763a822

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
    (i : Fin (2 * r + k + 1)) (b : Fin r) :
    bigCell k r c μ i (eI k r b) = if i.val = 2 * r + k - b.val then c b else 0 := by
  have hb : (eI k r b).val < r := b.isLt
  unfold bigCell
  rw [dif_pos hb]
  exact if_congr Fin.ext_iff rfl rfl
end GlobalTheory.BigCellUnitary
