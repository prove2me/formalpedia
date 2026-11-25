-- Prove2me | solution 1 for GlobalTheory.BigCellUnitary.col_es
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:26:45.921416+00:00
-- url     : https://prove2.me/submissions/24518179-fef3-4642-b8ce-37fa6df03935

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
    bigCell k r c μ i (esI k r b) = if i.val = b.val then (star (c b))⁻¹ else 0 := by
  have hb := b.isLt
  have hv : (esI k r b).val = 2 * r + k - b.val := rfl
  unfold bigCell
  rw [dif_neg (by omega), dif_neg (by omega)]
  refine if_congr (by omega) ?_ rfl
  congr 3
  apply Fin.ext
  show 2 * r + k - (esI k r b).val = b.val
  omega
end GlobalTheory.BigCellUnitary
