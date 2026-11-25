-- Prove2me | solution 1 for GlobalTheory.BigCellUnitary.bigCell_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:10:19.291246+00:00
-- url     : https://prove2.me/submissions/55a0020c-7e8d-4d66-bcb3-34b1e3c89a6f

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BigCellMemUnitary
import Theorems.Thm_GlobalTheory_BigCellUnitary_col_e
import Theorems.Thm_GlobalTheory_BigCellUnitary_col_w
import Theorems.Thm_GlobalTheory_BigCellUnitary_col_es

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
theorem _root_.solution (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (bigCell k r c μ).submatrix (pos k r) (pos k r) =
      fromBlocks (fromBlocks 0 (diagonal fun a => (star (c a))⁻¹) (diagonal c) 0) 0 0 μ := by
  ext ((a | a) | a) ((b | b) | b) <;>
    have ha := a.isLt <;> have hb := b.isLt <;>
    simp only [pos, Sum.elim_inl, Sum.elim_inr, submatrix_apply, col_e, col_w, col_es,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, diagonal_apply]
  · exact if_neg (by show ¬ a.val = _; omega)
  · have : ((eI k r a).val = b.val) ↔ a = b := (Fin.ext_iff (a := a) (b := b)).symm
    exact (if_congr this rfl rfl).trans (by split_ifs with h <;> simp [h])
  · exact dif_neg (by show ¬ (r ≤ a.val ∧ _); omega)
  · have : ((esI k r a).val = 2 * r + k - b.val) ↔ a = b := by
      rw [Fin.ext_iff]; show 2 * r + k - a.val = _ ↔ _; omega
    exact (if_congr this rfl rfl).trans (by split_ifs with h <;> simp [h])
  · exact if_neg (by show ¬ 2 * r + k - a.val = _; omega)
  · exact dif_neg (by show ¬ (_ ∧ 2 * r + k - a.val ≤ _); omega)
  · exact if_neg (by show ¬ r + a.val = _; omega)
  · exact if_neg (by show ¬ r + a.val = _; omega)
  · rw [dif_pos (by show r ≤ r + a.val ∧ r + a.val ≤ _; omega)]
    congr 1
    apply Fin.ext
    show r + a.val - r = a.val
    omega
end GlobalTheory.BigCellUnitary
