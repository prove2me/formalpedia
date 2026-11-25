-- Prove2me | solution 1 for GlobalTheory.LevelUnitary.incl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:41:02.267271+00:00
-- url     : https://prove2.me/submissions/5cfd1c51-263f-41d4-93d3-97cb965b24c1

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramRight

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
open GlobalTheory GlobalTheory.LevelUnitary
variable (k i r' : ℕ)
namespace GlobalTheory.LevelUnitary
theorem _root_.solution {m : Type} (M : Matrix (Fin (2 * r' + k + 1)) m ℂ) (p) (q : m) :
    (incl k i r' * M) p q =
      if hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i then M ⟨p.val - i, by omega⟩ q else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with hp
  · rw [Finset.sum_eq_single ⟨p.val - i, by omega⟩]
    · have : p = levPos k i r' ⟨p.val - i, by omega⟩ := by
        apply Fin.ext; simp only [levPos]; omega
      rw [incl, if_pos this, one_mul]
    · intro b _ hb
      have : ¬ p = levPos k i r' b := by
        intro h; apply hb; apply Fin.ext
        have := congrArg Fin.val h
        simp only [levPos] at this ⊢; omega
      rw [incl, if_neg this, zero_mul]
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    have : ¬ p = levPos k i r' b := by
      intro h; apply hp
      have := congrArg Fin.val h
      have hb := b.isLt
      simp only [levPos] at this ⊢; omega
    rw [incl, if_neg this, zero_mul]
end GlobalTheory.LevelUnitary
