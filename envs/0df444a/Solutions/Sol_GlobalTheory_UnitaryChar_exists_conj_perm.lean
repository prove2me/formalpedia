-- Prove2me | solution 1 for GlobalTheory.UnitaryChar.exists_conj_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:14.865211+00:00
-- url     : https://prove2.me/submissions/434462a6-a61b-4726-ae89-422d3a905741

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CircleHomEqZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.UnitaryChar
variable {n : ℕ}
namespace GlobalTheory.UnitaryChar
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (t : Fin n → Circle) :
    ∃ P : Matrix.unitaryGroup (Fin n) ℂ, P * diagHom n t = diagHom n (t ∘ σ) * P := by
  refine ⟨⟨σ.permMatrix ℂ, ?_⟩, Subtype.ext ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_permMatrix,
      ← permMatrix_mul]
    simp
  · change σ.permMatrix ℂ * diagonal _ = diagonal _ * σ.permMatrix ℂ
    ext i j
    rw [mul_diagonal, diagonal_mul]
    by_cases h : σ i = j
    · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]
    · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]
end GlobalTheory.UnitaryChar
