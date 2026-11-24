-- Prove2me | solution 1 for GlobalTheory.FirstColumnConjugation.exists_det_ne_zero_first_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:07:48.168673+00:00
-- url     : https://prove2.me/submissions/2402c9f5-c780-45a9-ae9e-17742779ffef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDetNeZeroFirstCol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FirstColumnConjugation
open Matrix
namespace GlobalTheory.FirstColumnConjugation
theorem _root_.solution {n : ℕ} (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, P.det ≠ 0 ∧ ∀ k, P k 0 = v k := by
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.1 hv
  let u : Fin (n + 1) → ℂ := v - Pi.single k₀ (1 : ℂ)
  let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    1 + replicateCol Unit u * replicateRow Unit (Pi.single k₀ (1 : ℂ))
  have hQdet : Q.det = v k₀ := by
    simp only [Q]
    rw [det_one_add_replicateCol_mul_replicateRow]
    simp [u]
  have hQcol : ∀ k, Q k k₀ = v k := by
    intro k
    simp only [Q, u]
    by_cases h : k = k₀ <;> simp [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, h]
  refine ⟨Q.submatrix id (Equiv.swap 0 k₀), ?_, fun k => ?_⟩
  · rw [det_permute', hQdet]
    exact mul_ne_zero (by simp) hk₀
  · simp [hQcol]
end GlobalTheory.FirstColumnConjugation
