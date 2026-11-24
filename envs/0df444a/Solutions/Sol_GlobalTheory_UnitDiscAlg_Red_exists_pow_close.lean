-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.Red.exists_pow_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:50.907734+00:00
-- url     : https://prove2.me/submissions/4778b765-8d4d-4e2d-8a95-3d66d7265552

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnilStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixDecompose
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg GlobalTheory.UnitDiscAlg.Red
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
namespace GlobalTheory.UnitDiscAlg.Red
theorem _root_.solution [LocallyCompactSpace E] (y : Matrix (Fin n) (Fin n) E)
    (hy : ∀ i j, ‖y i j‖ ≤ 1) : ∃ a b : ℕ, a < b ∧ Sm (y ^ b - y ^ a) := by
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  let f : ℕ → Fin n → Fin n → E := fun k i j => (y ^ k) i j
  have hs : IsCompact (Metric.closedBall (0 : Fin n → Fin n → E) 1) := isCompact_closedBall _ _
  have hf : ∀ k, f k ∈ Metric.closedBall (0 : Fin n → Fin n → E) 1 := by
    intro k
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    exact integ_pow hy k i j
  obtain ⟨x, -, φ, hφ, hlim⟩ := hs.tendsto_subseq hf
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq 1 one_pos
  refine ⟨φ N, φ (N + 1), hφ (Nat.lt_succ_self N), ?_⟩
  intro i j
  have h1 := hN (N + 1) (Nat.le_succ N) N le_rfl
  have h2 : dist (f (φ (N + 1)) i j) (f (φ N) i j) < 1 :=
    lt_of_le_of_lt ((dist_le_pi_dist _ _ j).trans (dist_le_pi_dist _ _ i)) h1
  rw [dist_eq_norm] at h2
  simpa [f, Matrix.sub_apply] using h2
end GlobalTheory.UnitDiscAlg.Red
