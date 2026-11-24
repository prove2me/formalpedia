-- Prove2me | solution 1 for GlobalTheory.IdemLift.idem_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:19.233338+00:00
-- url     : https://prove2.me/submissions/9366f8da-e6bc-4a9b-868a-a633f79176bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralIdempotentLiftNewton
import Theorems.Thm_GlobalTheory_IdemLift_seq_inv
import Theorems.Thm_GlobalTheory_IdemLift_seq_succ_sub
import Theorems.Thm_GlobalTheory_IdemLift_seq_sub_le
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_ClassParam_Intw_mul
import Theorems.Thm_GlobalTheory_ClassParam_Iso_mul
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_zero
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
open GlobalTheory GlobalTheory.IdemLift
open Filter Topology
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
namespace GlobalTheory.IdemLift
theorem _root_.solution (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [CompleteSpace E]
    (n : ℕ) (N x a : Matrix (Fin n) (Fin n) E) (ϖ : E) :
    ‖ϖ‖ < 1 → x * N = N * x → (∀ i j, ‖x i j‖ ≤ 1) → (∀ i j, ‖a i j‖ ≤ 1) → x * x - x = ϖ • a →
    ∃ e a' : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a' * N = N * a' ∧ e * e = e ∧
      (∀ i j, ‖e i j‖ ≤ 1) ∧ (∀ i j, ‖a' i j‖ ≤ 1) ∧ e - x = ϖ • a' := by
  intro hϖ hxN hx ha hxa
  have hinv := seq_inv x N a ϖ hxN hx ha hxa
  have hpow : ∀ k : ℕ, ‖ϖ‖ ^ (2 ^ k) ≤ ‖ϖ‖ ^ k := fun k =>
    pow_le_pow_of_le_one (norm_nonneg _) hϖ.le (Nat.lt_two_pow_self).le
  have hcs : ∀ i j, CauchySeq (fun k => seq x k i j) := by
    intro i j
    refine cauchySeq_of_le_geometric ‖ϖ‖ 1 hϖ (fun k => ?_)
    rw [dist_comm, dist_eq_norm, one_mul]
    exact (seq_succ_sub x N a ϖ hxN hx ha hxa k i j).trans (hpow k)
  choose e he using fun i j => cauchySeq_tendsto_of_complete (hcs i j)
  have hT : Tendsto (seq x) atTop (𝓝 (Matrix.of e)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => he i j

  have heN : Matrix.of e * N = N * Matrix.of e := by
    have hcl : IsClosed {M : Matrix (Fin n) (Fin n) E | M * N = N * M} :=
      isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
    exact hcl.mem_of_tendsto hT (Eventually.of_forall fun k => (hinv k).2.1)

  have heI : ∀ i j, ‖Matrix.of e i j‖ ≤ 1 := fun i j =>
    le_of_tendsto' (he i j).norm fun k => (hinv k).1 i j

  have hee : Matrix.of e * Matrix.of e = Matrix.of e := by
    have hD : Tendsto (fun k => seq x k * seq x k - seq x k) atTop
        (𝓝 (Matrix.of e * Matrix.of e - Matrix.of e)) := (hT.mul hT).sub hT
    rw [← sub_eq_zero]
    ext i j
    have h1 : Tendsto (fun k => (seq x k * seq x k - seq x k) i j) atTop
        (𝓝 ((Matrix.of e * Matrix.of e - Matrix.of e) i j)) :=
      tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hD i) j
    have h0 : Tendsto (fun k => (seq x k * seq x k - seq x k) i j) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one
        (norm_nonneg ϖ) hϖ)
      obtain ⟨-, -, b, hb, hd⟩ := hinv k
      rw [hd, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow]
      exact (mul_le_of_le_one_right (by positivity) (hb i j)).trans (hpow k)
    simpa using tendsto_nhds_unique h1 h0

  have hex : ∀ i j, ‖(Matrix.of e - x) i j‖ ≤ ‖ϖ‖ := by
    intro i j
    have h1 : Tendsto (fun k => (seq x k - x) i j) atTop (𝓝 ((Matrix.of e - x) i j)) := by
      simpa [Matrix.sub_apply] using (he i j).sub_const (x i j)
    exact le_of_tendsto' h1.norm fun k => seq_sub_le x N a ϖ hϖ hxN hx ha hxa k i j
  by_cases h0 : ϖ = 0
  · have hz : Matrix.of e - x = 0 := by
      ext i j
      have := hex i j
      rw [h0, norm_zero] at this
      simpa using norm_le_zero_iff.1 this
    refine ⟨Matrix.of e, 0, heN, by simp, hee, heI, integ_zero, ?_⟩
    rw [hz, smul_zero]
  · refine ⟨Matrix.of e, ϖ⁻¹ • (Matrix.of e - x), heN, ?_, hee, heI, ?_, ?_⟩
    · rw [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, heN, hxN]
    · intro i j
      rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
      exact inv_mul_le_one_of_le₀ (hex i j) (norm_nonneg _)
    · rw [smul_inv_smul₀ h0]
end GlobalTheory.IdemLift
