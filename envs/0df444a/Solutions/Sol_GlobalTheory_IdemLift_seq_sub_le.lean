-- Prove2me | solution 1 for GlobalTheory.IdemLift.seq_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:31:15.629876+00:00
-- url     : https://prove2.me/submissions/1e6ac6b7-3ac0-48be-817d-419924fc2735

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralIdempotentLiftNewton
import Theorems.Thm_GlobalTheory_IdemLift_seq_succ_sub
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
theorem _root_.solution (x N a : Matrix (Fin n) (Fin n) E) (ϖ : E) (hϖ : ‖ϖ‖ < 1) (hxN : x * N = N * x)
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (ha : ∀ i j, ‖a i j‖ ≤ 1) (hxa : x * x - x = ϖ • a) (k : ℕ) :
    ∀ i j, ‖(seq x k - x) i j‖ ≤ ‖ϖ‖ := by
  induction k with
  | zero => intro i j; simp [seq]
  | succ k ih =>
    intro i j
    have h1 := seq_succ_sub x N a ϖ hxN hx ha hxa k i j
    have h2 : ‖ϖ‖ ^ (2 ^ k) ≤ ‖ϖ‖ := by
      calc ‖ϖ‖ ^ (2 ^ k) ≤ ‖ϖ‖ ^ 1 :=
            pow_le_pow_of_le_one (norm_nonneg _) hϖ.le (Nat.one_le_two_pow)
        _ = ‖ϖ‖ := pow_one _
    have : (seq x (k + 1) - x) i j = (seq x (k + 1) - seq x k) i j + (seq x k - x) i j := by
      simp [Matrix.sub_apply]
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1.trans h2) (ih i j))
end GlobalTheory.IdemLift
