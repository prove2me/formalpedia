-- Prove2me | solution 1 for GlobalTheory.ThetaGen.le_pow_of_succ_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:31:06.804577+00:00
-- url     : https://prove2.me/submissions/c323b6e7-ea48-486b-b8d5-2fbd9f3e1e63

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaGen
variable {X : Type}
variable (R : ℕ → Submodule ℂ (X → ℂ))
namespace GlobalTheory.ThetaGen
theorem _root_.solution (hmul : ∀ a b, R a * R b ≤ R (a + b)) {e : ℕ} (h1e : 1 ≤ e)
    (he : ∀ d, e ≤ d → R (d + 1) ≤ R 1 * R d) (j : ℕ) : R (e * (j + 1)) ≤ R e ^ (j + 1) := by
  have h : ∀ d, e ≤ d → ∀ k, R (d + (k + 1)) ≤ R (k + 1) * R d := by
    intro d hd k
    induction k with
    | zero => exact he d hd
    | succ k ih =>
      calc R (d + (k + 1 + 1)) ≤ R 1 * R (d + (k + 1)) := he (d + (k + 1)) (by omega)
        _ ≤ R 1 * (R (k + 1) * R d) := by gcongr
        _ = (R 1 * R (k + 1)) * R d := (mul_assoc _ _ _).symm
        _ ≤ R (k + 1 + 1) * R d := by
          have := hmul 1 (k + 1)
          rw [add_comm 1] at this
          gcongr
  induction j with
  | zero => simp
  | succ j ih =>
    rcases e with _ | k
    · omega
    · have := h ((k + 1) * (j + 1)) (Nat.le_mul_of_pos_right _ (by omega)) k
      calc R ((k + 1) * (j + 1 + 1)) = R ((k + 1) * (j + 1) + (k + 1)) := by rw [mul_add_one]
        _ ≤ R (k + 1) * R ((k + 1) * (j + 1)) := this
        _ ≤ R (k + 1) * R (k + 1) ^ (j + 1) := by gcongr
        _ = _ := by rw [← pow_succ']
end GlobalTheory.ThetaGen
