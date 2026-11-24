-- Prove2me | solution 1 for GlobalTheory.EtaChar.exists_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:27:35.081232+00:00
-- url     : https://prove2.me/submissions/4409fff7-1d5b-40bc-bcd4-e3f71a34c7eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.EtaChar
namespace GlobalTheory.EtaChar
theorem _root_.solution (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] :
    ∃ π : F, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hc : IsCompact (Metric.ball (0 : F) 1) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball _ _)
      Metric.ball_subset_closedBall
  obtain ⟨π, hπm, hmax⟩ := hc.exists_isMaxOn ⟨0, Metric.mem_ball_self one_pos⟩ continuous_norm.continuousOn
  have hπ1 : ‖π‖ < 1 := by simpa using hπm
  have hle : ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖ := fun y hy => hmax (by simpa using hy)
  obtain ⟨x0, hx0, hx01⟩ := NormedField.exists_norm_lt_one F
  have hπ0 : 0 < ‖π‖ := lt_of_lt_of_le hx0 (hle x0 hx01)
  refine ⟨π, hπ0, hπ1, fun x hx => ?_⟩
  set q := ‖π‖ with hq
  have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hqi : 1 < q⁻¹ := one_lt_inv₀ hπ0 |>.2 hπ1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hxp hqi
  have hqn : 0 < q ^ (n + 1) := zpow_pos hπ0 _
  have hz : ‖x * π ^ (n + 1)‖ = ‖x‖ * q ^ (n + 1) := by rw [norm_mul, norm_zpow]
  have hup : ‖x‖ * q ^ (n + 1) ≤ 1 := by
    calc ‖x‖ * q ^ (n + 1) ≤ q⁻¹ ^ (n + 1) * q ^ (n + 1) := mul_le_mul_of_nonneg_right hn2 hqn.le
      _ = 1 := by rw [_root_.inv_zpow, inv_mul_cancel₀ hqn.ne']
  have hlo : q < ‖x‖ * q ^ (n + 1) := by
    calc q = q⁻¹ ^ n * q ^ (n + 1) := by
            rw [_root_.inv_zpow, zpow_add_one₀ hπ0.ne', ← mul_assoc, inv_mul_cancel₀ (zpow_pos hπ0 n).ne', one_mul]
      _ < ‖x‖ * q ^ (n + 1) := mul_lt_mul_of_pos_right hn1 hqn
  have heq : ‖x‖ * q ^ (n + 1) = 1 := by
    by_contra hne
    have := hle (x * π ^ (n + 1)) (by rw [hz]; exact lt_of_le_of_ne hup hne)
    rw [hz] at this
    linarith
  refine ⟨-(n + 1), ?_⟩
  rw [_root_.zpow_neg]; exact eq_inv_of_mul_eq_one_left heq
end GlobalTheory.EtaChar
