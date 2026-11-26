-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_observation_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:13:57.519955+00:00
-- url     : https://prove2.me/submissions/6f688b4a-e833-49d7-b2b1-f9981e94bc86

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem renewal_eq_of_bracket {e : ℕ → ℝ} (he : Monotone e) {s : ℝ} {j : ℕ}
    (hj : e j ≤ s) (hj_succ : s < e (j + 1)) : renewalCount e s = j := by
  unfold renewalCount
  refine le_antisymm (iSup_le fun r => iSup_le fun hr => ?_) (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  have h : r ≤ j := by
    by_contra! hjr
    exact (not_lt_of_ge hr) (hj_succ.trans_le (he hjr))
  exact_mod_cast h

private theorem epoch_strict {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) :
    StrictMono (M.arrivalEpoch n i ω) := by
  apply strictMono_nat_of_lt_succ
  intro j
  unfold SystemSequence.arrivalEpoch partialSum
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
  have hp : 0 < M.U i (j + 1) ω / M.lamN n i :=
    div_pos (M.U_pos i _ ω (by omega)) (M.lamN_pos n i)
  linarith


set_option maxHeartbeats 1350000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (u0 : Fin k → ℝ) (f : (Fin k → ℝ) → ℝ)
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ) (X0 : ℕ → Fin k → ℕ)
    (n : ℕ) (hC : M.IsControlled n (X0 n) (X n) (Ψ n)) (ω : Ω) :
    queueHJBObservation M L γ u0 f X Ψ n ω 0 =
      Fin.append (Fin.append (Fin.append (M.Xhat0 n (X0 n)) 0) 0) ![0,0] := by
  have hA (i : Fin k) : M.A n i ω 0 = 0 := by
    have h0 : M.arrivalEpoch n i ω 0 = 0 := by simp [SystemSequence.arrivalEpoch,partialSum]
    have h1 : 0 < M.arrivalEpoch n i ω 1 := h0 ▸ epoch_strict M n i ω (by omega : 0 < 1)
    change ((renewalCount (M.arrivalEpoch n i ω) 0).toNat:ℝ) = 0
    rw [renewal_eq_of_bracket (epoch_strict M n i ω).monotone h0.le h1]
    simp
  have hB (i : Fin k) : busyTime (Ψ n) ω i 0 = 0 := by simp [busyTime]
  have hQ (i : Fin k) : queueTime (X n) (Ψ n) ω i 0 = 0 := by simp [queueTime]
  have hX (i : Fin k) : M.Xhat n (X n) ω 0 i = M.Xhat0 n (X0 n) i := by
    have h := hC.eq7 ω 0 i (by norm_num)
    rw [hA,hB,hQ,(M.S_poisson n i).zero,(M.R_poisson n i).zero] at h
    simp only [add_zero,sub_zero] at h
    simp only [SystemSequence.Xhat,SystemSequence.Xhat0,h]
  have hW (i : Fin k) :
      (M.Ahat n ω 0 i-M.Shat n ω (busyTime (Ψ n) ω i 0/(n:ℝ)) i-
        M.Rhat n ω (queueTime (X n) (Ψ n) ω i 0/(n:ℝ)) i)/M.diffData.r i = 0 := by
    simp [SystemSequence.Ahat,SystemSequence.Shat,SystemSequence.Rhat,hA,hB,hQ,
      (M.S_poisson n i).zero,(M.R_poisson n i).zero]
  simp only [queueHJBObservation,funext hX,show (fun i =>
    (M.Ahat n ω 0 i-M.Shat n ω (busyTime (Ψ n) ω i 0/(n:ℝ)) i-
      M.Rhat n ω (queueTime (X n) (Ψ n) ω i 0/(n:ℝ)) i)/M.diffData.r i) = 0 from funext hW,
    intervalIntegral.integral_same]
  rfl
