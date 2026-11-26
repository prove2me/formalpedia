-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_zero_variance_arrivals_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:23:45.309916+00:00
-- url     : https://prove2.me/submissions/989d57e8-bc02-436c-82fc-40713ae402e5

import Definitions.Def_ManyServerQED_Scheduling_Model

open Filter Topology MeasureTheory ProbabilityTheory Set Finset
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
open scoped NNReal ENNReal

private theorem epoch_sum_eq {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (i : Fin k) (ω : Ω) (m : ℕ) :
    ∑ j ∈ range m, M.U i (j+1) ω = partialSum (fun j => M.U i j ω) m := by
  unfold partialSum
  rw [show Finset.Icc 1 m = Finset.Ico 1 (m+1) from by ext; simp,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, add_comm]

private theorem renewal_on_rate_clock {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (s : ℝ) :
    M.A n i ω s =
      ((renewalCount (fun j => ∑ l ∈ range j, M.U i (l+1) ω) (M.lamN n i * s)).toNat : ℝ) := by
  have heq (j : ℕ) : M.arrivalEpoch n i ω j = (∑ l ∈ range j, M.U i (l+1) ω) / M.lamN n i := by
    rw [epoch_sum_eq]
    simp [SystemSequence.arrivalEpoch, partialSum, Finset.sum_div]
  unfold SystemSequence.A renewalCount
  simp only [heq, div_le_iff₀ (M.lamN_pos n i), mul_comm s]

theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (i : Fin k) (hi : M.cU2 i = 0) :
    ∀ᵐ ω ∂M.P, ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
      |M.Ahat n ω t i| ≤ 1/Real.sqrt n := by
  let : IsProbabilityMeasure M.P := M.isProb
  have hm0 : AEMeasurable (M.U i 1) M.P := (M.U_meas i 1).aemeasurable
  have he : evariance (M.U i 1) M.P = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).1 hi).resolve_right (M.U_memLp i).evariance_ne_top
  have hU : M.U i 1 =ᵐ[M.P] fun _ => 1 := by
    simpa only [M.U_mean] using (evariance_eq_zero_iff hm0).1 he
  have hL : M.P.map (M.U i 1) = Measure.dirac (1:ℝ) := by
    rw [Measure.map_congr hU,Measure.map_const,measure_univ,one_smul]
  have hAll : ∀ᵐ ω ∂M.P, ∀ j : ℕ, M.U i (j+1) ω = 1 := by
    apply ae_all_iff.2
    intro j
    exact (show HasLaw (M.U i (j+1)) (Measure.dirac (1:ℝ)) M.P from
      ⟨(M.U_meas _ _).aemeasurable,(M.U_ident i (j+1) (by omega)).map_eq.trans hL⟩).ae_eq_of_dirac
  filter_upwards [hAll] with ω hω
  intro n t ht
  have hS : 0 ≤ M.lamN n i*t := mul_nonneg (M.lamN_pos n i).le ht
  let z := M.lamN n i*t
  have hR : renewalCount (fun j : ℕ => (j:ℝ)) z = (⌊z⌋₊:ℕ∞) := by
    unfold renewalCount
    apply le_antisymm
    · refine iSup₂_le fun j hj => ?_
      exact_mod_cast (Nat.le_floor hj)
    · exact le_iSup₂_of_le ⌊z⌋₊ (Nat.floor_le hS) le_rfl
  have hA : M.A n i ω t = (⌊z⌋₊:ℝ) := by
    rw [renewal_on_rate_clock M n i ω]
    simp only [hω,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
    rw [hR, ENat.toNat_natCast]
  unfold SystemSequence.Ahat
  rw [hA,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  change |(⌊z⌋₊:ℝ)-z| ≤ 1
  have hl := Nat.floor_le hS
  have hu := Nat.lt_floor_add_one z
  rw [abs_of_nonpos (sub_nonpos.2 hl)]
  linarith
