-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_past_generators_are_ambient_measurable
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:53:36.373626+00:00
-- url     : https://prove2.me/submissions/c55617dc-038f-493e-9c2b-e45c44b63c72

import Theorems.Thm_ManyServerQED_Scheduling_scp_joint_state_measurable
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

private theorem epoch_measurable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (m : ℕ) :
    Measurable (fun ω => M.arrivalEpoch n i ω m) := by
  unfold SystemSequence.arrivalEpoch partialSum
  exact Finset.measurable_sum _ (fun j _ => (M.U_meas i j).div_const _)

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

private theorem epoch_crosses {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (t : ℝ) :
    ∃ m : ℕ, t < M.arrivalEpoch n i ω m := by
  obtain ⟨m, hm⟩ := ((tendsto_atTop.1 (M.U_finite i ω)) (t * M.lamN n i + 1)).exists
  refine ⟨m, ?_⟩
  unfold SystemSequence.arrivalEpoch
  rw [show partialSum (fun j => M.U i j ω / M.lamN n i) m =
    partialSum (fun j => M.U i j ω) m / M.lamN n i by simp [partialSum, Finset.sum_div],
    lt_div_iff₀ (M.lamN_pos n i)]
  linarith

private theorem arrival_joint_measurable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) :
    Measurable (fun z : Ω × ℝ≥0 => M.A n i z.1 z.2) := by
  classical
  let h (z : Ω × ℝ≥0) := epoch_crosses M n i z.1 z.2
  have hf : Measurable (fun z : Ω × ℝ≥0 => Nat.find (h z)) := by
    exact measurable_find h (fun j => measurableSet_lt
      (measurable_snd.coe_nnreal_real) ((epoch_measurable M n i j).comp measurable_fst))
  have he (z : Ω × ℝ≥0) : M.A n i z.1 z.2 = ((Nat.find (h z) - 1 : ℕ) : ℝ) := by
    let b := Nat.find (h z)
    have hb : (z.2 : ℝ) < M.arrivalEpoch n i z.1 b := Nat.find_spec (h z)
    have hb0 : 0 < b := by
      by_contra! hh
      rw [Nat.eq_zero_of_le_zero hh] at hb
      simp [SystemSequence.arrivalEpoch, partialSum] at hb
    let j := b - 1
    have hj : j < b := by omega
    have hj' : j + 1 = b := by dsimp [j]; omega
    have h1 : M.arrivalEpoch n i z.1 j ≤ (z.2 : ℝ) :=
      le_of_not_gt (Nat.find_min (h z) hj)
    have h2 : (z.2 : ℝ) < M.arrivalEpoch n i z.1 (j + 1) := by rwa [hj']
    unfold SystemSequence.A
    rw [renewal_eq_of_bracket (epoch_strict M n i z.1).monotone h1 h2, ENat.toNat_natCast]
  simp_rw [he]
  have hm : Measurable (fun m : ℕ => ((m - 1 : ℕ) : ℝ)) := measurable_of_countable _
  exact hm.comp hf

private theorem poisson_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {a : ℝ} (hN : IsPoissonProcess P N a) :
    Measurable (fun z : Ω × ℝ≥0 => N z.1 z.2) := by
  have hRight (ω : Ω) (t : ℝ≥0) :
      ContinuousWithinAt (fun s : ℝ≥0 => N ω s) (Ici t) t := by
    exact (((hN.cadlag ω).1 t t.2).comp continuous_subtype_val.continuousWithinAt)
      (fun s hs => hs)
  exact (AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
    (fun t ω => N ω t) (fun t => hN.meas t) hRight).comp measurable_swap


private theorem interval_primitive_measurable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (v : Ω → ℝ → E) (hv : Measurable (Function.uncurry v))
    (t : ℝ) (ht : 0 ≤ t) :
    Measurable (fun ω => ∫ s in (0:ℝ)..t, v ω s) := by
  have hS : MeasurableSet (Prod.snd ⁻¹' Ioc (0:ℝ) t : Set (Ω × ℝ)) :=
    measurableSet_Ioc.preimage measurable_snd
  have hI : StronglyMeasurable ((Prod.snd ⁻¹' Ioc (0:ℝ) t : Set (Ω × ℝ)).indicator
      (Function.uncurry v)) := hv.stronglyMeasurable.indicator hS
  have h := hI.integral_prod_right' (ν := volume)
  convert h.measurable using 1
  funext ω
  have he (s : ℝ) : (Prod.snd ⁻¹' Ioc (0:ℝ) t : Set (Ω × ℝ)).indicator
      (Function.uncurry v) (ω,s) = (Ioc (0:ℝ) t).indicator (v ω) s := by
    by_cases hs : s ∈ Ioc (0:ℝ) t <;> simp [hs]
  simp only [he]
  rw [integral_indicator measurableSet_Ioc,intervalIntegral.integral_of_le ht]


set_option maxHeartbeats 900000 in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X₀ : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hC : M.IsSCP n X₀ X Ψ)
    (i : Fin k) (T : ℝ) (hT : 0 ≤ T) :
    Measurable (fun ω => M.A n i ω T) ∧
      Measurable (fun ω => M.S n i ω (busyTime Ψ ω i T)) ∧
      Measurable (fun ω => M.R n i ω (queueTime X Ψ ω i T)) ∧
      Measurable (fun ω => X ω T i-Ψ ω T i) ∧
      Measurable (fun ω => Ψ ω T i) ∧ Measurable (fun ω => X ω T i) := by
  obtain ⟨hX,hP⟩ := scp_joint_state_measurable M n X₀ X Ψ hC
  have hK (f : Ω → ℝ → ℝ) (hf : Measurable (fun z : Ω × ℝ≥0 => f z.1 z.2))
      (t : ℝ) (ht : 0 ≤ t) :
      Measurable (fun ω => ∫ s in (0:ℝ)..t,f ω s) := by
    have hm : Measurable (Function.uncurry (fun ω (s:ℝ) => f ω s.toNNReal)) :=
      hf.comp (measurable_fst.prodMk measurable_snd.real_toNNReal)
    have hE : (fun ω => ∫ s in (0:ℝ)..t,f ω s) = (fun ω => ∫ s in (0:ℝ)..t,f ω s.toNNReal) := by
      funext ω
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc (0:ℝ) t := (uIcc_of_le ht) ▸ hs
      change f ω s = f ω (s.toNNReal:ℝ)
      rw [Real.coe_toNNReal _ hs'.1]
    rw [hE]
    exact interval_primitive_measurable _ hm t ht
  have hClockEval (f : Ω → ℝ → ℝ) (hf : Measurable (fun z : Ω × ℝ≥0 => f z.1 z.2))
      (c : Ω → ℝ) (hc : Measurable c) (hn : ∀ ω, 0 ≤ c ω) : Measurable (fun ω => f ω (c ω)) := by
    have hm := hf.comp (measurable_id.prodMk hc.real_toNNReal)
    simpa only [Function.comp_def,id_eq,Real.coe_toNNReal _ (hn _)] using hm
  let t := T
  have ht : 0 ≤ t := hT
  let s : ℝ≥0 := ⟨t,ht⟩
  have hPt : Measurable (fun ω => Ψ ω t i) :=
    ((measurable_pi_apply i).comp hP).comp (measurable_id.prodMk (measurable_const (a := s)))
  have hXt : Measurable (fun ω => X ω t i) :=
    ((measurable_pi_apply i).comp hX).comp (measurable_id.prodMk (measurable_const (a := s)))
  have hΦt : Measurable (fun ω => X ω t i-Ψ ω t i) := hXt.sub hPt
  have hStamp : Measurable (fun ω : Ω => (ω, s)) :=
    measurable_id.prodMk measurable_const
  have hA : Measurable (fun ω => M.A n i ω t) := by
    change Measurable ((fun z : Ω × ℝ≥0 => M.A n i z.1 (z.2 : ℝ)) ∘ (fun ω : Ω => (ω,s)))
    exact (arrival_joint_measurable M n i).comp hStamp
  have hBT : Measurable (fun ω => busyTime Ψ ω i t) :=
    hK (fun ω s => Ψ ω s i) ((measurable_pi_apply i).comp hP) t ht
  have hQT : Measurable (fun ω => queueTime X Ψ ω i t) :=
    hK (fun ω s => X ω s i-Ψ ω s i)
      (((measurable_pi_apply i).comp hX).sub ((measurable_pi_apply i).comp hP)) t ht
  have hS : Measurable (fun ω => M.S n i ω (busyTime Ψ ω i t)) :=
    hClockEval (M.S n i) (poisson_joint_measurable (M.S_poisson n i)) _ hBT (fun ω =>
      intervalIntegral.integral_nonneg (μ := volume) ht (fun s hs => hC.controlled.psi_nonneg ω s i hs.1))
  have hR : Measurable (fun ω => M.R n i ω (queueTime X Ψ ω i t)) :=
    hClockEval (M.R n i) (poisson_joint_measurable (M.R_poisson n i)) _ hQT (fun ω =>
      intervalIntegral.integral_nonneg (μ := volume) ht (fun s hs => hC.controlled.phi_nonneg ω s i hs.1))
  exact ⟨hA,hS,hR,hΦt,hPt,hXt⟩
