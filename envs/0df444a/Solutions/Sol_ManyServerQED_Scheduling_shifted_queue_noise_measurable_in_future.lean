-- Prove2me | solution 1 for ManyServerQED.Scheduling.shifted_queue_noise_measurable_in_future
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:13:57.733734+00:00
-- url     : https://prove2.me/submissions/c08cf538-8f2c-4c0b-ad59-6539a43e25e1

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

private theorem next_arrival_joint_measurable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) :
    Measurable (fun z : Ω × ℝ => M.nextArrival n i z.1 z.2) := by
  classical
  let h (z : Ω × ℝ) : ∃ m : ℕ, z.2 ≤ M.arrivalEpoch n i z.1 (m + 1) := by
    obtain ⟨m, hm⟩ := epoch_crosses M n i z.1 z.2
    exact ⟨m, hm.le.trans ((epoch_strict M n i z.1).monotone (Nat.le_succ m))⟩
  have he (z : Ω × ℝ) :
      M.nextArrival n i z.1 z.2 = M.arrivalEpoch n i z.1 ((Nat.find (h z)) + 1) := by
    let b := Nat.find (h z)
    let S : Set ℝ := {s | z.2 ≤ s ∧ ∃ m : ℕ, 1 ≤ m ∧ M.arrivalEpoch n i z.1 m = s}
    have hb : IsLeast S (M.arrivalEpoch n i z.1 (b + 1)) := by
      refine ⟨⟨Nat.find_spec (h z), b + 1, by omega, rfl⟩, ?_⟩
      rintro s ⟨hs, m, hm, rfl⟩
      have hm' : m = (m - 1) + 1 := by omega
      have hmin : b ≤ m - 1 := Nat.find_min' (h z) (by rw [← hm']; exact hs)
      exact (epoch_strict M n i z.1).monotone (by omega)
    exact hb.csInf_eq
  simp_rw [he]
  exact Measurable.find (fun m => (epoch_measurable M n i (m + 1)).comp measurable_fst)
    (fun m => measurableSet_le measurable_snd
      ((epoch_measurable M n i (m + 1)).comp measurable_fst)) h

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


set_option maxHeartbeats 1850000 in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (hn : 1 ≤ n) (X₀ : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hC : M.IsSCP n X₀ X Ψ)
    (i : Fin k) (b u : ℝ≥0) :
    let V (ω : Ω) :=
      ((M.Ahat n ω (M.nextArrival n i ω b+u) i - M.Ahat n ω (M.nextArrival n i ω b) i) -
        (M.Shat n ω (busyTime Ψ ω i b/(n:ℝ)+M.rho i*u) i -
          M.Shat n ω (busyTime Ψ ω i b/(n:ℝ)) i))/M.diffData.r i
    Measurable V ∧ Measurable[M.futureInfo n X Ψ b] V := by
  intro V
  let T (ω : Ω) := M.nextArrival n i ω b
  let B (ω : Ω) := busyTime Ψ ω i b
  let c : ℝ := (n:ℝ)*M.rho i*u
  have hρ : 0 ≤ M.rho i := (div_pos (M.lam_pos i) (M.mu_pos i)).le
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hρ) u.2
  have hTm : Measurable T := (next_arrival_joint_measurable M n i).comp
    (measurable_id.prodMk measurable_const)
  have hT (ω : Ω) : 0 ≤ T ω := by
    apply b.2.trans
    apply le_csInf
    · obtain ⟨j,hj⟩ := epoch_crosses M n i ω b
      exact ⟨M.arrivalEpoch n i ω (j+1),hj.le.trans ((epoch_strict M n i ω).monotone (Nat.le_succ j)),
        j+1,by omega,rfl⟩
    · exact fun t ht => ht.1
  have hBn (ω : Ω) : 0 ≤ B ω := intervalIntegral.integral_nonneg (μ := volume) b.2
    (fun s hs => hC.controlled.psi_nonneg ω s i hs.1)
  have hP := (scp_joint_state_measurable M n X₀ X Ψ hC).2
  have hPm : Measurable (Function.uncurry (fun ω (t : ℝ) => Ψ ω (t.toNNReal:ℝ) i)) :=
    ((measurable_pi_apply i).comp hP).comp (measurable_fst.prodMk measurable_snd.real_toNNReal)
  have hBm : Measurable B := by
    have hB' := interval_primitive_measurable (fun ω (t : ℝ) => Ψ ω (t.toNNReal:ℝ) i) hPm b b.2
    have hE : B = (fun ω => ∫ s in (0:ℝ)..(b:ℝ), Ψ ω (s.toNNReal:ℝ) i) := by
      funext ω
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc (0:ℝ) (b:ℝ) := (uIcc_of_le (show (0:ℝ) ≤ (b:ℝ) from b.2)) ▸ hs
      change Ψ ω s i = Ψ ω (s.toNNReal:ℝ) i
      rw [Real.coe_toNNReal _ hs'.1]
    rw [hE]
    exact hB'
  let A (ω : Ω) := M.A n i ω (T ω+u)-M.A n i ω (T ω)
  let S (ω : Ω) := M.S n i ω (B ω+c)-M.S n i ω (B ω)
  have hLift (f : Ω → ℝ → ℝ) (h : Measurable (fun z : Ω × ℝ≥0 => f z.1 z.2))
      (t : Ω → ℝ) (ht : Measurable t) (hp : ∀ ω, 0 ≤ t ω) :
      Measurable (fun ω => f ω (t ω)) := by
    have h' := h.comp (measurable_id.prodMk ht.real_toNNReal)
    simpa only [Function.comp_def,id_eq,Real.coe_toNNReal _ (hp _)] using h'
  have hAm : Measurable A := (hLift _ (arrival_joint_measurable M n i)
    _ (hTm.add_const _) (fun ω => add_nonneg (hT ω) u.2)).sub
    (hLift _ (arrival_joint_measurable M n i) _ hTm hT)
  have hSm : Measurable S := (hLift _ (poisson_joint_measurable (M.S_poisson n i))
    _ (hBm.add_const _) (fun ω => add_nonneg (hBn ω) hc)).sub
    (hLift _ (poisson_joint_measurable (M.S_poisson n i)) _ hBm hBn)
  have he : V = fun ω =>
      ((A ω-M.lamN n i*u)/Real.sqrt n - (S ω-M.muN n i*c)/Real.sqrt n)/M.diffData.r i := by
    funext ω
    dsimp only [V,A,S,T,B,c,SystemSequence.Ahat,SystemSequence.Shat]
    have hn' : (0:ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
    have hb (s : ℝ) : (n:ℝ)*(s/n) = s := mul_div_cancel₀ _ hn'.ne'
    simp only [mul_add,hb]
    ring
  let G := M.futureInfo n X Ψ b
  have hAg : Measurable[G] A := by
    apply measurable_iff_comap_le.2
    exact le_iSup_of_le i (le_iSup₂_of_le (u:ℝ) u.2 (le_sup_left.trans le_sup_left))
  have hSg : Measurable[G] S := by
    apply measurable_iff_comap_le.2
    exact le_iSup_of_le i (le_iSup₂_of_le c hc (le_sup_right.trans le_sup_left))
  rw [he]
  exact ⟨(((hAm.sub_const _).div_const _).sub ((hSm.sub_const _).div_const _)).div_const _,
    (((hAg.sub_const _).div_const _).sub ((hSg.sub_const _).div_const _)).div_const _⟩
