-- Prove2me | solution 1 for ManyServerQED.Scheduling.feedback_stopped_primitives_restart
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T19:00:24.93048+00:00
-- url     : https://prove2.me/submissions/eabc2c05-cc9c-4c8b-ac94-2d39db9d4492

import Theorems.Thm_ManyServerQED_Scheduling_primitive_suffix_at_deterministic_cuts
import Theorems.Thm_ManyServerQED_Scheduling_stopped_product_law_of_countable_cuts
import Definitions.Def_ManyServerQED_Scheduling_PrimitiveCuts
import Theorems.Thm_ManyServerQED_Scheduling_feedback_past_restricted_to_primitive_cut
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto

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


private theorem nat_cast_right_constant (g : ℝ → ℝ) (t : ℝ)
    (h : ∀ s, t ≤ s → ∃ m : ℕ, g s = m) (hc : ContinuousWithinAt g (Ici t) t) :
    ∀ᶠ s in 𝓝[Ici t] t, g s = g t := by
  obtain ⟨m, hm⟩ := h t le_rfl
  have hh := Metric.tendsto_nhds.1 hc (1 : ℝ) zero_lt_one
  filter_upwards [hh, self_mem_nhdsWithin (s := Ici t)] with s hs hst
  obtain ⟨j, hj⟩ := h s hst
  rw [Real.dist_eq, hj, hm, abs_lt] at hs
  rcases lt_trichotomy j m with hlt | heq | hgt
  · have hn : (j : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt hlt
    linarith [hs.1]
  · simp [hj, hm, heq]
  · have hn : (m : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hgt
    linarith [hs.2]

open ProbabilityTheory

private theorem index_exists {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (t : ℝ) :
    ∃ m : ℕ, t ≤ M.arrivalEpoch n i ω (m + 1) := by
  obtain ⟨m, hm⟩ := epoch_crosses M n i ω t
  exact ⟨m, hm.le.trans ((epoch_strict M n i ω).monotone (Nat.le_succ m))⟩

private noncomputable def firstIndex {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (t : ℝ) : ℕ := by
  classical
  exact Nat.find (index_exists M n i ω t)

private theorem firstIndex_le {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (t : ℝ) (j : ℕ) :
    firstIndex M n i ω t ≤ j ↔ t ≤ M.arrivalEpoch n i ω (j + 1) := by
  classical
  unfold firstIndex
  exact ⟨fun h => (Nat.find_spec (index_exists M n i ω t)).trans
    ((epoch_strict M n i ω).monotone (Nat.succ_le_succ h)), Nat.find_min' (index_exists M n i ω t)⟩

private theorem nextArrival_eq_firstIndex {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (t : ℝ) :
    M.nextArrival n i ω t = M.arrivalEpoch n i ω (firstIndex M n i ω t + 1) := by
  let b := firstIndex M n i ω t
  let S : Set ℝ := {s | t ≤ s ∧ ∃ m : ℕ, 1 ≤ m ∧ M.arrivalEpoch n i ω m = s}
  have hb : IsLeast S (M.arrivalEpoch n i ω (b + 1)) := by
    refine ⟨⟨(firstIndex_le M n i ω t b).1 le_rfl, b + 1, by omega, rfl⟩, ?_⟩
    rintro s ⟨hs, m, hm, rfl⟩
    have hm' : m = (m - 1) + 1 := by omega
    have hmin := (firstIndex_le M n i ω t (m - 1)).2 (by rwa [← hm'])
    exact (epoch_strict M n i ω).monotone (by omega)
  exact hb.csInf_eq

private theorem epoch_nonneg {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (j : ℕ) :
    0 ≤ M.arrivalEpoch n i ω j := by
  have h := (epoch_strict M n i ω).monotone (Nat.zero_le j)
  simpa [SystemSequence.arrivalEpoch, partialSum] using h

private theorem suffix_measurable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) :
    Measurable (primitiveSuffix M n d p q) := by
  apply measurable_pi_lambda
  rintro (⟨i, u⟩ | (⟨i, u⟩ | ⟨i, u⟩))
  · let e : Ω → ℝ := fun ω => M.arrivalEpoch n i ω (d i)
    have he : Measurable e := epoch_measurable M n i (d i)
    have hA (s : ℝ≥0) : Measurable (fun ω => M.A n i ω (e ω + s)) := by
      have hh := (arrival_joint_measurable M n i).comp
        (measurable_id.prodMk ((he.add_const (s : ℝ)).real_toNNReal))
      convert hh using 1
      funext ω
      change _ = M.A n i ω ((e ω + (s : ℝ)).toNNReal : ℝ)
      have hpos : 0 ≤ e ω + (s : ℝ) := add_nonneg (epoch_nonneg M n i ω (d i)) s.2
      rw [Real.coe_toNNReal _ hpos]
    change Measurable (fun ω => M.A n i ω (e ω + u) - M.A n i ω (e ω))
    exact (hA u).sub (by simpa only [NNReal.coe_zero, add_zero] using hA 0)
  · exact ((M.S_poisson n i).meas _).sub ((M.S_poisson n i).meas _)
  · exact ((M.R_poisson n i).meas _).sub ((M.R_poisson n i).meas _)

private theorem prefix_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) :
    primitivePrefixInfo M n d p q ≤ mΩ := by
  unfold primitivePrefixInfo
  refine sup_le (sup_le ?_ ?_) ?_
  · exact iSup_le fun i => iSup_le fun j => iSup_le fun _ => (M.U_meas i (j + 1)).comap_le
  · exact iSup_le fun i => iSup_le fun u => iSup_le fun _ => ((M.S_poisson n i).meas u).comap_le
  · exact iSup_le fun i => iSup_le fun u => iSup_le fun _ => ((M.R_poisson n i).meas u).comap_le

private theorem prefix_mono {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) {d d' : Fin k → ℕ} {p p' q q' : Fin k → ℝ≥0}
    (hd : d ≤ d') (hp : p ≤ p') (hq : q ≤ q') :
    primitivePrefixInfo M n d p q ≤ primitivePrefixInfo M n d' p' q' := by
  unfold primitivePrefixInfo
  refine sup_le_sup (sup_le_sup ?_ ?_) ?_
  · refine iSup_le (fun i => iSup_le (fun j => iSup_le (fun hj =>
      le_iSup_of_le i (le_iSup_of_le j ?_))))
    exact le_iSup (fun _ : j < d' i => MeasurableSpace.comap (M.U i (j + 1)) inferInstance)
      (hj.trans_le (hd i))
  · refine iSup_le (fun i => iSup_le (fun u => iSup_le (fun hu =>
      le_iSup_of_le i (le_iSup_of_le u ?_))))
    exact le_iSup (fun _ : u ≤ p' i => MeasurableSpace.comap (fun ω => M.S n i ω u) inferInstance)
      (hu.trans (hp i))
  · refine iSup_le (fun i => iSup_le (fun u => iSup_le (fun hu =>
      le_iSup_of_le i (le_iSup_of_le u ?_))))
    exact le_iSup (fun _ : u ≤ q' i => MeasurableSpace.comap (fun ω => M.R n i ω u) inferInstance)
      (hu.trans (hq i))

private noncomputable def dyad (l j : ℕ) : ℝ≥0 :=
  (j : ℝ≥0) / (2 : ℝ≥0) ^ l

private noncomputable def dyadIndex (l : ℕ) (s : ℝ) : ℕ :=
  ⌈s * (2 : ℝ) ^ l⌉₊

private theorem dyadIndex_le (l j : ℕ) (s : ℝ) :
    dyadIndex l s ≤ j ↔ s ≤ (dyad l j : ℝ) := by
  rw [dyadIndex, Nat.ceil_le, dyad, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_ofNat]
  exact (le_div_iff₀ (by positivity)).symm

private theorem poisson_dyad_stable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → ℝ → ℝ} {rate : ℝ} (hN : IsPoissonProcess P N rate)
    (ω : Ω) {t : ℝ} (ht : 0 ≤ t) (u : ℝ≥0) :
    ∀ᶠ l in atTop,
      N ω ((dyad l (dyadIndex l t) : ℝ) + u) - N ω (dyad l (dyadIndex l t) : ℝ) =
        N ω (t + u) - N ω t := by
  let a (l : ℕ) : ℝ := dyad l (dyadIndex l t)
  have hcoe : (t.toNNReal : ℝ) = t := Real.coe_toNNReal _ ht
  have ha0 : Tendsto a atTop (𝓝 t) := by
    have hb := (NNReal.continuous_coe.tendsto t.toNNReal).comp
      (AvramDividend.Classical.dyadic_ceiling_nnreal_tendsto t.toNNReal)
    simpa only [a, dyad, dyadIndex, Function.comp_def, hcoe] using hb
  have hal (l : ℕ) : t ≤ a l := (dyadIndex_le l _ _).1 le_rfl
  have hflat (v : ℝ) (hv : 0 ≤ v) : ∀ᶠ r in 𝓝[Ici v] v, N ω r = N ω v := by
    exact nat_cast_right_constant (N ω) v (fun r hr => hN.nat_valued ω r (hv.trans hr))
      ((hN.cadlag ω).1 v hv)
  have hT : Tendsto a atTop (𝓝[Ici t] t) :=
    tendsto_nhdsWithin_iff.2 ⟨ha0, Eventually.of_forall hal⟩
  have hu : Tendsto (fun l => a l + (u : ℝ)) atTop (𝓝[Ici (t + u)] (t + u)) :=
    tendsto_nhdsWithin_iff.2 ⟨ha0.add_const _, Eventually.of_forall (fun l => add_le_add_left (hal l) _)⟩
  filter_upwards [hu.eventually (hflat _ (add_nonneg ht u.2)), hT.eventually (hflat _ ht)] with l h1 h2
  rw [h1, h2]
set_option maxHeartbeats 1200000 in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (n : ℕ)
    (hn : 1 ≤ n) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → (Fin k → ℕ))
    (hF_le : ∀ X i, F X i ≤ X i) (hF_sum : ∀ X, ∑ i, F X i ≤ n)
    (X : Ω → ℝ → Fin k → ℕ)
    (hX : M.IsSCP n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ))) :
    M.IsAdmissible n (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ)) := by
  classical
  letI : IsProbabilityMeasure M.P := M.isProb
  let Xr : Ω → ℝ → Fin k → ℝ := fun ω t i => X ω t i
  let Ψ : Ω → ℝ → Fin k → ℝ := fun ω t i => F (X ω t) i
  let base := primitiveSuffix M n (fun _ => 0) (fun _ => 0) (fun _ => 0)
  let Q := Measure.map base M.P
  let g (t : ℝ) (ω : Ω) : PrimitiveCoordinate k → ℝ :=
    Sum.elim (fun z => M.A n z.1 ω (M.nextArrival n z.1 ω t + z.2) - M.A n z.1 ω (M.nextArrival n z.1 ω t))
      (Sum.elim (fun z => M.S n z.1 ω (busyTime Ψ ω z.1 t + z.2) - M.S n z.1 ω (busyTime Ψ ω z.1 t))
        (fun z => M.R n z.1 ω (queueTime Xr Ψ ω z.1 t + z.2) - M.R n z.1 ω (queueTime Xr Ψ ω z.1 t)))
  have hproduct (t : ℝ) (ht : 0 ≤ t) (B : Set Ω) (hB : MeasurableSet[M.pastInfo n Xr Ψ t] B) :
      Measurable (g t) ∧ Measure.map (g t) (M.P.restrict B) = M.P B • Q := by
    let J := (Fin k → ℕ) × (Fin k → ℕ) × (Fin k → ℕ)
    let d (j : J) (i : Fin k) := j.1 i + 1
    let p (l : ℕ) (j : J) (i : Fin k) := dyad l (j.2.1 i)
    let q (l : ℕ) (j : J) (i : Fin k) := dyad l (j.2.2 i)
    let K (l : ℕ) (ω : Ω) : J :=
      (fun i => firstIndex M n i ω t, fun i => dyadIndex l (busyTime Ψ ω i t),
        fun i => dyadIndex l (queueTime Xr Ψ ω i t))
    let G (l : ℕ) (j : J) := primitivePrefixInfo M n (d j) (p l j) (q l j)
    let H (l : ℕ) (j : J) := primitiveSuffix M n (d j) (p l j) (q l j)
    have hG (l : ℕ) (j : J) : G l j ≤ mΩ := prefix_le M n _ _ _
    have hdMono (l : ℕ) : Monotone (G l) := by
      intro a b hab
      have ha : a.1 ≤ b.1 ∧ a.2.1 ≤ b.2.1 ∧ a.2.2 ≤ b.2.2 := hab
      exact prefix_mono M n (fun i => Nat.succ_le_succ (ha.1 i))
        (fun i => div_le_div_of_nonneg_right (by exact_mod_cast ha.2.1 i) (by positivity))
        (fun i => div_le_div_of_nonneg_right (by exact_mod_cast ha.2.2 i) (by positivity))
    have hLower (l : ℕ) (j : J) :
        {ω | K l ω ≤ j} = {ω | (∀ i, t ≤ M.arrivalEpoch n i ω (d j i)) ∧
          (∀ i, busyTime Ψ ω i t ≤ p l j i ∧ queueTime Xr Ψ ω i t ≤ q l j i)} := by
      ext ω
      change ((∀ i, firstIndex M n i ω t ≤ j.1 i) ∧
        (∀ i, dyadIndex l (busyTime Ψ ω i t) ≤ j.2.1 i) ∧
        (∀ i, dyadIndex l (queueTime Xr Ψ ω i t) ≤ j.2.2 i)) ↔ _
      simp only [firstIndex_le, dyadIndex_le, forall_and, d, p, q, mem_ofPred_eq]
    have hLow (B' : Set Ω) (hB' : MeasurableSet[M.pastInfo n Xr Ψ t] B')
        (l : ℕ) (j : J) : MeasurableSet[G l j] (B' ∩ {ω | K l ω ≤ j}) := by
      rw [hLower]
      exact feedback_past_restricted_to_primitive_cut M n X0 F hF_le X hX.controlled (d j) (p l j) (q l j) t ht B' hB'
    have hIndex (l : ℕ) (j : J) : MeasurableSet {ω | K l ω ≤ j} := by
      simpa only [univ_inter] using hG l j _ (hLow univ MeasurableSet.univ l j)
    have hSuffix (l : ℕ) (j : J) := primitive_suffix_at_deterministic_cuts M n (d j) (p l j) (q l j)
    refine stopped_product_law_of_countable_cuts M.P Q G H K (g t) B hG hdMono
      (fun l j => suffix_measurable M n (d j) (p l j) (q l j))
      (fun l j => (hSuffix l j).1.map_eq) (fun l j => (hSuffix l j).2) (hLow B hB) hIndex ?_
    intro ω z
    rcases z with (⟨i, u⟩ | (⟨i, u⟩ | ⟨i, u⟩))
    · exact Eventually.of_forall fun l => by
        simp only [H, primitiveSuffix, g, Sum.elim_inl, nextArrival_eq_firstIndex]
        rfl
    · have hs : 0 ≤ busyTime Ψ ω i t :=
        intervalIntegral.integral_nonneg ht (fun s hs => hX.controlled.psi_nonneg ω s i hs.1)
      exact poisson_dyad_stable (M.S_poisson n i) ω hs u
    · have hs : 0 ≤ queueTime Xr Ψ ω i t :=
        intervalIntegral.integral_nonneg ht (fun s hs => hX.controlled.phi_nonneg ω s i hs.1)
      exact poisson_dyad_stable (M.R_poisson n i) ω hs u
  have hBase : Measurable base := suffix_measurable M n _ _ _
  have hLaw (t : ℝ) (ht : 0 ≤ t) : IdentDistrib (g t) base M.P M.P := by
    have hAll := hproduct t ht univ MeasurableSet.univ
    refine ⟨hAll.1.aemeasurable, hBase.aemeasurable, ?_⟩
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using hAll.2
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have hle : M.futureInfo n Xr Ψ t ≤ MeasurableSpace.comap (g t) inferInstance := by
      unfold SystemSequence.futureInfo
      refine iSup_le fun i => iSup_le fun u => iSup_le fun hu => ?_
      let v : ℝ≥0 := ⟨u, hu⟩
      have hcoord (z : PrimitiveCoordinate k) :
          MeasurableSpace.comap (fun ω => g t ω z) inferInstance ≤
            MeasurableSpace.comap (g t) inferInstance := by
        change MeasurableSpace.comap ((fun v : PrimitiveCoordinate k → ℝ => v z) ∘ g t) _ ≤ _
        rw [← MeasurableSpace.comap_comp]
        exact MeasurableSpace.comap_mono (measurable_pi_apply z).comap_le
      exact sup_le (sup_le (hcoord (.inl (i, v))) (hcoord (.inr (.inl (i, v)))))
        (hcoord (.inr (.inr (i, v))))
    rw [Indep_iff]
    intro B C hB hC
    obtain ⟨C', hC', rfl⟩ := hle _ hC
    have hLC := hproduct t ht B hB
    have h := congrArg (fun μ : Measure (PrimitiveCoordinate k → ℝ) => μ C') hLC.2
    have hQ : Q C' = M.P (g t ⁻¹' C') := by
      change Measure.map base M.P C' = _
      rw [← (hLaw t ht).map_eq, Measure.map_apply hLC.1 hC']
    rw [Measure.map_apply hLC.1 hC', Measure.restrict_apply (hLC.1 hC'), Measure.smul_apply,
      smul_eq_mul, hQ, inter_comm] at h
    exact h
  · intro i t ht
    let project (z : PrimitiveCoordinate k → ℝ) (u : ℝ≥0) := z (.inr (.inl (i, u)))
    have hp : Measurable project := measurable_pi_lambda _ (fun u => measurable_pi_apply (.inr (.inl (i, u)) : PrimitiveCoordinate k))
    simpa [project, Function.comp_def, g, base, primitiveSuffix, (M.S_poisson n i).zero] using
      (hLaw t ht).comp hp
  · intro i t ht
    let project (z : PrimitiveCoordinate k → ℝ) (u : ℝ≥0) := z (.inr (.inr (i, u)))
    have hp : Measurable project := measurable_pi_lambda _ (fun u => measurable_pi_apply (.inr (.inr (i, u)) : PrimitiveCoordinate k))
    simpa [project, Function.comp_def, g, base, primitiveSuffix, (M.R_poisson n i).zero] using
      (hLaw t ht).comp hp
