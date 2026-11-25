-- Prove2me | solution 1 for ManyServerQED.Scheduling.primitive_suffix_at_deterministic_cuts
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T19:19:09.365041+00:00
-- url     : https://prove2.me/submissions/64b1b71b-e69a-482e-93e5-a9909de08072

import Theorems.Thm_AvramDividend_Classical_finiteTimeSet_monotoneZeroBasedGrid
import Theorems.Thm_ProbabilityTheory_HasIndependentIncrements_indep_naturalFiltration
import Definitions.Def_ManyServerQED_Scheduling_PrimitiveCuts

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem arrival_prefix_index {e : ℕ → ℝ} {s : ℝ}
    (h0 : e 0 ≤ s) (hm : ∃ m, s < e m) :
    ∃ j : ℕ, e j ≤ s ∧ s < e (j + 1) := by
  let b := Nat.find hm
  have hb : s < e b := Nat.find_spec hm
  have hb_pos : 0 < b := by
    by_contra! hb0
    rw [Nat.eq_zero_of_le_zero hb0] at hb
    exact (not_lt_of_ge h0) hb
  let j := b - 1
  have hsucc : j + 1 = b := by dsimp [j]; omega
  have hj_lt : j < b := by omega
  exact ⟨j, le_of_not_gt (Nat.find_min hm hj_lt), hsucc ▸ (show s < e b from hb)⟩

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

private theorem renewal_after_epoch {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω)
    (j : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    M.A n i ω (M.arrivalEpoch n i ω j + t) - M.A n i ω (M.arrivalEpoch n i ω j) =
      ((renewalCount (partialSum (fun m => M.U i (j + m) ω / M.lamN n i)) t).toNat : ℝ) := by
  let e := M.arrivalEpoch n i ω
  let f := partialSum (fun m => M.U i (j + m) ω / M.lamN n i)
  have hshift (m : ℕ) : e (j + m) = e j + f m := by
    induction m with
    | zero => simp [f, partialSum]
    | succ m hm =>
      have hleft : e (j + (m + 1)) = e (j + m) + M.U i (j + (m + 1)) ω / M.lamN n i := by
        unfold e SystemSequence.arrivalEpoch partialSum
        rw [show j + (m + 1) = (j + m) + 1 by omega,
          Finset.sum_Icc_succ_top (by omega : 1 ≤ (j + m) + 1)]
      have hright : f (m + 1) = f m + M.U i (j + (m + 1)) ω / M.lamN n i := by
        unfold f partialSum
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
      rw [hleft, hm, hright, add_assoc]
  have he := epoch_strict M n i ω
  have hz : f 0 = 0 := by simp [f, partialSum]
  have hf : Monotone f := by
    intro a b hab
    exact (add_le_add_iff_left (e j)).1 (by rw [← hshift, ← hshift]; exact he.monotone (by omega))
  have hcross : ∃ m : ℕ, t < f m := by
    obtain ⟨m, hm⟩ := epoch_crosses M n i ω (e j + t)
    have hm' := hm.trans_le (he.monotone (show m ≤ j + m by omega))
    change e j + t < e (j + m) at hm'
    rw [hshift, add_lt_add_iff_left] at hm'
    exact ⟨m, hm'⟩
  obtain ⟨m, hm, hm'⟩ := arrival_prefix_index (show f 0 ≤ t by rwa [hz]) hcross
  have h1 : renewalCount e (e j) = j :=
    renewal_eq_of_bracket he.monotone le_rfl (he (Nat.lt_succ_self j))
  have h2 : renewalCount e (e j + t) = (j + m : ℕ) := by
    apply renewal_eq_of_bracket (e := e) he.monotone
    · rw [hshift]
      exact add_le_add_right hm _
    · rw [show j + m + 1 = j + (m + 1) by omega, hshift]
      exact add_lt_add_right hm' _
  have h3 : renewalCount f t = m := renewal_eq_of_bracket hf hm hm'
  change (((renewalCount e (e j + t)).toNat : ℝ) - (renewalCount e (e j)).toNat) =
    ((renewalCount f t).toNat : ℝ)
  rw [h2, h1, h3, ENat.toNat_natCast, ENat.toNat_natCast, ENat.toNat_natCast, Nat.cast_add]
  ring

private noncomputable def renewal_from_sequence (rate : ℝ) (v : ℕ → ℝ) (t : ℝ≥0) : ℝ :=
  ((renewalCount (partialSum (fun j => v (j - 1) / rate)) t).toNat : ℝ)

private theorem renewal_from_sequence_meas (rate : ℝ) : Measurable (renewal_from_sequence rate) := by
  classical
  apply measurable_pi_lambda
  intro t
  let R (v : ℕ → ℝ) := renewalCount (partialSum (fun j => v (j - 1) / rate)) t
  have hL (a : ℕ∞) : MeasurableSet {v | R v ≤ a} := by
    have hEq : {v | R v ≤ a} = ⋂ l : ℕ, {v | partialSum (fun j => v (j - 1) / rate) l ≤
      (t : ℝ) → (l : ℕ∞) ≤ a} := by
      ext v
      simp only [mem_ofPred_eq, mem_iInter, R, renewalCount, iSup_le_iff]
    rw [hEq]
    apply MeasurableSet.iInter
    intro l
    by_cases hl : (l : ℕ∞) ≤ a
    · simp [hl]
    · simp only [hl, imp_false]
      change MeasurableSet ({v : ℕ → ℝ | partialSum (fun j => v (j - 1) / rate) l ≤ (t : ℝ)}ᶜ)
      exact (measurableSet_le (g := fun _ => (t : ℝ))
        (Finset.measurable_sum _ (fun j _ => (show Measurable (fun v : ℕ → ℝ => v (j - 1)) from measurable_pi_apply _).div_const rate) :
          Measurable (fun v : ℕ → ℝ => partialSum (fun j => v (j - 1) / rate) l))
        measurable_const).compl
  have hLt (a : ℕ∞) : MeasurableSet {v | R v < a} := by
    have hEq : {v | R v < a} = ⋃ b : ℕ∞, ⋃ (_ : b < a), {v | R v ≤ b} := by
      ext v
      simp only [mem_ofPred_eq, mem_iUnion]
      exact ⟨fun h => ⟨R v, h, le_rfl⟩, fun ⟨_, h, hb⟩ => hb.trans_lt h⟩
    rw [hEq]
    exact MeasurableSet.iUnion (fun b => MeasurableSet.iUnion (fun _ => hL b))
  have hR : Measurable R := by
    apply measurable_to_countable'
    intro a
    have hEq : R ⁻¹' {a} = {v | R v ≤ a} \ {v | R v < a} := by
      ext v
      simp only [mem_preimage, mem_singleton_iff, Set.mem_sdiff, mem_ofPred_eq, not_lt]
      exact le_antisymm_iff
    rw [hEq]
    exact (hL a).diff (hLt a)
  exact (measurable_of_countable (fun a : ℕ∞ => (a.toNat : ℝ))).comp hR

private theorem arrival_suffix_eq {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (d : ℕ) :
    (fun ω (u : ℝ≥0) => M.A n i ω (M.arrivalEpoch n i ω d + u) - M.A n i ω (M.arrivalEpoch n i ω d)) =
      (renewal_from_sequence (M.lamN n i)) ∘ (fun ω j => M.U i (d + j + 1) ω) := by
  funext ω u
  rw [renewal_after_epoch M n i ω d u u.2]
  simp only [Function.comp_def, renewal_from_sequence]
  have h (m : ℕ) :
      partialSum (fun j => M.U i (d + j) ω / M.lamN n i) m =
        partialSum (fun j => M.U i (d + (j - 1) + 1) ω / M.lamN n i) m := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := (Finset.mem_Icc.mp hj).1
    change M.U i (d + j) ω / M.lamN n i = M.U i (d + (j - 1) + 1) ω / M.lamN n i
    rw [show d + (j - 1) + 1 = d + j by omega]
  exact congrArg (fun e : ℕ → ℝ => ((renewalCount e (u : ℝ)).toNat : ℝ)) (funext h)

private theorem arrival_suffix_indep_law {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (d : ℕ) :
    let out (d : ℕ) (ω : Ω) (u : ℝ≥0) :=
      M.A n i ω (M.arrivalEpoch n i ω d + u) - M.A n i ω (M.arrivalEpoch n i ω d)
    IdentDistrib (out d) (out 0) M.P M.P ∧
    Indep (⨆ (j : ℕ) (_ : j < d), MeasurableSpace.comap (M.U i (j+1)) inferInstance)
      (MeasurableSpace.comap (out d) inferInstance) M.P := by
  let out (d : ℕ) (ω : Ω) (u : ℝ≥0) :=
      M.A n i ω (M.arrivalEpoch n i ω d + u) - M.A n i ω (M.arrivalEpoch n i ω d)
  let V (j : ℕ) := M.U i (j + 1)
  let G (j : ℕ) := MeasurableSpace.comap (V j) inferInstance
  have hC (j : ℕ) : G j ≤ mΩ := (M.U_meas i (j + 1)).comap_le
  let embed (j : ℕ) : (Fin k × ℕ) ⊕ (Fin k ⊕ Fin k) := .inl (i, j)
  have hInj : Function.Injective embed := fun a b h => congrArg Prod.snd (Sum.inl.inj h)
  have hi : iIndep G M.P := (M.indep n).precomp hInj
  have hiV : iIndepFun V M.P := (iIndepFun_iff_iIndep _ _ _).2 hi
  have hm (a : ℕ) : out a = (renewal_from_sequence (M.lamN n i)) ∘ (fun ω j => V (a + j) ω) :=
    arrival_suffix_eq M n i a
  have ht : IdentDistrib (fun ω j => V (d + j) ω) (fun ω j => V j ω) M.P M.P := by
    refine IdentDistrib.pi (fun j => ?_) (hiV.precomp (g := fun j => d + j) (fun a b h => Nat.add_left_cancel h)) hiV
    exact (M.U_ident i (d + j + 1) (by omega)).trans (M.U_ident i (j + 1) (by omega)).symm
  have hD : MeasurableSpace.comap (out d) inferInstance ≤ ⨆ (j : ℕ) (_ : d ≤ j), G j := by
    rw [hm, ← MeasurableSpace.comap_comp]
    refine (MeasurableSpace.comap_mono (renewal_from_sequence_meas (M.lamN n i)).comap_le).trans ?_
    rw [MeasurableSpace.comap_process_pi]
    exact iSup_le (fun j => le_iSup₂_of_le (d + j) (by omega : d ≤ d+j) le_rfl)
  have hi' : Indep (⨆ (j : ℕ) (_ : j < d), G j) (⨆ (j : ℕ) (_ : d ≤ j), G j) M.P := by
    refine indep_iSup_of_disjoint hC hi (S := {j | j < d}) (T := {j | d ≤ j}) ?_
    exact Set.disjoint_left.2 (fun j hj hk =>
      (Nat.not_le_of_lt (show j < d from hj)) (show d ≤ j from hk))
  refine ⟨?_, indep_of_indep_of_le_right hi' hD⟩
  change IdentDistrib (out d) (out 0) M.P M.P
  rw [hm d, hm 0]
  simpa only [Nat.zero_add] using ht.comp (renewal_from_sequence_meas (M.lamN n i))

private theorem count_increment_nat {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {rate : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N rate)
    (ω : Ω) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∃ j : ℕ, N ω t - N ω s = j := by
  obtain ⟨a, ha⟩ := hN.nat_valued ω s hs
  obtain ⟨b, hb⟩ := hN.nat_valued ω t (hs.trans hst)
  have hab : a ≤ b := by
    exact_mod_cast (show (a : ℝ) ≤ (b : ℝ) from ha ▸ hb ▸ hN.mono ω hs (hs.trans hst) hst)
  exact ⟨b - a, by rw [ha, hb, Nat.cast_sub hab]⟩

private theorem nat_floor_increment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {rate : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N rate)
    (ω : Ω) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (⌊N ω t - N ω s⌋₊ : ℝ) = N ω t - N ω s := by
  obtain ⟨j, hj⟩ := count_increment_nat hN ω hs hst
  rw [hj, Nat.floor_natCast]

private theorem map_floor_increment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {rate : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N rate)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Measure.map (fun ω => ⌊N ω t - N ω s⌋₊) P = poissonMeasure (rate * (t - s)).toNNReal := by
  apply Measure.ext_of_singleton
  intro j
  have hm : Measurable (fun ω => ⌊N ω t - N ω s⌋₊) := ((hN.meas t).sub (hN.meas s)).nat_floor
  rw [Measure.map_apply hm (measurableSet_singleton j)]
  convert hN.law s t hs hst j using 2
  ext ω
  change ⌊N ω t - N ω s⌋₊ = j ↔ N ω t - N ω s = j
  constructor
  · intro h
    rw [← nat_floor_increment hN ω hs hst, h]
  · intro h
    rw [h, Nat.floor_natCast]

private theorem count_increment_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {rate : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N rate)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    IdentDistrib (fun ω => N ω t - N ω s) (fun ω => N ω (t - s)) P P := by
  have ht0 : 0 ≤ t - s := sub_nonneg.mpr hst
  have h1 := ((hN.meas t).sub (hN.meas s))
  have h2 := (hN.meas (t - s)).sub (hN.meas 0)
  have hmap : Measure.map (fun ω => ⌊N ω t - N ω s⌋₊) P =
      Measure.map (fun ω => ⌊N ω (t - s) - N ω 0⌋₊) P := by
    rw [map_floor_increment hN hs hst, map_floor_increment hN le_rfl ht0, sub_zero]
  have hId : IdentDistrib (fun ω => ⌊N ω t - N ω s⌋₊) (fun ω => ⌊N ω (t - s) - N ω 0⌋₊) P P :=
    ⟨h1.nat_floor.aemeasurable, h2.nat_floor.aemeasurable, hmap⟩
  have hC := hId.comp (measurable_of_countable (fun j : ℕ => (j : ℝ)))
  have hR (ω : Ω) : (⌊N ω (t - s) - N ω 0⌋₊ : ℝ) = N ω (t - s) := by
    rw [nat_floor_increment hN ω le_rfl ht0, hN.zero, sub_zero]
  simpa only [Function.comp_def, nat_floor_increment hN _ hs hst, hR] using hC

private theorem grid_independence {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ∀ r, Measurable (X r)) (h0 : X 0 = fun _ => 0)
    (hi : HasIndependentIncrements X P)
    (s : ℝ≥0) (u : ℕ → ℝ≥0) (hu : Monotone u) (hs : s ≤ u 0) (n : ℕ) :
    Indep (⨆ i ∈ (Finset.range n : Set ℕ), MeasurableSpace.comap
        (fun ω => X (u (i + 1)) ω - X (u i) ω) inferInstance)
      ((Filtration.natural X (fun r => (hX r).stronglyMeasurable)) s) P := by
  classical
  let ℱ := Filtration.natural X (fun r => (hX r).stronglyMeasurable)
  let Δ (i : ℕ) (ω : Ω) := X (u (i + 1)) ω - X (u i) ω
  let G (i : ℕ) := MeasurableSpace.comap (Δ i) inferInstance
  have hΔ (i : ℕ) : Measurable (Δ i) := (hX _).sub (hX _)
  have had (v t : ℝ≥0) (hvt : v ≤ t) : Measurable[ℱ t] (X v) :=
    (comap_measurable (X v)).mono (le_iSup₂_of_le v hvt le_rfl) le_rfl
  have hInd (i : ℕ) : Indep (G i) (ℱ (u i)) P := by
    exact hi.indep_naturalFiltration (fun r => (hX r).stronglyMeasurable)
      h0 (fun r => r.2) (hu (Nat.le_succ i))
  have factor (A : Set Ω) (hA : MeasurableSet[ℱ s] A)
      (C : ℕ → Set Ω) (hC : ∀ i, MeasurableSet[G i] (C i)) (l : ℕ) :
      P (A ∩ ⋂ i ∈ Finset.range l, C i) = P A * ∏ i ∈ Finset.range l, P (C i) := by
    induction l with
    | zero => simp
    | succ l hl =>
      have hSet : (⋂ i ∈ Finset.range (l + 1), C i) =
          (⋂ i ∈ Finset.range l, C i) ∩ C l := by
        rw [Finset.range_add_one]
        ext ω
        simp only [mem_iInter, mem_inter_iff, Finset.mem_insert]
        exact ⟨fun h => ⟨fun i hi => h i (.inr hi), h l (.inl rfl)⟩,
          fun ⟨hr, he⟩ i hi => hi.elim (fun h => h ▸ he) (hr i)⟩
      have ha : MeasurableSet[ℱ (u l)] A :=
        ℱ.mono (hs.trans (hu (Nat.zero_le l))) _ hA
      have hCl (i : ℕ) (hit : i ∈ Finset.range l) : MeasurableSet[ℱ (u l)] (C i) := by
        have hil : i + 1 ≤ l := Finset.mem_range.mp hit
        have hmi : Measurable[ℱ (u l)] (Δ i) :=
          (had _ _ (hu hil)).sub (had _ _ (hu (by omega : i ≤ l)))
        exact hmi.comap_le _ (hC i)
      have hMeas : MeasurableSet[ℱ (u l)] (A ∩ ⋂ i ∈ Finset.range l, C i) :=
        ha.inter (MeasurableSet.biInter (Finset.range l).countable_toSet (fun i hit => hCl i hit))
      rw [hSet, ← inter_assoc, (Indep_iff _ _ _).1 (hInd l).symm _ _ hMeas (hC l),
        hl, Finset.prod_range_succ, mul_assoc]
  refine IndepSets.indep (p1 := piiUnionInter (fun i => {C | MeasurableSet[G i] C})
      (Finset.range n : Set ℕ)) (p2 := {A | MeasurableSet[ℱ s] A})
    (iSup₂_le fun i _ => (hΔ i).comap_le) (ℱ.le s)
    (isPiSystem_piiUnionInter _ (fun i => @MeasurableSpace.isPiSystem_measurableSet Ω (G i)) _)
    (@MeasurableSpace.isPiSystem_measurableSet Ω (ℱ s))
    (generateFrom_piiUnionInter_measurableSet _ _).symm
    (@MeasurableSpace.generateFrom_measurableSet Ω (ℱ s)).symm ?_
  rw [IndepSets_iff]
  rintro C A ⟨J, hJ, f, hf, rfl⟩ hA
  let B (i : ℕ) := if i ∈ J then f i else univ
  have hB (i : ℕ) : MeasurableSet[G i] (B i) := by
    unfold B
    split_ifs with h
    · exact hf i h
    · exact MeasurableSet.univ
  have hE : (⋂ i ∈ J, f i) = ⋂ i ∈ Finset.range n, B i := by
    ext ω
    simp only [mem_iInter]
    constructor
    · intro h i hi
      by_cases hj : i ∈ J
      · simpa only [B, if_pos hj] using h i hj
      · simp [B, hj]
    · intro h i hi
      simpa only [B, if_pos hi] using h i (hJ hi)
  have hProb := factor univ MeasurableSet.univ B hB n
  rw [univ_inter, measure_univ, one_mul] at hProb
  rw [hE, inter_comm, factor A hA B hB n, hProb, mul_comm]

private theorem deterministic_independence {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ∀ r, Measurable (X r)) (h0 : X 0 = fun _ => 0)
    (hi : HasIndependentIncrements X P) (s : ℝ≥0) :
    Indep
      (⨆ u : ℝ≥0, ⨆ (_ : u ≤ s), MeasurableSpace.comap (X u) inferInstance)
      (MeasurableSpace.comap (fun ω (t : ℝ≥0) => X (s + t) ω - X s ω) inferInstance) P := by
  classical
  let ℱ := Filtration.natural X (fun r => (hX r).stronglyMeasurable)
  let Y (r : ℝ≥0) (ω : Ω) := X (s + r) ω - X s ω
  let G (J : Finset ℝ≥0) := ⨆ r : ℝ≥0, ⨆ (_ : r ∈ J), MeasurableSpace.comap (Y r) inferInstance
  have hY (r : ℝ≥0) : Measurable (Y r) := (hX _).sub (hX _)
  have hGY : (MeasurableSpace.comap (fun ω r => Y r ω) inferInstance) = ⨆ J, G J := by
    rw [MeasurableSpace.comap_process_pi]
    exact le_antisymm
      (iSup_le fun r => le_iSup_of_le ({r} : Finset ℝ≥0)
        (le_iSup₂_of_le r (Finset.mem_singleton_self r) le_rfl))
      (iSup_le fun _ => iSup₂_le fun r _ => le_iSup (fun i => MeasurableSpace.comap (Y i) inferInstance) r)
  have hG (J : Finset ℝ≥0) : Indep (G J) (ℱ s) P := by
    obtain ⟨n, t, e, ht, ht0, he⟩ := AvramDividend.Classical.finiteTimeSet_monotoneZeroBasedGrid J
    let u (i : ℕ) := s + t i
    have hu : Monotone u := fun _ _ h => add_le_add_right (ht h) _
    have hst : s ≤ u 0 := by simp [u, ht0]
    have H := grid_independence P X hX h0 hi s u hu hst n
    refine indep_of_indep_of_le_left H (iSup₂_le fun r hr => ?_)
    let j : J := ⟨r, hr⟩
    let k := e j
    have htel : Y r = fun ω => ∑ i ∈ Finset.range (k.1 + 1), (X (u (i + 1)) ω - X (u i) ω) := by
      funext ω
      rw [Finset.sum_range_sub (fun i => X (u i) ω)]
      have hk : t (k.1 + 1) = r := he j
      simp [Y, u, ht0, hk]
    rw [htel]
    apply Measurable.comap_le
    refine Finset.measurable_sum _ fun i hmem => ?_
    have hin : i ∈ (Finset.range n : Set ℕ) := Finset.mem_range.2
      ((Finset.mem_range.1 hmem).trans_le (Nat.succ_le_of_lt k.2))
    exact (comap_measurable _).mono (le_iSup₂_of_le i hin le_rfl) le_rfl
  change Indep (ℱ s) (MeasurableSpace.comap (fun ω r => Y r ω) inferInstance) P
  rw [hGY]
  symm
  exact indep_iSup_of_monotone hG (fun J => iSup₂_le fun r _ => (hY r).comap_le)
    (ℱ.le s) (fun a b hab => iSup₂_le fun r hr => by
      have hs : (a : Set ℝ≥0) ⊆ (b : Set ℝ≥0) := Finset.coe_subset.mpr hab
      exact le_iSup₂_of_le r (hs hr) le_rfl)

private theorem deterministic_stationarity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ∀ r, Measurable (X r)) (h0 : X 0 = fun _ => 0)
    (hi : HasIndependentIncrements X P) (hl : HasStationaryIncrements X P) (s : ℝ≥0) :
    IdentDistrib (fun ω (r : ℝ≥0) => X (s + r) ω - X s ω) (fun ω r => X r ω) P P := by
  classical
  let Y (ω : Ω) (r : ℝ≥0) := X (s + r) ω - X s ω
  let Z (ω : Ω) (r : ℝ≥0) := X r ω
  have hy : Measurable Y := measurable_pi_lambda _ (fun _ => (hX _).sub (hX _))
  have hz : Measurable Z := measurable_pi_lambda _ hX
  refine ⟨hy.aemeasurable, hz.aemeasurable, ?_⟩
  have hu : Measure.map Y P univ = Measure.map Z P univ := by
    rw [Measure.map_apply hy MeasurableSet.univ, Measure.map_apply hz MeasurableSet.univ]
    simp only [preimage_univ]
  refine ext_of_generate_finite (measurableCylinders _) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun C hC => ?_) hu
  obtain ⟨J, B, hB, rfl⟩ := (mem_measurableCylinders C).mp hC
  obtain ⟨n, t, e, ht, ht0, he⟩ := AvramDividend.Classical.finiteTimeSet_monotoneZeroBasedGrid J
  let Dy (i : Fin n) (ω : Ω) := X (s + t (i.val + 1)) ω - X (s + t i.val) ω
  let Dz (i : Fin n) (ω : Ω) := X (t (i.val + 1)) ω - X (t i.val) ω
  have hiY : iIndepFun Dy P :=
    hi n (fun i => s + t i.val) (fun _ _ h => add_le_add_right (ht h) _)
  have hiZ : iIndepFun Dz P := hi n (fun i => t i.val) (fun _ _ h => ht h)
  have hDelta (i : Fin n) : IdentDistrib (Dy i) (Dz i) P P := by
    let a := t i.val
    let b := t (i.val + 1)
    have hab : a ≤ b := ht (Nat.le_succ i.val)
    have hb : a + (b - a) = b := add_tsub_cancel_of_le hab
    have hsB : (s + a) + (b - a) = s + b := by rw [add_assoc, hb]
    have hDy := hl (s + a) (b - a)
    have hDz := hl a (b - a)
    unfold increment at hDy hDz
    rw [hsB, h0] at hDy
    rw [hb, h0] at hDz
    exact hDy.trans hDz.symm
  let proj (v : Fin n → ℝ) (j : J) :=
    ∑ i ∈ Finset.range ((e j).val + 1), if h : i < n then v ⟨i, h⟩ else 0
  have hProj : Measurable proj := by
    apply measurable_pi_lambda
    intro j
    apply Finset.measurable_sum
    intro i _
    split_ifs with h
    · exact measurable_pi_apply (⟨i, h⟩ : Fin n)
    · exact measurable_const
  have hId := (IdentDistrib.pi hDelta hiY hiZ).comp hProj
  have hproj (a : ℝ≥0) (ω : Ω) (j : J) :
      proj (fun i => X (a + t (i.val + 1)) ω - X (a + t i.val) ω) j =
        X (a + (j : ℝ≥0)) ω - X a ω := by
    unfold proj
    rw [show (∑ i ∈ Finset.range ((e j).val + 1),
        if h : i < n then X (a + t (i + 1)) ω - X (a + t i) ω else 0) =
          ∑ i ∈ Finset.range ((e j).val + 1),
            (X (a + t (i + 1)) ω - X (a + t i) ω) from
      Finset.sum_congr rfl (fun i hi => if_pos
        ((Finset.mem_range.1 hi).trans_le (Nat.succ_le_of_lt (e j).2)))]
    rw [Finset.sum_range_sub (fun i => X (a + t i) ω), ht0, he j, add_zero]
  have hproY : proj ∘ (fun ω i => Dy i ω) = fun ω => J.restrict (Y ω) := by
    funext ω j
    exact hproj s ω j
  have hproZ : proj ∘ (fun ω i => Dz i ω) = fun ω => J.restrict (Z ω) := by
    funext ω j
    simpa [Dz, Z, zero_add, h0] using hproj 0 ω j
  rw [hproY, hproZ] at hId
  rw [Measure.map_apply hy hB.cylinder, Measure.map_apply hz hB.cylinder]
  exact hId.measure_mem_eq hB

private theorem poisson_suffix_indep_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : Ω → ℝ → ℝ} {rate : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N rate) (s : ℝ≥0) :
    let tail (ω : Ω) (t : ℝ≥0) := N ω ((s : ℝ) + t) - N ω s
    IdentDistrib tail (fun ω (t : ℝ≥0) => N ω t) P P ∧
      Indep (⨆ (t : ℝ≥0) (_ : t ≤ s), MeasurableSpace.comap (fun ω => N ω t) inferInstance)
        (MeasurableSpace.comap tail inferInstance) P := by
  let X (t : ℝ≥0) (ω : Ω) := N ω t
  have hX (t : ℝ≥0) : Measurable (X t) := hN.meas _
  have h0 : X 0 = fun _ => 0 := funext hN.zero
  have hi : HasIndependentIncrements X P := by
    intro n v hv
    exact hN.indep_incr n (fun i => v i) (v 0).2 (fun _ _ h => by exact_mod_cast hv h)
  have hl : HasStationaryIncrements X P := by
    intro a b
    have hh := count_increment_law hN (s := (a : ℝ)) (t := (a : ℝ) + (b : ℝ))
      a.2 (le_add_of_nonneg_right b.2)
    change IdentDistrib (fun ω => N ω ((a + b : ℝ≥0) : ℝ) - N ω a)
      (fun ω => N ω b - N ω (0 : ℝ≥0)) P P
    simpa only [hN.zero, NNReal.coe_add, NNReal.coe_zero, sub_zero, add_sub_cancel_left] using hh
  exact ⟨deterministic_stationarity P X hX h0 hi hl s, deterministic_independence P X hX h0 hi s⟩

private theorem generate_iSup_from_finite_inter {Ω ι : Type*} (m : ι → MeasurableSpace Ω) :
    MeasurableSpace.generateFrom (piiUnionInter (fun i => {s | MeasurableSet[m i] s}) univ) =
      ⨆ i, m i := by
  rw [generateFrom_piiUnionInter_measurableSet]
  simp

private theorem grouped_indep {Ω ι : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A B : ι → MeasurableSpace Ω)
    (hA : ∀ i, A i ≤ mΩ) (hB : ∀ i, B i ≤ mΩ)
    (hJoint : iIndep (fun i => A i ⊔ B i) P)
    (hPairs : ∀ i, Indep (A i) (B i) P) :
    Indep (⨆ i, A i) (⨆ i, B i) P := by
  classical
  let PA := piiUnionInter (fun i => {s | MeasurableSet[A i] s}) univ
  let PB := piiUnionInter (fun i => {s | MeasurableSet[B i] s}) univ
  refine IndepSets.indep (iSup_le hA) (iSup_le hB)
    (isPiSystem_piiUnionInter _ (fun i => (fun s hs t ht _ => @MeasurableSet.inter Ω (A i) s t hs ht)) _)
    (isPiSystem_piiUnionInter _ (fun i => (fun s hs t ht _ => @MeasurableSet.inter Ω (B i) s t hs ht)) _)
    (generate_iSup_from_finite_inter A).symm (generate_iSup_from_finite_inter B).symm ?_
  rw [IndepSets_iff]
  intro a b ha hb
  obtain ⟨s, _, f, hf, rfl⟩ := (show a ∈ PA from ha)
  obtain ⟨t, _, g, hg, rfl⟩ := (show b ∈ PB from hb)
  let f' i := if i ∈ s then f i else univ
  let g' i := if i ∈ t then g i else univ
  have hf' (i : ι) : MeasurableSet[A i] (f' i) := by
    dsimp [f']
    split_ifs with hi
    · exact hf i hi
    · exact MeasurableSet.univ
  have hg' (i : ι) : MeasurableSet[B i] (g' i) := by
    dsimp [g']
    split_ifs with hi
    · exact hg i hi
    · exact MeasurableSet.univ
  have hpad (u v : Finset ι) (huv : u ⊆ v) (q : ι → Set Ω) :
      (⋂ i ∈ u, q i) = ⋂ i ∈ v, (if i ∈ u then q i else univ) := by
    ext ω
    simp only [mem_iInter]
    constructor
    · intro h i hi
      split_ifs with hui
      · exact h i hui
      · trivial
    · intro h i hi
      simpa only [if_pos hi] using h i (huv hi)
  rw [hpad s (s ∪ t) Finset.subset_union_left f, hpad t (s ∪ t) Finset.subset_union_right g]
  change P ((⋂ i ∈ s ∪ t, f' i) ∩ (⋂ i ∈ s ∪ t, g' i)) =
    P (⋂ i ∈ s ∪ t, f' i) * P (⋂ i ∈ s ∪ t, g' i)
  have hEq : (⋂ i ∈ s ∪ t, f' i) ∩ (⋂ i ∈ s ∪ t, g' i) =
      ⋂ i ∈ s ∪ t, (f' i ∩ g' i) := by
    ext ω
    simp only [mem_inter_iff, mem_iInter]
    exact ⟨fun h i hi => ⟨h.1 i hi, h.2 i hi⟩,
      fun h => ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩⟩
  have hfI := (iIndep_of_iIndep_of_le hJoint (fun i => le_sup_left : ∀ i, A i ≤ A i ⊔ B i))
  have hgI := (iIndep_of_iIndep_of_le hJoint (fun i => le_sup_right : ∀ i, B i ≤ A i ⊔ B i))
  rw [hEq, hJoint.meas_biInter (fun i _ =>
    MeasurableSet.inter ((show A i ≤ A i ⊔ B i from le_sup_left) _ (hf' i))
      ((show B i ≤ A i ⊔ B i from le_sup_right) _ (hg' i))),
    hfI.meas_biInter (fun i _ => hf' i), hgI.meas_biInter (fun i _ => hg' i), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (Indep_iff _ _ _).1 (hPairs i) _ _ (hf' i) (hg' i)

private theorem regroup_independent {Ω I J : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (G : I → MeasurableSpace Ω) (c : I → J) (hG : ∀ i, G i ≤ mΩ) (h : iIndep G P) :
    iIndep (fun j => ⨆ (i : I) (_ : c i = j), G i) P := by
  classical
  let π (j : J) := piiUnionInter (fun i => {s | MeasurableSet[G i] s}) {i | c i = j}
  refine iIndepSets.iIndep (fun _ => iSup₂_le (fun i _ => hG i)) π
    (fun j => isPiSystem_piiUnionInter _
      (fun i => @MeasurableSpace.isPiSystem_measurableSet Ω (G i)) _)
    (fun j => (generateFrom_piiUnionInter_measurableSet G {i | c i = j}).symm) ?_
  rw [iIndepSets_iff]
  intro S E hE
  have hmem (j : J) (hj : j ∈ S) :
      ∃ (L : Finset I), ((L : Set I) ⊆ {i | c i = j}) ∧
        ∃ f : I → Set Ω, (∀ i ∈ L, MeasurableSet[G i] (f i)) ∧ E j = ⋂ i ∈ L, f i :=
    by
      obtain ⟨L, hL, f, hf, he⟩ := hE j hj
      exact ⟨L, hL, f, hf, he⟩
  choose! L hL f hf he using hmem
  let H (i : I) := f (c i) i
  have hH (j : J) (hj : j ∈ S) (i : I) (hi : i ∈ L j) : H i = f j i := by
    have hc : c i = j := hL j hj hi
    simp only [H, hc]
  have hdisj : Set.PairwiseDisjoint (S : Set J) L := by
    intro a ha b hb hne
    refine Finset.disjoint_left.2 fun i ha' hb' => ?_
    exact hne ((hL a ha ha').symm.trans (hL b hb hb'))
  have hEs (j : J) (hj : j ∈ S) : E j = ⋂ i ∈ L j, H i := by
    rw [he j hj]
    ext ω
    simp only [mem_iInter]
    exact forall_congr' (fun i => forall_congr' (fun hi => (hH j hj i hi).symm ▸ Iff.rfl))
  have hEunion : (⋂ j ∈ S, E j) = ⋂ i ∈ S.biUnion L, H i := by
    ext ω
    simp only [mem_iInter, Finset.mem_biUnion]
    constructor
    · rintro hw i ⟨j, hj, hi⟩
      have hE := hw j hj
      rw [hEs j hj] at hE
      exact (mem_iInter.1 (mem_iInter.1 hE i)) hi
    · intro hw j hj
      rw [hEs j hj]
      exact mem_iInter.2 fun i => mem_iInter.2 fun hi => hw i ⟨j, hj, hi⟩
  rw [hEunion, h.meas_biInter (fun i hi => by
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.1 hi
    rw [hH j hj i hij]
    exact hf j hj i hij), Finset.prod_biUnion hdisj]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [hEs j hj, h.meas_biInter (fun i hi => by
    rw [hH j hj i hi]
    exact hf j hj i hi)]

private abbrev PrimitiveKind (k : ℕ) := Fin k ⊕ (Fin k ⊕ Fin k)

private noncomputable def pathsAfter {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) :
    PrimitiveKind k → Ω → ℝ≥0 → ℝ :=
  Sum.elim (fun i ω u =>
    M.A n i ω (M.arrivalEpoch n i ω (d i) + u) - M.A n i ω (M.arrivalEpoch n i ω (d i)))
    (Sum.elim (fun i ω u => M.S n i ω ((p i : ℝ) + u) - M.S n i ω (p i))
      (fun i ω u => M.R n i ω ((q i : ℝ) + u) - M.R n i ω (q i)))

private noncomputable def reorganize {k : ℕ} (x : PrimitiveKind k → ℝ≥0 → ℝ) :
    PrimitiveCoordinate k → ℝ :=
  Sum.elim (fun z => x (.inl z.1) z.2)
    (Sum.elim (fun z => x (.inr (.inl z.1)) z.2) (fun z => x (.inr (.inr z.1)) z.2))

private theorem reorganize_meas {k : ℕ} : Measurable (@reorganize k) := by
  apply measurable_pi_lambda
  rintro (⟨i, u⟩ | (⟨i, u⟩ | ⟨i, u⟩))
  · exact (measurable_pi_apply u).comp (measurable_pi_apply (.inl i : PrimitiveKind k))
  · exact (measurable_pi_apply u).comp (measurable_pi_apply (.inr (.inl i) : PrimitiveKind k))
  · exact (measurable_pi_apply u).comp (measurable_pi_apply (.inr (.inr i) : PrimitiveKind k))

set_option maxHeartbeats 1600000 in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k)
    (n : ℕ) (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) :
    IdentDistrib (primitiveSuffix M n d p q)
      (primitiveSuffix M n (fun _ => 0) (fun _ => 0) (fun _ => 0)) M.P M.P ∧
    Indep (primitivePrefixInfo M n d p q)
      (MeasurableSpace.comap (primitiveSuffix M n d p q) inferInstance) M.P := by
  letI : IsProbabilityMeasure M.P := M.isProb
  let ι := (Fin k × ℕ) ⊕ (Fin k ⊕ Fin k)
  let c : ι → PrimitiveKind k := Sum.map Prod.fst id
  let G : ι → MeasurableSpace Ω :=
    Sum.elim (fun x : Fin k × ℕ => MeasurableSpace.comap (M.U x.1 (x.2 + 1)) inferInstance)
      (Sum.elim
        (fun i : Fin k => MeasurableSpace.comap (fun ω (u : ℝ≥0) => M.S n i ω u) inferInstance)
        (fun i : Fin k => MeasurableSpace.comap (fun ω (u : ℝ≥0) => M.R n i ω u) inferInstance))
  let H (j : PrimitiveKind k) := ⨆ (i : ι) (_ : c i = j), G i
  let out := pathsAfter M n d p q
  let out0 := pathsAfter M n (fun _ => 0) (fun _ => 0) (fun _ => 0)
  let A : PrimitiveKind k → MeasurableSpace Ω :=
    Sum.elim (fun i : Fin k => ⨆ (j : ℕ) (_ : j < d i),
      MeasurableSpace.comap (M.U i (j + 1)) inferInstance)
      (Sum.elim (fun i => ⨆ (u : ℝ≥0) (_ : u ≤ p i),
        MeasurableSpace.comap (fun ω => M.S n i ω u) inferInstance)
        (fun i => ⨆ (u : ℝ≥0) (_ : u ≤ q i),
          MeasurableSpace.comap (fun ω => M.R n i ω u) inferInstance))
  let B (j : PrimitiveKind k) := MeasurableSpace.comap (out j) inferInstance
  let B0 (j : PrimitiveKind k) := MeasurableSpace.comap (out0 j) inferInstance
  have hG (a : ι) : G a ≤ mΩ := by
    rcases a with (⟨i, l⟩ | (i | i))
    · exact (M.U_meas i (l + 1)).comap_le
    · exact (measurable_pi_lambda _ (fun u : ℝ≥0 => (M.S_poisson n i).meas u)).comap_le
    · exact (measurable_pi_lambda _ (fun u : ℝ≥0 => (M.R_poisson n i).meas u)).comap_le
  have hH (j : PrimitiveKind k) : H j ≤ mΩ := iSup₂_le fun a _ => hG a
  have hIndH : iIndep H M.P := regroup_independent M.P G c hG (M.indep n)
  have hSub (a : ι) : G a ≤ H (c a) := le_iSup₂_of_le a rfl le_rfl
  have hUle (i : Fin k) (l : ℕ) :
      MeasurableSpace.comap (M.U i (l+1)) inferInstance ≤ H (.inl i) := hSub (.inl (i,l))
  have hSle (i : Fin k) :
      MeasurableSpace.comap (fun ω (u : ℝ≥0) => M.S n i ω u) inferInstance ≤ H (.inr (.inl i)) :=
    hSub (.inr (.inl i))
  have hRle (i : Fin k) :
      MeasurableSpace.comap (fun ω (u : ℝ≥0) => M.R n i ω u) inferInstance ≤ H (.inr (.inr i)) :=
    hSub (.inr (.inr i))
  have hSread (i : Fin k) (u : ℝ≥0) : Measurable[H (.inr (.inl i))] (fun ω => M.S n i ω u) :=
    (measurable_pi_apply u).comp ((comap_measurable _).mono (hSle i) le_rfl)
  have hRread (i : Fin k) (u : ℝ≥0) : Measurable[H (.inr (.inr i))] (fun ω => M.R n i ω u) :=
    (measurable_pi_apply u).comp ((comap_measurable _).mono (hRle i) le_rfl)
  have hALe (j : PrimitiveKind k) : A j ≤ H j := by
    rcases j with (i | (i | i))
    · exact iSup₂_le (fun l _ => hUle i l)
    · exact iSup₂_le (fun u _ => (hSread i u).comap_le)
    · exact iSup₂_le (fun u _ => (hRread i u).comap_le)
  have hTail (p q : Fin k → ℝ≥0) (d : Fin k → ℕ) (j : PrimitiveKind k) :
      MeasurableSpace.comap (pathsAfter M n d p q j) inferInstance ≤ H j := by
    apply Measurable.comap_le
    rcases j with (i | (i | i))
    · change Measurable[H (.inl i)] (fun ω (u : ℝ≥0) =>
        M.A n i ω (M.arrivalEpoch n i ω (d i) + u) - M.A n i ω (M.arrivalEpoch n i ω (d i)))
      rw [arrival_suffix_eq M n i (d i)]
      have hseq (j : ℕ) : Measurable[H (.inl i)] (M.U i (d i + j + 1)) :=
        measurable_iff_comap_le.2 (hUle i (d i + j))
      have hl := renewal_from_sequence_meas (M.lamN n i)
      letI : MeasurableSpace Ω := H (.inl i)
      exact hl.comp (measurable_pi_lambda _ hseq)
    · letI : MeasurableSpace Ω := H (.inr (.inl i))
      exact measurable_pi_lambda _ (fun u : ℝ≥0 => (hSread i (p i + u)).sub (hSread i (p i)))
    · letI : MeasurableSpace Ω := H (.inr (.inr i))
      exact measurable_pi_lambda _ (fun u : ℝ≥0 => (hRread i (q i + u)).sub (hRread i (q i)))
  have hBLe (j : PrimitiveKind k) : B j ≤ H j := hTail p q d j
  have hB0Le (j : PrimitiveKind k) : B0 j ≤ H j := hTail _ _ _ j
  have hDAndI (j : PrimitiveKind k) : IdentDistrib (out j) (out0 j) M.P M.P ∧ Indep (A j) (B j) M.P := by
    rcases j with (i | (i | i))
    · exact arrival_suffix_indep_law M n i (d i)
    · have hs := poisson_suffix_indep_law (M.S_poisson n i) (p i)
      refine ⟨?_, hs.2⟩
      change IdentDistrib (fun ω (u : ℝ≥0) => M.S n i ω ((p i : ℝ) + u) - M.S n i ω (p i))
        (fun ω (u : ℝ≥0) => M.S n i ω ((0 : ℝ≥0) + u : ℝ) - M.S n i ω (0 : ℝ≥0)) M.P M.P
      simpa only [NNReal.coe_zero, zero_add, (M.S_poisson n i).zero, sub_zero] using hs.1
    · have hs := poisson_suffix_indep_law (M.R_poisson n i) (q i)
      refine ⟨?_, hs.2⟩
      change IdentDistrib (fun ω (u : ℝ≥0) => M.R n i ω ((q i : ℝ) + u) - M.R n i ω (q i))
        (fun ω (u : ℝ≥0) => M.R n i ω ((0 : ℝ≥0) + u : ℝ) - M.R n i ω (0 : ℝ≥0)) M.P M.P
      simpa only [NNReal.coe_zero, zero_add, (M.R_poisson n i).zero, sub_zero] using hs.1
  have hIOut : iIndepFun out M.P := (iIndepFun_iff_iIndep _ _ _).2 (iIndep_of_iIndep_of_le hIndH hBLe)
  have hIOut0 : iIndepFun out0 M.P := (iIndepFun_iff_iIndep _ _ _).2 (iIndep_of_iIndep_of_le hIndH hB0Le)
  have hWhole := (IdentDistrib.pi (fun j => (hDAndI j).1) hIOut hIOut0).comp
    (@reorganize_meas k)
  have hFutureEq (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) :
      primitiveSuffix M n d p q = reorganize ∘ (fun ω j => pathsAfter M n d p q j ω) := by
    funext ω z
    rcases z with (z | (z | z)) <;> rfl
  refine ⟨?_, ?_⟩
  · rw [hFutureEq, hFutureEq]
    exact hWhole
  · have hTogether := grouped_indep M.P A B
        (fun j => (hALe j).trans (hH j)) (fun j => (hBLe j).trans (hH j))
        (iIndep_of_iIndep_of_le hIndH (fun j => sup_le (hALe j) (hBLe j))) (fun j => (hDAndI j).2)
    have hP : primitivePrefixInfo M n d p q ≤ ⨆ j, A j := by
      unfold primitivePrefixInfo
      exact sup_le (sup_le (iSup_le (fun i => le_iSup A (.inl i)))
        (iSup_le (fun i => le_iSup A (.inr (.inl i)))))
        (iSup_le (fun i => le_iSup A (.inr (.inr i))))
    have hF : MeasurableSpace.comap (primitiveSuffix M n d p q) inferInstance ≤ ⨆ j, B j := by
      rw [hFutureEq, ← MeasurableSpace.comap_comp]
      refine (MeasurableSpace.comap_mono (@reorganize_meas k).comap_le).trans ?_
      rw [MeasurableSpace.comap_process_pi]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hTogether hP) hF
