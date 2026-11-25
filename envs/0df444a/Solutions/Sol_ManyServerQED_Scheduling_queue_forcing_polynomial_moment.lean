-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_forcing_polynomial_moment
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:05:03.216948+00:00
-- url     : https://prove2.me/submissions/be18e328-4991-42c0-9b07-fa7b67328bbe

import Theorems.Thm_ManyServerQED_Scheduling_lemma_2
import Theorems.Thm_ManyServerQED_Scheduling_centered_poisson_scaled_sup_moment
import Definitions.Def_ManyServerQED_Scheduling_Policy

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

set_option maxHeartbeats 1200000 in
private theorem arrival_envelope_indep_abandonment {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (i : Fin k) (T : ℝ≥0) :
    Measurable (fun ω => (T : ℝ) * ((X0 i : ℝ) + M.A n i ω T) / (n : ℝ)) ∧
    IndepFun (fun ω => (T : ℝ) * ((X0 i : ℝ) + M.A n i ω T) / (n : ℝ))
      (fun ω (u : ℝ≥0) => M.R n i ω u) M.P := by
  let ι := (Fin k × ℕ) ⊕ (Fin k ⊕ Fin k)
  let G : ι → MeasurableSpace Ω :=
    Sum.elim (fun x : Fin k × ℕ => MeasurableSpace.comap (M.U x.1 (x.2 + 1)) inferInstance)
      (Sum.elim
        (fun i : Fin k => MeasurableSpace.comap (fun ω (u : ℝ≥0) => M.S n i ω u) inferInstance)
        (fun i : Fin k => MeasurableSpace.comap (fun ω (u : ℝ≥0) => M.R n i ω u) inferInstance))
  have hG (a : ι) : G a ≤ mΩ := by
    rcases a with (⟨j, l⟩ | (j | j))
    · exact (M.U_meas j (l + 1)).comap_le
    · exact (measurable_pi_lambda _ (fun u : ℝ≥0 => (M.S_poisson n j).meas u)).comap_le
    · exact (measurable_pi_lambda _ (fun u : ℝ≥0 => (M.R_poisson n j).meas u)).comap_le
  let a : ι := .inr (.inr i)
  let U : Set ι := Set.range (fun j : ℕ => (Sum.inl (i, j) : ι))
  have hdisj : Disjoint U {a} := by
    apply Set.disjoint_left.2
    rintro b ⟨j, rfl⟩ hb
    have hb' : (Sum.inl (i, j) : ι) = a := hb
    change (Sum.inl (i, j) : (Fin k × ℕ) ⊕ (Fin k ⊕ Fin k)) = Sum.inr (Sum.inr i) at hb'
    cases hb'
  have h := indep_iSup_of_disjoint hG (M.indep n) hdisj
  let Arrival (ω : Ω) := M.A n i ω T
  let v (ω : Ω) (j : ℕ) := M.U i (j + 1) ω
  let f (w : ℕ → ℝ) := renewal_from_sequence (M.lamN n i) w T
  have hEq : Arrival = f ∘ v := by
    funext ω
    have hz : M.arrivalEpoch n i ω 0 = 0 := by simp [SystemSequence.arrivalEpoch, partialSum]
    have hp := (epoch_strict M n i ω) (Nat.zero_lt_succ 0)
    rw [hz] at hp
    have hA0 : M.A n i ω 0 = 0 := by
      simp only [SystemSequence.A, renewal_eq_of_bracket (epoch_strict M n i ω).monotone hz.le hp,
        ENat.toNat_zero, Nat.cast_zero]
    have he := congrFun (congrFun (arrival_suffix_eq M n i 0) ω) T
    simpa only [hz, hA0, zero_add, sub_zero, Function.comp_def, f, v] using he
  have hi : Measurable f := (measurable_pi_apply T).comp (renewal_from_sequence_meas (M.lamN n i))
  let Cut := ⨆ b ∈ U, G b
  have hMeas : Measurable[Cut] Arrival := by
    rw [hEq]
    have hu (j : ℕ) : Measurable[Cut] (@SystemSequence.U Ω mΩ k M i (j + 1)) :=
      measurable_iff_comap_le.2 (le_iSup₂_of_le (.inl (i,j)) ⟨j, rfl⟩ le_rfl)
    letI : MeasurableSpace Ω := Cut
    have hv : Measurable v := measurable_pi_lambda v hu
    exact hi.comp hv
  have hH : Measurable[Cut] (fun ω => (T : ℝ) * ((X0 i : ℝ) + Arrival ω) / (n : ℝ)) := by
    letI : MeasurableSpace Ω := Cut
    exact ((measurable_const.add hMeas).const_mul _).div_const _
  refine ⟨hH.mono (iSup₂_le (fun i _ => hG i)) le_rfl, ?_⟩
  apply (IndepFun_iff_Indep _ _ _).2
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left h hH.comap_le)
    (le_iSup₂_of_le a (Set.mem_singleton a) le_rfl)

private theorem arrival_monotoneOn {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) :
    MonotoneOn (M.A n i ω) (Set.Ici 0) := by
  let e := M.arrivalEpoch n i ω
  let r := M.lamN n i
  have hr : 0 < r := M.lamN_pos n i
  have he (j : ℕ) : e j = partialSum (fun m => M.U i m ω) j / r := by
    simp [e, r, SystemSequence.arrivalEpoch, partialSum, Finset.sum_div]
  have hm : Monotone e := (strictMono_nat_of_lt_succ (fun j => by
    have hj := M.U_pos i (j + 1) ω (by omega)
    rw [he, he]
    apply (div_lt_div_iff_of_pos_right hr).2
    unfold partialSum
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
    linarith)).monotone
  intro a _ b _ hab
  have hcross : ∃ m : ℕ, b < e m := by
    obtain ⟨m, hm⟩ := ((tendsto_atTop.1 (M.U_finite i ω)) (b * r + 1)).exists
    refine ⟨m, ?_⟩
    rw [he, lt_div_iff₀ hr]
    linarith
  obtain ⟨m, hm'⟩ := hcross
  have hfin : renewalCount e b ≠ ⊤ := by
    have hb : renewalCount e b ≤ (m : ℕ∞) := by
      unfold renewalCount
      refine iSup_le (fun j => iSup_le (fun hj => ?_))
      have : j ≤ m := by
        by_contra! h
        exact (not_le_of_gt (hm'.trans_le (hm h.le))) hj
      exact_mod_cast this
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top m) hb
  have hab' : renewalCount e a ≤ renewalCount e b := by
    unfold renewalCount
    exact iSup_le (fun j => iSup_le (fun hj => le_iSup_of_le j (le_iSup_of_le (hj.trans hab) le_rfl)))
  change ((renewalCount e a).toNat : ℝ) ≤ ((renewalCount e b).toNat : ℝ)
  exact_mod_cast ENat.toNat_le_toNat hab' hfin


private theorem queue_clock_le_arrival_envelope {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (X Ψ : Ω → ℝ → Fin k → ℝ)
    (hC : M.IsControlled n X0 X Ψ) (ω : Ω) (i : Fin k) (T : ℝ) (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T, queueTime X Ψ ω i t / (n : ℝ) ≤
      T * ((X0 i : ℝ) + M.A n i ω T) / (n : ℝ) := by
  intro t ht
  have hNonnegA : 0 ≤ M.A n i ω T := Nat.cast_nonneg _
  have hbase : 0 ≤ (X0 i : ℝ) + M.A n i ω T := add_nonneg (Nat.cast_nonneg _) hNonnegA
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have he (s : ℝ) (hs : s ∈ Icc 0 t) : X ω s i - Ψ ω s i ≤ X0 i + M.A n i ω T := by
    have hbusy : 0 ≤ busyTime Ψ ω i s :=
      intervalIntegral.integral_nonneg hs.1 (fun r hr => hC.psi_nonneg ω r i hr.1)
    have hqueue : 0 ≤ queueTime X Ψ ω i s :=
      intervalIntegral.integral_nonneg hs.1 (fun r hr => hC.phi_nonneg ω r i hr.1)
    obtain ⟨r, hr⟩ := (M.R_poisson n i).nat_valued ω _ hqueue
    obtain ⟨p, hp⟩ := (M.S_poisson n i).nat_valued ω _ hbusy
    have heq := hC.eq7 ω s i hs.1
    rw [hr, hp] at heq
    have ha := arrival_monotoneOn M n i ω hs.1 hT (hs.2.trans ht.2)
    linarith [hC.psi_nonneg ω s i hs.1, Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) p]
  have hb := intervalIntegral.integral_mono_on ht.1 (hC.integrable ω i t ht.1).2
    (intervalIntegrable_const (c := (X0 i : ℝ) + M.A n i ω T)) he
  unfold queueTime
  refine hb.trans ?_
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  exact mul_le_mul_of_nonneg_right ht.2 hbase

private noncomputable def rational_clock_sup (n T : ℕ) (a : ℝ)
    (x : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ⨆ q : ℚ, if 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ (T : ℝ) then
    ENNReal.ofReal |(x (((n : ℝ) * (q : ℝ)).toNNReal) - a * (n : ℝ) * (q : ℝ)) / Real.sqrt n|
    else 0

private theorem rational_clock_sup_meas (n T : ℕ) (a : ℝ) :
    Measurable (rational_clock_sup n T a) := by
  unfold rational_clock_sup
  apply Measurable.iSup
  intro q
  by_cases h : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ (T : ℝ)
  · simp only [if_pos h]
    exact (((measurable_pi_apply (((n : ℝ) * (q : ℝ)).toNNReal)).sub_const _).div_const _).abs.ennreal_ofReal
  · simp only [if_neg h]
    exact measurable_const

private theorem rational_clock_sup_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {a : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N a)
    (n T : ℕ) (ω : Ω) :
    rational_clock_sup n T a (fun u => N ω u) =
      ⨆ t : ℝ, ⨆ (_ : t ∈ Icc 0 (T : ℝ)), ENNReal.ofReal |(N ω (n * t) - a*n*t)/Real.sqrt n| := by
  classical
  let M (t : ℝ) := ENNReal.ofReal |(N ω ((n : ℝ)*t) - a*(n : ℝ)*t)/Real.sqrt n|
  let R := rational_clock_sup n T a (fun u => N ω u)
  have hRat (q : ℚ) (hq : (q : ℝ) ∈ Icc 0 (T : ℝ)) : M q ≤ R := by
    have h := le_iSup (fun r : ℚ => if 0 ≤ (r : ℝ) ∧ (r : ℝ) ≤ (T : ℝ) then
      ENNReal.ofReal |(N ω (((n : ℝ) * (r : ℝ)).toNNReal : ℝ) -
        a * (n : ℝ) * (r : ℝ)) / Real.sqrt n| else 0) q
    have hq' : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ (T : ℝ) := hq
    rw [if_pos hq', Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg n) hq.1)] at h
    exact h
  change R = ⨆ t : ℝ, ⨆ (_ : t ∈ Icc 0 (T : ℝ)), M t
  apply le_antisymm
  · unfold R rational_clock_sup
    apply iSup_le
    intro q
    split_ifs with h
    · dsimp only
      rw [Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg n) h.1)]
      exact le_iSup₂_of_le (q : ℝ) h le_rfl
    · exact bot_le
  · apply iSup₂_le
    intro t ht
    by_cases htT : t = (T : ℝ)
    · have h := hRat (T : ℚ) (by simp : ((T : ℚ) : ℝ) ∈ Icc 0 (T : ℝ))
      simpa only [Rat.cast_natCast, htT] using h
    have hlt : t < (T : ℝ) := lt_of_le_of_ne ht.2 htT
    have hchoose (j : ℕ) : ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < min (T : ℝ) (t + 1 / (j + 1 : ℝ)) := by
      exact exists_rat_btwn (lt_min hlt (lt_add_of_pos_right _ (by positivity)))
    choose q hq using hchoose
    have hub (j : ℕ) : (q j : ℝ) ≤ t + 1 / (j + 1 : ℝ) :=
      (hq j).2.le.trans (min_le_right _ _)
    have hlb (j : ℕ) : t ≤ (q j : ℝ) := (hq j).1.le
    have hInv : Tendsto (fun j : ℕ => 1 / (j + 1 : ℝ)) atTop (𝓝 0) := by
      have hn : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      have hn' : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
        tendsto_atTop.2 (fun b => ((tendsto_atTop.1 hn) b).mono (fun _ h => by linarith))
      exact tendsto_const_nhds.div_atTop hn' 
    have hUp : Tendsto (fun j : ℕ => t + 1 / (j + 1 : ℝ)) atTop (𝓝 t) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := t)).add hInv
    have hqT : Tendsto (fun j : ℕ => (q j : ℝ)) atTop (𝓝[Ici t] t) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUp hlb hub,
        Eventually.of_forall hlb⟩
    have hC : ContinuousWithinAt (fun s : ℝ => N ω (n*s)) (Ici t) t :=
      (((hN.cadlag ω).1 _ (mul_nonneg (Nat.cast_nonneg _) ht.1)).comp
        (continuous_const.mul continuous_id).continuousWithinAt)
        (fun s hs => show (n : ℝ)*t ≤ (n : ℝ)*s from mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n))
    have hMC : ContinuousWithinAt M (Ici t) t := by
      exact ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
        (((hC.sub (continuous_const.mul continuous_id).continuousWithinAt).div_const _).abs)
    exact le_of_tendsto (hMC.tendsto.comp hqT) (Eventually.of_forall (fun j =>
      hRat (q j) ⟨ht.1.trans (hlb j), (hq j).2.le.trans (min_le_left _ _)⟩))

private theorem independent_countable_horizon_bound {Ω J : Type*} [MeasurableSpace Ω] [Countable J]
    [MeasurableSpace J] [DiscreteMeasurableSpace J] (P : Measure Ω)
    (K : Ω → J) (F : J → Ω → ℝ≥0∞) (G : J → ℝ≥0∞)
    (hK : Measurable K) (hF : ∀ j, Measurable (F j))
    (hI : ∀ j, IndepFun K (F j) P)
    (hB : ∀ j, ∫⁻ ω, F j ω ∂P ≤ G j) :
    ∫⁻ ω, F (K ω) ω ∂P ≤ ∫⁻ ω, G (K ω) ∂P := by
  classical
  let I (j : J) (ω : Ω) : ℝ≥0∞ := if K ω = j then 1 else 0
  have hm (j : J) : Measurable (I j) :=
    Measurable.ite (hK (measurableSet_singleton j)) measurable_const measurable_const
  have hI' (j : J) : IndepFun (I j) (F j) P :=
    (hI j).comp (measurable_of_countable (fun z : J => if z = j then (1 : ℝ≥0∞) else 0)) measurable_id
  have hsum (H : J → Ω → ℝ≥0∞) (ω : Ω) : ∑' j, I j ω * H j ω = H (K ω) ω := by
    rw [tsum_eq_single (K ω)]
    · simp [I]
    · intro j hj
      simp [I, Ne.symm hj]
  calc
    _ = ∫⁻ ω, ∑' j, I j ω * F j ω ∂P := by simp_rw [hsum]
    _ = ∑' j, (∫⁻ ω, I j ω ∂P) * (∫⁻ ω, F j ω ∂P) := by
      rw [lintegral_tsum (μ := P) (f := fun j ω => I j ω * F j ω) (fun j => ((hm j).mul (hF j)).aemeasurable)]
      exact tsum_congr (fun j => lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hm j) (hF j) (hI' j))
    _ ≤ ∑' j, (∫⁻ ω, I j ω ∂P) * G j := ENNReal.tsum_le_tsum (fun j => mul_le_mul_right (hB j) _)
    _ = ∫⁻ ω, ∑' j, I j ω * G j ∂P := by
      rw [lintegral_tsum (μ := P) (f := fun j ω => I j ω * G j) (fun j => ((hm j).mul measurable_const).aemeasurable)]
      exact tsum_congr (fun j => (lintegral_mul_const _ (hm j)).symm)
    _ = _ := by
      have h (ω : Ω) : ∑' j, I j ω * G j = G (K ω) := hsum (fun j _ => G j) ω
      simp_rw [h]

private theorem abandonment_ranged_grid_moment {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (hn : 1 ≤ n) (X0 : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hCtl : M.IsControlled n X0 X Ψ)
    (A p : ℝ) (hp : 1 < p) (i : Fin k) (hA : M.thetaN n i ≤ A) (T : ℝ≥0) :
    let C := (2 : ℝ)^p * (((p/(p-1))^p) * (2 * (⌈p⌉₊.factorial : ℝ) * Real.exp A) + A^p)
    let K (ω : Ω) := ⌈(T : ℝ) * ((X0 i : ℝ) + M.A n i ω T) / (n : ℝ)⌉₊
    (∫⁻ ω, (⨆ t : ℝ, ⨆ (_ : t ∈ Icc 0 (T : ℝ)),
      ENNReal.ofReal |M.Rhat n ω (queueTime X Ψ ω i t / (n : ℝ)) i|)^p ∂M.P) ≤
        ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal ((1 + (K ω : ℝ))^p) ∂M.P := by
  letI : IsProbabilityMeasure M.P := M.isProb
  let C := (2 : ℝ)^p * (((p/(p-1))^p) * (2 * (⌈p⌉₊.factorial : ℝ) * Real.exp A) + A^p)
  let H (ω : Ω) := (T : ℝ) * ((X0 i : ℝ) + M.A n i ω T) / (n : ℝ)
  let K (ω : Ω) := ⌈H ω⌉₊
  let Q (ω : Ω) (u : ℝ≥0) := M.R n i ω u
  let a := M.thetaN n i
  let J (d : ℕ) (ω : Ω) := (rational_clock_sup n d a (Q ω))^p
  have hQ : Measurable Q := measurable_pi_lambda _ (fun u => (M.R_poisson n i).meas u)
  have hj (d : ℕ) : Measurable (fun v : ℝ≥0 → ℝ => (rational_clock_sup n d a v)^p) :=
    (show Monotone (fun v : ℝ≥0∞ => v ^ p) from
      fun _ _ h => ENNReal.rpow_le_rpow h (by linarith)).measurable.comp (rational_clock_sup_meas n d a)
  have hJ (d : ℕ) : Measurable (J d) := (hj d).comp hQ
  have hHis : Measurable H ∧ IndepFun H Q M.P := arrival_envelope_indep_abandonment M n X0 i T
  have hK : Measurable K := hHis.1.nat_ceil
  have hInd (d : ℕ) : IndepFun K (J d) M.P :=
    hHis.2.comp measurable_id.nat_ceil (hj d)
  let G (d : ℕ) : ℝ≥0∞ := ENNReal.ofReal (C * (1 + (d : ℝ))^p)
  have hLin (d : ℕ) : (∫⁻ ω, J d ω ∂M.P) ≤ G d := by
    simp only [J, Q, rational_clock_sup_eq (M.R_poisson n i), a]
    exact centered_poisson_scaled_sup_moment (M.R_poisson n i) p A hp hA n hn d (Nat.cast_nonneg _)
  have hA0 : 0 ≤ A := (M.thetaN_nonneg n i).trans hA
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hCl (ω : Ω) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
      queueTime X Ψ ω i t / (n : ℝ) ∈ Icc 0 (K ω : ℝ) := by
    refine ⟨div_nonneg (intervalIntegral.integral_nonneg ht.1 (fun r hr => hCtl.phi_nonneg ω r i hr.1))
      (Nat.cast_nonneg _), ?_⟩
    exact (queue_clock_le_arrival_envelope M n X0 X Ψ hCtl ω i T T.2 t ht).trans (Nat.le_ceil _)
  dsimp only
  calc
    _ ≤ ∫⁻ ω, J (K ω) ω ∂M.P := by
      apply lintegral_mono
      intro ω
      change (⨆ t : ℝ, ⨆ (_ : t ∈ Icc 0 (T : ℝ)),
        ENNReal.ofReal |M.Rhat n ω (queueTime X Ψ ω i t / (n : ℝ)) i|)^p ≤
        (rational_clock_sup n (K ω) (M.thetaN n i) (fun u => M.R n i ω u))^p
      rw [rational_clock_sup_eq (M.R_poisson n i)]
      apply ENNReal.rpow_le_rpow _ (by linarith)
      refine iSup₂_le (fun t ht => le_iSup₂_of_le (queueTime X Ψ ω i t / (n : ℝ)) (hCl ω t ht) ?_)
      apply ENNReal.ofReal_le_ofReal
      unfold SystemSequence.Rhat
      rw [mul_comm (n : ℝ) (M.thetaN n i)]
    _ ≤ ∫⁻ ω, G (K ω) ∂M.P := independent_countable_horizon_bound M.P K J G hK hJ hInd hLin
    _ = _ := by
      simp only [G, ENNReal.ofReal_mul hC0]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

set_option maxHeartbeats 1300000 in
private theorem abandonment_ranged_grid_majorant {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (hn : 1 ≤ n) (X0 : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hCtl : M.IsControlled n X0 X Ψ)
    (A p : ℝ) (hp : 1 < p) (i : Fin k) (hA : M.thetaN n i ≤ A) (T : ℝ≥0) :
    let C := (2 : ℝ)^p * (((p/(p-1))^p) * (2 * (⌈p⌉₊.factorial : ℝ) * Real.exp A) + A^p)
    let K (ω : Ω) := ⌈(T : ℝ) * ((X0 i : ℝ) + M.A n i ω T) / (n : ℝ)⌉₊
    ∃ V : Ω → ℝ≥0∞, Measurable V ∧
      (∀ ω t, t ∈ Icc 0 (T : ℝ) → ENNReal.ofReal |M.Rhat n ω (queueTime X Ψ ω i t / (n : ℝ)) i| ≤ V ω) ∧
      (∫⁻ ω, (V ω)^p ∂M.P) ≤
        ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal ((1 + (K ω : ℝ))^p) ∂M.P := by
  letI : IsProbabilityMeasure M.P := M.isProb
  let C := (2 : ℝ)^p * (((p/(p-1))^p) * (2 * (⌈p⌉₊.factorial : ℝ) * Real.exp A) + A^p)
  let H (ω : Ω) := (T : ℝ) * ((X0 i : ℝ) + M.A n i ω T) / (n : ℝ)
  let K (ω : Ω) := ⌈H ω⌉₊
  let Q (ω : Ω) (u : ℝ≥0) := M.R n i ω u
  let a := M.thetaN n i
  let J (d : ℕ) (ω : Ω) := (rational_clock_sup n d a (Q ω))^p
  have hQ : Measurable Q := measurable_pi_lambda _ (fun u => (M.R_poisson n i).meas u)
  have hj (d : ℕ) : Measurable (fun v : ℝ≥0 → ℝ => (rational_clock_sup n d a v)^p) :=
    (show Monotone (fun v : ℝ≥0∞ => v ^ p) from
      fun _ _ h => ENNReal.rpow_le_rpow h (by linarith)).measurable.comp (rational_clock_sup_meas n d a)
  have hJ (d : ℕ) : Measurable (J d) := (hj d).comp hQ
  have hHis : Measurable H ∧ IndepFun H Q M.P := arrival_envelope_indep_abandonment M n X0 i T
  have hK : Measurable K := hHis.1.nat_ceil
  have hInd (d : ℕ) : IndepFun K (J d) M.P :=
    hHis.2.comp measurable_id.nat_ceil (hj d)
  let G (d : ℕ) : ℝ≥0∞ := ENNReal.ofReal (C * (1 + (d : ℝ))^p)
  have hLin (d : ℕ) : (∫⁻ ω, J d ω ∂M.P) ≤ G d := by
    simp only [J, Q, rational_clock_sup_eq (M.R_poisson n i), a]
    exact centered_poisson_scaled_sup_moment (M.R_poisson n i) p A hp hA n hn d (Nat.cast_nonneg _)
  have hA0 : 0 ≤ A := (M.thetaN_nonneg n i).trans hA
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hCl (ω : Ω) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
      queueTime X Ψ ω i t / (n : ℝ) ∈ Icc 0 (K ω : ℝ) := by
    refine ⟨div_nonneg (intervalIntegral.integral_nonneg ht.1 (fun r hr => hCtl.phi_nonneg ω r i hr.1))
      (Nat.cast_nonneg _), ?_⟩
    exact (queue_clock_le_arrival_envelope M n X0 X Ψ hCtl ω i T T.2 t ht).trans (Nat.le_ceil _)
  let V (ω : Ω) := rational_clock_sup n (K ω) a (Q ω)
  have hV : Measurable V := by
    let g (q : Ω × ℕ) := rational_clock_sup n q.2 a (Q q.1)
    have hg : Measurable g := measurable_from_prod_countable_left (f := g)
      (fun d => (rational_clock_sup_meas n d a).comp hQ)
    exact hg.comp (measurable_id.prodMk hK)
  refine ⟨V, hV, ?_, ?_⟩
  · intro ω t ht
    change _ ≤ rational_clock_sup n (K ω) (M.thetaN n i) (fun u => M.R n i ω u)
    rw [rational_clock_sup_eq (M.R_poisson n i)]
    refine le_iSup₂_of_le (queueTime X Ψ ω i t / (n : ℝ)) (hCl ω t ht) ?_
    apply ENNReal.ofReal_le_ofReal
    unfold SystemSequence.Rhat
    rw [mul_comm (n : ℝ) (M.thetaN n i)]
  · change (∫⁻ ω, J (K ω) ω ∂M.P) ≤ _
    calc
      _ ≤ ∫⁻ ω, G (K ω) ∂M.P := independent_countable_horizon_bound M.P K J G hK hJ hInd hLin
      _ = _ := by
        simp only [G, ENNReal.ofReal_mul hC0]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private theorem queue_arrival_envelope_moment {Ω : Type*} [MeasurableSpace Ω]
    {k : ℕ} (M : SystemSequence Ω k) (n : ℕ) (hn : 1 ≤ n) (X0 : Fin k → ℕ)
    (x : Fin k → ℝ) (i : Fin k) (A c p : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (T : ℝ) (hT : 0 ≤ T)
    (hX0 : (X0 i : ℝ)/(n : ℝ) ≤ A + 1 + l1norm x)
    (hRate : M.lamN n i / (n : ℝ) ≤ A)
    (hMom : (∫⁻ ω, ENNReal.ofReal |M.Ahat n ω T i|^p ∂M.P) ≤
      ENNReal.ofReal (c*(1+T^(p/2)))) :
    let K (ω : Ω) := ⌈T * ((X0 i : ℝ) + M.A n i ω T) / (n : ℝ)⌉₊
    (∫⁻ ω, ENNReal.ofReal ((1+(K ω : ℝ))^p) ∂M.P) ≤
      ENNReal.ofReal (2^p * ((A+3)^p + 2*c) * (1 + l1norm x)^p * (1+T)^(2*p)) := by
  letI : IsProbabilityMeasure M.P := M.isProb
  let K (ω : Ω) := ⌈T * ((X0 i : ℝ) + M.A n i ω T) / (n : ℝ)⌉₊
  let X := l1norm x
  let D := (A+3)*(1+X)*(1+T)^2
  let v (ω : Ω) := |M.Ahat n ω T i|
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnP : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hS : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnP
  have hS1 : 1 ≤ Real.sqrt (n : ℝ) := by simpa using Real.sqrt_le_sqrt hnR
  have hX : 0 ≤ X := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hDX : 1 ≤ (1+X) * (1+T)^2 := by
    calc
      (1 : ℝ) ≤ (1+X) := by linarith
      _ ≤ (1+X) * (1+T)^2 := le_mul_of_one_le_right (by positivity) (by nlinarith)
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hDpow : D^p = (A+3)^p * (1+X)^p * (1+T)^(2*p) := by
    unfold D
    rw [Real.mul_rpow (by positivity) (sq_nonneg _),
      Real.mul_rpow (by positivity) (by positivity : 0 ≤ 1+X),
      ← Real.rpow_natCast (1+T) 2, ← Real.rpow_mul (by positivity : 0 ≤ 1+T), Nat.cast_ofNat]
  have hPoint (ω : Ω) : 1 + (K ω : ℝ) ≤ D + T * v ω := by
    let H (ω : Ω) := T * ((X0 i : ℝ) + M.A n i ω T) / (n : ℝ)
    have hHA (ω : Ω) : 0 ≤ M.A n i ω T := Nat.cast_nonneg _
    have hH0 : 0 ≤ H ω := div_nonneg (mul_nonneg hT (add_nonneg (Nat.cast_nonneg _) (hHA ω)))
      (Nat.cast_nonneg _)
    have hceil : 1 + (K ω : ℝ) ≤ 2 + H ω := by
      have h := (Nat.ceil_lt_add_one hH0).le
      change (K ω : ℝ) ≤ H ω + 1 at h
      linarith
    have hAeq : M.A n i ω T / (n : ℝ) =
        (M.lamN n i / (n : ℝ))*T + M.Ahat n ω T i / Real.sqrt n := by
      unfold SystemSequence.Ahat
      rw [div_div, ← sq, Real.sq_sqrt hnP.le]
      ring
    have hV : M.Ahat n ω T i / Real.sqrt n ≤ v ω := by
      refine (div_le_div_of_nonneg_right (le_abs_self _) hS.le).trans ?_
      exact div_le_self (abs_nonneg _) hS1
    have hA' : M.A n i ω T / (n : ℝ) ≤ A*T + v ω := by
      rw [hAeq]
      exact add_le_add (mul_le_mul_of_nonneg_right hRate hT) hV
    have hB : A + 1 + X + A*T ≤ (A+1)*(1+X)*(1+T) := by
      have hh : A+1+X ≤ (A+1)*(1+X) := by nlinarith [mul_nonneg hA hX]
      have hg : A ≤ (A+1)*(1+X) := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hg hT]
    have hBound : 2 + T*(A+1+X + (A*T+v ω)) ≤ D + T*v ω := by
      have h₁ := mul_le_mul_of_nonneg_left hB hT
      have h₂ : T * ((A+1)*(1+X)*(1+T)) ≤ (A+1)*(1+X)*(1+T)^2 := by
        have h : T*(1+T) ≤ (1+T)^2 := by nlinarith
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left h (show 0 ≤ (A+1)*(1+X) by positivity)
      dsimp [D]
      have h₃ := mul_le_mul_of_nonneg_left hDX (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith
    refine hceil.trans ?_
    unfold H
    rw [mul_div_assoc, add_div]
    exact (add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add hX0 hA') hT) 2).trans hBound
  have hTpow : T^p * (c*(1+T^(p/2))) ≤ 2*c*(1+T)^(2*p) := by
    have ht := Real.rpow_le_rpow hT (by linarith : T ≤ 1+T) hp
    have hq := Real.rpow_le_rpow hT (by linarith : T ≤ 1+T) (by positivity : 0 ≤ p/2)
    have hq' := hq.trans (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 1+T) (by linarith : p/2 ≤ p))
    have h1 := Real.one_le_rpow (by linarith : 1 ≤ 1+T) hp
    calc
      _ ≤ (1+T)^p * (c*(2*(1+T)^p)) := by gcongr; linarith
      _ = _ := by
        rw [show 2*p = p+p from by ring, Real.rpow_add (by positivity : 0 < 1+T)]
        ring
  let E (ω : Ω) := ENNReal.ofReal ((1+(K ω : ℝ))^p)
  have hPointI (ω : Ω) :
      E ω ≤ ENNReal.ofReal ((2:ℝ)^p) * (ENNReal.ofReal (D^p) +
        ENNReal.ofReal (T^p) * ENNReal.ofReal (v ω)^p) := by
    unfold E
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ 1+(K ω : ℝ)) hp]
    refine (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hPoint ω)) hp).trans ?_
    rw [ENNReal.ofReal_add hD0 (mul_nonneg hT (abs_nonneg _)), ENNReal.ofReal_mul hT]
    refine (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hp).trans_eq ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp, ENNReal.ofReal_rpow_of_nonneg hT hp,
      ENNReal.ofReal_rpow_of_nonneg hD0 hp, ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hp,
      ENNReal.ofReal_ofNat]
  change (∫⁻ ω, E ω ∂M.P) ≤ _
  refine (lintegral_mono hPointI).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
    lintegral_const, measure_univ, mul_one, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal ((2:ℝ)^p) * (ENNReal.ofReal (D^p) +
        ENNReal.ofReal (T^p) * ENNReal.ofReal (c*(1+T^(p/2)))) := by gcongr
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hT _)]
      refine (mul_le_mul_right (add_le_add_right (ENNReal.ofReal_le_ofReal hTpow) _) _).trans ?_
      rw [← ENNReal.ofReal_add (Real.rpow_nonneg hD0 _) (by positivity),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), hDpow]
      apply ENNReal.ofReal_le_ofReal
      have hh := Real.one_le_rpow (by linarith : 1 ≤ 1+X) hp
      nlinarith [mul_nonneg (by positivity : 0 ≤ (2:ℝ)^p * (2*c) * (1+T)^(2*p)) (sub_nonneg.mpr hh)]

private theorem right_continuous_sup_meas {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hf : ∀ t : ℝ, 0 ≤ t → Measurable (fun ω => f ω t))
    (hr : ∀ ω t, 0 ≤ t → ContinuousWithinAt (f ω) (Ici t) t) :
    Measurable (fun ω => ⨆ t : ℝ, ⨆ (_ : t ∈ Icc 0 T), ENNReal.ofReal (f ω t)) := by
  classical
  let G (ω : Ω) := ⨆ q : ℚ, if (q : ℝ) ∈ Icc 0 T then ENNReal.ofReal (f ω q) else 0
  let H (ω : Ω) := max (G ω) (ENNReal.ofReal (f ω T))
  have hG : Measurable G := by
    unfold G
    apply Measurable.iSup
    intro q
    by_cases h : (q : ℝ) ∈ Icc 0 T
    · simp only [if_pos h]
      exact (hf q h.1).ennreal_ofReal
    · simp only [if_neg h]
      exact measurable_const
  have hH : Measurable H := hG.max (hf T hT).ennreal_ofReal
  have hEq (ω : Ω) : H ω =
      ⨆ t : ℝ, ⨆ (_ : t ∈ Icc 0 T), ENNReal.ofReal (f ω t) := by
    apply le_antisymm
    · apply max_le
      · unfold G
        apply iSup_le
        intro q
        split_ifs with h
        · exact le_iSup₂_of_le (q : ℝ) h le_rfl
        · exact bot_le
      · exact le_iSup₂_of_le T ⟨hT, le_rfl⟩ le_rfl
    · apply iSup₂_le
      intro t ht
      by_cases h : t = T
      · exact h ▸ le_max_right _ _
      have htT : t < T := lt_of_le_of_ne ht.2 h
      have hchoose (j : ℕ) : ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < min T (t + 1 / (j + 1 : ℝ)) :=
        exists_rat_btwn (lt_min htT (lt_add_of_pos_right _ (by positivity)))
      choose q hq using hchoose
      have hub (j : ℕ) : (q j : ℝ) ≤ t + 1 / (j + 1 : ℝ) :=
        (hq j).2.le.trans (min_le_right _ _)
      have hlb (j : ℕ) : t ≤ (q j : ℝ) := (hq j).1.le
      have hInv : Tendsto (fun j : ℕ => 1 / (j + 1 : ℝ)) atTop (𝓝 0) := by
        have hn : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
        have hn' : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
          tendsto_atTop.2 (fun b => ((tendsto_atTop.1 hn) b).mono (fun _ h => by linarith))
        exact tendsto_const_nhds.div_atTop hn'
      have hUp : Tendsto (fun j : ℕ => t + 1 / (j + 1 : ℝ)) atTop (𝓝 t) := by
        simpa only [add_zero] using (tendsto_const_nhds (x := t)).add hInv
      have hqT : Tendsto (fun j : ℕ => (q j : ℝ)) atTop (𝓝[Ici t] t) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUp hlb hub,
          Eventually.of_forall hlb⟩
      have hL : Tendsto (fun j => ENNReal.ofReal (f ω (q j))) atTop (𝓝 (ENNReal.ofReal (f ω t))) :=
        (ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt (hr ω t ht.1)).tendsto.comp hqT
      refine le_of_tendsto hL (Eventually.of_forall fun j => ?_)
      have hqI : (q j : ℝ) ∈ Icc (0 : ℝ) T := ⟨ht.1.trans (hlb j), (hq j).2.le.trans (min_le_left _ _)⟩
      apply le_trans _ (le_max_left _ _)
      have hi := le_iSup (fun q : ℚ => if (q : ℝ) ∈ Icc 0 T then ENNReal.ofReal (f ω q) else 0) (q j)
      rwa [if_pos hqI] at hi
  simp_rw [← hEq]
  exact hH

private theorem finset_lintegral_rpow_sum_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : Finset ι) (Z : ι → Ω → ℝ≥0∞) (p : ℝ) (hp : 0 < p)
    (hZ : ∀ i ∈ s, Measurable (Z i)) :
    (∫⁻ ω, (∑ i ∈ s, Z i ω)^p ∂P) ≤
      (s.card : ℝ≥0∞)^p * ∑ i ∈ s, ∫⁻ ω, (Z i ω)^p ∂P := by
  by_cases hs : s.Nonempty
  · have hpow : Measurable (fun z : ℝ≥0∞ => z^p) :=
      (show Monotone (fun z : ℝ≥0∞ => z^p) from fun _ _ h => ENNReal.rpow_le_rpow h hp.le).measurable
    calc
      _ ≤ ∫⁻ ω, (s.card : ℝ≥0∞)^p * ∑ i ∈ s, (Z i ω)^p ∂P := by
        apply lintegral_mono
        intro ω
        obtain ⟨j, hj, he⟩ := s.exists_mem_eq_sup hs (fun i => Z i ω)
        have hU : ∑ i ∈ s, Z i ω ≤ (s.card : ℝ≥0∞) * Z j ω := by
          calc
            _ ≤ ∑ i ∈ s, Z j ω := Finset.sum_le_sum fun i hi => he ▸ Finset.le_sup (f := fun i => Z i ω) hi
            _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
        refine (ENNReal.rpow_le_rpow hU hp.le).trans ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
        exact mul_le_mul_right (Finset.single_le_sum (f := fun i => (Z i ω)^p) (fun _ _ => zero_le) hj) _
      _ = _ := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le (ENNReal.natCast_ne_top s.card))]
        congr 1
        exact lintegral_finsetSum s (f := fun i ω => (Z i ω)^p) (fun i hi => hpow.comp (hZ i hi))
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he, ENNReal.zero_rpow_of_pos hp]

private noncomputable def inputRate {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) : ℝ :=
  (M.lamN n i - M.rho i * M.muN n i * n) / Real.sqrt n

private theorem inputRate_tendsto {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (i : Fin k) :
    Tendsto (fun n => inputRate M n i) atTop (𝓝 (M.ell i)) := by
  have hlim := (M.lamHat_lim i).sub (tendsto_const_nhds.mul (M.muHat_lim i) :
    Tendsto (fun n : ℕ => M.rho i * (Real.sqrt n * (M.muN n i - M.mu i))) atTop
      (𝓝 (M.rho i * M.muHat i)))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn'
  have hmul : Real.sqrt (n : ℝ) * Real.sqrt n = n := Real.mul_self_sqrt hn'.le
  have hρ : M.rho i * M.mu i = M.lam i := div_mul_cancel₀ _ (M.mu_pos i).ne'
  unfold inputRate
  symm
  apply (div_eq_iff hs.ne').2
  symm
  calc
    (Real.sqrt (n : ℝ) * (M.lamN n i / n - M.lam i) -
        M.rho i * (Real.sqrt n * (M.muN n i - M.mu i))) * Real.sqrt n =
      (Real.sqrt n * Real.sqrt n) *
        (M.lamN n i / n - M.lam i - M.rho i * (M.muN n i - M.mu i)) := by ring
    _ = _ := by
      rw [hmul]
      calc
        (n : ℝ) * (M.lamN n i / n - M.lam i - M.rho i * (M.muN n i - M.mu i)) =
            M.lamN n i - (n : ℝ) * M.lam i -
              (n : ℝ) * M.rho i * M.muN n i + (n : ℝ) * (M.rho i * M.mu i) := by
          rw [mul_sub, mul_sub, mul_div_cancel₀ _ hn'.ne']
          ring
        _ = _ := by rw [hρ]; ring


private theorem arrivalCount_zero {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) : M.A n i ω 0 = 0 := by
  have hz : M.arrivalEpoch n i ω 0 = 0 := by simp [SystemSequence.arrivalEpoch, partialSum]
  have hp := (epoch_strict M n i ω) (Nat.zero_lt_succ 0)
  rw [hz] at hp
  simp only [SystemSequence.A, renewal_eq_of_bracket (epoch_strict M n i ω).monotone hz.le hp,
    ENat.toNat_zero, Nat.cast_zero]

set_option maxHeartbeats 1000000 in
private theorem arrivalCount_meas {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (t : ℝ) (ht : 0 ≤ t) :
    Measurable (fun ω => M.A n i ω t) := by
  let u : ℝ≥0 := ⟨t, ht⟩
  let v (ω : Ω) (j : ℕ) := M.U i (j+1) ω
  let f (w : ℕ → ℝ) := renewal_from_sequence (M.lamN n i) w u
  have heq : (fun ω => M.A n i ω t) = f ∘ v := by
    funext ω
    have h := congrFun (congrFun (arrival_suffix_eq M n i 0) ω) u
    have hz : M.arrivalEpoch n i ω 0 = 0 := by simp [SystemSequence.arrivalEpoch, partialSum]
    have hut : (u : ℝ) = t := rfl
    simpa only [hz, arrivalCount_zero M n i ω, zero_add, sub_zero, hut,
      Function.comp_def, Nat.zero_add, f, v] using h
  rw [heq]
  have hf : Measurable f := (measurable_pi_apply u).comp (renewal_from_sequence_meas _)
  have hv : Measurable v := measurable_pi_lambda v (fun j => M.U_meas i (j+1))
  exact hf.comp hv

private theorem arrivalCount_rightCont {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
    ContinuousWithinAt (M.A n i ω) (Ici t) t := by
  let e := M.arrivalEpoch n i ω
  have he0 : e 0 = 0 := by simp [e, SystemSequence.arrivalEpoch, partialSum]
  have hle : e 0 ≤ t := by rwa [he0]
  obtain ⟨j, hj, hu⟩ := arrival_prefix_index (e := e) hle (epoch_crosses M n i ω t)
  have hC (s : ℝ) (hs : t ≤ s) (hs' : s < e (j+1)) : M.A n i ω s = j := by
    unfold SystemSequence.A
    rw [renewal_eq_of_bracket (epoch_strict M n i ω).monotone (hj.trans hs) hs', ENat.toNat_natCast]
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [self_mem_nhdsWithin (s := Ici t), mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hu)] with s hs hs'
  rw [hC s hs hs', hC t le_rfl hu]

private theorem uniform_primitive_rate_bounds {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) :
    ∃ a > 0, ∀ᶠ n in atTop, ∀ i, M.lamN n i / (n : ℝ) ≤ a ∧ M.muN n i ≤ a ∧
      M.thetaN n i ≤ a ∧ |inputRate M n i| ≤ a ∧ M.rho i ≤ a := by
  let z (i : Fin k) := M.lam i + M.mu i + M.theta i + |M.ell i| + M.rho i
  let a := 1 + ∑ i, z i
  have hr (i : Fin k) : 0 ≤ M.rho i := div_nonneg (M.lam_pos i).le (M.mu_pos i).le
  have hz (i : Fin k) : 0 ≤ z i := by
    dsimp [z]
    linarith [(M.lam_pos i).le, (M.mu_pos i).le, M.theta_nonneg i, abs_nonneg (M.ell i), hr i]
  refine ⟨a, add_pos_of_pos_of_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => hz i)), ?_⟩
  rw [Filter.eventually_all]
  intro i
  have hzi := Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ i)
  have hAll : M.lam i < a ∧ M.mu i < a ∧ M.theta i < a ∧ |M.ell i| < a ∧ M.rho i < a := by
    dsimp [z] at hzi
    dsimp [a]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      linarith [(M.lam_pos i).le, (M.mu_pos i).le, M.theta_nonneg i, abs_nonneg (M.ell i), hr i]
  filter_upwards [(tendsto_order.1 (M.lam_lim i)).2 a hAll.1,
    (tendsto_order.1 (M.mu_lim i)).2 a hAll.2.1,
    (tendsto_order.1 (M.theta_lim i)).2 a hAll.2.2.1,
    (tendsto_order.1 (inputRate_tendsto M i).abs).2 a hAll.2.2.2.1]
    with n h₁ h₂ h₃ h₄
  exact ⟨h₁.le, h₂.le, h₃.le, h₄.le, hAll.2.2.2.2.le⟩

private theorem point_service_clock_le {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (hn : 1 ≤ n) (X0 : Fin k → ℕ) (X Ψ : Ω → ℝ → Fin k → ℝ)
    (hC : M.IsControlled n X0 X Ψ) (ω : Ω) (i : Fin k) (T : ℝ) (t : ℝ) (ht : t ∈ Icc 0 T) :
    busyTime Ψ ω i t / (n : ℝ) ∈ Icc 0 T := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine ⟨div_nonneg (intervalIntegral.integral_nonneg ht.1 (fun s hs => hC.psi_nonneg ω s i hs.1))
    hnR.le, ?_⟩
  apply (div_le_iff₀ hnR).2
  have hI := intervalIntegral.integral_mono_on ht.1 (hC.integrable ω i t ht.1).1
    (intervalIntegrable_const (c := (n : ℝ))) (fun s hs => (Finset.single_le_sum
      (fun j _ => hC.psi_nonneg ω s j hs.1) (Finset.mem_univ i)).trans (hC.servers ω s hs.1))
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hI
  exact hI.trans (mul_le_mul_of_nonneg_right ht.2 hnR.le)

private theorem shifted_factor_poly (s p : ℝ) (hs : 0 ≤ s) (hp : 0 ≤ p) (d : ℕ) (hd : p ≤ (d : ℝ)) :
    (1+s)^p ≤ (2:ℝ)^p * (1+s^d) := by
  rcases le_total s 1 with h | h
  · exact (Real.rpow_le_rpow (by positivity) (by linarith : 1+s ≤ 2) hp).trans
      (le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hs d]))
  · calc
      _ ≤ (2*s)^p := Real.rpow_le_rpow (by positivity) (by linarith) hp
      _ = (2:ℝ)^p * s^p := Real.mul_rpow (by norm_num) hs
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Real.rpow_natCast]
        exact (Real.rpow_le_rpow_of_exponent_le h hd).trans (le_add_of_nonneg_left zero_le_one)

set_option maxHeartbeats 3000000 in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] (M : SystemSequence Ω k)
    (mL mU : ℝ) (hA3 : M.Assumption3 mL mU) :
    ∃ (c : ℝ≥0) (m : ℕ), ∀ (x : Fin k → ℝ) (X0 : ℕ → Fin k → ℕ),
      Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x) →
      ∀ (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ),
      (∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n) ∧ IsWorkConserving n (X n) (Ψ n)) →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t : ℝ, 0 ≤ t →
      let W (ω : Ω) (s : ℝ) (i : Fin k) :=
        M.Xhat0 n (X0 n) i + M.Ahat n ω s i -
        M.Rhat n ω (queueTime (X n) (Ψ n) ω i s / n) i -
        M.Shat n ω (busyTime (Ψ n) ω i s / n) i +
        ((M.lamN n i - M.rho i * M.muN n i * n) / Real.sqrt n) * s
      (∫⁻ ω, (supDist (W ω) (fun _ => 0) t) ^ mU ∂M.P) ≤
        ENNReal.ofReal ((c : ℝ) * (1 + l1norm x ^ m) * (1 + t ^ m)) := by
  classical
  letI : IsProbabilityMeasure M.P := M.isProb
  let p := mU
  have hp : 1 < p := (by norm_num : (1 : ℝ) < 2).trans_le hA3.1
  have hp0 : 0 ≤ p := (zero_lt_one.trans hp).le
  obtain ⟨a, ha, haEv⟩ := uniform_primitive_rate_bounds M
  obtain ⟨cA, hcA⟩ := lemma_2 M mL mU hA3
  let c := max cA 0
  have hc : 0 ≤ c := le_max_right _ _
  let BP := (2 : ℝ)^p * (((p/(p-1))^p) * (2 * (⌈p⌉₊.factorial : ℝ) * Real.exp a) + a^p)
  let BR := (2 : ℝ)^p * ((a+3)^p + 2*c)
  let D := 1 + 2*c + BP + BP*BR + a^p
  let k5 := k * 5
  let E := ((k5 : ℝ)^p) * k5 * D
  let Mbar := ⌈2*p⌉₊
  have hBP : 0 ≤ BP := by dsimp [BP]; positivity
  have hBR : 0 ≤ BR := by dsimp [BR]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have h2p : 2*p ≤ (Mbar : ℝ) := Nat.le_ceil _
  refine ⟨⟨E * (2:ℝ)^p * (2:ℝ)^(2*p), by positivity⟩, Mbar, ?_⟩
  intro x X0 hx X Ψ hPol
  let u := l1norm x
  have hu : 0 ≤ u := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hInit : ∀ᶠ n in atTop, ∀ i, |M.Xhat0 n (X0 n) i| ≤ 1 + u := by
    rw [eventually_all]
    intro i
    have hi := (((continuous_apply i).tendsto x).comp hx).abs
    have hup : |x i| < 1 + u := by
      have h : |x i| ≤ u := Finset.single_le_sum (f := fun j => |x j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      linarith
    exact ((tendsto_order.1 hi).2 _ hup).mono (fun _ h => h.le)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (haEv.and (hInit.and (eventually_ge_atTop (1 : ℕ))))
  refine ⟨N, fun n hn T hT => ?_⟩
  obtain ⟨hRate, hX0, hn1⟩ := hN n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnP : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnP
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnR
  let G := (1+u)^p*(1+T)^(2*p)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have huPow : 1 ≤ (1+u)^p := Real.one_le_rpow (by linarith) hp0
  have hTpow : 1 ≤ (1+T)^(2*p) := Real.one_le_rpow (by linarith) (by positivity)
  have hG1 : (1+T)^(2*p) ≤ G := le_mul_of_one_le_left (by positivity) huPow
  have hG2 : (1+u)^p ≤ G := le_mul_of_one_le_right (by positivity) hTpow
  have hpowT : T^p ≤ (1+T)^(2*p) :=
    (Real.rpow_le_rpow hT (by linarith) hp0).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
  have hpowT' : (1+T)^p ≤ (1+T)^(2*p) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hpHalf : 1+T^(p/2) ≤ 2*(1+T)^(2*p) := by
    have h := (Real.rpow_le_rpow hT (by linarith : T ≤ 1+T) (by positivity : 0 ≤ p/2)).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith : p/2 ≤ 2*p))
    linarith
  let VA (i : Fin k) (ω : Ω) := ⨆ s : ℝ, ⨆ (_ : s ∈ Icc 0 T),
      ENNReal.ofReal |M.Ahat n ω s i|
  let VS (i : Fin k) (ω : Ω) := ⨆ s : ℝ, ⨆ (_ : s ∈ Icc 0 T),
      ENNReal.ofReal |M.Shat n ω s i|
  have hAm (i : Fin k) : Measurable (VA i) := by
    apply right_continuous_sup_meas _ _ hT
    · intro s hs
      exact (((arrivalCount_meas M n i s hs).sub_const _).div_const _).abs
    · intro ω s hs
      exact (((arrivalCount_rightCont M n i ω s hs).sub
        (continuous_const.mul continuous_id).continuousWithinAt).div_const _).abs
  have hSm (i : Fin k) : Measurable (VS i) := by
    apply right_continuous_sup_meas _ _ hT
    · intro s _
      exact ((((M.S_poisson n i).meas ((n : ℝ)*s)).sub_const _).div_const _).abs
    · intro ω s hs
      have hN := (((M.S_poisson n i).cadlag ω).1 ((n : ℝ)*s)
        (mul_nonneg (Nat.cast_nonneg _) hs)).comp (continuous_const.mul continuous_id).continuousWithinAt
        (fun b hb => show (n : ℝ)*s ≤ (n : ℝ)*b from mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n))
      exact ((hN.sub (continuous_const.mul continuous_id).continuousWithinAt).div_const _).abs
  have hAI (i : Fin k) : ∫⁻ ω, (VA i ω)^p ∂M.P ≤ ENNReal.ofReal (c*(1+T^(p/2))) := by
    have hPoint (ω : Ω) : VA i ω ≤ supDist (M.Ahat n ω) (fun _ => 0) T := by
      apply iSup₂_le
      intro s hs
      refine le_iSup₂_of_le s hs (ENNReal.ofReal_le_ofReal ?_)
      simpa only [Pi.zero_apply, sub_zero] using
        (Finset.single_le_sum (f := fun j => |M.Ahat n ω s j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
    refine (lintegral_mono (fun ω => ENNReal.rpow_le_rpow (hPoint ω) hp0)).trans
      ((hcA n hn1 T hT).trans (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hSI (i : Fin k) : ∫⁻ ω, (VS i ω)^p ∂M.P ≤ ENNReal.ofReal (BP * G) := by
    have H := centered_poisson_scaled_sup_moment (M.S_poisson n i) p a hp (hRate i).2.1 n hn1 T hT
    dsimp only at H
    have H' : (∫⁻ ω, (VS i ω)^p ∂M.P) ≤ ENNReal.ofReal (BP * (1+T)^p) := by
      simpa only [VS, SystemSequence.Shat, mul_comm (M.muN n i) (n : ℝ)] using H
    exact H'.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hpowT'.trans hG1) hBP))
  let Tb : ℝ≥0 := ⟨T, hT⟩
  choose VR hRm hRP hRI using (fun i : Fin k => abandonment_ranged_grid_majorant M n hn1 (X0 n) (X n) (Ψ n)
    (hPol n hn1).1 a p hp i (hRate i).2.2.1 Tb)
  have hInitialFluid (i : Fin k) : (X0 n i : ℝ)/(n : ℝ) ≤ a+1+u := by
    have he : (X0 n i : ℝ)/(n : ℝ) = M.rho i + M.Xhat0 n (X0 n) i / Real.sqrt n := by
      unfold SystemSequence.Xhat0
      rw [div_div, ← sq, Real.sq_sqrt hnP.le]
      field_simp
      ring
    have hxx : M.Xhat0 n (X0 n) i / Real.sqrt n ≤ 1+u :=
      ((div_le_div_of_nonneg_right (le_abs_self _) hs.le).trans (div_le_self (abs_nonneg _) hs1)).trans (hX0 i)
    rw [he]
    linarith [(hRate i).2.2.2.2]
  have hRI' (i : Fin k) : ∫⁻ ω, (VR i ω)^p ∂M.P ≤ ENNReal.ofReal ((BP*BR) * G) := by
    have hFinite : (∫⁻ ω, ENNReal.ofReal |M.Ahat n ω T i|^p ∂M.P) ≤
        ENNReal.ofReal (c*(1+T^(p/2))) :=
      (lintegral_mono (fun ω => ENNReal.rpow_le_rpow (le_iSup₂_of_le T ⟨hT, le_rfl⟩ le_rfl) hp0)).trans (hAI i)
    have hE := queue_arrival_envelope_moment M n hn1 (X0 n) x i a c p ha.le hc hp0 T hT
      (hInitialFluid i) (hRate i).1 hFinite
    dsimp only at hE
    refine (hRI i).trans ((mul_le_mul_right hE _).trans_eq ?_)
    rw [← ENNReal.ofReal_mul hBP]
    congr 1
    unfold BR G u
    ring
  let Z (j : Fin k × Fin 5) (ω : Ω) : ℝ≥0∞ :=
    ![ENNReal.ofReal (1+u), VA j.1 ω, VR j.1 ω, VS j.1 ω, ENNReal.ofReal (a*T)] j.2
  have hZm (j : Fin k × Fin 5) : Measurable (Z j) := by
    rcases j with ⟨i, j⟩
    fin_cases j <;> simp [Z, hAm, hRm, hSm, measurable_const]
  have hparts : 1 ≤ D ∧ 2*c ≤ D ∧ BP*BR ≤ D ∧ BP ≤ D ∧ a^p ≤ D := by
    dsimp [D]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith [mul_nonneg hBP hBR, Real.rpow_nonneg ha.le p]
  have hZI (j : Fin k × Fin 5) : ∫⁻ ω, (Z j ω)^p ∂M.P ≤ ENNReal.ofReal (D * G) := by
    rcases j with ⟨i, j⟩
    fin_cases j
    · change (∫⁻ _ : Ω, ENNReal.ofReal (1+u)^p ∂M.P) ≤ _
      rw [lintegral_const, measure_univ, mul_one, ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ 1+u) hp0]
      apply ENNReal.ofReal_le_ofReal
      exact hG2.trans (le_mul_of_one_le_left hG hparts.1)
    · change (∫⁻ ω, (VA i ω)^p ∂M.P) ≤ _
      refine (hAI i).trans (ENNReal.ofReal_le_ofReal ?_)
      have hm := mul_le_mul_of_nonneg_left (hpHalf.trans (mul_le_mul_of_nonneg_left hG1 (by norm_num))) hc
      exact hm.trans (by nlinarith [mul_le_mul_of_nonneg_right hparts.2.1 hG])
    · exact (hRI' i).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hparts.2.2.1 hG))
    · exact (hSI i).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hparts.2.2.2.1 hG))
    · change (∫⁻ _ : Ω, ENNReal.ofReal (a*T)^p ∂M.P) ≤ _
      rw [lintegral_const, measure_univ, mul_one,
        ENNReal.ofReal_rpow_of_nonneg (mul_nonneg ha.le hT) hp0, Real.mul_rpow ha.le hT]
      apply ENNReal.ofReal_le_ofReal
      exact (mul_le_mul_of_nonneg_left (hpowT.trans hG1) (by positivity)).trans
        (mul_le_mul_of_nonneg_right hparts.2.2.2.2 hG)
  let W (ω : Ω) (s : ℝ) (i : Fin k) :=
    M.Xhat0 n (X0 n) i + M.Ahat n ω s i -
    M.Rhat n ω (queueTime (X n) (Ψ n) ω i s / n) i -
    M.Shat n ω (busyTime (Ψ n) ω i s / n) i + inputRate M n i * s
  have hPoint (ω : Ω) (s : ℝ) (hsT : s ∈ Icc 0 T) (i : Fin k) :
      ENNReal.ofReal |W ω s i| ≤ ∑ j : Fin 5, Z (i,j) ω := by
    let b1 := M.Xhat0 n (X0 n) i
    let b2 := M.Ahat n ω s i
    let b3 := M.Rhat n ω (queueTime (X n) (Ψ n) ω i s / n) i
    let b4 := M.Shat n ω (busyTime (Ψ n) ω i s / n) i
    let b5 := inputRate M n i * s
    have hab1 := abs_add_le b1 b2
    have hab2 := (abs_sub (b1+b2) b3).trans (add_le_add_left hab1 _)
    have hab3 := (abs_sub (b1+b2-b3) b4).trans (add_le_add_left hab2 _)
    have abs_term : |W ω s i| ≤ |b1| + |b2| + |b3| + |b4| + |b5| :=
      (abs_add_le (b1+b2-b3-b4) b5).trans (add_le_add_left hab3 _)
    have hv1 : ENNReal.ofReal |b1| ≤ ENNReal.ofReal (1+u) := ENNReal.ofReal_le_ofReal (hX0 i)
    have hv2 : ENNReal.ofReal |b2| ≤ VA i ω := le_iSup₂_of_le s hsT le_rfl
    have hv3 : ENNReal.ofReal |b3| ≤ VR i ω := hRP i ω s hsT
    have hv4 : ENNReal.ofReal |b4| ≤ VS i ω :=
      le_iSup₂_of_le _ (point_service_clock_le M n hn1 (X0 n) (X n) (Ψ n) (hPol n hn1).1 ω i T s hsT) le_rfl
    have hv5 : ENNReal.ofReal |b5| ≤ ENNReal.ofReal (a*T) := ENNReal.ofReal_le_ofReal (by
      rw [show b5 = inputRate M n i * s from rfl, abs_mul, abs_of_nonneg hsT.1]
      exact mul_le_mul (hRate i).2.2.2.1 hsT.2 hsT.1 ha.le)
    calc
      _ ≤ ENNReal.ofReal (|b1| + |b2| + |b3| + |b4| + |b5|) := ENNReal.ofReal_le_ofReal abs_term
      _ = ENNReal.ofReal |b1| + ENNReal.ofReal |b2| + ENNReal.ofReal |b3| +
          ENNReal.ofReal |b4| + ENNReal.ofReal |b5| := by
        repeat rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ _ := by
        calc
          _ ≤ ENNReal.ofReal (1+u) + VA i ω + VR i ω + VS i ω + ENNReal.ofReal (a*T) := by gcongr
          _ = _ := by simp [Fin.sum_univ_succ, Z, add_assoc]
  have hSup (ω : Ω) : supDist (W ω) (fun _ => 0) T ≤ ∑ j, Z j ω := by
    unfold supDist
    apply iSup₂_le
    intro s hsT
    simp only [Pi.zero_apply, sub_zero]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _), Fintype.sum_prod_type]
    exact Finset.sum_le_sum (fun i _ => hPoint ω s hsT i)
  change (∫⁻ ω, (supDist (W ω) (fun _ => 0) T)^p ∂M.P) ≤ _
  refine (lintegral_mono (fun ω => ENNReal.rpow_le_rpow (hSup ω) hp0)).trans ?_
  refine (finset_lintegral_rpow_sum_bound M.P Finset.univ Z p (by linarith) (fun i _ => hZm i)).trans ?_
  have hcard : (Finset.univ : Finset (Fin k × Fin 5)).card = k5 := by simp [k5]
  rw [hcard]
  calc
    _ ≤ (k5 : ℝ≥0∞)^p * ∑ _ : Fin k × Fin 5, ENNReal.ofReal (D*G) := by gcongr; exact hZI _
    _ = ENNReal.ofReal (E * G) := by
      rw [Finset.sum_const, hcard, ← ENNReal.ofReal_nsmul, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) hp0,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      congr 1
      unfold E
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hX := shifted_factor_poly u p hu hp0 Mbar (by linarith)
      have hT' := shifted_factor_poly T (2*p) hT (by positivity) Mbar h2p
      have hh := mul_le_mul hX hT' (by positivity) (by positivity)
      refine (mul_le_mul_of_nonneg_left hh hE).trans_eq ?_
      change E * ((2:ℝ)^p * (1 + u^Mbar) * ((2:ℝ)^(2*p) * (1 + T^Mbar))) =
        E * (2:ℝ)^p * (2:ℝ)^(2*p) * (1 + u^Mbar) * (1 + T^Mbar)
      ring
