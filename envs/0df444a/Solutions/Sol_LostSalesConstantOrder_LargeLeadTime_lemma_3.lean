-- Prove2me | solution 1 for LostSalesConstantOrder.LargeLeadTime.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:36:47.256473+00:00
-- url     : https://prove2.me/submissions/f365342d-3458-40d0-9c18-a2d42cb15fa6

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_Model

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LSCOL3

open CappedBaseStock LostSalesConstantOrder.LargeLeadTime

lemma history_congr (t : ℕ) (ω η : Sample) (h1 : ∀ k < t, ω.1 k = η.1 k) (h2 : ω.2 = η.2) :
    history t ω = history t η := by
  unfold history
  rw [h2]
  congr 1
  funext i
  exact h1 i i.2

lemma run_congr (prm : Parameters) (π : AdmissiblePolicy) (t : ℕ) (ω η : Sample)
    (h1 : ∀ k < t, ω.1 k = η.1 k) (h2 : ω.2 = η.2) : run prm π ω t = run prm π η t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hs := ih (fun k hk => h1 k (Nat.lt_succ_of_lt hk))
    have ho : order π t ω = order π t η := by
      unfold order
      rw [history_congr t ω η (fun k hk => h1 k (Nat.lt_succ_of_lt hk)) h2]
    simp only [run, hs, ho, h1 t (Nat.lt_succ_self t)]

lemma measurable_history (t : ℕ) : Measurable (history t) := by
  unfold history
  fun_prop

lemma measurable_order (π : AdmissiblePolicy) (t : ℕ) : Measurable (order π t) :=
  (π.measurable_decision t).comp (measurable_history t)

lemma measurable_run (prm : Parameters) (π : AdmissiblePolicy) (t : ℕ) :
    Measurable (fun ω => run prm π ω t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have ho := measurable_order π t
    simp only [run, step, arrival]
    refine Measurable.prodMk ?_ (measurable_pi_lambda _ (fun i => ?_))
    · have h1 : Measurable (fun ω : Sample => (run prm π ω t).1) := measurable_fst.comp ih
      have h2 : Measurable (fun ω : Sample => (run prm π ω t).2
          ⟨0, lt_of_lt_of_le Nat.zero_lt_one prm.leadTime_pos⟩) :=
        (measurable_pi_apply _).comp (measurable_snd.comp ih)
      have h3 : Measurable (fun ω : Sample => ω.1 t) := (measurable_pi_apply t).comp measurable_fst
      fun_prop
    · split_ifs
      · exact (measurable_pi_apply _).comp (measurable_snd.comp ih)
      · exact ho

lemma measurable_periodCost (prm : Parameters) :
    Measurable (fun p : State prm.L × ℝ≥0 => periodCost prm p.1 p.2) := by
  unfold periodCost lostSales arrival
  have h2 : Measurable (fun p : State prm.L × ℝ≥0 => p.1.2
      ⟨0, lt_of_lt_of_le Nat.zero_lt_one prm.leadTime_pos⟩) :=
    (measurable_pi_apply _).comp (measurable_snd.comp measurable_fst)
  fun_prop

lemma measurable_periodCost_comp (prm : Parameters) {α : Type*} [MeasurableSpace α]
    {f : α → State prm.L} {g : α → ℝ≥0} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => periodCost prm (f a) (g a)) := by
  unfold periodCost lostSales arrival
  have h1 : Measurable (fun a => (f a).1) := measurable_fst.comp hf
  have h2 : Measurable (fun a => (f a).2
      ⟨0, lt_of_lt_of_le Nat.zero_lt_one prm.leadTime_pos⟩) :=
    (measurable_pi_apply _).comp (measurable_snd.comp hf)
  fun_prop

/-- extension of a finite history by zeros -/
noncomputable def ext (t : ℕ) (a : Finset.range t → ℝ≥0) (u : ℝ) : Sample :=
  (fun k => if hk : k ∈ Finset.range t then a ⟨k, hk⟩ else 0, u)

lemma measurable_ext (t : ℕ) (u : ℝ) : Measurable (fun a => ext t a u) := by
  unfold ext
  refine Measurable.prodMk (measurable_pi_lambda _ (fun k => ?_)) measurable_const
  split_ifs <;> fun_prop

lemma run_ext (prm : Parameters) (π : AdmissiblePolicy) (t : ℕ) (d : DemandPath) (u : ℝ) :
    run prm π (d, u) t = run prm π (ext t ((Finset.range t).restrict d) u) t := by
  apply run_congr
  · intro k hk
    simp only [ext, Finset.mem_range, hk, dif_pos, Finset.restrict]
  · rfl

lemma fromState_pipe (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath)
    (k : ℕ) (i : Fin prm.L) : (fromState prm (I, x) d k).2 i = slot x (i.val + k) := by
  induction k generalizing i with
  | zero => simp [fromState, slot, i.2]
  | succ k ih =>
    simp only [fromState, step]
    split_ifs with hi
    · rw [ih]
      congr 1
      simp only
      omega
    · unfold slot
      rw [dif_neg (by omega)]

lemma arrival_fromState (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath)
    (k : ℕ) : arrival prm (fromState prm (I, x) d k) = slot x k := by
  unfold arrival
  rw [fromState_pipe]
  simp

lemma measurable_fromState (prm : Parameters) (s : State prm.L) (k : ℕ) :
    Measurable (fun d : DemandPath => fromState prm s d k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    simp only [fromState, step, arrival]
    refine Measurable.prodMk ?_ (measurable_pi_lambda _ (fun i => ?_))
    · have h1 : Measurable (fun d : DemandPath => (fromState prm s d k).1) :=
        measurable_fst.comp ih
      have h2 : Measurable (fun d : DemandPath => (fromState prm s d k).2
          ⟨0, lt_of_lt_of_le Nat.zero_lt_one prm.leadTime_pos⟩) :=
        (measurable_pi_apply _).comp (measurable_snd.comp ih)
      have h3 : Measurable (fun d : DemandPath => d k) := measurable_pi_apply k
      fun_prop
    · split_ifs
      · exact (measurable_pi_apply _).comp (measurable_snd.comp ih)
      · exact measurable_const


lemma measurable_fromState2 (prm : Parameters) (k : ℕ) :
    Measurable (fun p : State prm.L × DemandPath => fromState prm p.1 p.2 k) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    simp only [fromState, step, arrival]
    refine Measurable.prodMk ?_ (measurable_pi_lambda _ (fun i => ?_))
    · have h1 : Measurable (fun p : State prm.L × DemandPath => (fromState prm p.1 p.2 k).1) :=
        measurable_fst.comp ih
      have h2 : Measurable (fun p : State prm.L × DemandPath => (fromState prm p.1 p.2 k).2
          ⟨0, lt_of_lt_of_le Nat.zero_lt_one prm.leadTime_pos⟩) :=
        (measurable_pi_apply _).comp (measurable_snd.comp ih)
      have h3 : Measurable (fun p : State prm.L × DemandPath => p.2 k) :=
        (measurable_pi_apply k).comp measurable_snd
      fun_prop
    · split_ifs
      · exact (measurable_pi_apply _).comp (measurable_snd.comp ih)
      · exact measurable_const

/-- the demand path shifted by `t₀` -/
def shift (t₀ : ℕ) (d : DemandPath) : DemandPath := fun j => d (t₀ + j)

lemma measurable_shift (t₀ : ℕ) : Measurable (shift t₀) :=
  measurable_pi_lambda _ (fun j => measurable_pi_apply (t₀ + j))

lemma map_shift (P : DemandLaw) (t₀ : ℕ) :
    (demandPathLaw P).map (shift t₀) = demandPathLaw P := by
  unfold demandPathLaw
  refine Measure.eq_infinitePi _ (fun s t ht => ?_)
  rw [Measure.map_apply (measurable_shift t₀) (MeasurableSet.pi s.countable_toSet
    (fun i _ => ht i))]
  have hset : shift t₀ ⁻¹' (Set.pi (↑s) t) =
      Set.pi (↑(s.map (addLeftEmbedding t₀))) (fun i => t (i - t₀)) := by
    ext d
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_map,
      addLeftEmbedding_apply, forall_exists_index, and_imp, shift]
    constructor
    · rintro h i j hj rfl
      simpa using h j hj
    · intro h j hj
      have := h (t₀ + j) j hj rfl
      simpa using this
  rw [hset, Measure.infinitePi_pi _ (fun i _ => ht _), Finset.prod_map]
  simp

lemma indep_restrict_shift (P : DemandLaw) (t₀ : ℕ) :
    IndepFun (fun d : DemandPath => (Finset.range t₀).restrict d) (shift t₀)
      (demandPathLaw P) := by
  have hI := iIndepFun_infinitePi (P := fun _ : ℕ => P.law) (X := fun _ x => x)
    (fun _ => measurable_id)
  rw [iIndepFun_iff_iIndep] at hI
  have hle : ∀ i, MeasurableSpace.comap (fun d : DemandPath => d i) inferInstance ≤
      (inferInstance : MeasurableSpace DemandPath) :=
    fun i => (measurable_pi_apply i).comap_le
  have hind := indep_iSup_of_disjoint hle hI (S := {i | i < t₀}) (T := {i | t₀ ≤ i})
    (by
      rw [Set.disjoint_left]
      intro a ha hb
      simp only [Set.mem_setOf_eq] at ha hb
      omega)
  rw [IndepFun_iff_Indep]
  have h1 : MeasurableSpace.comap (fun d : DemandPath => (Finset.range t₀).restrict d)
      MeasurableSpace.pi ≤ ⨆ i ∈ {i | i < t₀},
      MeasurableSpace.comap (fun d : DemandPath => d i) inferInstance := by
    simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def]
    refine iSup_le (fun j => ?_)
    have hj : (j : ℕ) < t₀ := Finset.mem_range.1 j.2
    exact le_iSup₂ (f := fun i (_ : i ∈ {i | i < t₀}) =>
      MeasurableSpace.comap (fun d : DemandPath => d i) inferInstance) (j : ℕ) hj
  have h2 : MeasurableSpace.comap (shift t₀) MeasurableSpace.pi ≤ ⨆ i ∈ {i | t₀ ≤ i},
      MeasurableSpace.comap (fun d : DemandPath => d i) inferInstance := by
    simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def]
    refine iSup_le (fun j => ?_)
    exact le_iSup₂ (f := fun i (_ : i ∈ {i | t₀ ≤ i}) =>
      MeasurableSpace.comap (fun d : DemandPath => d i) inferInstance) (t₀ + j)
      (by simp)
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind h1) h2

lemma key_indep (P : DemandLaw) (prm : Parameters) (π : AdmissiblePolicy) (t₀ : ℕ)
    (Φ : State prm.L × DemandPath → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ ω, Φ (run prm π ω t₀, shift t₀ ω.1) ∂sampleLaw P =
      ∫⁻ ω, ∫⁻ d', Φ (run prm π ω t₀, d') ∂demandPathLaw P ∂sampleLaw P := by
  have hR := measurable_run prm π t₀
  have hS : Measurable (fun ω : Sample => shift t₀ ω.1) := (measurable_shift t₀).comp measurable_fst
  have hInt : Measurable (fun s : State prm.L => ∫⁻ d', Φ (s, d') ∂demandPathLaw P) :=
    hΦ.lintegral_prod_right'
  have hL : Measurable (fun ω : Sample => Φ (run prm π ω t₀, shift t₀ ω.1)) :=
    hΦ.comp (hR.prodMk hS)
  have hL2 : Measurable (fun ω : Sample => ∫⁻ d', Φ (run prm π ω t₀, d') ∂demandPathLaw P) :=
    hInt.comp hR
  unfold sampleLaw
  rw [lintegral_prod_symm _ hL.aemeasurable, lintegral_prod_symm _ hL2.aemeasurable]
  refine lintegral_congr (fun u => ?_)
  simp only [Function.comp]
  simp_rw [run_ext prm π t₀ _ u]
  set G : (Finset.range t₀ → ℝ≥0) → State prm.L := fun a => run prm π (ext t₀ a u) t₀ with hG
  have hGm : Measurable G := (measurable_run prm π t₀).comp (measurable_ext t₀ u)
  have hY : Measurable (fun d : DemandPath => (Finset.range t₀).restrict d) :=
    Finset.measurable_restrict _
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable
    (measurable_shift t₀).aemeasurable).1 (indep_restrict_shift P t₀)
  rw [map_shift] at hmap
  have hΨ : Measurable (fun p : (Finset.range t₀ → ℝ≥0) × DemandPath => Φ (G p.1, p.2)) :=
    hΦ.comp ((hGm.comp measurable_fst).prodMk measurable_snd)
  have hcomp : ∫⁻ d, Φ (G ((Finset.range t₀).restrict d), shift t₀ d) ∂demandPathLaw P
      = ∫⁻ p, Φ (G p.1, p.2) ∂((demandPathLaw P).map
          (fun d => ((Finset.range t₀).restrict d, shift t₀ d))) := by
    rw [lintegral_map hΨ (hY.prodMk (measurable_shift t₀))]
  have hIG : Measurable (fun a => ∫⁻ d', Φ (G a, d') ∂demandPathLaw P) := hInt.comp hGm
  rw [hcomp, hmap, lintegral_prod _ hΨ.aemeasurable]
  exact lintegral_map hIG hY

lemma run_window (prm : Parameters) (π : AdmissiblePolicy) (ω : Sample) (t₀ : ℕ) (k : ℕ)
    (hk : k ≤ prm.L) :
    (run prm π ω (t₀ + k)).1 = (fromState prm (run prm π ω t₀) (shift t₀ ω.1) k).1 ∧
      ∀ i : Fin prm.L, i.val + k < prm.L →
        (run prm π ω (t₀ + k)).2 i = (fromState prm (run prm π ω t₀) (shift t₀ ω.1) k).2 i := by
  induction k with
  | zero => exact ⟨rfl, fun i _ => rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    have harr : arrival prm (run prm π ω (t₀ + k)) =
        arrival prm (fromState prm (run prm π ω t₀) (shift t₀ ω.1) k) := by
      unfold arrival
      exact h2 _ (by simp; omega)
    rw [← add_assoc]
    simp only [run, fromState, step]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [h1, harr]
      rfl
    · have hi1 : i.val + 1 < prm.L := by omega
      simp only [hi1, dif_pos]
      exact h2 _ (by simp; omega)

lemma periodCost_congr (prm : Parameters) (s s' : State prm.L) (e : ℝ≥0)
    (h1 : s.1 = s'.1) (h2 : arrival prm s = arrival prm s') :
    periodCost prm s e = periodCost prm s' e := by
  unfold periodCost lostSales
  rw [h1, h2]

theorem part1 (P : DemandLaw) (prm : Parameters) (π : AdmissiblePolicy) (t₀ : ℕ) :
    costWindow P prm π t₀ =
      ∫⁻ ω, windowCost P prm (run prm π ω t₀).2 (run prm π ω t₀).1 ∂sampleLaw P := by
  unfold costWindow windowCost periodExpectedCost
  simp only [Prod.mk.eta]
  have hΦ : ∀ k, Measurable (fun p : State prm.L × DemandPath =>
      periodCost prm (fromState prm p.1 p.2 k) (p.2 k)) := fun k =>
    measurable_periodCost_comp prm (measurable_fromState2 prm k)
      ((measurable_pi_apply k).comp measurable_snd)
  have hm : ∀ k, Measurable (fun ω : Sample => ∫⁻ d, periodCost prm
      (fromState prm (run prm π ω t₀) d k) (d k) ∂demandPathLaw P) := fun k =>
    ((hΦ k).lintegral_prod_right').comp (measurable_run prm π t₀)
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
    lintegral_finsetSum _ (fun k _ => hm k)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k < prm.L := Finset.mem_range.1 hk
  have := key_indep P prm π t₀ _ (hΦ k)
  simp only at this
  rw [← this]
  refine lintegral_congr (fun ω => ?_)
  obtain ⟨h1, h2⟩ := run_window prm π ω t₀ k hk'.le
  apply periodCost_congr
  · exact h1
  · unfold arrival
    exact h2 _ (by simp; omega)

/-- the `j`-th term of the Lindley maximum -/
noncomputable def Tm {L : ℕ} (x : Fin L → ℝ≥0) (I : ℝ≥0) (k : ℕ) (d : DemandPath) (j : ℕ) : ℝ :=
  (∑ i ∈ Finset.Icc (k + 1 - j) k, ((slot x (i - 1) : ℝ) - (d (i - 1) : ℝ))) +
    if j = k then (I : ℝ) else 0

lemma Tm_zero {L : ℕ} (x : Fin L → ℝ≥0) (I : ℝ≥0) (k : ℕ) (d : DemandPath) :
    Tm x I (k + 1) d 0 = 0 := by
  unfold Tm
  have : Finset.Icc (k + 1 + 1 - 0) (k + 1) = ∅ := by
    ext i; simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
  rw [this]
  simp

lemma Tm_succ {L : ℕ} (x : Fin L → ℝ≥0) (I : ℝ≥0) (k : ℕ) (d : DemandPath) (j : ℕ) :
    Tm x I (k + 1) d (j + 1) = Tm x I k d j + ((slot x k : ℝ) - (d k : ℝ)) := by
  unfold Tm
  have h1 : k + 1 + 1 - (j + 1) = k + 1 - j := by omega
  rw [h1, Finset.sum_Icc_succ_top (by omega)]
  simp only [Nat.add_sub_cancel, add_left_inj]
  by_cases hj : j = k
  · simp [hj]; ring
  · simp [hj]

lemma lindley (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath) (k : ℕ) :
    ((fromState prm (I, x) d k).1 : ℝ) =
      (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one (Tm x I k d) := by
  induction k with
  | zero =>
    apply le_antisymm
    · refine le_trans (le_of_eq ?_) (Finset.le_sup' (Tm x I 0 d) (Finset.mem_range.2
        (Nat.zero_lt_one)))
      simp [Tm, fromState]
    · refine Finset.sup'_le _ _ (fun j hj => ?_)
      have : j = 0 := by simpa using hj
      subst this
      simp [Tm, fromState]
  | succ k ih =>
    have hstep : ((fromState prm (I, x) d (k + 1)).1 : ℝ) =
        max (((fromState prm (I, x) d k).1 : ℝ) + (slot x k : ℝ) - (d k : ℝ)) 0 := by
      simp only [fromState, step]
      rw [arrival_fromState, NNReal.coe_sub_def]
      push_cast
      rfl
    rw [hstep, ih]
    apply le_antisymm
    · refine max_le ?_ ?_
      · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
          (Tm x I k d)
        rw [hjeq]
        refine le_trans (le_of_eq ?_) (Finset.le_sup' (Tm x I (k + 1) d) (b := j + 1)
          (Finset.mem_range.2 (by have := Finset.mem_range.1 hj; omega)))
        rw [Tm_succ]; ring
      · refine le_trans (le_of_eq ?_) (Finset.le_sup' (Tm x I (k + 1) d) (b := 0)
          (Finset.mem_range.2 (by omega)))
        rw [Tm_zero]
    · refine Finset.sup'_le _ _ (fun j hj => ?_)
      rcases j with _ | j
      · rw [Tm_zero]; exact le_max_right _ _
      · rw [Tm_succ]
        refine le_trans ?_ (le_max_left _ _)
        have hjk : j < k + 1 := by have := Finset.mem_range.1 hj; omega
        have := Finset.le_sup' (s := Finset.range (k + 1)) (Tm x I k d) (b := j)
          (Finset.mem_range.2 hjk)
        linarith

lemma slot_le_sum {L : ℕ} (x : Fin L → ℝ≥0) (j : ℕ) : slot x j ≤ ∑ i, x i := by
  unfold slot
  split_ifs with h
  · exact Finset.single_le_sum (f := x) (fun _ _ => zero_le) (Finset.mem_univ _)
  · exact zero_le

lemma onhand_le (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath)
    (k : ℕ) : (fromState prm (I, x) d k).1 ≤ I + k * ∑ i, x i := by
  induction k with
  | zero => simp [fromState]
  | succ k ih =>
    simp only [fromState, step]
    rw [arrival_fromState]
    calc (fromState prm (I, x) d k).1 + slot x k - d k
        ≤ (fromState prm (I, x) d k).1 + slot x k := tsub_le_self
      _ ≤ (I + k * ∑ i, x i) + ∑ i, x i := add_le_add ih (slot_le_sum x k)
      _ = I + ((k + 1 : ℕ) : ℝ≥0) * ∑ i, x i := by push_cast; ring


lemma integrable_coord (P : DemandLaw) (k : ℕ) :
    Integrable (fun d : DemandPath => (d k : ℝ)) (demandPathLaw P) := by
  have h := Measure.infinitePi_map_eval (fun _ : ℕ => P.law) k
  have hi : Integrable (fun e : ℝ≥0 => (e : ℝ)) ((demandPathLaw P).map (fun d => d k)) := by
    unfold demandPathLaw; rw [h]; exact P.finiteMean
  exact (integrable_map_measure (by fun_prop) (measurable_pi_apply k).aemeasurable).1 hi

lemma integral_coord (P : DemandLaw) (k : ℕ) :
    ∫ d : DemandPath, (d k : ℝ) ∂(demandPathLaw P) = mean P := by
  have h := Measure.infinitePi_map_eval (fun _ : ℕ => P.law) k
  unfold mean
  rw [← integral_map (measurable_pi_apply k).aemeasurable (by fun_prop)]
  unfold demandPathLaw
  rw [h]

lemma integrable_onhand (P : DemandLaw) (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0)
    (k : ℕ) : Integrable (fun d => ((fromState prm (I, x) d k).1 : ℝ)) (demandPathLaw P) := by
  refine Integrable.mono' (integrable_const ((I : ℝ) + k * ∑ i, (x i : ℝ))) ?_ ?_
  · exact (measurable_fst.comp
      (measurable_fromState prm (I, x) k)).coe_nnreal_real.aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    have := onhand_le prm x I d k
    have h2 : (((fromState prm (I, x) d k).1 : ℝ≥0) : ℝ) ≤ ((I + k * ∑ i, x i : ℝ≥0) : ℝ) :=
      NNReal.coe_le_coe.2 this
    push_cast at h2
    exact h2

/-- lost sales in window period `k` -/
noncomputable def lost (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath)
    (k : ℕ) : ℝ :=
  max ((d k : ℝ) - (((fromState prm (I, x) d k).1 : ℝ) + (slot x k : ℝ))) 0

lemma onhand_succ (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath) (k : ℕ) :
    ((fromState prm (I, x) d (k + 1)).1 : ℝ) =
      max (((fromState prm (I, x) d k).1 : ℝ) + (slot x k : ℝ) - (d k : ℝ)) 0 := by
  simp only [fromState, step]
  rw [arrival_fromState, NNReal.coe_sub_def]
  push_cast
  rfl

lemma lost_eq (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath) (k : ℕ) :
    lost prm x I d k = ((fromState prm (I, x) d (k + 1)).1 : ℝ) -
      ((fromState prm (I, x) d k).1 : ℝ) - (slot x k : ℝ) + (d k : ℝ) := by
  rw [onhand_succ]
  unfold lost
  rcases le_total (((fromState prm (I, x) d k).1 : ℝ) + (slot x k : ℝ)) (d k : ℝ) with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring

lemma cost_eq (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath) (k : ℕ) :
    periodCost prm (fromState prm (I, x) d k) (d k) =
      ENNReal.ofReal (prm.h * ((fromState prm (I, x) d (k + 1)).1 : ℝ) +
        prm.p * lost prm x I d k) := by
  have hp := prm.penalty_pos
  have hh := prm.holding_pos
  unfold periodCost lostSales lost
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hh.le,
    ENNReal.ofReal_mul hp.le, arrival_fromState]
  congr 2
  · simp only [fromState, step]
    rw [arrival_fromState, ENNReal.ofReal_coe_nnreal]
  · rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_sub_def]
    push_cast
    rfl

lemma integrable_lost (P : DemandLaw) (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0)
    (k : ℕ) : Integrable (fun d => lost prm x I d k) (demandPathLaw P) := by
  have : (fun d => lost prm x I d k) = fun d => ((fromState prm (I, x) d (k + 1)).1 : ℝ) -
      ((fromState prm (I, x) d k).1 : ℝ) - (slot x k : ℝ) + (d k : ℝ) := by
    funext d; exact lost_eq prm x I d k
  rw [this]
  exact (((integrable_onhand P prm x I (k + 1)).sub (integrable_onhand P prm x I k)).sub
    (integrable_const _)).add (integrable_coord P k)

lemma sum_Icc_one (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma sum_slot {L : ℕ} (x : Fin L → ℝ≥0) :
    ∑ k ∈ Finset.range L, (slot x k : ℝ) = ∑ i, (x i : ℝ) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => (slot x k : ℝ)) L]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [slot, i.2]

theorem part2 (P : DemandLaw) (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) :
    windowCost P prm x I =
      ENNReal.ofReal
        (prm.h * ∑ k ∈ Finset.Icc 1 prm.L,
            ∫ d, (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
              (fun j => (∑ i ∈ Finset.Icc (k + 1 - j) k,
                  ((slot x (i - 1) : ℝ) - (d (i - 1) : ℝ))) +
                if j = k then (I : ℝ) else 0) ∂demandPathLaw P +
          prm.p * ((∫ d, (endInventory prm x I d : ℝ) ∂demandPathLaw P) -
            I + prm.L * mean P - ∑ i, (x i : ℝ))) := by
  have hp := prm.penalty_pos
  have hh := prm.holding_pos
  set a : ℕ → ℝ := fun k => ∫ d, ((fromState prm (I, x) d k).1 : ℝ) ∂demandPathLaw P with ha
  have hint : ∀ k, Integrable (fun d => prm.h * ((fromState prm (I, x) d (k + 1)).1 : ℝ) +
      prm.p * lost prm x I d k) (demandPathLaw P) := fun k =>
    ((integrable_onhand P prm x I (k + 1)).const_mul _).add ((integrable_lost P prm x I k).const_mul _)
  have hlost : ∀ k, ∫ d, lost prm x I d k ∂demandPathLaw P =
      a (k + 1) - a k - slot x k + mean P := by
    intro k
    simp_rw [lost_eq]
    have i1 : Integrable (fun d => ((fromState prm (I, x) d (k + 1)).1 : ℝ) -
        ((fromState prm (I, x) d k).1 : ℝ)) (demandPathLaw P) :=
      (integrable_onhand P prm x I (k + 1)).sub (integrable_onhand P prm x I k)
    have i2 : Integrable (fun d => ((fromState prm (I, x) d (k + 1)).1 : ℝ) -
        ((fromState prm (I, x) d k).1 : ℝ) - (slot x k : ℝ)) (demandPathLaw P) :=
      i1.sub (integrable_const _)
    rw [integral_add i2 (integrable_coord P k), integral_sub i1 (integrable_const _),
      integral_sub (integrable_onhand P prm x I (k + 1)) (integrable_onhand P prm x I k),
      integral_const, integral_coord]
    simp [ha]
  have hnn : ∀ k, 0 ≤ prm.h * a (k + 1) + prm.p * (a (k + 1) - a k - slot x k + mean P) := by
    intro k
    rw [← hlost]
    have h1 : 0 ≤ a (k + 1) := integral_nonneg (fun d => NNReal.coe_nonneg _)
    have h2 : 0 ≤ ∫ d, lost prm x I d k ∂demandPathLaw P :=
      integral_nonneg (fun d => le_max_right _ _)
    positivity
  have hterm : ∀ k, ∫⁻ d, periodCost prm (fromState prm (I, x) d k) (d k) ∂demandPathLaw P =
      ENNReal.ofReal (prm.h * a (k + 1) + prm.p * (a (k + 1) - a k - slot x k + mean P)) := by
    intro k
    simp_rw [cost_eq]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint k) (Filter.Eventually.of_forall (fun d => by
      have : 0 ≤ lost prm x I d k := le_max_right _ _
      have : (0 : ℝ) ≤ ((fromState prm (I, x) d (k + 1)).1 : ℝ) := NNReal.coe_nonneg _
      positivity))]
    congr 1
    rw [integral_add ((integrable_onhand P prm x I (k + 1)).const_mul _)
      ((integrable_lost P prm x I k).const_mul _), integral_const_mul, integral_const_mul,
      hlost]
  unfold windowCost
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hnn k)]
  congr 1
  have hA : ∀ k, ∫ d, (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
      (fun j => (∑ i ∈ Finset.Icc (k + 1 - j) k,
        ((slot x (i - 1) : ℝ) - (d (i - 1) : ℝ))) + if j = k then (I : ℝ) else 0)
        ∂demandPathLaw P = a k := by
    intro k
    rw [ha]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun d => ?_))
    simp only
    rw [lindley]
    rfl
  simp_rw [hA]
  rw [sum_Icc_one (fun k => a k)]
  have ha0 : a 0 = I := by simp [ha, fromState]
  have htel := Finset.sum_range_sub a prm.L
  have hend : ∫ d, (endInventory prm x I d : ℝ) ∂demandPathLaw P = a prm.L := rfl
  rw [hend, ← sum_slot x]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have : ∑ k ∈ Finset.range prm.L, (a (k + 1) - a k - (slot x k : ℝ) + mean P) =
      (a prm.L - a 0) - ∑ k ∈ Finset.range prm.L, (slot x k : ℝ) + prm.L * mean P := by
    rw [← htel, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp
  rw [this, ha0]
  ring

end LSCOL3

open LostSalesConstantOrder.LargeLeadTime in
theorem solution (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P) :
    (∀ (π : CappedBaseStock.AdmissiblePolicy) (t₀ : ℕ),
      costWindow P prm π t₀ =
        ∫⁻ ω, windowCost P prm (CappedBaseStock.run prm π ω t₀).2
          (CappedBaseStock.run prm π ω t₀).1 ∂CappedBaseStock.sampleLaw P) ∧
    ∀ (x : Fin prm.L → ℝ≥0) (I : ℝ≥0),
      windowCost P prm x I =
        ENNReal.ofReal
          (prm.h * ∑ k ∈ Finset.Icc 1 prm.L,
              ∫ d, (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
                (fun j => (∑ i ∈ Finset.Icc (k + 1 - j) k,
                    ((slot x (i - 1) : ℝ) - (d (i - 1) : ℝ))) +
                  if j = k then (I : ℝ) else 0) ∂CappedBaseStock.demandPathLaw P +
            prm.p * ((∫ d, (endInventory prm x I d : ℝ) ∂CappedBaseStock.demandPathLaw P) -
              I + prm.L * CappedBaseStock.mean P - ∑ i, (x i : ℝ))) :=
  ⟨fun π t₀ => LSCOL3.part1 P prm π t₀, fun x I => LSCOL3.part2 P prm x I⟩
