-- Prove2me | solution 1 for LostSalesConstantOrder.LargeLeadTime.minimizer_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:28:59.752182+00:00
-- url     : https://prove2.me/submissions/1f3891f5-8be7-4202-a912-cd2038770188

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace LSCOMin

open CappedBaseStock LostSalesConstantOrder.LargeLeadTime

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

lemma level_le (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath)
    (k : ℕ) : (fromState prm (I, x) d k).1 + arrival prm (fromState prm (I, x) d k) ≤
      I + (k + 1) * ∑ i, x i := by
  rw [arrival_fromState]
  calc (fromState prm (I, x) d k).1 + slot x k ≤ (I + k * ∑ i, x i) + ∑ i, x i :=
        add_le_add (onhand_le prm x I d k) (slot_le_sum x k)
    _ = I + (k + 1) * ∑ i, x i := by ring

lemma periodCost_le (prm : Parameters) (s : State prm.L) (e : ℝ≥0) :
    periodCost prm s e ≤ ENNReal.ofReal prm.h * ((s.1 + arrival prm s : ℝ≥0) : ℝ≥0∞) +
      ENNReal.ofReal prm.p * (e : ℝ≥0∞) := by
  unfold periodCost lostSales
  gcongr
  · exact tsub_le_self
  · exact tsub_le_self

lemma periodCost_ge (prm : Parameters) (s : State prm.L) (e : ℝ≥0) :
    ENNReal.ofReal prm.h * ENNReal.ofReal ((s.1 : ℝ) - e) ≤ periodCost prm s e := by
  unfold periodCost
  refine le_trans ?_ le_self_add
  gcongr
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_sub_def]
  apply ENNReal.ofReal_le_ofReal
  have : ((s.1 : ℝ) - e) ≤ ((s.1 + arrival prm s : ℝ≥0) : ℝ) - e := by
    push_cast
    have := (arrival prm s).2
    linarith
  exact le_trans this (le_max_left _ _)

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

lemma measurable_periodCost_comp (prm : Parameters) {α : Type*} [MeasurableSpace α]
    {f : α → State prm.L} {g : α → ℝ≥0} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => periodCost prm (f a) (g a)) := by
  unfold periodCost lostSales arrival
  have h1 : Measurable (fun a => (f a).1) := measurable_fst.comp hf
  have h2 : Measurable (fun a => (f a).2
      ⟨0, lt_of_lt_of_le Nat.zero_lt_one prm.leadTime_pos⟩) :=
    (measurable_pi_apply _).comp (measurable_snd.comp hf)
  fun_prop

lemma continuous_fromState (prm : Parameters) (d : DemandPath) (k : ℕ) :
    Continuous (fun z : (Fin prm.L → ℝ≥0) × ℝ≥0 => fromState prm (z.2, z.1) d k) := by
  induction k with
  | zero =>
    simp only [fromState]
    exact continuous_snd.prodMk continuous_fst
  | succ k ih =>
    simp only [fromState, step, arrival]
    refine Continuous.prodMk ?_ (continuous_pi (fun i => ?_))
    · have h1 : Continuous (fun z : (Fin prm.L → ℝ≥0) × ℝ≥0 => (fromState prm (z.2, z.1) d k).1) :=
        continuous_fst.comp ih
      have h2 : Continuous (fun z : (Fin prm.L → ℝ≥0) × ℝ≥0 => (fromState prm (z.2, z.1) d k).2
          ⟨0, lt_of_lt_of_le Nat.zero_lt_one prm.leadTime_pos⟩) :=
        (continuous_apply _).comp (continuous_snd.comp ih)
      exact (h1.add h2).sub continuous_const
    · split_ifs
      · exact (continuous_apply _).comp (continuous_snd.comp ih)
      · exact continuous_const

lemma continuous_periodCost_comp (prm : Parameters) {α : Type*} [TopologicalSpace α]
    {f : α → State prm.L} (hf : Continuous f) (e : ℝ≥0) :
    Continuous (fun a => periodCost prm (f a) e) := by
  unfold periodCost lostSales arrival
  have h1 : Continuous (fun a => (f a).1) := continuous_fst.comp hf
  have h2 : Continuous (fun a => (f a).2
      ⟨0, lt_of_lt_of_le Nat.zero_lt_one prm.leadTime_pos⟩) :=
    (continuous_apply _).comp (continuous_snd.comp hf)
  have hA : Continuous (fun a => (((f a).1 + (f a).2
      ⟨0, lt_of_lt_of_le Nat.zero_lt_one prm.leadTime_pos⟩ - e : ℝ≥0) : ℝ≥0∞)) :=
    ENNReal.continuous_coe.comp ((h1.add h2).sub continuous_const)
  have hB : Continuous (fun a => ((e - ((f a).1 + (f a).2
      ⟨0, lt_of_lt_of_le Nat.zero_lt_one prm.leadTime_pos⟩) : ℝ≥0) : ℝ≥0∞)) :=
    ENNReal.continuous_coe.comp (continuous_const.sub (h1.add h2))
  exact ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp hA).add
    ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp hB)

lemma lintegral_coord (P : DemandLaw) (k : ℕ) :
    ∫⁻ d, ((d k : ℝ≥0) : ℝ≥0∞) ∂demandPathLaw P = ∫⁻ e, (e : ℝ≥0∞) ∂P.law := by
  unfold demandPathLaw
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) k).lintegral_comp
    (f := fun e : ℝ≥0 => (e : ℝ≥0∞)) (by fun_prop)

lemma lintegral_coe_lt_top (P : DemandLaw) : ∫⁻ e, (e : ℝ≥0∞) ∂P.law < ∞ := by
  have := P.finiteMean.lintegral_lt_top
  simpa [ENNReal.ofReal_coe_nnreal] using this

lemma bound_lintegral_ne_top (P : DemandLaw) (prm : Parameters) (B : ℝ≥0) (k : ℕ) :
    ∫⁻ d, (ENNReal.ofReal prm.h * (B : ℝ≥0∞) + ENNReal.ofReal prm.p * ((d k : ℝ≥0) : ℝ≥0∞))
      ∂demandPathLaw P ≠ ∞ := by
  rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul _
    (by fun_prop), lintegral_coord]
  simp only [measure_univ, mul_one]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_coe_lt_top P).ne⟩

lemma term_le (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (d : DemandPath) (k : ℕ) :
    periodCost prm (fromState prm (I, x) d k) (d k) ≤
      ENNReal.ofReal prm.h * ((I + (k + 1) * ∑ i, x i : ℝ≥0) : ℝ≥0∞) +
        ENNReal.ofReal prm.p * ((d k : ℝ≥0) : ℝ≥0∞) := by
  refine le_trans (periodCost_le prm _ _) ?_
  refine add_le_add_left (mul_le_mul_right ?_ _) _
  exact ENNReal.coe_le_coe.2 (level_le prm x I d k)

lemma windowCost_ne_top (P : DemandLaw) (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) :
    windowCost P prm x I ≠ ∞ := by
  unfold windowCost
  rw [ENNReal.sum_ne_top]
  intro k _
  exact ne_top_of_le_ne_top (bound_lintegral_ne_top P prm _ k)
    (lintegral_mono (fun d => term_le prm x I d k))

lemma continuous_windowCost (P : DemandLaw) (prm : Parameters) :
    Continuous (fun z : (Fin prm.L → ℝ≥0) × ℝ≥0 => windowCost P prm z.1 z.2) := by
  unfold windowCost
  refine continuous_finsetSum _ (fun k _ => ?_)
  rw [continuous_iff_continuousAt]
  intro z0
  unfold ContinuousAt
  set B : ℝ≥0 := (z0.2 + 1) + (k + 1) * ∑ i, (z0.1 i + 1)
  have hev2 : ∀ᶠ z : (Fin prm.L → ℝ≥0) × ℝ≥0 in 𝓝 z0, z.2 < z0.2 + 1 :=
    (continuous_snd.tendsto z0).eventually (gt_mem_nhds (lt_add_one _))
  have hev1 : ∀ᶠ z : (Fin prm.L → ℝ≥0) × ℝ≥0 in 𝓝 z0, ∀ i, z.1 i < z0.1 i + 1 := by
    rw [Filter.eventually_all]
    intro i
    exact (((continuous_apply i).comp continuous_fst).tendsto z0).eventually
      (gt_mem_nhds (lt_add_one _))
  refine tendsto_lintegral_filter_of_dominated_convergence
    (fun d => ENNReal.ofReal prm.h * (B : ℝ≥0∞) + ENNReal.ofReal prm.p * ((d k : ℝ≥0) : ℝ≥0∞))
    ?_ ?_ (bound_lintegral_ne_top P prm B k) ?_
  · exact Filter.Eventually.of_forall (fun z =>
      measurable_periodCost_comp prm (measurable_fromState prm _ k) (measurable_pi_apply k))
  · filter_upwards [hev1, hev2] with z hz1 hz2
    refine Filter.Eventually.of_forall (fun d => le_trans (term_le prm z.1 z.2 d k) ?_)
    refine add_le_add_left (mul_le_mul_right ?_ _) _
    refine ENNReal.coe_le_coe.2 (add_le_add hz2.le (mul_le_mul_right ?_ _))
    exact Finset.sum_le_sum (fun i _ => (hz1 i).le)
  · refine Filter.Eventually.of_forall (fun d => ?_)
    exact ((continuous_periodCost_comp prm (continuous_fromState prm d k) (d k)).tendsto z0)


lemma periodCost_ge2 (prm : Parameters) (s : State prm.L) (e : ℝ≥0) :
    ENNReal.ofReal prm.h * ((s.1 - e : ℝ≥0) : ℝ≥0∞) ≤ periodCost prm s e := by
  unfold periodCost
  refine le_trans ?_ le_self_add
  refine mul_le_mul_right ?_ _
  exact ENNReal.coe_le_coe.2 (tsub_le_tsub_right le_self_add _)

lemma coercive (P : DemandLaw) (prm : Parameters) (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) :
    ENNReal.ofReal prm.h * ((I : ℝ≥0∞) - ∫⁻ e, (e : ℝ≥0∞) ∂P.law) ≤ windowCost P prm x I := by
  unfold windowCost
  have h0 : 0 ∈ Finset.range prm.L := Finset.mem_range.2 prm.leadTime_pos
  refine le_trans ?_ (Finset.single_le_sum (f := fun k => ∫⁻ d, periodCost prm
    (fromState prm (I, x) d k) (d k) ∂demandPathLaw P) (fun _ _ => zero_le) h0)
  simp only [fromState]
  calc ENNReal.ofReal prm.h * ((I : ℝ≥0∞) - ∫⁻ e, (e : ℝ≥0∞) ∂P.law)
      ≤ ENNReal.ofReal prm.h * ∫⁻ d, ((I - d 0 : ℝ≥0) : ℝ≥0∞) ∂demandPathLaw P := by
        refine mul_le_mul_right ?_ _
        rw [tsub_le_iff_right, ← lintegral_coord P 0,
          ← lintegral_add_left (by fun_prop)]
        calc (I : ℝ≥0∞) = ∫⁻ _d, (I : ℝ≥0∞) ∂demandPathLaw P := by simp
          _ ≤ _ := by
            apply lintegral_mono
            intro d
            show (I : ℝ≥0∞) ≤ ((I - d 0 : ℝ≥0) : ℝ≥0∞) + ((d 0 : ℝ≥0) : ℝ≥0∞)
            rw [← ENNReal.coe_add]
            exact ENNReal.coe_le_coe.2 le_tsub_add
    _ = ∫⁻ d, ENNReal.ofReal prm.h * ((I - d 0 : ℝ≥0) : ℝ≥0∞) ∂demandPathLaw P := by
        rw [lintegral_const_mul _ (by fun_prop)]
    _ ≤ _ := lintegral_mono (fun d => periodCost_ge2 prm _ _)

theorem main (P : DemandLaw) (prm : Parameters) :
    ∃ (x : Fin prm.L → ℝ≥0) (I : ℝ≥0), IsWindowMinimizer P prm x I := by
  have hh := prm.holding_pos
  set m := ∫⁻ e, (e : ℝ≥0∞) ∂P.law
  have hm : m ≠ ∞ := (lintegral_coe_lt_top P).ne
  set W0 := windowCost P prm (fun _ => 0) 0
  have hW0 : W0 ≠ ∞ := windowCost_ne_top P prm _ _
  have hH0 : ENNReal.ofReal prm.h ≠ 0 := by simpa using hh
  set M : ℝ≥0 := (m + W0 / ENNReal.ofReal prm.h).toNNReal
  have hMt : m + W0 / ENNReal.ofReal prm.h ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hm, ENNReal.div_ne_top hW0 hH0⟩
  have hM : (M : ℝ≥0∞) = m + W0 / ENNReal.ofReal prm.h := ENNReal.coe_toNNReal hMt
  set K : Set ((Fin prm.L → ℝ≥0) × ℝ≥0) :=
    (Set.univ.pi fun _ => Set.Icc 0 (Qlevel P prm)) ×ˢ Set.Icc 0 M
  have hK : IsCompact K := (isCompact_univ_pi (fun _ => isCompact_Icc)).prod isCompact_Icc
  have h0K : ((fun _ => 0), 0) ∈ K := by
    refine ⟨?_, ?_⟩
    · intro i _
      exact ⟨le_refl _, zero_le⟩
    · exact ⟨le_refl _, zero_le⟩
  obtain ⟨z, hzK, hmin⟩ := hK.exists_isMinOn ⟨_, h0K⟩
    (continuous_windowCost P prm).continuousOn
  have hmin' := isMinOn_iff.1 hmin
  refine ⟨z.1, z.2, ?_, ?_⟩
  · intro i
    exact (hzK.1 i (Set.mem_univ _)).2
  · intro x' I' hx'
    by_cases hI : I' ≤ M
    · have : (x', I') ∈ K := by
        refine ⟨?_, ⟨zero_le, hI⟩⟩
        intro i _
        exact ⟨zero_le, hx' i⟩
      have h2 := hmin' (x', I') this
      exact h2
    · push Not at hI
      have h1 := hmin' _ h0K
      refine le_trans h1 (le_trans ?_ (coercive P prm x' I'))
      have hle : (M : ℝ≥0∞) - m ≤ (I' : ℝ≥0∞) - m :=
        tsub_le_tsub_right (ENNReal.coe_le_coe.2 hI.le) _
      have hMm : (M : ℝ≥0∞) - m = W0 / ENNReal.ofReal prm.h := by
        rw [hM, ENNReal.add_sub_cancel_left hm]
      calc W0 = ENNReal.ofReal prm.h * (W0 / ENNReal.ofReal prm.h) := by
            rw [ENNReal.mul_div_cancel hH0 ENNReal.ofReal_ne_top]
        _ = ENNReal.ofReal prm.h * ((M : ℝ≥0∞) - m) := by rw [hMm]
        _ ≤ _ := mul_le_mul_right hle _

end LSCOMin

open LostSalesConstantOrder.LargeLeadTime in
theorem solution (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P) :
    ∃ (x : Fin prm.L → ℝ≥0) (I : ℝ≥0), IsWindowMinimizer P prm x I :=
  LSCOMin.main P prm
