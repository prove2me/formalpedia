-- Prove2me | solution 1 for LostSalesOrderUpTo.Asymptotic.lemma13
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T04:56:37.503989+00:00
-- url     : https://prove2.me/submissions/5544fa83-abf1-4dac-ba64-d1ec90c3201c

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder
import Theorems.Thm_CappedBaseStock_base_stock_cost_of_loss_bound

-- Proven component: Definitions/Def_CappedBaseStock_Integration.lean
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
namespace LostSalesBracketIntegration
open CappedBaseStock

lemma demand_measurePreserving (P : DemandLaw) (t : ℕ) :
    MeasurePreserving (fun ω : Sample => ω.1 t) (sampleLaw P) P.law := by
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) t).comp
    (measurePreserving_fst (μ := demandPathLaw P) (ν := seedLaw))

lemma demand_integrable (P : DemandLaw) (t : ℕ) :
    Integrable (fun ω : Sample => (ω.1 t : ℝ)) (sampleLaw P) := by
  exact (demand_measurePreserving P t).integrable_comp_of_integrable P.finiteMean

lemma demand_integral (P : DemandLaw) (t : ℕ) :
    (∫ ω : Sample, (ω.1 t : ℝ) ∂sampleLaw P) = mean P := by
  have hd := demand_measurePreserving P t
  rw [mean, ← hd.map_eq]
  exact (integral_map hd.aemeasurable (by fun_prop)).symm

lemma loss_measurable (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    Measurable (fun ω : Sample =>
      (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ)) := by
  have hs := measurable_cbsRun c S r t
  unfold lostSales arrival
  fun_prop

lemma loss_integrable (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    Integrable (fun ω : Sample =>
      (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ)) (sampleLaw P) := by
  refine (demand_integrable P t).mono' (loss_measurable c S r t).aestronglyMeasurable ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
  exact_mod_cast (tsub_le_self : ω.1 t - ((cbsRun c S r ω t).1 + arrival c (cbsRun c S r ω t)) ≤ ω.1 t)

lemma loss_integral_nonneg (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    0 ≤ ∫ ω : Sample, (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ) ∂sampleLaw P := by
  exact integral_nonneg (fun _ => NNReal.coe_nonneg _)

lemma loss_integral_le_mean (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    (∫ ω : Sample, (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ) ∂sampleLaw P) ≤ mean P := by
  rw [← demand_integral P t]
  apply integral_mono (loss_integrable P c S r t) (demand_integrable P t)
  intro ω
  exact_mod_cast (tsub_le_self : ω.1 t - ((cbsRun c S r ω t).1 + arrival c (cbsRun c S r ω t)) ≤ ω.1 t)

lemma lintegral_loss_eq (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    (∫⁻ ω : Sample, (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ≥0∞) ∂sampleLaw P) =
      ENNReal.ofReal (∫ ω : Sample, (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ) ∂sampleLaw P) := by
  exact lintegral_coe_eq_integral _ (loss_integrable P c S r t)

end LostSalesBracketIntegration

-- Proven component: Solutions/CbsBaseStockDynamics.lean
noncomputable section
open scoped NNReal ENNReal BigOperators

namespace LostSalesBracketDynamics
open CappedBaseStock

def bsPos {L : ℕ} (s : State L) : ℝ :=
  (s.1 : ℝ) + ∑ i : Fin L, (s.2 i : ℝ)
lemma bs_queue_sum (L : ℕ) (hL : 0 < L) (x : Fin L → ℝ≥0) (q : ℝ≥0) :
    (∑ i : Fin L, (if hi : i.val + 1 < L then (x ⟨i.val + 1, hi⟩ : ℝ) else (q : ℝ))) +
      (x ⟨0, hL⟩ : ℝ) = (∑ i : Fin L, (x i : ℝ)) + (q : ℝ) := by
  cases L with
  | zero => omega
  | succ n =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp only [Fin.val_last, lt_self_iff_false, dite_false]
    have heq : (∑ i : Fin n, if hi : i.castSucc.val + 1 < n + 1 then
        (x ⟨i.castSucc.val + 1, hi⟩ : ℝ) else (q : ℝ)) =
        ∑ i : Fin n, (x i.succ : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_castSucc, Nat.succ_lt_succ_iff, i.isLt, dite_true]
      rfl
    rw [heq]
    have hz : (⟨0, hL⟩ : Fin (n + 1)) = 0 := rfl
    rw [hz]
    ring

lemma bs_pos_nonneg {L : ℕ} (s : State L) : 0 ≤ bsPos s := by
  unfold bsPos
  positivity

lemma bs_available_le_pos (c : Parameters) (s : State c.L) :
    ((s.1 + arrival c s : ℝ≥0) : ℝ) ≤ bsPos s := by
  simp only [NNReal.coe_add, bsPos]
  apply add_le_add le_rfl
  exact Finset.single_le_sum (fun i _ => (s.2 i).coe_nonneg) (Finset.mem_univ _)

lemma bs_fill_le_pos (c : Parameters) (s : State c.L) (d : ℝ≥0) :
    (filledDemand c s d : ℝ) ≤ bsPos s := by
  calc
    _ ≤ ((s.1 + arrival c s : ℝ≥0) : ℝ) := by
      exact_mod_cast min_le_right d (s.1 + arrival c s)
    _ ≤ _ := bs_available_le_pos c s

lemma bs_step_inventory (c : Parameters) (s : State c.L) (q d : ℝ≥0) :
    ((step c s q d).1 : ℝ) + (filledDemand c s d : ℝ) =
      (s.1 : ℝ) + (arrival c s : ℝ) := by
  simp only [step, filledDemand, NNReal.coe_add, NNReal.coe_sub_def, NNReal.coe_min]
  rcases le_total (d : ℝ) ((s.1 : ℝ) + (arrival c s : ℝ)) with h | h
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h)]
    ring

lemma bs_step_pos (c : Parameters) (s : State c.L) (q d : ℝ≥0) :
    bsPos (step c s q d) + (filledDemand c s d : ℝ) = bsPos s + (q : ℝ) := by
  have hq := bs_queue_sum c.L (lt_of_lt_of_le Nat.zero_lt_one c.leadTime_pos) s.2 q
  have hi := bs_step_inventory c s q d
  have heq : (∑ i : Fin c.L, ((if hi : i.val + 1 < c.L then s.2 ⟨i.val + 1, hi⟩ else q : ℝ≥0) : ℝ)) =
      ∑ i : Fin c.L, if hi : i.val + 1 < c.L then (s.2 ⟨i.val + 1, hi⟩ : ℝ) else (q : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> rfl
  unfold bsPos
  change ((step c s q d).1 : ℝ) +
    (∑ i : Fin c.L, ((if hi : i.val + 1 < c.L then s.2 ⟨i.val + 1, hi⟩ else q : ℝ≥0) : ℝ)) +
      (filledDemand c s d : ℝ) = _
  rw [heq]
  change _ + (s.2 ⟨0, _⟩ : ℝ) = _ at hq
  unfold arrival at hi
  linarith

lemma bs_order_eq (c : Parameters) (S : ℝ≥0) (s : State c.L)
    (hs : bsPos s ≤ (S : ℝ)) :
    (cbsOrder c.L S S s : ℝ) = (S : ℝ) - bsPos s := by
  unfold cbsOrder
  rw [min_eq_left (tsub_le_self : S - (s.1 + ∑ i, s.2 i) ≤ S)]
  rw [NNReal.coe_sub]
  · simp [bsPos]
  · apply NNReal.coe_le_coe.mp
    simpa only [bsPos, NNReal.coe_add, NNReal.coe_sum] using hs

lemma bs_pos_bound (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    bsPos (cbsRun c S S ω t) ≤ (S : ℝ) := by
  induction t with
  | zero => simp [cbsRun, initialState, bsPos]
  | succ t ih =>
    have hp := bs_step_pos c (cbsRun c S S ω t)
      (cbsOrder c.L S S (cbsRun c S S ω t)) (ω.1 t)
    rw [bs_order_eq c S _ ih] at hp
    change bsPos (cbsRun c S S ω (t+1)) + _ = _ at hp
    linarith [(filledDemand c (cbsRun c S S ω t) (ω.1 t)).coe_nonneg]

lemma bs_pos_fill (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    bsPos (cbsRun c S S ω (t+1)) +
      (filledDemand c (cbsRun c S S ω t) (ω.1 t) : ℝ) = (S : ℝ) := by
  have hp := bs_step_pos c (cbsRun c S S ω t)
    (cbsOrder c.L S S (cbsRun c S S ω t)) (ω.1 t)
  rw [bs_order_eq c S _ (bs_pos_bound c S ω t)] at hp
  change bsPos (cbsRun c S S ω (t+1)) + _ = _ at hp
  linarith

lemma bs_inventory_le (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    ((cbsRun c S S ω t).1 : ℝ) ≤ (S : ℝ) := by
  have h := bs_pos_bound c S ω t
  have hp : 0 ≤ ∑ i : Fin c.L, ((cbsRun c S S ω t).2 i : ℝ) := by positivity
  unfold bsPos at h
  linarith

lemma bs_order_initial (c : Parameters) (S : ℝ≥0) (ω : Sample) :
    cbsOrder c.L S S (cbsRun c S S ω 0) = S := by
  simp [cbsRun, initialState, cbsOrder]

lemma bs_order_next (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    (cbsOrder c.L S S (cbsRun c S S ω (t+1)) : ℝ) =
      (filledDemand c (cbsRun c S S ω t) (ω.1 t) : ℝ) := by
  rw [bs_order_eq c S _ (bs_pos_bound c S ω (t+1))]
  linarith [bs_pos_fill c S ω t]

end LostSalesBracketDynamics

namespace LostSalesBracketDynamics
open CappedBaseStock

lemma bs_order_fill (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    (cbsOrder c.L S S (cbsRun c S S ω (t + 1)) : ℝ) =
      (filledDemand c (cbsRun c S S ω t) (ω.1 t) : ℝ) := by
  rw [bs_order_eq c S _ (bs_pos_bound c S ω (t + 1))]
  linarith [bs_pos_fill c S ω t]

private lemma bs_queue_age (c : Parameters) (S : ℝ≥0) (ω : Sample) (t k : ℕ)
    (i : Fin c.L) (hi : i.val + k + 1 = c.L) :
    (cbsRun c S S ω (t + k + 1)).2 i = cbsOrder c.L S S (cbsRun c S S ω t) := by
  induction k generalizing i with
  | zero =>
    simp only [cbsRun, step]
    rw [dif_neg (by omega)]
  | succ k ih =>
    have hi' : i.val + 1 < c.L := by omega
    have ht : t + (k + 1) + 1 = (t + k + 1) + 1 := by omega
    rw [ht, cbsRun]
    dsimp only [step]
    rw [dif_pos hi']
    exact ih ⟨i.val + 1, hi'⟩ (by dsimp; omega)

lemma bs_pipeline_order (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) (i : Fin c.L) :
    (cbsRun c S S ω (t + c.L)).2 i =
      cbsOrder c.L S S (cbsRun c S S ω (t + i.val)) := by
  have h := bs_queue_age c S ω (t + i.val) (c.L - i.val - 1) i (by omega)
  have ht : t + i.val + (c.L - i.val - 1) + 1 = t + c.L := by omega
  rwa [ht] at h

lemma bs_pipeline_fill (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) (i : Fin c.L) :
    ((cbsRun c S S ω (t + c.L + 1)).2 i : ℝ) =
      (filledDemand c (cbsRun c S S ω (t + i.val)) (ω.1 (t + i.val)) : ℝ) := by
  rw [show t + c.L + 1 = (t + 1) + c.L by omega, bs_pipeline_order]
  rw [show t + 1 + i.val = (t + i.val) + 1 by omega, bs_order_fill]

lemma bs_available_window (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    ((cbsRun c S S ω (t + c.L)).1 : ℝ) +
      (arrival c (cbsRun c S S ω (t + c.L)) : ℝ) +
      (∑ i ∈ Finset.range c.L,
        (filledDemand c (cbsRun c S S ω (t + i)) (ω.1 (t + i)) : ℝ)) = (S : ℝ) := by
  have hp := bs_pos_fill c S ω (t + c.L)
  have hi := bs_step_inventory c (cbsRun c S S ω (t + c.L))
    (cbsOrder c.L S S (cbsRun c S S ω (t + c.L))) (ω.1 (t + c.L))
  change ((cbsRun c S S ω (t + c.L + 1)).1 : ℝ) + _ = _ at hi
  unfold bsPos at hp
  have hq : (∑ i : Fin c.L, ((cbsRun c S S ω (t + c.L + 1)).2 i : ℝ)) =
      ∑ i ∈ Finset.range c.L,
        (filledDemand c (cbsRun c S S ω (t + i)) (ω.1 (t + i)) : ℝ) := by
    simp_rw [bs_pipeline_fill]
    exact Fin.sum_univ_eq_sum_range
      (fun i => (filledDemand c (cbsRun c S S ω (t + i)) (ω.1 (t + i)) : ℝ)) c.L
  rw [hq] at hp
  linarith

lemma bs_filled_add_lost (c : Parameters) (s : State c.L) (d : ℝ≥0) :
    (filledDemand c s d : ℝ) + (lostSales c s d : ℝ) = (d : ℝ) := by
  have h : lostSales c s d + filledDemand c s d = d := tsub_add_min
  exact_mod_cast (add_comm (filledDemand c s d) (lostSales c s d)).trans h

lemma bs_loss_recursion (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    (lostSales c (cbsRun c S S ω (t + c.L)) (ω.1 (t + c.L)) : ℝ) =
      max ((∑ i ∈ Finset.range (c.L + 1), (ω.1 (t + i) : ℝ)) - (S : ℝ) -
        ∑ i ∈ Finset.range c.L,
          (lostSales c (cbsRun c S S ω (t + i)) (ω.1 (t + i)) : ℝ)) 0 := by
  have ha := bs_available_window c S ω t
  have hsum : (∑ i ∈ Finset.range c.L,
        (filledDemand c (cbsRun c S S ω (t + i)) (ω.1 (t + i)) : ℝ)) +
      (∑ i ∈ Finset.range c.L,
        (lostSales c (cbsRun c S S ω (t + i)) (ω.1 (t + i)) : ℝ)) =
      ∑ i ∈ Finset.range c.L, (ω.1 (t + i) : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact bs_filled_add_lost c _ _
  rw [Finset.sum_range_succ]
  conv_lhs => rw [lostSales, NNReal.coe_sub_def, NNReal.coe_add]
  congr 1
  linarith


end LostSalesBracketDynamics

noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
namespace LostSalesBracket
open CappedBaseStock LostSalesOrderUpTo.Asymptotic LostSalesBracketIntegration LostSalesBracketDynamics

lemma sum_le_of_block_bound (a : ℕ → ℝ) (q L : ℕ) (hq : 0 < q)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ n, a n ≤ D)
    (hb : ∀ m, L ≤ m → ∑ i ∈ Finset.range q, a (m + i) ≤ C) :
    ∀ N, ∑ i ∈ Finset.range N, a i ≤ (N : ℝ) * (C / q) + (L + q : ℕ) * D := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hsmall : N ≤ L + q
    · calc
        ∑ i ∈ Finset.range N, a i ≤ ∑ _i ∈ Finset.range N, D :=
          Finset.sum_le_sum (fun i _ => ha i)
        _ = (N : ℝ) * D := by simp
        _ ≤ (L + q : ℕ) * D := mul_le_mul_of_nonneg_right (by exact_mod_cast hsmall) hD
        _ ≤ _ := le_add_of_nonneg_left (by positivity)
    · have hNq : q ≤ N := by omega
      have hN : N - q + q = N := Nat.sub_add_cancel hNq
      have hi := ih (N - q) (by omega)
      have hb' := hb (N - q) (by omega)
      have hcast : ((N - q : ℕ) : ℝ) + (q : ℝ) = (N : ℝ) := by exact_mod_cast hN
      have hq0 : (q : ℝ) ≠ 0 := by positivity
      have hmul : (q : ℝ) * (C / q) = C := by field_simp
      calc
        ∑ i ∈ Finset.range N, a i =
            (∑ i ∈ Finset.range (N - q), a i) +
              ∑ i ∈ Finset.range q, a (N - q + i) := by
                rw [← Finset.sum_range_add, hN]
        _ ≤ (N - q : ℕ) * (C / q) + (L + q : ℕ) * D + C := add_le_add hi hb'
        _ = (((N - q : ℕ) : ℝ) + q) * (C / q) + (L + q : ℕ) * D := by
          rw [add_mul, hmul]
          ring
        _ = _ := by rw [hcast]

lemma ennreal_average_le_of_block_bound (a : ℕ → ℝ) (q L : ℕ) (hq : 0 < q)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ D)
    (hb : ∀ m, L ≤ m → ∑ i ∈ Finset.range q, a (m + i) ≤ C) :
    Filter.limsup (fun T : ℕ =>
      (∑ t ∈ Finset.range (T + 1), ENNReal.ofReal (a t)) / (T + 1 : ℝ≥0∞)) atTop ≤
      ENNReal.ofReal (C / q) := by
  let bound : ℕ → ℝ := fun T => C / q + ((L + q : ℕ) : ℝ) * D / (T + 1)
  have hle : ∀ T : ℕ,
      (∑ t ∈ Finset.range (T + 1), ENNReal.ofReal (a t)) / (T + 1 : ℝ≥0∞) ≤
        ENNReal.ofReal (bound T) := by
    intro T
    have hsum := sum_le_of_block_bound a q L hq C D hC hD ha hb (T+1)
    have ht : 0 < (T : ℝ) + 1 := by positivity
    have hdiv : (∑ t ∈ Finset.range (T + 1), a t) / ((T : ℝ) + 1) ≤ bound T := by
      apply (div_le_iff₀ ht).mpr
      dsimp [bound]
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt ht)]
      simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hsum
    have hden : ENNReal.ofReal ((T : ℝ) + 1) = (T + 1 : ℝ≥0∞) := by
      simp [ENNReal.ofReal_add (Nat.cast_nonneg T) zero_le_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => ha0 i), ← hden,
      ← ENNReal.ofReal_div_of_pos ht]
    exact ENNReal.ofReal_le_ofReal hdiv
  have ht : Tendsto (fun T : ℕ => (T : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hconv : Tendsto bound atTop (nhds (C / q)) := by
    simpa [bound] using (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop ht) :
      Tendsto (fun T : ℕ => C / q + ((L + q : ℕ) : ℝ) * D / ((T : ℝ) + 1))
        atTop (nhds (C / q + 0)))
  exact (Filter.limsup_le_limsup (Filter.Eventually.of_forall hle)).trans_eq
    (ENNReal.tendsto_ofReal hconv).limsup_eq



lemma sum_ge_of_block_bound (a : ℕ → ℝ) (q L : ℕ) (hq : 0 < q)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, 0 ≤ a n)
    (hb : ∀ m, L ≤ m → C ≤ ∑ i ∈ Finset.range q, a (m + i)) :
    ∀ N : ℕ, (N : ℝ) * (C / q) - (L + q : ℕ) * (C / q) ≤
      ∑ i ∈ Finset.range N, a i := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    have hCq : 0 ≤ C / (q : ℝ) := by positivity
    by_cases hsmall : N ≤ L + q
    · have hmul := mul_le_mul_of_nonneg_right (show (N : ℝ) ≤ (L+q : ℕ) by exact_mod_cast hsmall) hCq
      exact (sub_nonpos.mpr hmul).trans (Finset.sum_nonneg fun i _ => ha i)
    · have hNq : q ≤ N := by omega
      have hN : N - q + q = N := Nat.sub_add_cancel hNq
      have hi := ih (N - q) (by omega)
      have hb' := hb (N - q) (by omega)
      have hcast : ((N - q : ℕ) : ℝ) + (q : ℝ) = (N : ℝ) := by exact_mod_cast hN
      have hq0 : (q : ℝ) ≠ 0 := by positivity
      have hmul : (q : ℝ) * (C / q) = C := by field_simp
      have hs : (∑ i ∈ Finset.range N, a i) =
          (∑ i ∈ Finset.range (N-q), a i) + ∑ i ∈ Finset.range q, a (N-q+i) := by
        rw [← Finset.sum_range_add, hN]
      rw [hs]
      nlinarith

lemma ennreal_average_ge_of_block_bound (a : ℕ → ℝ) (q L : ℕ) (hq : 0 < q)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, 0 ≤ a n)
    (hb : ∀ m, L ≤ m → C ≤ ∑ i ∈ Finset.range q, a (m + i)) :
    ENNReal.ofReal (C / q) ≤ Filter.limsup (fun T : ℕ =>
      (∑ t ∈ Finset.range (T + 1), ENNReal.ofReal (a t)) / (T + 1 : ℝ≥0∞)) atTop := by
  let bound : ℕ → ℝ := fun T => C / q - ((L + q : ℕ) : ℝ) * (C / q) / (T + 1)
  have hle : ∀ T : ℕ, ENNReal.ofReal (bound T) ≤
      (∑ t ∈ Finset.range (T + 1), ENNReal.ofReal (a t)) / (T + 1 : ℝ≥0∞) := by
    intro T
    have hsum := sum_ge_of_block_bound a q L hq C hC ha hb (T+1)
    have ht : 0 < (T : ℝ) + 1 := by positivity
    have hdiv : bound T ≤ (∑ t ∈ Finset.range (T + 1), a t) / ((T : ℝ) + 1) := by
      apply (le_div_iff₀ ht).mpr
      dsimp [bound]
      rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt ht)]
      simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hsum
    have hden : ENNReal.ofReal ((T : ℝ) + 1) = (T + 1 : ℝ≥0∞) := by
      simp [ENNReal.ofReal_add (Nat.cast_nonneg T) zero_le_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => ha i), ← hden,
      ← ENNReal.ofReal_div_of_pos ht]
    exact ENNReal.ofReal_le_ofReal hdiv
  have ht : Tendsto (fun T : ℕ => (T : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hconv : Tendsto bound atTop (nhds (C / q)) := by
    simpa [bound] using (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop ht) :
      Tendsto (fun T : ℕ => C / q - ((L + q : ℕ) : ℝ) * (C / q) / ((T : ℝ) + 1))
        atTop (nhds (C / q - 0)))
  rw [← (ENNReal.tendsto_ofReal hconv).limsup_eq]
  exact Filter.limsup_le_limsup (Filter.Eventually.of_forall hle)

lemma shift_measurePreserving (P : DemandLaw) (m : ℕ) :
    MeasurePreserving (fun d : DemandPath => fun j => d (m+j))
      (demandPathLaw P) (demandPathLaw P) := by
  constructor
  · fun_prop
  · exact Measure.map_infinitePi_infinitePi_of_inj (fun i j hij => Nat.add_left_cancel hij)

def window (c : Parameters) (t : ℕ) (ω : Sample) : ℝ≥0 :=
  ∑ i ∈ Finset.range (c.L+1), ω.1 (t+i)

lemma window_mp (P : DemandLaw) (c : Parameters) (t : ℕ) :
    MeasurePreserving (window c t) (sampleLaw P) (leadTimeLaw P c.L) := by
  have hm := (shift_measurePreserving P t).comp
    (measurePreserving_fst (μ := demandPathLaw P) (ν := seedLaw))
  have hsum : Measurable (fun d : DemandPath => ∑ i ∈ Finset.range (c.L+1), d i) := by fun_prop
  have hh : MeasurePreserving (fun d : DemandPath => ∑ i ∈ Finset.range (c.L+1), d i)
      (demandPathLaw P) (leadTimeLaw P c.L) := ⟨hsum, rfl⟩
  exact hh.comp hm

lemma leadtime_integrable (P : DemandLaw) (c : Parameters) :
    Integrable (fun d : ℝ≥0 => (d : ℝ)) (leadTimeLaw P c.L) := by
  have hm := window_mp P c 0
  apply (hm.integrable_comp (by fun_prop)).mp
  change Integrable (fun ω : Sample => (window c 0 ω : ℝ)) (sampleLaw P)
  simp only [window, NNReal.coe_sum]
  exact integrable_finsetSum _ (fun i _ => demand_integrable P (0+i))

lemma window_holding_integral (P : DemandLaw) (c : Parameters) (S : ℝ≥0) (t : ℕ) :
    (∫ ω : Sample, max ((S : ℝ) - (window c t ω : ℝ)) 0 ∂sampleLaw P) =
      expectedHolding (leadTimeLaw P c.L) S := by
  have hm := window_mp P c t
  unfold expectedHolding
  rw [← hm.map_eq]
  exact (integral_map hm.aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun d : ℝ≥0 => max ((S : ℝ) - (d : ℝ)) 0) _)).symm

lemma window_shortfall_integral (P : DemandLaw) (c : Parameters) (S : ℝ≥0) (t : ℕ) :
    (∫ ω : Sample, max ((window c t ω : ℝ) - (S : ℝ)) 0 ∂sampleLaw P) =
      expectedShortfall (leadTimeLaw P c.L) S := by
  have hm := window_mp P c t
  unfold expectedShortfall
  rw [← hm.map_eq]
  exact (integral_map hm.aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun d : ℝ≥0 => max ((d : ℝ) - (S : ℝ)) 0) _)).symm

lemma window_balance (c : Parameters) (S : ℝ≥0) (ω : Sample) (t : ℕ) :
    ((cbsRun c S S ω (t+c.L+1)).1 : ℝ) = (S : ℝ) - (window c t ω : ℝ) +
      ∑ i ∈ Finset.range (c.L+1), (lostSales c (cbsRun c S S ω (t+i)) (ω.1 (t+i)) : ℝ) := by
  have ha := bs_available_window c S ω t
  have hi := bs_step_inventory c (cbsRun c S S ω (t+c.L))
    (cbsOrder c.L S S (cbsRun c S S ω (t+c.L))) (ω.1 (t+c.L))
  change ((cbsRun c S S ω (t+c.L+1)).1 : ℝ) + _ = _ at hi
  have hs : (∑ i ∈ Finset.range (c.L+1),
      (filledDemand c (cbsRun c S S ω (t+i)) (ω.1 (t+i)) : ℝ)) +
      (∑ i ∈ Finset.range (c.L+1),
      (lostSales c (cbsRun c S S ω (t+i)) (ω.1 (t+i)) : ℝ)) = (window c t ω : ℝ) := by
    rw [← Finset.sum_add_distrib]
    simp only [window, NNReal.coe_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact bs_filled_add_lost c _ _
  rw [Finset.sum_range_succ] at hs
  linarith

lemma holding_integrable (P : DemandLaw) (c : Parameters) (S : ℝ≥0) (t : ℕ) :
    Integrable (fun ω : Sample => ((cbsRun c S S ω (t+1)).1 : ℝ)) (sampleLaw P) := by
  refine (integrable_const (S : ℝ)).mono' ?_ ?_
  · exact ((measurable_cbsRun c S S (t+1)).fst.coe_nnreal_real).aestronglyMeasurable
  · filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact bs_inventory_le c S ω (t+1)

lemma holding_lower (P : DemandLaw) (c : Parameters) (S : ℝ≥0) (t : ℕ) :
    expectedHolding (leadTimeLaw P c.L) S ≤
      ∫ ω : Sample, ((cbsRun c S S ω (t+c.L+1)).1 : ℝ) ∂sampleLaw P := by
  rw [← window_holding_integral P c S t]
  apply integral_mono
    (((integrable_const (S : ℝ)).sub
      ((window_mp P c t).integrable_comp_of_integrable (leadtime_integrable P c))).pos_part)
    (holding_integrable P c S (t+c.L))
  intro ω
  dsimp only [Pi.sub_apply, Function.comp_apply]
  apply max_le _ (NNReal.coe_nonneg _)
  have hh := window_balance c S ω t
  have hn : 0 ≤ ∑ i ∈ Finset.range (c.L+1),
      (lostSales c (cbsRun c S S ω (t+i)) (ω.1 (t+i)) : ℝ) := by positivity
  linarith

lemma loss_block_lower (P : DemandLaw) (c : Parameters) (S : ℝ≥0) (t : ℕ) :
    expectedShortfall (leadTimeLaw P c.L) S ≤
      ∑ i ∈ Finset.range (c.L+1),
        ∫ ω : Sample, (lostSales c (cbsRun c S S ω (t+i)) (ω.1 (t+i)) : ℝ) ∂sampleLaw P := by
  rw [← window_shortfall_integral P c S t, ← integral_finsetSum _ (fun i _ => loss_integrable P c S S (t+i))]
  apply integral_mono
    ((((window_mp P c t).integrable_comp_of_integrable (leadtime_integrable P c)).sub
      (integrable_const (S : ℝ))).pos_part)
    (integrable_finsetSum _ (fun i _ => loss_integrable P c S S (t+i)))
  intro ω
  dsimp only [Pi.sub_apply, Function.comp_apply]
  apply max_le _ (by positivity)
  have hh := window_balance c S ω t
  have hn := NNReal.coe_nonneg (cbsRun c S S ω (t+c.L+1)).1
  linarith

lemma loss_upper (P : DemandLaw) (c : Parameters) (S : ℝ≥0) (t : ℕ) :
    (∫ ω : Sample, (lostSales c (cbsRun c S S ω (t+c.L)) (ω.1 (t+c.L)) : ℝ) ∂sampleLaw P) ≤
      expectedShortfall (leadTimeLaw P c.L) S := by
  rw [← window_shortfall_integral P c S t]
  apply integral_mono (loss_integrable P c S S (t+c.L))
    ((((window_mp P c t).integrable_comp_of_integrable (leadtime_integrable P c)).sub
      (integrable_const (S : ℝ))).pos_part)
  intro ω
  dsimp only
  rw [bs_loss_recursion]
  have hn : 0 ≤ ∑ i ∈ Finset.range c.L,
      (lostSales c (cbsRun c S S ω (t+i)) (ω.1 (t+i)) : ℝ) := by positivity
  simpa only [window, NNReal.coe_sum, Pi.sub_apply, Function.comp_apply] using
    (max_le_max (sub_le_self
      ((∑ i ∈ Finset.range (c.L+1), (ω.1 (t+i) : ℝ)) - (S : ℝ)) hn)
      (le_refl (0 : ℝ)))

def costMean (P : DemandLaw) (c : Parameters) (S : ℝ≥0) (t : ℕ) : ℝ :=
  c.h * (∫ ω : Sample, ((cbsRun c S S ω (t+1)).1 : ℝ) ∂sampleLaw P) +
    c.p * (∫ ω : Sample, (lostSales c (cbsRun c S S ω t) (ω.1 t) : ℝ) ∂sampleLaw P)

lemma costMean_nonneg (P : DemandLaw) (c : Parameters) (S : ℝ≥0) (t : ℕ) :
    0 ≤ costMean P c S t := by
  exact add_nonneg (mul_nonneg c.holding_pos.le (integral_nonneg fun _ => NNReal.coe_nonneg _))
    (mul_nonneg c.penalty_pos.le (loss_integral_nonneg P c S S t))

lemma costMean_lintegral (P : DemandLaw) (c : Parameters) (S : ℝ≥0) (t : ℕ) :
    (∫⁻ ω, periodCost c (cbsRun c S S ω t) (ω.1 t) ∂sampleLaw P) =
      ENNReal.ofReal (costMean P c S t) := by
  let H (ω : Sample) : ℝ := (cbsRun c S S ω (t+1)).1
  let Y (ω : Sample) : ℝ := lostSales c (cbsRun c S S ω t) (ω.1 t)
  let C (ω : Sample) : ℝ := c.h * H ω + c.p * Y ω
  have hH : Integrable H (sampleLaw P) := holding_integrable P c S t
  have hY : Integrable Y (sampleLaw P) := loss_integrable P c S S t
  have hC : Integrable C (sampleLaw P) := (hH.const_mul _).add (hY.const_mul _)
  have hC0 (ω : Sample) : 0 ≤ C ω :=
    add_nonneg (mul_nonneg c.holding_pos.le (NNReal.coe_nonneg _))
      (mul_nonneg c.penalty_pos.le (NNReal.coe_nonneg _))
  have hp (ω : Sample) : periodCost c (cbsRun c S S ω t) (ω.1 t) = ENNReal.ofReal (C ω) := by
    have := c.holding_pos
    have := c.penalty_pos
    dsimp [C, H, Y, periodCost, cbsRun, step]
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul c.holding_pos.le, ENNReal.ofReal_mul c.penalty_pos.le]
    simp
  simp_rw [hp]
  rw [← ofReal_integral_eq_lintegral_ofReal hC (Eventually.of_forall hC0)]
  congr 1
  exact (integral_add (hH.const_mul _) (hY.const_mul _)).trans
    (by simp only [integral_const_mul, costMean, H, Y])

lemma costMean_block_lower (P : DemandLaw) (c : Parameters) (S : ℝ≥0) (t : ℕ) (ht : c.L ≤ t) :
    ((c.L : ℝ)+1) * c.h * expectedHolding (leadTimeLaw P c.L) S +
      c.p * expectedShortfall (leadTimeLaw P c.L) S ≤
      ∑ i ∈ Finset.range (c.L+1), costMean P c S (t+i) := by
  have hH : ((c.L : ℝ)+1) * expectedHolding (leadTimeLaw P c.L) S ≤
      ∑ i ∈ Finset.range (c.L+1),
        ∫ ω : Sample, ((cbsRun c S S ω (t+i+1)).1 : ℝ) ∂sampleLaw P := by
    calc
      _ = ∑ _i ∈ Finset.range (c.L+1), expectedHolding (leadTimeLaw P c.L) S := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        have hi := holding_lower P c S (t+i-c.L)
        simpa only [Nat.sub_add_cancel (show c.L ≤ t+i by omega)] using hi
  have hY := loss_block_lower P c S t
  unfold costMean
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hH c.holding_pos.le,
    mul_le_mul_of_nonneg_left hY c.penalty_pos.le]

lemma cost_lower (P : DemandLaw) (c : Parameters) (S : ℝ≥0) :
    ENNReal.ofReal (backorderCost (leadTimeLaw P c.L) c.h (c.p / ((c.L : ℝ)+1)) S) ≤
      baseStockCost P c S := by
  let H := expectedHolding (leadTimeLaw P c.L) S
  let B := expectedShortfall (leadTimeLaw P c.L) S
  have hH : 0 ≤ H := integral_nonneg fun _ => le_max_right _ _
  have hB : 0 ≤ B := integral_nonneg fun _ => le_max_right _ _
  have hbound := ennreal_average_ge_of_block_bound (costMean P c S) (c.L+1) c.L (by omega)
    (((c.L : ℝ)+1)*c.h*H+c.p*B)
    (by have := c.holding_pos; have := c.penalty_pos; positivity)
    (costMean_nonneg P c S) (costMean_block_lower P c S)
  unfold baseStockCost cbsCost averageCost
  simp_rw [costMean_lintegral]
  convert hbound using 1
  congr 1
  dsimp [backorderCost, H, B]
  push_cast
  field_simp

lemma average_loss_upper (P : DemandLaw) (c : Parameters) (S : ℝ≥0) :
    baseStockAverageLoss P c S ≤ ENNReal.ofReal (expectedShortfall (leadTimeLaw P c.L) S) := by
  let a : ℕ → ℝ := fun t => ∫ ω : Sample,
    (lostSales c (cbsRun c S S ω t) (ω.1 t) : ℝ) ∂sampleLaw P
  have ha0 : ∀ t, 0 ≤ a t := fun t => loss_integral_nonneg P c S S t
  have ha : ∀ t, a t ≤ mean P := fun t => loss_integral_le_mean P c S S t
  have hB : 0 ≤ expectedShortfall (leadTimeLaw P c.L) S :=
    integral_nonneg fun _ => le_max_right _ _
  have hb : ∀ t, c.L ≤ t → ∑ i ∈ Finset.range 1, a (t+i) ≤
      expectedShortfall (leadTimeLaw P c.L) S := by
    intro t ht
    simpa only [Finset.sum_range_one, Nat.add_zero, a, Nat.sub_add_cancel ht] using
      loss_upper P c S (t-c.L)
  have hl := ennreal_average_le_of_block_bound a 1 c.L (by omega)
    (expectedShortfall (leadTimeLaw P c.L) S) (mean P) hB
    P.positiveMean.le ha0 ha hb
  unfold baseStockAverageLoss averageCost
  simp_rw [lintegral_loss_eq]
  simpa only [Nat.cast_one, div_one, a] using hl

lemma leadtime_mean (P : DemandLaw) (c : Parameters) :
    (∫ d : ℝ≥0, (d : ℝ) ∂leadTimeLaw P c.L) = ((c.L : ℝ)+1)*mean P := by
  have hm := window_mp P c 0
  rw [← hm.map_eq, integral_map hm.aemeasurable (by fun_prop)]
  simp only [window, NNReal.coe_sum]
  rw [integral_finsetSum _ (fun i _ => demand_integrable P (0+i))]
  simp only [demand_integral, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]

lemma holding_shortfall_balance (P : DemandLaw) (c : Parameters) (S : ℝ≥0) :
    expectedHolding (leadTimeLaw P c.L) S =
      (S : ℝ) - ((c.L : ℝ)+1)*mean P + expectedShortfall (leadTimeLaw P c.L) S := by
  have hprob : IsProbabilityMeasure (leadTimeLaw P c.L) := by
    unfold leadTimeLaw
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have := hprob
  have hd := leadtime_integrable P c
  have hp : Integrable (fun d : ℝ≥0 => max ((d : ℝ) - (S : ℝ)) 0) (leadTimeLaw P c.L) :=
    (hd.sub (integrable_const (S : ℝ))).pos_part
  have hm : Integrable (fun d : ℝ≥0 => max ((S : ℝ) - (d : ℝ)) 0) (leadTimeLaw P c.L) :=
    ((integrable_const (S : ℝ)).sub hd).pos_part
  have hparts (d : ℝ≥0) :
      max ((d : ℝ) - (S : ℝ)) 0 - max ((S : ℝ) - (d : ℝ)) 0 = (d : ℝ) - (S : ℝ) := by
    simpa only [neg_sub] using max_zero_sub_max_neg_zero_eq_self ((d : ℝ) - (S : ℝ))
  have hb : expectedShortfall (leadTimeLaw P c.L) S - expectedHolding (leadTimeLaw P c.L) S =
      ((c.L : ℝ)+1)*mean P - (S : ℝ) := by
    unfold expectedShortfall expectedHolding
    rw [← integral_sub hp hm]
    simp_rw [hparts]
    rw [integral_sub hd (integrable_const _), leadtime_mean]
    simp
  linarith

lemma cost_upper (P : DemandLaw) (c : Parameters) (S : ℝ≥0) :
    baseStockCost P c S ≤
      ENNReal.ofReal (backorderCost (leadTimeLaw P c.L) c.h (c.p+(c.L : ℝ)*c.h) S) := by
  have hh := CappedBaseStock.base_stock_cost_of_loss_bound P c S
    (expectedShortfall (leadTimeLaw P c.L) S)
    (integral_nonneg fun _ => le_max_right _ _) (average_loss_upper P c S)
  convert hh using 1
  congr 1
  unfold backorderCost
  rw [holding_shortfall_balance]
  ring

end LostSalesBracket

open LostSalesOrderUpTo.Asymptotic

theorem solution (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (S : ℝ≥0) :
    ENNReal.ofReal (backorderCost (leadTimeLaw P c.L) c.h
        (c.p / ((c.L : ℝ) + 1)) S) ≤
      CappedBaseStock.baseStockCost P c S ∧
    CappedBaseStock.baseStockCost P c S ≤
      ENNReal.ofReal (backorderCost (leadTimeLaw P c.L) c.h
        (c.p + (c.L : ℝ) * c.h) S) := by
  exact ⟨LostSalesBracket.cost_lower P c S, LostSalesBracket.cost_upper P c S⟩
