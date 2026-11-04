-- Prove2me | solution 1 for LostSalesOrderUpTo.Asymptotic.lemma9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T04:50:03.92875+00:00
-- url     : https://prove2.me/submissions/c5f3ea2c-d20c-4dcf-98b2-b6b36d36b517

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Coupling

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesOrderUpTo.Asymptotic

private def pipePrefix {L : ℕ} (m : ℕ) (hm : m ≤ L) (p : Fin L → ℝ) : ℝ :=
  ∑ i : Fin m, p ⟨i.val, lt_of_lt_of_le i.isLt hm⟩

private lemma pipePrefix_succ {L m : ℕ} (hm : m + 1 ≤ L) (p : Fin L → ℝ) :
    pipePrefix (m + 1) hm p = p ⟨0, by omega⟩ +
      ∑ i : Fin m, p ⟨i.val + 1, by omega⟩ := by
  exact Fin.sum_univ_succ _

private lemma pipePrefix_shift {L m : ℕ} (hm : m + 1 ≤ L)
    (p p' : Fin L → ℝ)
    (hp : ∀ i : Fin L, ∀ h : i.val + 1 < L, p' i = p ⟨i.val + 1, h⟩) :
    p ⟨0, by omega⟩ + pipePrefix m (by omega) p' = pipePrefix (m + 1) hm p := by
  rw [pipePrefix_succ]
  unfold pipePrefix
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply hp

private lemma pipePrefix_telescope {L : ℕ} (hL : 0 < L)
    (x e : ℕ → ℝ) (p : ℕ → Fin L → ℝ)
    (hx : ∀ t, x (t + 1) = x t + p t ⟨0, hL⟩ - e t)
    (hp : ∀ t (i : Fin L) (h : i.val + 1 < L),
      p (t + 1) i = p t ⟨i.val + 1, h⟩)
    (t k m : ℕ) (hm : m + k ≤ L) :
    x (t + k) + pipePrefix m (by omega) (p (t + k)) =
      x t + pipePrefix (m + k) hm (p t) - ∑ j ∈ Finset.Ico t (t + k), e j := by
  induction k generalizing m with
  | zero => simp [pipePrefix]
  | succ k ih =>
    have hm' : m + 1 + k ≤ L := by omega
    have hs := pipePrefix_shift (L := L) (m := m) (by omega)
      (p (t + k)) (p (t + k + 1)) (hp (t + k))
    have hi := ih (m + 1) hm'
    rw [Nat.add_succ, hx]
    rw [Finset.sum_Ico_succ_top (by omega : t ≤ t + k)]
    have heq : m + 1 + k = m + (k + 1) := by omega
    simp only [heq] at hi
    linarith

private lemma pipePrefix_all {L : ℕ} (p : Fin L → ℝ) :
    pipePrefix L le_rfl p = ∑ i : Fin L, p i := by
  rfl

private lemma pipePrefix_one {L : ℕ} (hL : 0 < L) (p : Fin L → ℝ) :
    pipePrefix 1 hL p = p ⟨0, hL⟩ := by
  simp [pipePrefix]

private lemma pipeline_total_shift {M : Type*} [AddCommMonoid M]
    {L : ℕ} (hL : 0 < L) (p : Fin L → M) (q : M) :
    p ⟨0, hL⟩ +
      (∑ i : Fin L, if h : i.val + 1 < L then p ⟨i.val + 1, h⟩ else q) =
      (∑ i : Fin L, p i) + q := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL)
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ p]
  simp only [Fin.val_last, lt_self_iff_false, dite_false]
  have hs : (∑ i : Fin n, if h : i.castSucc.val + 1 < n + 1 then
      p ⟨i.castSucc.val + 1, h⟩ else q) = ∑ i : Fin n, p i.succ := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.val_castSucc, Nat.add_lt_add_iff_right, i.isLt, dite_true]
    rfl
  rw [hs]
  change p 0 + ((∑ i : Fin n, p i.succ) + q) =
    (p 0 + ∑ i : Fin n, p i.succ) + q
  exact (add_assoc _ _ _).symm

private lemma pipeline_horizon {L : ℕ} (hL : 0 < L)
    (x e : ℕ → ℝ) (p : ℕ → Fin L → ℝ)
    (hx : ∀ t, x (t + 1) = x t + p t ⟨0, hL⟩ - e t)
    (hp : ∀ t (i : Fin L) (h : i.val + 1 < L),
      p (t + 1) i = p t ⟨i.val + 1, h⟩)
    (t : ℕ) :
    x (t + L) + p (t + L) ⟨0, hL⟩ =
      x (t + 1) + (∑ i : Fin L, p (t + 1) i) -
        ∑ j ∈ Finset.Ico (t + 1) (t + L), e j := by
  have h := pipePrefix_telescope hL x e p hx hp (t + 1) (L - 1) 1 (by omega)
  have ht : t + 1 + (L - 1) = t + L := by omega
  have hm : 1 + (L - 1) = L := by omega
  simpa only [ht, hm, pipePrefix_one, pipePrefix_all] using h

private lemma pipeline_horizon_saturated {L : ℕ} (hL : 0 < L)
    (x e : ℕ → ℝ) (p : ℕ → Fin L → ℝ) (S : ℝ)
    (hx : ∀ t, x (t + 1) = x t + p t ⟨0, hL⟩ - e t)
    (hp : ∀ t (i : Fin L) (h : i.val + 1 < L),
      p (t + 1) i = p t ⟨i.val + 1, h⟩)
    (hs : ∀ t, x (t + 1) + (∑ i : Fin L, p (t + 1) i) = S - e t)
    (t : ℕ) :
    x (t + L) + p (t + L) ⟨0, hL⟩ =
      S - ∑ j ∈ Finset.Ico t (t + L), e j := by
  rw [pipeline_horizon hL x e p hx hp, hs]
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : t < t + L) e]
  ring

private lemma positive_part_balance (a d : ℝ) :
    max (a - d) 0 = a - d + max (d - a) 0 := by
  by_cases h : a ≤ d
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring
  · have h' := le_of_not_ge h
    rw [max_eq_left (sub_nonneg.mpr h'), max_eq_right (sub_nonpos.mpr h')]
    ring

private def lostPosition (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) (t : ℕ) : ℝ :=
  ((CappedBaseStock.cbsRun c S S ω t).1 : ℝ) +
    ∑ i : Fin c.L, ((CappedBaseStock.cbsRun c S S ω t).2 i : ℝ)

private def backPosition (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) (t : ℕ) : ℝ :=
  (backorderRun c S ω t).1 + ∑ i : Fin c.L, ((backorderRun c S ω t).2 i : ℝ)

private lemma lost_order_fills (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (s : CappedBaseStock.State c.L)
    (hs : (s.1 : ℝ) + ∑ i : Fin c.L, (s.2 i : ℝ) ≤ S) :
    (CappedBaseStock.cbsOrder c.L S S s : ℝ) =
      (S : ℝ) - ((s.1 : ℝ) + ∑ i : Fin c.L, (s.2 i : ℝ)) := by
  simp only [CappedBaseStock.cbsOrder, min_eq_left (tsub_le_self),
    NNReal.coe_sub_def, NNReal.coe_add, NNReal.coe_sum]
  exact max_eq_left (sub_nonneg.mpr hs)

private lemma back_order_fills (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (s : BackorderState c.L)
    (hs : s.1 + ∑ i : Fin c.L, (s.2 i : ℝ) ≤ S) :
    (backorderOrder c S s : ℝ) =
      (S : ℝ) - (s.1 + ∑ i : Fin c.L, (s.2 i : ℝ)) := by
  exact Real.coe_toNNReal _ (sub_nonneg.mpr hs)

private lemma lost_step_balance (c : CappedBaseStock.Parameters)
    (s : CappedBaseStock.State c.L) (q d : ℝ≥0) :
    ((CappedBaseStock.step c s q d).1 : ℝ) =
      (s.1 : ℝ) + (CappedBaseStock.arrival c s : ℝ) - (d : ℝ) +
        (CappedBaseStock.lostSales c s d : ℝ) := by
  simp only [CappedBaseStock.step, CappedBaseStock.lostSales, NNReal.coe_sub_def,
    NNReal.coe_add]
  exact positive_part_balance _ _

private lemma lost_step_pipeline (c : CappedBaseStock.Parameters)
    (s : CappedBaseStock.State c.L) (q d : ℝ≥0) :
    (CappedBaseStock.arrival c s : ℝ) +
        ∑ i : Fin c.L, ((CappedBaseStock.step c s q d).2 i : ℝ) =
      (∑ i : Fin c.L, (s.2 i : ℝ)) + (q : ℝ) := by
  have h := pipeline_total_shift
    (lt_of_lt_of_le Nat.zero_lt_one c.leadTime_pos) s.2 q
  have hr := congrArg (fun a : ℝ≥0 ↦ (a : ℝ)) h
  simpa only [NNReal.coe_add, NNReal.coe_sum,
    CappedBaseStock.arrival, CappedBaseStock.step] using hr

private lemma back_step_pipeline (c : CappedBaseStock.Parameters)
    (s : BackorderState c.L) (q d : ℝ≥0) :
    (backorderArrival c s : ℝ) +
        ∑ i : Fin c.L, ((backorderStep c s q d).2 i : ℝ) =
      (∑ i : Fin c.L, (s.2 i : ℝ)) + (q : ℝ) := by
  have h := pipeline_total_shift
    (lt_of_lt_of_le Nat.zero_lt_one c.leadTime_pos) s.2 q
  have hr := congrArg (fun a : ℝ≥0 ↦ (a : ℝ)) h
  simpa only [NNReal.coe_add, NNReal.coe_sum, backorderArrival, backorderStep] using hr

private lemma lost_position_step (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) (t : ℕ) (ht : lostPosition c S ω t ≤ S) :
    lostPosition c S ω (t + 1) =
      (S : ℝ) - ((ω.1 t : ℝ) - (lostUnits c S ω t : ℝ)) := by
  let s := CappedBaseStock.cbsRun c S S ω t
  let q := CappedBaseStock.cbsOrder c.L S S s
  have hq := lost_order_fills c S s ht
  have hp := lost_step_pipeline c s q (ω.1 t)
  have hi := lost_step_balance c s q (ω.1 t)
  change ((CappedBaseStock.step c s q (ω.1 t)).1 : ℝ) +
      (∑ i : Fin c.L, ((CappedBaseStock.step c s q (ω.1 t)).2 i : ℝ)) =
    (S : ℝ) - ((ω.1 t : ℝ) - (CappedBaseStock.lostSales c s (ω.1 t) : ℝ))
  change (q : ℝ) = _ at hq
  linarith only [hq, hp, hi]

private lemma back_position_step (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) (t : ℕ) (ht : backPosition c S ω t ≤ S) :
    backPosition c S ω (t + 1) = (S : ℝ) - (ω.1 t : ℝ) := by
  let s := backorderRun c S ω t
  let q := backorderOrder c S s
  have hq := back_order_fills c S s ht
  have hp := back_step_pipeline c s q (ω.1 t)
  change s.1 + (backorderArrival c s : ℝ) - (ω.1 t : ℝ) +
      (∑ i : Fin c.L, ((backorderStep c s q (ω.1 t)).2 i : ℝ)) =
    (S : ℝ) - (ω.1 t : ℝ)
  change (q : ℝ) = _ at hq
  linarith only [hq, hp]

private lemma positions_bounded (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) (t : ℕ) :
    lostPosition c S ω t ≤ S ∧ backPosition c S ω t ≤ S := by
  induction t with
  | zero =>
    simp [lostPosition, backPosition, CappedBaseStock.cbsRun,
      CappedBaseStock.initialState, backorderRun, backorderInitialState]
  | succ t ih =>
    have hl := lost_position_step c S ω t ih.1
    have hb := back_position_step c S ω t ih.2
    have hle : lostUnits c S ω t ≤ ω.1 t := tsub_le_self
    have hle' : (lostUnits c S ω t : ℝ) ≤ (ω.1 t : ℝ) :=
      NNReal.coe_le_coe.mpr hle
    have hd := NNReal.coe_nonneg (ω.1 t)
    constructor
    · linarith only [hl, hle']
    · linarith only [hb, hd]

private lemma lost_inventory_formula (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) (u : ℕ) :
    (lostInventory c S ω (u + c.L) : ℝ) =
      (S : ℝ) - ∑ i ∈ Finset.Ico u (u + c.L),
        ((ω.1 i : ℝ) - (lostUnits c S ω i : ℝ)) := by
  change ((CappedBaseStock.cbsRun c S S ω (u + c.L)).1 : ℝ) +
      ((CappedBaseStock.cbsRun c S S ω (u + c.L)).2 ⟨0, _⟩ : ℝ) = _
  refine pipeline_horizon_saturated
    (lt_of_lt_of_le Nat.zero_lt_one c.leadTime_pos)
    (fun t ↦ ((CappedBaseStock.cbsRun c S S ω t).1 : ℝ))
    (fun t ↦ (ω.1 t : ℝ) - (lostUnits c S ω t : ℝ))
    (fun t i ↦ ((CappedBaseStock.cbsRun c S S ω t).2 i : ℝ))
    (S : ℝ) ?_ ?_ ?_ u
  · intro t
    change ((CappedBaseStock.step c (CappedBaseStock.cbsRun c S S ω t)
      (CappedBaseStock.cbsOrder c.L S S (CappedBaseStock.cbsRun c S S ω t))
      (ω.1 t)).1 : ℝ) = _
    rw [lost_step_balance]
    simp only [lostUnits, CappedBaseStock.arrival]
    ring
  · intro t i hi
    simp only [CappedBaseStock.cbsRun, CappedBaseStock.step, dif_pos hi]
  · intro t
    exact lost_position_step c S ω t (positions_bounded c S ω t).1

private lemma back_inventory_formula (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) (u : ℕ) :
    backorderInventory c S ω (u + c.L) =
      (S : ℝ) - ∑ i ∈ Finset.Ico u (u + c.L), (ω.1 i : ℝ) := by
  change (backorderRun c S ω (u + c.L)).1 +
      ((backorderRun c S ω (u + c.L)).2 ⟨0, _⟩ : ℝ) = _
  refine pipeline_horizon_saturated
    (lt_of_lt_of_le Nat.zero_lt_one c.leadTime_pos)
    (fun t ↦ (backorderRun c S ω t).1) (fun t ↦ (ω.1 t : ℝ))
    (fun t i ↦ ((backorderRun c S ω t).2 i : ℝ)) (S : ℝ) ?_ ?_ ?_ u
  · intro t
    rfl
  · intro t i hi
    simp only [backorderRun, backorderStep, dif_pos hi]
  · intro t
    exact back_position_step c S ω t (positions_bounded c S ω t).2

private lemma inventory_gap (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) (t : ℕ) (ht : c.L ≤ t) :
    (lostInventory c S ω t : ℝ) = backorderInventory c S ω t +
      ∑ i ∈ Finset.Ico (t - c.L) t, (lostUnits c S ω i : ℝ) := by
  have hl := lost_inventory_formula c S ω (t - c.L)
  have hb := back_inventory_formula c S ω (t - c.L)
  rw [Nat.sub_add_cancel ht, Finset.sum_sub_distrib] at hl
  rw [Nat.sub_add_cancel ht] at hb
  linarith only [hl, hb]

end LostSalesOrderUpTo.Asymptotic

open LostSalesOrderUpTo.Asymptotic

/-- The two systems differ exactly by the lost sales during the preceding lead time. -/
theorem solution (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) (t : ℕ) (ht : c.L ≤ t) :
    backorderInventory c S ω t ≤ (lostInventory c S ω t : ℝ) ∧
    backorderUnits c S ω t -
      ∑ i ∈ Finset.Ico (t - c.L) t, (lostUnits c S ω i : ℝ) ≤
      (lostUnits c S ω t : ℝ) ∧
    (lostUnits c S ω t : ℝ) ≤ backorderUnits c S ω t := by
  have hgap := inventory_gap c S ω t ht
  have hnonneg : 0 ≤ ∑ i ∈ Finset.Ico (t - c.L) t, (lostUnits c S ω i : ℝ) :=
    Finset.sum_nonneg (fun i _ ↦ NNReal.coe_nonneg _)
  have hinv : backorderInventory c S ω t ≤ (lostInventory c S ω t : ℝ) := by
    linarith only [hgap, hnonneg]
  have hloss : (lostUnits c S ω t : ℝ) =
      max ((ω.1 t : ℝ) - (lostInventory c S ω t : ℝ)) 0 := by
    simp only [lostUnits, lostInventory, CappedBaseStock.lostSales, NNReal.coe_sub_def]
  refine ⟨hinv, ?_, ?_⟩
  · apply (sub_le_iff_le_add).2
    unfold backorderUnits
    apply max_le
    · have h := le_max_left ((ω.1 t : ℝ) - (lostInventory c S ω t : ℝ)) 0
      rw [← hloss] at h
      linarith only [hgap, h]
    · exact add_nonneg (NNReal.coe_nonneg _) hnonneg
  · rw [hloss, backorderUnits]
    exact max_le_max (sub_le_sub_left hinv _) le_rfl
