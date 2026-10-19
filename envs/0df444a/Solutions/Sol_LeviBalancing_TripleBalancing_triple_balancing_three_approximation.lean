-- Prove2me | solution 1 for LeviBalancing.TripleBalancing.triple_balancing_three_approximation
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-18T08:18:16.622364+00:00
-- url     : https://prove2.me/submissions/be15d13c-8cd5-426a-b906-8c4f83b6ad25

-- Licensed under Apache 2.0. Complete triple-balancing three-approximation theorem.
import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Model
import Definitions.Def_LeviBalancing_TripleBalancing_Policy
import Definitions.Def_LeviBalancing_TripleBalancing_TBPolicy

open MeasureTheory ProbabilityTheory


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
open scoped ENNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

def holdCost (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  M.h t * max (levelAfter M Q t ω - M.D t ω) 0

def backCost (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  M.p t * max (M.D t ω - levelAfter M Q t ω) 0

def setupCost (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if 0 < Q t ω then M.K else 0

def intervalHolding (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ)
    (s : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Icc 1 M.T, if lastOrder TB (t+1) ω = s then holdCost M Q t ω else 0

def intervalBacklog (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ)
    (s : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Icc 1 M.T, if lastOrder TB t ω = s then backCost M Q t ω else 0

def intervalSetup (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ)
    (s : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Icc 1 M.T, if lastOrder TB t ω = s then setupCost M Q t ω else 0

def intervalCost (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ)
    (s : ℕ) (ω : Ω) : ℝ :=
  intervalHolding M TB Q s ω + intervalBacklog M TB Q s ω + intervalSetup M TB Q s ω

def nextFlag (M : LotSizingModel Ω) (TB : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Icc 1 M.T, if lastOrder TB t ω = s ∧ 0 < TB t ω then 1 else 0

def startEvent (TB : ℕ → Ω → ℝ) (s : ℕ) : Set Ω := {ω | 0 < TB s ω}

def highEvent (M : LotSizingModel Ω) (TB P : ℕ → Ω → ℝ) (s : ℕ) : Set Ω :=
  {ω | levelAfter M TB s ω ≤ levelAfter M P s ω}

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem lastOrder_lt (Q : ℕ → Ω → ℝ) (ω : Ω) {t : ℕ} (ht : 0 < t) :
    lastOrder Q t ω < t := by
  classical
  apply (Finset.sup_lt_iff ht).2
  intro j hj
  exact (mem_Ico.mp (mem_filter.mp hj).1).2

omit [MeasurableSpace Ω] in
theorem lastOrder_le (Q : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) :
    lastOrder Q (t+1) ω ≤ t := by
  exact Nat.le_of_lt_succ (lastOrder_lt Q ω (Nat.zero_lt_succ t))

omit [MeasurableSpace Ω] in
theorem order_le_last (Q : ℕ → Ω → ℝ) (ω : Ω) {j t : ℕ}
    (hj : 1 ≤ j) (hjt : j < t) (hq : 0 < Q j ω) : j ≤ lastOrder Q t ω := by
  classical
  exact Finset.le_sup (f := id) (s := (Ico 1 t).filter (fun j => 0 < Q j ω))
    (mem_filter.mpr ⟨mem_Ico.mpr ⟨hj,hjt⟩,hq⟩)

omit [MeasurableSpace Ω] in
theorem lastOrder_succ (Q : ℕ → Ω → ℝ) (ω : Ω) {t : ℕ} (ht : 1 ≤ t) :
    lastOrder Q (t+1) ω = if 0 < Q t ω then t else lastOrder Q t ω := by
  classical
  unfold lastOrder
  rw [Nat.Ico_succ_right_eq_insert_Ico ht, filter_insert]
  split_ifs with h
  · rw [sup_insert]
    exact max_eq_left (Nat.le_of_lt (lastOrder_lt Q ω ht))
  · rfl

theorem no_order_after_last (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ)
    (hQ : IsFeasiblePolicy M Q) (ω : Ω) {j t : ℕ}
    (hj : 1 ≤ j) (hjt : j < t) (hl : lastOrder Q t ω < j) : Q j ω = 0 := by
  have hn : ¬0 < Q j ω := fun h => (not_le_of_gt hl) (order_le_last Q ω hj hjt h)
  exact le_antisymm (le_of_not_gt hn) (hQ.1 j ω)

theorem level_step (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (ω : Ω)
    {t : ℕ} (ht : 1 ≤ t) :
    levelBefore M Q (t+1) ω = levelAfter M Q t ω - M.D t ω := by
  unfold levelAfter levelBefore
  rw [sum_Ico_succ_top ht]
  ring

theorem hold_nonneg (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ holdCost M Q t ω := mul_nonneg (M.h_nonneg t) (le_max_right _ _)

theorem back_nonneg (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ backCost M Q t ω := mul_nonneg (M.p_nonneg t) (le_max_right _ _)

theorem setup_nonneg (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ setupCost M Q t ω := by
  unfold setupCost
  split_ifs
  · exact M.K_nonneg
  · rfl

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open Finset
open LeviBalancing.TripleBalancing

variable {Ω : Type*}

theorem lastOrder_mono (Q : ℕ → Ω → ℝ) (ω : Ω) : Monotone (fun t => lastOrder Q t ω) := by
  classical
  intro a b hab
  apply Finset.sup_le
  intro j hj
  exact order_le_last Q ω (mem_Ico.mp (mem_filter.mp hj).1).1
    (lt_of_lt_of_le (mem_Ico.mp (mem_filter.mp hj).1).2 hab) (mem_filter.mp hj).2

theorem lastOrder_positive (Q : ℕ → Ω → ℝ) (ω : Ω) {t : ℕ}
    (h : 0 < lastOrder Q t ω) : 0 < Q (lastOrder Q t ω) ω := by
  classical
  have hn : ((Ico 1 t).filter (fun j => 0 < Q j ω)).Nonempty := by
    by_contra he
    have := Finset.not_nonempty_iff_eq_empty.mp he
    simp [lastOrder, this] at h
  have hm := Finset.sup_mem_of_nonempty (f := id) hn
  obtain ⟨j,hj,hjv⟩ := hm
  simp only [id_eq] at hjv
  change j = lastOrder Q t ω at hjv
  rw [← hjv]
  exact (mem_filter.mp hj).2

theorem lastOrder_eq_of_gap (Q : ℕ → Ω → ℝ) (ω : Ω) {s t : ℕ}
    (hs : 1 ≤ s) (hst : s ≤ t) (hp : 0 < Q s ω)
    (hg : ∀ j, s < j → j ≤ t → ¬0 < Q j ω) : lastOrder Q (t+1) ω = s := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    have hjt := (mem_Ico.mp (mem_filter.mp hj).1).2
    by_contra h
    exact hg j (lt_of_not_ge h) (by omega) (mem_filter.mp hj).2
  · exact order_le_last Q ω hs (by omega) hp

theorem lastOrder_zero_of_gap (Q : ℕ → Ω → ℝ) (ω : Ω) {t : ℕ}
    (hg : ∀ j ∈ Ico 1 t, ¬0 < Q j ω) : lastOrder Q t ω = 0 := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    exact (hg j (mem_filter.mp hj).1 (mem_filter.mp hj).2).elim
  · exact Nat.zero_le _

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing

variable {Ω : Type*} [MeasurableSpace Ω]

theorem level_difference (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (ω : Ω)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    levelBefore M Q b ω = levelBefore M Q a ω + ∑ j ∈ Ico a b, (Q j ω - M.D j ω) := by
  unfold levelBefore
  rw [← sum_Ico_consecutive (fun j => Q j ω - M.D j ω) ha hab]
  ring

theorem level_no_orders (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (ω : Ω)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hq : ∀ j ∈ Ico a b, Q j ω = 0) :
    levelBefore M Q b ω = levelBefore M Q a ω - ∑ j ∈ Ico a b, M.D j ω := by
  rw [level_difference M Q ω ha hab]
  have hs : (∑ j ∈ Ico a b, (Q j ω - M.D j ω)) = -∑ j ∈ Ico a b, M.D j ω := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl (fun j hj => by rw [hq j hj, zero_sub])
  rw [hs]
  ring

theorem cumulative_gap (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (ω : Ω)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hq : ∀ j ∈ Ico a b, Q j ω = 0) :
    (∑ j ∈ Icc a b, M.D j ω) - levelBefore M Q a ω =
      M.D b ω - levelBefore M Q b ω := by
  rw [level_no_orders M Q ω ha hab hq, ← Ico_add_one_right_eq_Icc, sum_Ico_succ_top hab]
  ring

def preBack (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  M.p t * max (M.D t ω - levelBefore M Q t ω) 0

theorem accBacklog_eq (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ)
    (hQ : IsFeasiblePolicy M Q) (ω : Ω) (s : ℕ) :
    accBacklog M Q s ω =
      ∑ j ∈ Icc (lastOrder Q s ω+1) s, preBack M Q j ω := by
  unfold accBacklog preBack
  apply sum_congr rfl
  intro j hj
  rw [cumulative_gap M Q ω (by omega) (mem_Icc.mp hj).1]
  intro i hi
  apply no_order_after_last M Q hQ ω
  · exact le_trans (by omega) (mem_Ico.mp hi).1
  · exact lt_of_lt_of_le (mem_Ico.mp hi).2 (mem_Icc.mp hj).2
  · exact lt_of_lt_of_le (Nat.lt_succ_self _) (mem_Ico.mp hi).1

theorem preBack_eq_back (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (ω : Ω)
    (t : ℕ) (hq : Q t ω = 0) : preBack M Q t ω = backCost M Q t ω := by
  simp [preBack, backCost, levelAfter, hq]

theorem accBacklog_one (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (ω : Ω) :
    accBacklog M Q 1 ω = preBack M Q 1 ω := by
  simp [accBacklog, lastOrder, preBack, levelBefore]

theorem accBacklog_succ (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ)
    (hQ : IsFeasiblePolicy M Q) (ω : Ω) {s : ℕ} (hs : 1 ≤ s) :
    accBacklog M Q (s+1) ω =
      (if 0 < Q s ω then 0 else accBacklog M Q s ω) + preBack M Q (s+1) ω := by
  classical
  rw [accBacklog_eq M Q hQ, lastOrder_succ Q ω hs]
  split_ifs with h
  · simp
  · rw [← Ico_add_one_right_eq_Icc, sum_Ico_succ_top (by have := lastOrder_lt Q ω hs; omega)]
    rw [Ico_add_one_right_eq_Icc, ← accBacklog_eq M Q hQ]

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing

theorem assigned_sum {α : Type*} (S : Finset α) (N : ℕ) (a : α → ℕ)
    (v : α → ℝ) (ha : ∀ t ∈ S, a t ≤ N) :
    ∑ s ∈ range (N+1), ∑ t ∈ S, (if a t = s then v t else 0) = ∑ t ∈ S, v t := by
  classical
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  rw [sum_eq_single (a t)]
  · simp
  · intro b hb hba
    simp [Ne.symm hba]
  · intro hnot
    exact (hnot (mem_range.mpr (Nat.lt_succ_of_le (ha t ht)))).elim

variable {Ω : Type*} [MeasurableSpace Ω]

theorem interval_partition (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ) (ω : Ω) :
    ∑ s ∈ range (M.T+1), intervalCost M TB Q s ω = totalCost M Q ω := by
  have hh : ∀ t ∈ Icc 1 M.T, lastOrder TB (t+1) ω ≤ M.T := by
    intro t ht
    exact (lastOrder_le TB ω t).trans (mem_Icc.mp ht).2
  have hb : ∀ t ∈ Icc 1 M.T, lastOrder TB t ω ≤ M.T := by
    intro t ht
    exact (Nat.le_of_lt (lastOrder_lt TB ω (mem_Icc.mp ht).1)).trans (mem_Icc.mp ht).2
  simp only [intervalCost, sum_add_distrib, intervalHolding, intervalBacklog, intervalSetup]
  rw [assigned_sum _ _ _ _ hh, assigned_sum _ _ _ _ hb, assigned_sum _ _ _ _ hb]
  unfold totalCost periodCost holdCost backCost setupCost
  simp only [sum_add_distrib]
  ring

theorem interval_nonneg (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) :
    0 ≤ intervalCost M TB Q s ω := by
  unfold intervalCost intervalHolding intervalBacklog intervalSetup
  apply add_nonneg (add_nonneg ?_ ?_) ?_
  all_goals apply sum_nonneg; intro t ht; split_ifs
  · exact hold_nonneg M Q t ω
  · rfl
  · exact back_nonneg M Q t ω
  · rfl
  · exact setup_nonneg M Q t ω
  · rfl

theorem setup_eq_flag (M : LotSizingModel Ω) (TB : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) :
    intervalSetup M TB TB s ω = M.K * nextFlag M TB s ω := by
  classical
  unfold intervalSetup nextFlag setupCost
  rw [mul_sum]
  apply sum_congr rfl
  intro t ht
  by_cases h : lastOrder TB t ω = s <;> by_cases hq : 0 < TB t ω <;> simp [h,hq]

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem inactive_assignment (Q : ℕ → Ω → ℝ) (ω : Ω) {s t : ℕ}
    (hs : 0 < s) (hq : Q s ω = 0) : lastOrder Q t ω ≠ s := by
  intro he
  have hp := lastOrder_positive Q ω (t := t) (he.symm ▸ hs)
  rw [he,hq] at hp
  exact lt_irrefl _ hp

theorem inactive_interval (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ)
    (ω : Ω) {s : ℕ} (hs : 0 < s) (hq : TB s ω = 0) :
    intervalCost M TB Q s ω = 0 := by
  have h : ∀ t, lastOrder TB t ω ≠ s := fun t => inactive_assignment TB ω hs hq
  simp [intervalCost,intervalHolding,intervalBacklog,intervalSetup,h]

theorem inactive_flag (M : LotSizingModel Ω) (TB : ℕ → Ω → ℝ)
    (ω : Ω) {s : ℕ} (hs : 0 < s) (hq : TB s ω = 0) : nextFlag M TB s ω = 0 := by
  have h : ∀ t, lastOrder TB t ω ≠ s := fun t => inactive_assignment TB ω hs hq
  simp [nextFlag,h]

theorem nextFlag_le_one (M : LotSizingModel Ω) (TB : ℕ → Ω → ℝ)
    (s : ℕ) (ω : Ω) : nextFlag M TB s ω ≤ 1 := by
  classical
  let S := (Icc 1 M.T).filter (fun t => lastOrder TB t ω = s ∧ 0 < TB t ω)
  have hc : S.card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha,has,hap⟩ := mem_filter.mp ha
    obtain ⟨hb,hbs,hbp⟩ := mem_filter.mp hb
    rcases lt_trichotomy a b with hab | hab | hab
    · have h := order_le_last TB ω (mem_Icc.mp ha).1 hab hap
      have hl := lastOrder_lt TB ω (mem_Icc.mp ha).1
      omega
    · exact hab
    · have h := order_le_last TB ω (mem_Icc.mp hb).1 hab hbp
      have hl := lastOrder_lt TB ω (mem_Icc.mp hb).1
      omega
  have he : nextFlag M TB s ω = (S.card : ℝ) := by
    simp [nextFlag,S]
  rw [he]
  exact_mod_cast hc

theorem sum_nextFlag (M : LotSizingModel Ω) (TB : ℕ → Ω → ℝ) (ω : Ω) :
    ∑ s ∈ range (M.T+1), nextFlag M TB s ω = (numOrders M TB ω : ℝ) := by
  classical
  have hb : ∀ t ∈ Icc 1 M.T, lastOrder TB t ω ≤ M.T := by
    intro t ht
    exact (Nat.le_of_lt (lastOrder_lt TB ω (mem_Icc.mp ht).1)).trans (mem_Icc.mp ht).2
  have he : ∀ s, nextFlag M TB s ω =
      ∑ t ∈ Icc 1 M.T, if lastOrder TB t ω = s then (if 0 < TB t ω then (1:ℝ) else 0) else 0 := by
    intro s
    unfold nextFlag
    apply sum_congr rfl
    intro t ht
    split_ifs <;> simp_all
  simp_rw [he]
  rw [assigned_sum _ _ _ _ hb]
  simp [numOrders, sum_boole]

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω A B : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace A] [mB : MeasurableSpace B]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem conditional_pair_law {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (κ : @Kernel Ω B mΩ inferInstance) [IsMarkovKernel κ] {U : Ω → A} {V : Ω → B}
    (hU : Measurable[m] U) (hV : Measurable[mΩ] V)
    (hc : ∀ (C : Set B) (E : Set Ω), MeasurableSet C → MeasurableSet[m] E →
      μ (E ∩ V ⁻¹' C) = ∫⁻ ω in E, κ ω C ∂μ) :
    (@Measure.map Ω (A × B) mΩ inferInstance (fun ω => (U ω, V ω)) μ) =
      (@Measure.map (Ω × B) (A × B) (mΩ.prod mB) inferInstance
        (fun z : Ω × B => (U z.1, z.2)) (μ ⊗ₘ κ)) := by
  let : MeasurableSpace Ω := mΩ
  have hUa : Measurable U := hU.mono hm le_rfl
  have hF : Measurable (fun z : Ω × B => (U z.1, z.2)) :=
    (hUa.comp measurable_fst).prodMk measurable_snd
  apply Measure.ext_prod
  intro C D hC hD
  rw [Measure.map_apply (hUa.prodMk hV) (hC.prod hD),
    Measure.map_apply hF (hC.prod hD), Measure.compProd_apply (hF (hC.prod hD))]
  change μ (U ⁻¹' C ∩ V ⁻¹' D) =
    ∫⁻ ω, κ ω ((fun b => (U ω, b)) ⁻¹' (C ×ˢ D)) ∂μ
  rw [hc D (U ⁻¹' C) hD (hU hC)]
  rw [← lintegral_indicator (hUa hC)]
  apply lintegral_congr
  intro ω
  by_cases hω : U ω ∈ C
  · have he : ((fun b => (U ω, b)) ⁻¹' (C ×ˢ D)) = D := by
      ext b
      simp [hω]
    simp [Set.indicator, hω, he]
  · have he : ((fun b => (U ω, b)) ⁻¹' (C ×ˢ D)) = ∅ := by
      ext b
      simp [hω]
    simp [Set.indicator, hω, he]

theorem conditional_kernel_substitution {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (κ : @Kernel Ω B mΩ inferInstance) [IsMarkovKernel κ] {U : Ω → A} {V : Ω → B}
    (hU : Measurable[m] U) (hV : Measurable[mΩ] V)
    (hc : ∀ (C : Set B) (E : Set Ω), MeasurableSet C → MeasurableSet[m] E →
      μ (E ∩ V ⁻¹' C) = ∫⁻ ω in E, κ ω C ∂μ)
    {f : A × B → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ω, f (U ω, V ω) ∂μ) = ∫⁻ ω, ∫⁻ b, f (U ω, b) ∂κ ω ∂μ := by
  let : MeasurableSpace Ω := mΩ
  have hUa : Measurable U := hU.mono hm le_rfl
  have hF : Measurable (fun z : Ω × B => (U z.1, z.2)) :=
    (hUa.comp measurable_fst).prodMk measurable_snd
  calc
    _ = ∫⁻ z, f z ∂μ.map (fun ω => (U ω, V ω)) :=
      (lintegral_map hf (hUa.prodMk hV)).symm
    _ = ∫⁻ z, f z ∂(μ ⊗ₘ κ).map (fun z : Ω × B => (U z.1, z.2)) := by
      rw [conditional_pair_law hm κ hU hV hc]
    _ = ∫⁻ z : Ω × B, f (U z.1, z.2) ∂(μ ⊗ₘ κ) := lintegral_map hf hF
    _ = _ := Measure.lintegral_compProd (hf.comp hF)

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
open scoped ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

 theorem marginalHolding_nonneg (M : LotSizingModel Ω) (s : ℕ) (q x : ℝ)
    (d : ℕ → ℝ) : 0 ≤ marginalHolding M s q x d := by
  exact sum_nonneg fun j _ => mul_nonneg (M.h_nonneg j) (le_max_right _ _)

 theorem marginalHolding_clear_zero (M : LotSizingModel Ω) (s : ℕ) (x : ℝ)
    (d : ℕ → ℝ) (hd : ∀ t, 0 ≤ d t) :
    marginalHolding M s (max (d s - x) 0) x d = 0 := by
  apply sum_eq_zero
  intro j hj
  have hs : s ∈ Icc s j := mem_Icc.mpr ⟨le_rfl, (mem_Icc.mp hj).1⟩
  have hsum : d s ≤ ∑ i ∈ Icc s j, d i :=
    single_le_sum (fun i _ => hd i) hs
  have hm : max (d s - x) 0 ≤ max ((∑ i ∈ Icc s j, d i) - x) 0 :=
    max_le_max (sub_le_sub_right hsum x) le_rfl
  rw [max_eq_right (sub_nonpos.mpr hm), mul_zero]

 theorem condMarginalHolding_clear_zero (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (Q : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) :
    condMarginalHolding M I Q s
      (max (M.D s ω - levelBefore M Q s ω) 0) ω = 0 := by
  unfold condMarginalHolding
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hI.2.2.2.1 s ω, hI.2.2.2.2.1 s ω] with d hds hd
  rw [← hds, marginalHolding_clear_zero M s _ d hd, ENNReal.ofReal_zero]
  rfl

 theorem greatest_order_clears (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (Q : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω)
    (hg : IsGreatest {q : ℝ | 0 ≤ q ∧
      condMarginalHolding M I Q s q ω ≤ ENNReal.ofReal M.K} (Q s ω)) :
    max (M.D s ω - levelBefore M Q s ω) 0 ≤ Q s ω := by
  apply hg.2
  exact ⟨le_max_right _ _, by rw [condMarginalHolding_clear_zero M I hI]; exact bot_le⟩

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
open scoped ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem marginalHolding_measurable (M : LotSizingModel Ω) (s : ℕ) :
    Measurable (fun z : (ℝ × ℝ) × (ℕ → ℝ) =>
      marginalHolding M s z.1.1 z.1.2 z.2) := by
  unfold marginalHolding
  fun_prop

theorem marginalHolding_path_measurable (M : LotSizingModel Ω) (s : ℕ)
    (q x : ℝ) : Measurable (fun d : ℕ → ℝ => marginalHolding M s q x d) := by
  unfold marginalHolding
  fun_prop

theorem marginalHolding_increment (M : LotSizingModel Ω) (s : ℕ)
    (q x δ : ℝ) (hδ : 0 ≤ δ) (d : ℕ → ℝ) :
    marginalHolding M s (q + δ) x d ≤ marginalHolding M s q x d +
      δ * ∑ j ∈ Icc s M.T, M.h j := by
  unfold marginalHolding
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro j hj
  have hh : max (q + δ - max ((∑ i ∈ Icc s j, d i) - x) 0) 0 ≤
      max (q - max ((∑ i ∈ Icc s j, d i) - x) 0) 0 + δ := by
    apply max_le
    · linarith [le_max_left (q - max ((∑ i ∈ Icc s j, d i) - x) 0) 0]
    · linarith [le_max_right (q - max ((∑ i ∈ Icc s j, d i) - x) 0) 0]
  nlinarith [mul_le_mul_of_nonneg_left hh (M.h_nonneg j)]

theorem condMarginalHolding_increment (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (Q : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) (q δ : ℝ) (hδ : 0 ≤ δ) :
    condMarginalHolding M I Q s (q + δ) ω ≤
      condMarginalHolding M I Q s q ω +
      ENNReal.ofReal (δ * ∑ j ∈ Icc s M.T, M.h j) := by
  let : IsMarkovKernel (I s) := hI.1 s
  have hm : Measurable (fun d : ℕ → ℝ =>
      ENNReal.ofReal (marginalHolding M s q (levelBefore M Q s ω) d)) := by
    exact (marginalHolding_path_measurable M s q (levelBefore M Q s ω)).ennreal_ofReal
  unfold condMarginalHolding
  calc
    _ ≤ ∫⁻ d, ENNReal.ofReal (marginalHolding M s q (levelBefore M Q s ω) d) +
        ENNReal.ofReal (δ * ∑ j ∈ Icc s M.T, M.h j) ∂I s ω := by
      apply lintegral_mono
      intro d
      dsimp only
      rw [← ENNReal.ofReal_add (marginalHolding_nonneg M s q _ d)
        (mul_nonneg hδ (sum_nonneg fun j _ => M.h_nonneg j))]
      exact ENNReal.ofReal_le_ofReal (marginalHolding_increment M s q _ δ hδ d)
    _ = _ := by rw [lintegral_add_left hm]; simp

theorem greatest_order_saturates (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (Q : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω)
    (hg : IsGreatest {q : ℝ | 0 ≤ q ∧
      condMarginalHolding M I Q s q ω ≤ ENNReal.ofReal M.K} (Q s ω)) :
    condMarginalHolding M I Q s (Q s ω) ω = ENNReal.ofReal M.K := by
  by_contra hn
  obtain ⟨r, hr, hgap⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp (lt_of_le_of_ne hg.1.2 hn)
  let C : ℝ := ∑ j ∈ Icc s M.T, M.h j
  have hC : 0 ≤ C := sum_nonneg fun j _ => M.h_nonneg j
  let δ : ℝ := (r : ℝ) / (C + 1)
  have hrR : 0 < (r : ℝ) := hr
  have hδ : 0 < δ := div_pos hrR (by linarith)
  have hδC : δ * C ≤ r := by
    have he : δ * (C + 1) = (r : ℝ) := div_mul_cancel₀ _ (by linarith)
    nlinarith
  have he : ENNReal.ofReal (δ * C) ≤ (r : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hδC
  have hnew : condMarginalHolding M I Q s (Q s ω + δ) ω ≤ ENNReal.ofReal M.K :=
    (condMarginalHolding_increment M I hI Q s ω _ δ hδ.le).trans
      ((add_le_add_right he _).trans hgap.le)
  have hh := hg.2 ⟨by linarith [hg.1.1], hnew⟩
  linarith

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
open scoped ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem levelBefore_measurable (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ)
    (hQ : IsFeasiblePolicy M Q) (t : ℕ) : Measurable[M.ℱ t] (levelBefore M Q t) := by
  apply measurable_const.add
  apply Finset.measurable_sum
  intro j hj
  have hjt : j ≤ t := (mem_Ico.mp hj).2.le
  exact ((hQ.2 j).mono (M.ℱ.mono hjt) le_rfl).sub
    ((M.D_known j).mono (M.ℱ.mono hjt) le_rfl)

theorem levelAfter_measurable (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ)
    (hQ : IsFeasiblePolicy M Q) (t : ℕ) : Measurable[M.ℱ t] (levelAfter M Q t) :=
  (levelBefore_measurable M Q hQ t).add (hQ.2 t)

theorem lastOrder_measurable (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ)
    (hQ : IsFeasiblePolicy M Q) (t : ℕ) :
    Measurable[M.ℱ t] (fun ω => lastOrder Q (t+1) ω) := by
  classical
  induction t with
  | zero => simp [lastOrder]
  | succ t ih =>
    have he : (fun ω => lastOrder Q (t+1+1) ω) =
        fun ω => if 0 < Q (t+1) ω then t+1 else lastOrder Q (t+1) ω := by
      funext ω
      exact lastOrder_succ Q ω (by omega)
    rw [he]
    exact Measurable.ite (measurableSet_lt measurable_const (hQ.2 (t+1)))
      measurable_const (ih.mono (M.ℱ.mono (by omega : t ≤ t+1)) le_rfl)

theorem lastOrder_ambient_measurable (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ)
    (hQ : IsFeasiblePolicy M Q) (t : ℕ) : Measurable (lastOrder Q t) := by
  cases t with
  | zero =>
    have he : lastOrder Q 0 = fun _ : Ω => (0 : ℕ) := by
      funext ω
      simp [lastOrder]
    rw [he]
    exact measurable_const
  | succ t => exact (lastOrder_measurable M Q hQ t).mono (M.ℱ.le t) le_rfl

theorem startEvent_measurable (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ)
    (hQ : IsFeasiblePolicy M Q) (s : ℕ) : MeasurableSet[M.ℱ s] (startEvent Q s) :=
  measurableSet_lt measurable_const (hQ.2 s)

theorem highEvent_measurable (M : LotSizingModel Ω) (TB P : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) (hP : IsFeasiblePolicy M P) (s : ℕ) :
    MeasurableSet[M.ℱ s] (highEvent M TB P s) :=
  measurableSet_le (levelAfter_measurable M TB hTB s) (levelAfter_measurable M P hP s)

theorem holdCost_measurable (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ)
    (hQ : IsFeasiblePolicy M Q) (t : ℕ) : Measurable (holdCost M Q t) := by
  exact measurable_const.mul (((levelAfter_measurable M Q hQ t).mono (M.ℱ.le t) le_rfl |>.sub
    ((M.D_known t).mono (M.ℱ.le t) le_rfl)).max measurable_const)

theorem backCost_measurable (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ)
    (hQ : IsFeasiblePolicy M Q) (t : ℕ) : Measurable (backCost M Q t) := by
  exact measurable_const.mul (((M.D_known t).mono (M.ℱ.le t) le_rfl |>.sub
    ((levelAfter_measurable M Q hQ t).mono (M.ℱ.le t) le_rfl)).max measurable_const)

theorem setupCost_measurable (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ)
    (hQ : IsFeasiblePolicy M Q) (t : ℕ) : Measurable (setupCost M Q t) := by
  exact Measurable.ite ((M.ℱ.le t) _ (startEvent_measurable M Q hQ t))
    measurable_const measurable_const

theorem intervalHolding_measurable (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) (hQ : IsFeasiblePolicy M Q) (s : ℕ) :
    Measurable (intervalHolding M TB Q s) := by
  apply Finset.measurable_sum
  intro t ht
  exact Measurable.ite (measurableSet_eq_fun (lastOrder_ambient_measurable M TB hTB _) measurable_const)
    (holdCost_measurable M Q hQ t) measurable_const

theorem intervalBacklog_measurable (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) (hQ : IsFeasiblePolicy M Q) (s : ℕ) :
    Measurable (intervalBacklog M TB Q s) := by
  apply Finset.measurable_sum
  intro t ht
  exact Measurable.ite (measurableSet_eq_fun (lastOrder_ambient_measurable M TB hTB _) measurable_const)
    (backCost_measurable M Q hQ t) measurable_const

theorem intervalSetup_measurable (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) (hQ : IsFeasiblePolicy M Q) (s : ℕ) :
    Measurable (intervalSetup M TB Q s) := by
  apply Finset.measurable_sum
  intro t ht
  exact Measurable.ite (measurableSet_eq_fun (lastOrder_ambient_measurable M TB hTB _) measurable_const)
    (setupCost_measurable M Q hQ t) measurable_const

theorem intervalCost_measurable (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) (hQ : IsFeasiblePolicy M Q) (s : ℕ) :
    Measurable (intervalCost M TB Q s) :=
  ((intervalHolding_measurable M TB Q hTB hQ s).add
    (intervalBacklog_measurable M TB Q hTB hQ s)).add
    (intervalSetup_measurable M TB Q hTB hQ s)

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing

variable {Ω : Type*} [MeasurableSpace Ω]

theorem positive_order_trigger (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (Q : ℕ → Ω → ℝ) (hQ : IsTripleBalancing M I Q) (ω : Ω)
    {s : ℕ} (hs : s ∈ Icc 1 M.T) (hq : 0 < Q s ω) : M.K < accBacklog M Q s ω := by
  by_contra h
  have := (hQ.2 s hs ω).1 (le_of_not_gt h)
  linarith

theorem triggered_clears (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (Q : ℕ → Ω → ℝ) (hQ : IsTripleBalancing M I Q)
    (ω : Ω) {s : ℕ} (hs : s ∈ Icc 1 M.T) (ht : M.K < accBacklog M Q s ω) :
    M.D s ω - levelBefore M Q s ω ≤ Q s ω := by
  rcases lt_or_eq_of_le (mem_Icc.mp hs).2 with hlt | heq
  · exact (le_max_left _ _).trans (greatest_order_clears M I hI Q s ω (((hQ.2 s hs ω).2 ht).1 hlt))
  · exact (((hQ.2 s hs ω).2 ht).2 heq).ge

theorem trigger_structure (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (Q : ℕ → Ω → ℝ) (hQ : IsTripleBalancing M I Q)
    (ω : Ω) : ∀ s, 1 ≤ s → s ≤ M.T →
      (M.K < accBacklog M Q s ω → levelBefore M Q s ω < M.D s ω) ∧
      (Q s ω = 0 → accBacklog M Q s ω ≤ M.K) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro hs hT
    cases s with
    | zero => omega
    | succ s =>
      have hprev : (if 0 < Q s ω then 0 else accBacklog M Q s ω) ≤ M.K := by
        by_cases hz : s = 0
        · subst s
          simp [accBacklog, lastOrder, M.K_nonneg]
        · split_ifs with hp
          · exact M.K_nonneg
          · apply (ih s (by omega) (by omega) (by omega)).2
            exact le_antisymm (le_of_not_gt hp) (hQ.1.1 s ω)
      have hacc : accBacklog M Q (s+1) ω ≤ M.K + preBack M Q (s+1) ω := by
        by_cases hz : s = 0
        · subst s
          rw [accBacklog_one]
          linarith [M.K_nonneg]
        · rw [accBacklog_succ M Q hQ.1 ω (by omega)]
          linarith
      have hex : M.K < accBacklog M Q (s+1) ω → levelBefore M Q (s+1) ω < M.D (s+1) ω := by
        intro ht
        have hp : 0 < preBack M Q (s+1) ω := by linarith
        by_contra hn
        have he : preBack M Q (s+1) ω = 0 := by
          simp [preBack, max_eq_right (sub_nonpos.mpr (le_of_not_gt hn))]
        linarith
      refine ⟨hex, ?_⟩
      intro hz
      by_contra hn
      have ht := lt_of_not_ge hn
      have hc := triggered_clears M I hI Q hQ ω (mem_Icc.mpr ⟨hs,hT⟩) ht
      have := hex ht
      rw [hz] at hc
      linarith

theorem positive_order_exhausts (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (Q : ℕ → Ω → ℝ) (hQ : IsTripleBalancing M I Q)
    (ω : Ω) {s : ℕ} (hs : s ∈ Icc 1 M.T) (hp : 0 < Q s ω) :
    levelBefore M Q s ω < M.D s ω ∧ M.D s ω ≤ levelAfter M Q s ω := by
  have ht := positive_order_trigger M I Q hQ ω hs hp
  refine ⟨(trigger_structure M I hI Q hQ ω s (mem_Icc.mp hs).1 (mem_Icc.mp hs).2).1 ht, ?_⟩
  have := triggered_clears M I hI Q hQ ω hs ht
  unfold levelAfter
  linarith

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
variable {Ω : Type*} [MeasurableSpace Ω]

theorem batch_level (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (ω : Ω)
    {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t)
    (hq : ∀ j, s < j → j ≤ t → Q j ω = 0) :
    levelAfter M Q t ω - M.D t ω =
      levelAfter M Q s ω - ∑ j ∈ Icc s t, M.D j ω := by
  have hsum : (∑ j ∈ Ico s (t+1), Q j ω) = Q s ω := by
    apply sum_eq_single s
    · intro b hb hbs
      exact hq b (by have := (mem_Ico.mp hb).1; omega) (by have := (mem_Ico.mp hb).2; omega)
    · intro hn
      exact (hn (mem_Ico.mpr ⟨le_rfl,by omega⟩)).elim
  have hl := level_difference M Q ω hs (show s ≤ t+1 by omega)
  rw [sum_sub_distrib, hsum, Ico_add_one_right_eq_Icc, level_step M Q ω (by omega)] at hl
  unfold levelAfter at *
  linarith

theorem no_orders_if_batch_remains (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (Q : ℕ → Ω → ℝ) (hQ : IsTripleBalancing M I Q)
    (ω : Ω) {s t : ℕ} (hs : 1 ≤ s) (ht : t ≤ M.T)
    (hr : (∑ j ∈ Icc s t, M.D j ω) < levelAfter M Q s ω) :
    ∀ j, s < j → j ≤ t → Q j ω = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hsj hjt
    by_contra hn
    have hp : 0 < Q j ω := lt_of_le_of_ne (hQ.1.1 j ω) (Ne.symm hn)
    have hgap : ∀ i, s < i → i ≤ j-1 → Q i ω = 0 := by
      intro i hsi hij
      exact ih i (by omega) hsi (by omega)
    have hl := batch_level M Q ω hs (show s ≤ j-1 by omega) hgap
    have hj : 1 ≤ j := by omega
    have hstep := level_step M Q ω (show 1 ≤ j-1 by omega)
    have hjid : j-1+1=j := by omega
    rw [hjid] at hstep
    have hex := (positive_order_exhausts M I hI Q hQ ω (mem_Icc.mpr ⟨hj,by omega⟩) hp).1
    have hsum : (∑ i ∈ Icc s (j-1), M.D i ω) + M.D j ω = ∑ i ∈ Icc s j, M.D i ω := by
      rw [← Ico_add_one_right_eq_Icc, hjid, ← Ico_add_one_right_eq_Icc,
        sum_Ico_succ_top (show s ≤ j by omega)]
    have hle : (∑ i ∈ Icc s j, M.D i ω) ≤ ∑ i ∈ Icc s t, M.D i ω := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact mem_Icc.mpr ⟨(mem_Icc.mp hi).1, (mem_Icc.mp hi).2.trans hjt⟩
      · intro i hi hni
        exact M.D_nonneg i ω
    linarith

theorem batch_holding_term (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (Q : ℕ → Ω → ℝ) (hQ : IsTripleBalancing M I Q)
    (ω : Ω) {s t : ℕ} (hs : s ∈ Icc 1 M.T) (hp : 0 < Q s ω)
    (ht : t ∈ Icc s M.T) :
    (if lastOrder Q (t+1) ω = s then holdCost M Q t ω else 0) =
      M.h t * max (Q s ω - max ((∑ j ∈ Icc s t, M.D j ω) - levelBefore M Q s ω) 0) 0 := by
  classical
  have hst := (mem_Icc.mp ht).1
  have hd : M.D s ω ≤ ∑ j ∈ Icc s t, M.D j ω :=
    single_le_sum (fun j _ => M.D_nonneg j ω) (mem_Icc.mpr ⟨le_rfl,hst⟩)
  have hex := (positive_order_exhausts M I hI Q hQ ω hs hp).1
  rw [max_eq_left (show 0 ≤ (∑ j ∈ Icc s t, M.D j ω) - levelBefore M Q s ω by linarith)]
  have he : Q s ω - ((∑ j ∈ Icc s t, M.D j ω) - levelBefore M Q s ω) =
      levelAfter M Q s ω - ∑ j ∈ Icc s t, M.D j ω := by unfold levelAfter; ring
  rw [he]
  split_ifs with ha
  · unfold holdCost
    rw [batch_level M Q ω (mem_Icc.mp hs).1 hst]
    intro j hsj hjt
    apply no_order_after_last M Q hQ.1 ω (t := t+1) (by have := (mem_Icc.mp hs).1; omega) (by omega)
    rwa [ha]
  · have hr : levelAfter M Q s ω ≤ ∑ j ∈ Icc s t, M.D j ω := by
      by_contra h
      have hg := no_orders_if_batch_remains M I hI Q hQ ω (mem_Icc.mp hs).1
        (mem_Icc.mp ht).2 (lt_of_not_ge h)
      apply ha
      exact lastOrder_eq_of_gap Q ω (mem_Icc.mp hs).1 hst hp
        (fun j hsj hjt => by rw [hg j hsj hjt]; exact lt_irrefl _)
    rw [max_eq_right (sub_nonpos.mpr hr), mul_zero]

theorem intervalHolding_eq_marginal (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (Q : ℕ → Ω → ℝ) (hQ : IsTripleBalancing M I Q)
    (ω : Ω) {s : ℕ} (hs : s ∈ Icc 1 M.T) (hp : 0 < Q s ω) :
    intervalHolding M Q Q s ω =
      marginalHolding M s (Q s ω) (levelBefore M Q s ω) (M.demandPath ω) := by
  classical
  unfold intervalHolding marginalHolding
  have hsub : (∑ t ∈ Icc s M.T, if lastOrder Q (t+1) ω = s then holdCost M Q t ω else 0) =
      ∑ t ∈ Icc 1 M.T, if lastOrder Q (t+1) ω = s then holdCost M Q t ω else 0 := by
    apply sum_subset
    · intro j hj
      exact mem_Icc.mpr ⟨(mem_Icc.mp hs).1.trans (mem_Icc.mp hj).1,(mem_Icc.mp hj).2⟩
    · intro t ht hts
      have hlt : t < s := by simp only [mem_Icc] at *; omega
      have hl := lastOrder_le Q ω t
      simp [show lastOrder Q (t+1) ω ≠ s by omega]
  rw [← hsub]
  apply sum_congr rfl
  intro t ht
  exact batch_holding_term M I hI Q hQ ω hs hp ht

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
variable {Ω : Type*} [MeasurableSpace Ω]

theorem ordered_back_zero (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (Q : ℕ → Ω → ℝ) (hQ : IsTripleBalancing M I Q)
    (ω : Ω) {t : ℕ} (ht : t ∈ Icc 1 M.T) (hp : 0 < Q t ω) : backCost M Q t ω = 0 := by
  have h := (positive_order_exhausts M I hI Q hQ ω ht hp).2
  simp [backCost,max_eq_right (sub_nonpos.mpr h)]

theorem intervalBacklog_le_K (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (Q : ℕ → Ω → ℝ) (hQ : IsTripleBalancing M I Q)
    (ω : Ω) (s : ℕ) : intervalBacklog M Q Q s ω ≤ M.K := by
  classical
  let S := (Icc 1 M.T).filter (fun t => lastOrder Q t ω = s ∧ Q t ω = 0)
  have he : intervalBacklog M Q Q s ω = ∑ t ∈ S, backCost M Q t ω := by
    unfold intervalBacklog
    rw [sum_filter]
    apply sum_congr rfl
    intro t ht
    by_cases hl : lastOrder Q t ω = s
    · by_cases hz : Q t ω = 0
      · simp [hl,hz]
      · have hp : 0 < Q t ω := lt_of_le_of_ne (hQ.1.1 t ω) (Ne.symm hz)
        simp [hl,hz,ordered_back_zero M I hI Q hQ ω ht hp]
    · simp [hl]
  rw [he]
  by_cases hn : S.Nonempty
  · let r := S.max' hn
    have hr : r ∈ S := max'_mem S hn
    obtain ⟨hrt,hrs,hrq⟩ := mem_filter.mp hr
    have hacc := (trigger_structure M I hI Q hQ ω r (mem_Icc.mp hrt).1 (mem_Icc.mp hrt).2).2 hrq
    apply le_trans ?_ hacc
    rw [accBacklog_eq M Q hQ.1,hrs]
    apply le_trans (show (∑ t ∈ S, backCost M Q t ω) ≤ ∑ t ∈ S, preBack M Q t ω from ?_) ?_
    · apply sum_le_sum
      intro t ht
      have htq := (mem_filter.mp ht).2.2
      exact (preBack_eq_back M Q ω t htq).ge
    · apply sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨htt,hts,htq⟩ := mem_filter.mp ht
        have hl := lastOrder_lt Q ω (mem_Icc.mp htt).1
        rw [hts] at hl
        exact mem_Icc.mpr ⟨by omega, le_max' S t ht⟩
      · intro t ht hnt
        exact mul_nonneg (M.p_nonneg t) (le_max_right _ _)
  · rw [not_nonempty_iff_eq_empty.mp hn,sum_empty]
    exact M.K_nonneg

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
variable {Ω : Type*} [MeasurableSpace Ω]

theorem level_compare_gap (M : LotSizingModel Ω) (Q P : ℕ → Ω → ℝ)
    (hP : IsFeasiblePolicy M P) (ω : Ω) {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t)
    (hstart : levelAfter M Q s ω ≤ levelAfter M P s ω)
    (hq : ∀ j, s < j → j ≤ t → Q j ω = 0) :
    levelAfter M Q t ω ≤ levelAfter M P t ω := by
  have hrec : ∀ r, s ≤ r → r ≤ t → levelAfter M Q r ω ≤ levelAfter M P r ω := by
    intro r hsr
    induction r, hsr using Nat.le_induction with
    | base => exact fun _ => hstart
    | succ r hsr ih =>
      intro hrt
      have hbeforeQ := level_step M Q ω (show 1 ≤ r by omega)
      have hbeforeP := level_step M P ω (show 1 ≤ r by omega)
      have hp := hP.1 (r+1) ω
      have hz := hq (r+1) (by omega) hrt
      have hi := ih (by omega)
      unfold levelAfter at *
      rw [hz]
      linarith
  exact hrec t hst le_rfl

theorem initial_level_compare (M : LotSizingModel Ω) (Q P : ℕ → Ω → ℝ)
    (hP : IsFeasiblePolicy M P) (ω : Ω) {t : ℕ} (ht : 1 ≤ t)
    (hq : ∀ j ∈ Icc 1 t, Q j ω = 0) : levelAfter M Q t ω ≤ levelAfter M P t ω := by
  unfold levelAfter levelBefore
  have hz := hq t (mem_Icc.mpr ⟨ht,le_rfl⟩)
  have hs : (∑ j ∈ Ico 1 t, (Q j ω - M.D j ω)) ≤
      ∑ j ∈ Ico 1 t, (P j ω - M.D j ω) := by
    apply sum_le_sum
    intro j hj
    rw [hq j (mem_Icc.mpr ⟨(mem_Ico.mp hj).1,(mem_Ico.mp hj).2.le⟩)]
    linarith [hP.1 j ω]
  linarith [hP.1 t ω]

theorem interval_holding_high (M : LotSizingModel Ω) (TB P : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) (hP : IsFeasiblePolicy M P) (ω : Ω)
    {s : ℕ} (hs : 1 ≤ s) (hhigh : levelAfter M TB s ω ≤ levelAfter M P s ω) :
    intervalHolding M TB TB s ω ≤ intervalHolding M TB P s ω := by
  classical
  unfold intervalHolding
  apply sum_le_sum
  intro t ht
  split_ifs with hl
  · have hst : s ≤ t := by have := lastOrder_le TB ω t; omega
    have hc := level_compare_gap M TB P hP ω hs hst hhigh (fun j hsj hjt =>
      no_order_after_last M TB hTB ω (t := t+1) (by omega) (by omega) (by rwa [hl]))
    exact mul_le_mul_of_nonneg_left (max_le_max (sub_le_sub_right hc _) le_rfl) (M.h_nonneg t)
  · rfl

theorem initial_holding_le (M : LotSizingModel Ω) (TB P : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) (hP : IsFeasiblePolicy M P) (ω : Ω) :
    intervalHolding M TB TB 0 ω ≤ intervalHolding M TB P 0 ω := by
  classical
  unfold intervalHolding
  apply sum_le_sum
  intro t ht
  split_ifs with hl
  · have hc := initial_level_compare M TB P hP ω (mem_Icc.mp ht).1 (fun j hj =>
      no_order_after_last M TB hTB ω (t := t+1) (mem_Icc.mp hj).1 (by have := (mem_Icc.mp hj).2; omega)
        (by rw [hl]; exact (mem_Icc.mp hj).1))
    exact mul_le_mul_of_nonneg_left (max_le_max (sub_le_sub_right hc _) le_rfl) (M.h_nonneg t)
  · rfl

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem lastOrder_between (Q : ℕ → Ω → ℝ) (ω : Ω) {s t j : ℕ}
    (hl : lastOrder Q t ω = s) (hsj : s < j) (hjt : j ≤ t) : lastOrder Q j ω = s := by
  apply le_antisymm
  · exact (lastOrder_mono Q ω hjt).trans hl.le
  · by_cases hs : s=0
    · omega
    · have hp := lastOrder_positive Q ω (t := t) (by omega)
      rw [hl] at hp
      exact order_le_last Q ω (by omega) hsj hp

theorem setup_pays (M : LotSizingModel Ω) (TB P : ℕ → Ω → ℝ) (ω : Ω) {s t : ℕ}
    (ht : t ∈ Icc 1 M.T) (hl : lastOrder TB t ω = s) (hp : 0 < P t ω) :
    M.K ≤ intervalSetup M TB P s ω := by
  classical
  have h := single_le_sum (s := Icc 1 M.T)
    (f := fun j => if lastOrder TB j ω = s then setupCost M P j ω else 0)
    (fun j _ => by split_ifs; exact setup_nonneg M P j ω; rfl) ht
  simpa [intervalSetup,hl,setupCost,hp] using h

theorem interval_no_order_level (M : LotSizingModel Ω) (TB P : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) (ω : Ω) {s t : ℕ} (ht : t ∈ Icc 1 M.T)
    (hl : lastOrder TB t ω = s)
    (hstart : s=0 ∨ levelAfter M P s ω ≤ levelAfter M TB s ω)
    (hn : ∀ j ∈ Icc 1 M.T, lastOrder TB j ω = s → P j ω = 0) :
    levelAfter M P t ω ≤ levelBefore M TB t ω := by
  have hst : s < t := by have := lastOrder_lt TB ω (mem_Icc.mp ht).1; omega
  have hp : ∀ j, s < j → j ≤ t → P j ω = 0 := by
    intro j hsj hjt
    exact hn j (mem_Icc.mpr ⟨by omega,hjt.trans (mem_Icc.mp ht).2⟩)
      (lastOrder_between TB ω hl hsj hjt)
  have hq : ∀ j, s < j → j < t → TB j ω = 0 := by
    intro j hsj hjt
    exact no_order_after_last M TB hTB ω (by omega) hjt (by rwa [hl])
  have hpt := hp t hst le_rfl
  unfold levelAfter
  rw [hpt,add_zero]
  rcases hstart with hs | hstart
  · rw [hs] at hp hq
    unfold levelBefore
    apply add_le_add_right
    apply sum_le_sum
    intro j hj
    rw [hp j (mem_Ico.mp hj).1 (mem_Ico.mp hj).2.le,
      hq j (mem_Ico.mp hj).1 (mem_Ico.mp hj).2]
  · by_cases hs : s=0
    · rw [hs] at hp hq
      unfold levelBefore
      apply add_le_add_right
      apply sum_le_sum
      intro j hj
      rw [hp j (mem_Ico.mp hj).1 (mem_Ico.mp hj).2.le,
        hq j (mem_Ico.mp hj).1 (mem_Ico.mp hj).2]
    · have hbP := batch_level M P ω (show 1 ≤ s by omega) (show s ≤ t-1 by omega)
        (fun j hsj hjt => hp j hsj (by omega))
      have hbQ := batch_level M TB ω (show 1 ≤ s by omega) (show s ≤ t-1 by omega)
        (fun j hsj hjt => hq j hsj (by omega))
      have ht1 : t-1+1=t := by omega
      have hstepP := level_step M P ω (show 1 ≤ t-1 by omega)
      have hstepQ := level_step M TB ω (show 1 ≤ t-1 by omega)
      rw [ht1] at hstepP hstepQ
      linarith

theorem interval_back_low (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (TB P : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB)
    (hP : IsFeasiblePolicy M P) (ω : Ω) (s : ℕ) (hstart : s=0 ∨ levelAfter M P s ω ≤ levelAfter M TB s ω) :
    intervalBacklog M TB TB s ω ≤ intervalBacklog M TB P s ω + intervalSetup M TB P s ω := by
  classical
  by_cases hx : ∃ t ∈ Icc 1 M.T, lastOrder TB t ω = s ∧ 0 < P t ω
  · obtain ⟨t,ht,hl,hp⟩ := hx
    have hK := setup_pays M TB P ω ht hl hp
    have hb : 0 ≤ intervalBacklog M TB P s ω := by
      apply sum_nonneg
      intro j hj
      split_ifs
      · exact back_nonneg M P j ω
      · rfl
    have := intervalBacklog_le_K M I hI TB hTB ω s
    linarith
  · have hn : ∀ j ∈ Icc 1 M.T, lastOrder TB j ω = s → P j ω ≤ 0 := by
      intro j hj hl
      exact le_of_not_gt (fun hp => hx ⟨j,hj,hl,hp⟩)
    have hcmp : intervalBacklog M TB TB s ω ≤ intervalBacklog M TB P s ω := by
      unfold intervalBacklog
      apply sum_le_sum
      intro t ht
      split_ifs with hl
      · have hlevel : levelAfter M P t ω ≤ levelBefore M TB t ω := by
          exact interval_no_order_level M TB P hTB.1 ω ht hl hstart
            (fun j hj hlj => le_antisymm (hn j hj hlj) (hP.1 j ω))
        have htble : levelBefore M TB t ω ≤ levelAfter M TB t ω := by
          unfold levelAfter
          linarith [hTB.1.1 t ω]
        exact mul_le_mul_of_nonneg_left (max_le_max (sub_le_sub_left (hlevel.trans htble) _) le_rfl) (M.p_nonneg t)
      · rfl
    have hsetup : 0 ≤ intervalSetup M TB P s ω := by
      apply sum_nonneg
      intro j hj
      split_ifs
      · exact setup_nonneg M P j ω
      · rfl
    linarith

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
open scoped ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem intervalHolding_nonneg (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ)
    (s : ℕ) (ω : Ω) : 0 ≤ intervalHolding M TB Q s ω := by
  apply sum_nonneg
  intro t ht
  split_ifs
  · exact hold_nonneg M Q t ω
  · rfl

theorem intervalBacklog_nonneg (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ)
    (s : ℕ) (ω : Ω) : 0 ≤ intervalBacklog M TB Q s ω := by
  apply sum_nonneg
  intro t ht
  split_ifs
  · exact back_nonneg M Q t ω
  · rfl

theorem intervalSetup_nonneg (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ)
    (s : ℕ) (ω : Ω) : 0 ≤ intervalSetup M TB Q s ω := by
  apply sum_nonneg
  intro t ht
  split_ifs
  · exact setup_nonneg M Q t ω
  · rfl

theorem nextFlag_nonneg (M : LotSizingModel Ω) (TB : ℕ → Ω → ℝ)
    (s : ℕ) (ω : Ω) : 0 ≤ nextFlag M TB s ω := by
  apply sum_nonneg
  intro t ht
  split_ifs <;> norm_num

theorem nextFlag_measurable (M : LotSizingModel Ω) (TB : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) (s : ℕ) : Measurable (nextFlag M TB s) := by
  apply Finset.measurable_sum
  intro t ht
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_eq_fun (lastOrder_ambient_measurable M TB hTB t) measurable_const).inter
    ((M.ℱ.le t) _ (startEvent_measurable M TB hTB t))

theorem expectedCost_interval_partition (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) (hQ : IsFeasiblePolicy M Q) :
    expectedCost M Q = ∑ s ∈ range (M.T+1),
      ∫⁻ ω, ENNReal.ofReal (intervalCost M TB Q s ω) ∂M.μ := by
  unfold expectedCost
  have he : (fun ω => ENNReal.ofReal (totalCost M Q ω)) =
      fun ω => ∑ s ∈ range (M.T+1), ENNReal.ofReal (intervalCost M TB Q s ω) := by
    funext ω
    rw [← interval_partition M TB Q ω, ENNReal.ofReal_sum_of_nonneg
      (fun s _ => interval_nonneg M TB Q s ω)]
  rw [he]
  exact lintegral_finsetSum _ fun s _ =>
    (intervalCost_measurable M TB Q hTB hQ s).ennreal_ofReal

theorem intervalCost_lintegral (M : LotSizingModel Ω) (TB Q : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) (hQ : IsFeasiblePolicy M Q)
    (s : ℕ) (E : Set Ω) :
    (∫⁻ ω in E, ENNReal.ofReal (intervalCost M TB Q s ω) ∂M.μ) =
      (∫⁻ ω in E, ENNReal.ofReal (intervalHolding M TB Q s ω) ∂M.μ) +
      (∫⁻ ω in E, ENNReal.ofReal (intervalBacklog M TB Q s ω) ∂M.μ) +
      (∫⁻ ω in E, ENNReal.ofReal (intervalSetup M TB Q s ω) ∂M.μ) := by
  simp only [intervalCost, ENNReal.ofReal_add
    (add_nonneg (intervalHolding_nonneg M TB Q s _) (intervalBacklog_nonneg M TB Q s _))
    (intervalSetup_nonneg M TB Q s _), ENNReal.ofReal_add
    (intervalHolding_nonneg M TB Q s _) (intervalBacklog_nonneg M TB Q s _)]
  rw [lintegral_add_left (f := fun ω => ENNReal.ofReal (intervalHolding M TB Q s ω) +
    ENNReal.ofReal (intervalBacklog M TB Q s ω)) ((intervalHolding_measurable M TB Q hTB hQ s).ennreal_ofReal.add
    (intervalBacklog_measurable M TB Q hTB hQ s).ennreal_ofReal),
    lintegral_add_left (intervalHolding_measurable M TB Q hTB hQ s).ennreal_ofReal]

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
variable {Ω : Type*} [MeasurableSpace Ω]

theorem next_order_backlog_lower (M : LotSizingModel Ω) (TB P : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) (ω : Ω) {s t : ℕ} (ht : t ∈ Icc 1 M.T)
    (hl : lastOrder TB t ω = s)
    (hstart : s=0 ∨ levelAfter M P s ω ≤ levelAfter M TB s ω)
    (hn : ∀ j ∈ Icc 1 M.T, lastOrder TB j ω = s → P j ω = 0) :
    accBacklog M TB t ω ≤ intervalBacklog M TB P s ω := by
  classical
  rw [accBacklog_eq M TB hTB,hl]
  have hsub : Icc (s+1) t ⊆ Icc 1 M.T := by
    intro j hj
    exact mem_Icc.mpr ⟨by have := (mem_Icc.mp hj).1; omega,(mem_Icc.mp hj).2.trans (mem_Icc.mp ht).2⟩
  calc
    (∑ j ∈ Icc (s+1) t, preBack M TB j ω) ≤
        ∑ j ∈ Icc (s+1) t, if lastOrder TB j ω = s then backCost M P j ω else 0 := by
      apply sum_le_sum
      intro j hj
      have hlj := lastOrder_between TB ω hl (by have := (mem_Icc.mp hj).1; omega) (mem_Icc.mp hj).2
      rw [if_pos hlj]
      have hlev := interval_no_order_level M TB P hTB ω (hsub hj) hlj hstart hn
      exact mul_le_mul_of_nonneg_left (max_le_max (sub_le_sub_left hlev _) le_rfl) (M.p_nonneg j)
    _ ≤ intervalBacklog M TB P s ω := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro j hj hnj
      split_ifs
      · exact back_nonneg M P j ω
      · rfl

theorem interval_next_lower (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (TB P : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB) (hP : IsFeasiblePolicy M P)
    (ω : Ω) (s : ℕ) (hstart : s=0 ∨ levelAfter M P s ω ≤ levelAfter M TB s ω) :
    M.K * nextFlag M TB s ω ≤ intervalBacklog M TB P s ω + intervalSetup M TB P s ω := by
  classical
  have hb := intervalBacklog_nonneg M TB P s ω
  have hf := intervalSetup_nonneg M TB P s ω
  by_cases hnxt : ∃ t ∈ Icc 1 M.T, lastOrder TB t ω = s ∧ 0 < TB t ω
  · have hnle : M.K * nextFlag M TB s ω ≤ M.K := by
      simpa using mul_le_mul_of_nonneg_left (nextFlag_le_one M TB s ω) M.K_nonneg
    apply hnle.trans
    by_cases hp : ∃ j ∈ Icc 1 M.T, lastOrder TB j ω = s ∧ 0 < P j ω
    · obtain ⟨j,hj,hl,hp⟩ := hp
      have := setup_pays M TB P ω hj hl hp
      linarith
    · obtain ⟨t,ht,hl,hpos⟩ := hnxt
      have hn : ∀ j ∈ Icc 1 M.T, lastOrder TB j ω = s → P j ω = 0 := by
        intro j hj hlj
        exact le_antisymm (le_of_not_gt (fun h => hp ⟨j,hj,hlj,h⟩)) (hP.1 j ω)
      have ha := next_order_backlog_lower M TB P hTB.1 ω ht hl hstart hn
      have hg := positive_order_trigger M I TB hTB ω ht hpos
      linarith
  · have hz : nextFlag M TB s ω = 0 := by
      apply sum_eq_zero
      intro t ht
      simp [show ¬(lastOrder TB t ω = s ∧ 0 < TB t ω) from fun h => hnxt ⟨t,ht,h⟩]
    rw [hz,mul_zero]
    linarith

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
variable {Ω : Type*} [MeasurableSpace Ω]

theorem interval_high_bounds (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (TB P : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB)
    (hP : IsFeasiblePolicy M P) (ω : Ω) {s : ℕ} (hs : 1 ≤ s)
    (hh : levelAfter M TB s ω ≤ levelAfter M P s ω) :
    intervalHolding M TB TB s ω ≤ intervalCost M TB P s ω ∧
    intervalCost M TB TB s ω ≤ intervalCost M TB P s ω + M.K + M.K * nextFlag M TB s ω := by
  have hhold := interval_holding_high M TB P hTB.1 hP ω hs hh
  have hback := intervalBacklog_le_K M I hI TB hTB ω s
  have hsetup := setup_eq_flag M TB s ω
  have hb := intervalBacklog_nonneg M TB P s ω
  have hf := intervalSetup_nonneg M TB P s ω
  unfold intervalCost
  constructor <;> linarith

theorem interval_low_bounds (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (TB P : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB)
    (hP : IsFeasiblePolicy M P) (ω : Ω) (s : ℕ)
    (hh : levelAfter M P s ω ≤ levelAfter M TB s ω) :
    M.K * nextFlag M TB s ω ≤ intervalCost M TB P s ω ∧
    intervalCost M TB TB s ω ≤ intervalCost M TB P s ω + intervalHolding M TB TB s ω + M.K * nextFlag M TB s ω := by
  have hb := interval_back_low M I hI TB P hTB hP ω s (Or.inr hh)
  have hn := interval_next_lower M I TB P hTB hP ω s (Or.inr hh)
  have hhP := intervalHolding_nonneg M TB P s ω
  have hsetup := setup_eq_flag M TB s ω
  unfold intervalCost
  constructor <;> linarith

theorem initial_bounds (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (TB P : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB)
    (hP : IsFeasiblePolicy M P) (ω : Ω) :
    M.K * nextFlag M TB 0 ω ≤ intervalCost M TB P 0 ω ∧
    intervalCost M TB TB 0 ω ≤ intervalCost M TB P 0 ω + M.K * nextFlag M TB 0 ω := by
  have hh := initial_holding_le M TB P hTB.1 hP ω
  have hb := interval_back_low M I hI TB P hTB hP ω 0 (Or.inl rfl)
  have hn := interval_next_lower M I TB P hTB hP ω 0 (Or.inl rfl)
  have hhP := intervalHolding_nonneg M TB P 0 ω
  have hsetup := setup_eq_flag M TB 0 ω
  unfold intervalCost
  constructor <;> linarith

theorem terminal_interval_zero (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB) (ω : Ω) :
    intervalCost M TB TB M.T ω = 0 ∧ nextFlag M TB M.T ω = 0 := by
  classical
  have hneq : ∀ t ∈ Icc 1 M.T, lastOrder TB t ω ≠ M.T := by
    intro t ht
    have := lastOrder_lt TB ω (mem_Icc.mp ht).1
    have := (mem_Icc.mp ht).2
    omega
  have hh : intervalHolding M TB TB M.T ω = 0 := by
    apply sum_eq_zero
    intro t ht
    split_ifs with hl
    · have he : t=M.T := by have := lastOrder_le TB ω t; have := (mem_Icc.mp ht).2; omega
      have hp := lastOrder_positive TB ω (t := t+1) (by have := (mem_Icc.mp ht).1; omega)
      rw [hl,← he] at hp
      have hg := positive_order_trigger M I TB hTB ω ht hp
      have hc := ((hTB.2 t ht ω).2 hg).2 he
      simp [holdCost,levelAfter,hc]
    · rfl
  have hb : intervalBacklog M TB TB M.T ω = 0 := by
    exact sum_eq_zero (fun t ht => by simp [hneq t ht])
  have hf : intervalSetup M TB TB M.T ω = 0 := by
    exact sum_eq_zero (fun t ht => by simp [hneq t ht])
  refine ⟨by simp [intervalCost,hh,hb,hf], ?_⟩
  exact sum_eq_zero (fun t ht => by simp [hneq t ht])

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
open scoped ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem demandPath_measurable (M : LotSizingModel Ω) : Measurable M.demandPath := by
  exact measurable_pi_lambda _ fun t => (M.D_known t).mono (M.ℱ.le t) le_rfl

theorem conditional_marginal_balance (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (Q : ℕ → Ω → ℝ) (hQ : IsFeasiblePolicy M Q) (s : ℕ)
    (E : Set Ω) (hE : MeasurableSet[M.ℱ s] E)
    (hg : ∀ ω ∈ E, IsGreatest {q : ℝ | 0 ≤ q ∧
      condMarginalHolding M I Q s q ω ≤ ENNReal.ofReal M.K} (Q s ω)) :
    (∫⁻ ω in E, ENNReal.ofReal (marginalHolding M s (Q s ω)
      (levelBefore M Q s ω) (M.demandPath ω)) ∂M.μ) =
      ENNReal.ofReal M.K * M.μ E := by
  classical
  let : IsMarkovKernel (I s) := hI.1 s
  let U : Ω → (ℝ × ℝ) × ℝ≥0∞ := fun ω =>
    ((Q s ω, levelBefore M Q s ω), E.indicator (fun _ => 1) ω)
  have hU : Measurable[M.ℱ s] U :=
    ((hQ.2 s).prodMk (levelBefore_measurable M Q hQ s)).prodMk
      (measurable_const.indicator hE)
  let f : ((ℝ × ℝ) × ℝ≥0∞) × (ℕ → ℝ) → ℝ≥0∞ := fun z =>
    z.1.2 * ENNReal.ofReal (marginalHolding M s z.1.1.1 z.1.1.2 z.2)
  have hf : Measurable f := measurable_fst.snd.mul
    ((marginalHolding_measurable M s).comp
      (measurable_fst.fst.prodMk measurable_snd)).ennreal_ofReal
  have he := conditional_kernel_substitution (M.ℱ.le s) (I s) hU
    (demandPath_measurable M) (hI.2.2.1 s) hf
  have hEa : MeasurableSet E := (M.ℱ.le s) E hE
  have hleft : (fun ω => f (U ω, M.demandPath ω)) =
      E.indicator (fun ω => ENNReal.ofReal (marginalHolding M s (Q s ω)
        (levelBefore M Q s ω) (M.demandPath ω))) := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [f, U, hω]
  have hright : (fun ω => ∫⁻ d, f (U ω, d) ∂I s ω) =
      E.indicator (fun _ => ENNReal.ofReal M.K) := by
    funext ω
    by_cases hω : ω ∈ E
    · simp only [f, U, Set.indicator_of_mem hω, one_mul]
      exact greatest_order_saturates M I hI Q s ω (hg ω hω)
    · simp [f, U, hω]
  rw [hleft, hright, lintegral_indicator hEa, lintegral_indicator hEa] at he
  simpa using he

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem balanced_interval_bounds (μ : Measure Ω) (E F : Set Ω)
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    (H C P N : Ω → ℝ≥0∞) (K : ℝ≥0∞)
    (hH : Measurable H) (hP : Measurable P) (hN : Measurable N)
    (hcap : ∀ ω ∈ E, N ω ≤ 1)
    (hbH : (∫⁻ ω in E ∩ F, H ω ∂μ) = K * μ (E ∩ F))
    (hbL : (∫⁻ ω in E \ F, H ω ∂μ) = K * μ (E \ F))
    (hhigh : ∀ ω ∈ E ∩ F, H ω ≤ P ω ∧ C ω ≤ P ω + K + K * N ω)
    (hlow : ∀ ω ∈ E \ F, K * N ω ≤ P ω ∧ C ω ≤ P ω + H ω + K * N ω) :
    K * (∫⁻ ω in E, N ω ∂μ) ≤ ∫⁻ ω in E, P ω ∂μ ∧
    (∫⁻ ω in E, C ω ∂μ) ≤ (∫⁻ ω in E, P ω ∂μ) + K * μ E +
      K * (∫⁻ ω in E, N ω ∂μ) := by
  have hnH : K * (∫⁻ ω in E ∩ F, N ω ∂μ) ≤ ∫⁻ ω in E ∩ F, P ω ∂μ := by
    calc
      _ = ∫⁻ ω in E ∩ F, K * N ω ∂μ := (lintegral_const_mul K hN).symm
      _ ≤ ∫⁻ _ in E ∩ F, K ∂μ := setLIntegral_mono' (hE.inter hF) fun ω hω => by
        simpa using mul_le_mul' (le_refl K) (hcap ω hω.1)
      _ = K * μ (E ∩ F) := by simp
      _ = ∫⁻ ω in E ∩ F, H ω ∂μ := hbH.symm
      _ ≤ _ := setLIntegral_mono' (hE.inter hF) fun ω hω => (hhigh ω hω).1
  have hnL : K * (∫⁻ ω in E \ F, N ω ∂μ) ≤ ∫⁻ ω in E \ F, P ω ∂μ := by
    rw [← lintegral_const_mul K hN]
    exact setLIntegral_mono' (hE.diff hF) fun ω hω => (hlow ω hω).1
  have hcH : (∫⁻ ω in E ∩ F, C ω ∂μ) ≤
      (∫⁻ ω in E ∩ F, P ω ∂μ) + K * μ (E ∩ F) +
        K * (∫⁻ ω in E ∩ F, N ω ∂μ) := by
    calc
      _ ≤ ∫⁻ ω in E ∩ F, P ω + K + K * N ω ∂μ :=
        setLIntegral_mono' (hE.inter hF) fun ω hω => (hhigh ω hω).2
      _ = _ := by
        rw [lintegral_add_left (f := fun ω => P ω + K) (hP.add measurable_const), lintegral_add_left hP,
          lintegral_const_mul K hN]
        simp
  have hcL : (∫⁻ ω in E \ F, C ω ∂μ) ≤
      (∫⁻ ω in E \ F, P ω ∂μ) + K * μ (E \ F) +
        K * (∫⁻ ω in E \ F, N ω ∂μ) := by
    calc
      _ ≤ ∫⁻ ω in E \ F, P ω + H ω + K * N ω ∂μ :=
        setLIntegral_mono' (hE.diff hF) fun ω hω => (hlow ω hω).2
      _ = _ := by
        rw [lintegral_add_left (f := fun ω => P ω + H ω) (hP.add hH), lintegral_add_left hP,
          lintegral_const_mul K hN, hbL]
  constructor
  · rw [← lintegral_inter_add_sdiff N E hF, mul_add,
      ← lintegral_inter_add_sdiff P E hF]
    exact add_le_add hnH hnL
  · rw [← lintegral_inter_add_sdiff C E hF]
    calc
      _ ≤ _ := add_le_add hcH hcL
      _ = ((∫⁻ ω in E ∩ F, P ω ∂μ) + (∫⁻ ω in E \ F, P ω ∂μ)) +
          K * (μ (E ∩ F) + μ (E \ F)) +
          K * ((∫⁻ ω in E ∩ F, N ω ∂μ) + (∫⁻ ω in E \ F, N ω ∂μ)) := by ring
      _ = _ := by rw [lintegral_inter_add_sdiff P E hF,
        measure_inter_add_sdiff E hF, lintegral_inter_add_sdiff N E hF]

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
open scoped ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

def orderBudget (M : LotSizingModel Ω) (TB : ℕ → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal M.K * ENNReal.ofReal (numOrders M TB ω : ℝ) ∂M.μ

theorem orderBudget_flags (M : LotSizingModel Ω) (TB : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) :
    (∑ s ∈ range (M.T+1), ENNReal.ofReal M.K *
      ∫⁻ ω, ENNReal.ofReal (nextFlag M TB s ω) ∂M.μ) = orderBudget M TB := by
  have hp : ∀ ω, ENNReal.ofReal M.K * ENNReal.ofReal (numOrders M TB ω : ℝ) =
      ∑ s ∈ range (M.T+1), ENNReal.ofReal M.K * ENNReal.ofReal (nextFlag M TB s ω) := by
    intro ω
    rw [← sum_nextFlag M TB ω, ENNReal.ofReal_sum_of_nonneg
      (fun s _ => nextFlag_nonneg M TB s ω), mul_sum]
  unfold orderBudget
  simp_rw [hp]
  rw [lintegral_finsetSum (f := fun s ω => ENNReal.ofReal M.K *
    ENNReal.ofReal (nextFlag M TB s ω)) _ (fun s _ => measurable_const.mul
    (nextFlag_measurable M TB hTB s).ennreal_ofReal)]
  apply sum_congr rfl
  intro s hs
  exact (lintegral_const_mul _ (nextFlag_measurable M TB hTB s).ennreal_ofReal).symm

theorem orderBudget_starts (M : LotSizingModel Ω) (TB : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) :
    (∑ s ∈ Icc 1 M.T, ENNReal.ofReal M.K * M.μ (startEvent TB s)) = orderBudget M TB := by
  classical
  have hp : ∀ ω, ENNReal.ofReal (numOrders M TB ω : ℝ) =
      ∑ s ∈ Icc 1 M.T, (startEvent TB s).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    simp only [numOrders, ENNReal.ofReal_natCast, Set.indicator_apply, startEvent, Set.mem_ofPred_eq]
    exact natCast_card_filter _ _
  unfold orderBudget
  simp_rw [hp, mul_sum]
  rw [lintegral_finsetSum (f := fun s ω => ENNReal.ofReal M.K *
    (startEvent TB s).indicator (fun _ => (1 : ℝ≥0∞)) ω) _ (fun s _ => measurable_const.mul
    (measurable_const.indicator ((M.ℱ.le s) _ (startEvent_measurable M TB hTB s))))]
  apply sum_congr rfl
  intro s hs
  rw [lintegral_const_mul _ (measurable_const.indicator
    ((M.ℱ.le s) _ (startEvent_measurable M TB hTB s))),
    lintegral_indicator ((M.ℱ.le s) _ (startEvent_measurable M TB hTB s))]
  simp

theorem triple_bound_of_additive (A B K : ℝ≥0∞) (hl : K ≤ B)
    (hu : A ≤ B + K + K) : A ≤ 3 * B := by
  calc
    A ≤ B + K + K := hu
    _ ≤ B + B + B := add_le_add (add_le_add le_rfl hl) hl
    _ = 3 * B := by ring
def startBudget (M : LotSizingModel Ω) (TB : ℕ → Ω → ℝ) (s : ℕ) : ℝ≥0∞ :=
  if s = 0 then 0 else ENNReal.ofReal M.K * M.μ (startEvent TB s)

theorem sum_startBudget (M : LotSizingModel Ω) (TB : ℕ → Ω → ℝ)
    (hTB : IsFeasiblePolicy M TB) :
    (∑ s ∈ range (M.T+1), startBudget M TB s) = orderBudget M TB := by
  classical
  have hsub : Icc 1 M.T ⊆ range (M.T+1) := by
    intro s hs
    exact mem_range.mpr (by have := (mem_Icc.mp hs).2; omega)
  rw [← sum_subset hsub]
  · rw [← orderBudget_starts M TB hTB]
    apply sum_congr rfl
    intro s hs
    exact if_neg (by have := (mem_Icc.mp hs).1; omega)
  · intro s hs hn
    have hz : s = 0 := by simp only [mem_Icc, mem_range] at *; omega
    simp [startBudget, hz]

theorem three_approx_of_interval_estimates (M : LotSizingModel Ω)
    (TB P : ℕ → Ω → ℝ) (hTB : IsFeasiblePolicy M TB) (hP : IsFeasiblePolicy M P)
    (hl : ∀ s ∈ range (M.T+1),
      ENNReal.ofReal M.K * (∫⁻ ω, ENNReal.ofReal (nextFlag M TB s ω) ∂M.μ) ≤
      ∫⁻ ω, ENNReal.ofReal (intervalCost M TB P s ω) ∂M.μ)
    (hu : ∀ s ∈ range (M.T+1),
      (∫⁻ ω, ENNReal.ofReal (intervalCost M TB TB s ω) ∂M.μ) ≤
      (∫⁻ ω, ENNReal.ofReal (intervalCost M TB P s ω) ∂M.μ) + startBudget M TB s +
      ENNReal.ofReal M.K * (∫⁻ ω, ENNReal.ofReal (nextFlag M TB s ω) ∂M.μ)) :
    expectedCost M TB ≤ 3 * expectedCost M P := by
  apply triple_bound_of_additive (K := orderBudget M TB)
  · rw [← orderBudget_flags M TB hTB, expectedCost_interval_partition M TB P hTB hP]
    exact sum_le_sum hl
  · rw [expectedCost_interval_partition M TB TB hTB hTB]
    calc
      _ ≤ ∑ s ∈ range (M.T+1), ((∫⁻ ω, ENNReal.ofReal (intervalCost M TB P s ω) ∂M.μ) +
          startBudget M TB s + ENNReal.ofReal M.K *
          (∫⁻ ω, ENNReal.ofReal (nextFlag M TB s ω) ∂M.μ)) := sum_le_sum hu
      _ = _ := by
        rw [sum_add_distrib, sum_add_distrib, orderBudget_flags M TB hTB,
          sum_startBudget M TB hTB, ← expectedCost_interval_partition M TB P hTB hP]

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
open scoped ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem intervalHolding_balance (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB)
    (s : ℕ) (hs : s ∈ Ico 1 M.T)
    (hmatch : ∀ ω, 0 < TB s ω → intervalHolding M TB TB s ω =
      marginalHolding M s (TB s ω) (levelBefore M TB s ω) (M.demandPath ω))
    (E : Set Ω) (hE : MeasurableSet[M.ℱ s] E) (hsub : E ⊆ startEvent TB s) :
    (∫⁻ ω in E, ENNReal.ofReal (intervalHolding M TB TB s ω) ∂M.μ) =
      ENNReal.ofReal M.K * M.μ E := by
  calc
    _ = ∫⁻ ω in E, ENNReal.ofReal (marginalHolding M s (TB s ω)
        (levelBefore M TB s ω) (M.demandPath ω)) ∂M.μ := by
      apply setLIntegral_congr_fun ((M.ℱ.le s) E hE)
      intro ω hω
      dsimp only
      rw [hmatch ω (hsub hω)]
    _ = _ := conditional_marginal_balance M I hI TB hTB.1 s E hE (by
      intro ω hω
      have hs' : s ∈ Icc 1 M.T := mem_Icc.mpr ⟨(mem_Ico.mp hs).1, (mem_Ico.mp hs).2.le⟩
      exact ((hTB.2 s hs' ω).2 (positive_order_trigger M I TB hTB ω hs' (hsub hω))).1
        (mem_Ico.mp hs).2)

theorem native_interval_expected_bounds (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB P : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB) (hP : IsFeasiblePolicy M P)
    (s : ℕ) (hs : s ∈ Ico 1 M.T)
    (hmatch : ∀ ω, 0 < TB s ω → intervalHolding M TB TB s ω =
      marginalHolding M s (TB s ω) (levelBefore M TB s ω) (M.demandPath ω))
    (hhigh : ∀ ω, 0 < TB s ω → ω ∈ highEvent M TB P s →
      intervalHolding M TB TB s ω ≤ intervalCost M TB P s ω ∧
      intervalCost M TB TB s ω ≤ intervalCost M TB P s ω + M.K + M.K * nextFlag M TB s ω)
    (hlow : ∀ ω, 0 < TB s ω → ω ∉ highEvent M TB P s →
      M.K * nextFlag M TB s ω ≤ intervalCost M TB P s ω ∧
      intervalCost M TB TB s ω ≤ intervalCost M TB P s ω + intervalHolding M TB TB s ω +
        M.K * nextFlag M TB s ω) :
    ENNReal.ofReal M.K * (∫⁻ ω, ENNReal.ofReal (nextFlag M TB s ω) ∂M.μ) ≤
      ∫⁻ ω, ENNReal.ofReal (intervalCost M TB P s ω) ∂M.μ ∧
    (∫⁻ ω, ENNReal.ofReal (intervalCost M TB TB s ω) ∂M.μ) ≤
      (∫⁻ ω, ENNReal.ofReal (intervalCost M TB P s ω) ∂M.μ) +
      ENNReal.ofReal M.K * M.μ (startEvent TB s) +
      ENNReal.ofReal M.K * (∫⁻ ω, ENNReal.ofReal (nextFlag M TB s ω) ∂M.μ) := by
  let E := startEvent TB s
  let F := highEvent M TB P s
  have hE := startEvent_measurable M TB hTB.1 s
  have hF := highEvent_measurable M TB P hTB.1 hP s
  have hbH := intervalHolding_balance M I hI TB hTB s hs hmatch (E ∩ F)
    (hE.inter hF) Set.inter_subset_left
  have hbL := intervalHolding_balance M I hI TB hTB s hs hmatch (E \ F)
    (hE.diff hF) Set.sdiff_subset
  have hh := balanced_interval_bounds M.μ E F ((M.ℱ.le s) _ hE) ((M.ℱ.le s) _ hF)
    (fun ω => ENNReal.ofReal (intervalHolding M TB TB s ω))
    (fun ω => ENNReal.ofReal (intervalCost M TB TB s ω))
    (fun ω => ENNReal.ofReal (intervalCost M TB P s ω))
    (fun ω => ENNReal.ofReal (nextFlag M TB s ω)) (ENNReal.ofReal M.K)
    (intervalHolding_measurable M TB TB hTB.1 hTB.1 s).ennreal_ofReal
    (intervalCost_measurable M TB P hTB.1 hP s).ennreal_ofReal
    (nextFlag_measurable M TB hTB.1 s).ennreal_ofReal
    (fun ω _ => by simpa using ENNReal.ofReal_le_ofReal (nextFlag_le_one M TB s ω))
    hbH hbL (by
      intro ω hω
      obtain ⟨h1,h2⟩ := hhigh ω hω.1 hω.2
      refine ⟨ENNReal.ofReal_le_ofReal h1, ?_⟩
      have he := ENNReal.ofReal_le_ofReal h2
      rwa [ENNReal.ofReal_add (add_nonneg (interval_nonneg M TB P s ω) M.K_nonneg)
        (mul_nonneg M.K_nonneg (nextFlag_nonneg M TB s ω)),
        ENNReal.ofReal_add (interval_nonneg M TB P s ω) M.K_nonneg,
        ENNReal.ofReal_mul M.K_nonneg] at he) (by
      intro ω hω
      obtain ⟨h1,h2⟩ := hlow ω hω.1 hω.2
      constructor
      · simpa only [ENNReal.ofReal_mul M.K_nonneg] using ENNReal.ofReal_le_ofReal h1
      · have he := ENNReal.ofReal_le_ofReal h2
        rwa [ENNReal.ofReal_add
          (add_nonneg (interval_nonneg M TB P s ω) (intervalHolding_nonneg M TB TB s ω))
          (mul_nonneg M.K_nonneg (nextFlag_nonneg M TB s ω)),
          ENNReal.ofReal_add (interval_nonneg M TB P s ω) (intervalHolding_nonneg M TB TB s ω),
          ENNReal.ofReal_mul M.K_nonneg] at he)
  have hz : ∀ ω ∉ E, TB s ω = 0 := by
    intro ω hω
    exact le_antisymm (le_of_not_gt hω) (hTB.1.1 s ω)
  have hn : (fun ω => ENNReal.ofReal (nextFlag M TB s ω)).support ⊆ E := by
    intro ω hω
    by_contra hn
    exact hω (by dsimp only; rw [inactive_flag M TB ω (mem_Ico.mp hs).1 (hz ω hn), ENNReal.ofReal_zero])
  have hc (Q : ℕ → Ω → ℝ) :
      (fun ω => ENNReal.ofReal (intervalCost M TB Q s ω)).support ⊆ E := by
    intro ω hω
    by_contra hn
    exact hω (by dsimp only; rw [inactive_interval M TB Q ω (mem_Ico.mp hs).1 (hz ω hn), ENNReal.ofReal_zero])
  rw [setLIntegral_eq_of_support_subset hn,
    setLIntegral_eq_of_support_subset (hc P), setLIntegral_eq_of_support_subset (hc TB)] at hh
  exact hh

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory
open LeviBalancing.TripleBalancing
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem initial_interval_expected_bounds (M : LotSizingModel Ω)
    (TB P : ℕ → Ω → ℝ) (hTB : IsFeasiblePolicy M TB) (hP : IsFeasiblePolicy M P)
    (hl : ∀ ω, M.K * nextFlag M TB 0 ω ≤ intervalCost M TB P 0 ω)
    (hu : ∀ ω, intervalCost M TB TB 0 ω ≤ intervalCost M TB P 0 ω +
      M.K * nextFlag M TB 0 ω) :
    ENNReal.ofReal M.K * (∫⁻ ω, ENNReal.ofReal (nextFlag M TB 0 ω) ∂M.μ) ≤
      ∫⁻ ω, ENNReal.ofReal (intervalCost M TB P 0 ω) ∂M.μ ∧
    (∫⁻ ω, ENNReal.ofReal (intervalCost M TB TB 0 ω) ∂M.μ) ≤
      (∫⁻ ω, ENNReal.ofReal (intervalCost M TB P 0 ω) ∂M.μ) + startBudget M TB 0 +
      ENNReal.ofReal M.K * (∫⁻ ω, ENNReal.ofReal (nextFlag M TB 0 ω) ∂M.μ) := by
  constructor
  · rw [← lintegral_const_mul _ (nextFlag_measurable M TB hTB 0).ennreal_ofReal]
    apply lintegral_mono
    intro ω
    simpa only [ENNReal.ofReal_mul M.K_nonneg] using ENNReal.ofReal_le_ofReal (hl ω)
  · have he : (∫⁻ ω, ENNReal.ofReal (intervalCost M TB TB 0 ω) ∂M.μ) ≤
        ∫⁻ ω, ENNReal.ofReal (intervalCost M TB P 0 ω) +
          ENNReal.ofReal M.K * ENNReal.ofReal (nextFlag M TB 0 ω) ∂M.μ := by
      apply lintegral_mono
      intro ω
      have hh := ENNReal.ofReal_le_ofReal (hu ω)
      simpa only [ENNReal.ofReal_add (interval_nonneg M TB P 0 ω)
        (mul_nonneg M.K_nonneg (nextFlag_nonneg M TB 0 ω)),
        ENNReal.ofReal_mul M.K_nonneg] using hh
    rw [lintegral_add_left (intervalCost_measurable M TB P hTB hP 0).ennreal_ofReal,
      lintegral_const_mul _ (nextFlag_measurable M TB hTB 0).ennreal_ofReal] at he
    simpa [startBudget] using he

end TripleBalancingProof


noncomputable section
namespace TripleBalancingProof
open MeasureTheory ProbabilityTheory Finset
open LeviBalancing.TripleBalancing
open scoped ENNReal

theorem full_native_result {Ω : Type*} [MeasurableSpace Ω]
    (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB)
    (P : ℕ → Ω → ℝ) (hP : IsFeasiblePolicy M P) :
    expectedCost M TB ≤ 3 * expectedCost M P := by
  have hlocal : ∀ s ∈ range (M.T+1),
      ENNReal.ofReal M.K * (∫⁻ ω, ENNReal.ofReal (nextFlag M TB s ω) ∂M.μ) ≤
        ∫⁻ ω, ENNReal.ofReal (intervalCost M TB P s ω) ∂M.μ ∧
      (∫⁻ ω, ENNReal.ofReal (intervalCost M TB TB s ω) ∂M.μ) ≤
        (∫⁻ ω, ENNReal.ofReal (intervalCost M TB P s ω) ∂M.μ) + startBudget M TB s +
        ENNReal.ofReal M.K * (∫⁻ ω, ENNReal.ofReal (nextFlag M TB s ω) ∂M.μ) := by
    intro s hs
    by_cases hz : s=0
    · subst s
      exact initial_interval_expected_bounds M TB P hTB.1 hP
        (fun ω => (initial_bounds M I hI TB P hTB hP ω).1)
        (fun ω => (initial_bounds M I hI TB P hTB hP ω).2)
    · by_cases he : s=M.T
      · subst s
        have hc : ∀ ω, intervalCost M TB TB M.T ω = 0 := fun ω => (terminal_interval_zero M I TB hTB ω).1
        have hn : ∀ ω, nextFlag M TB M.T ω = 0 := fun ω => (terminal_interval_zero M I TB hTB ω).2
        simp_rw [hc,hn]
        simp
      · have hsi : s ∈ Ico 1 M.T := by simp only [mem_range] at hs; exact mem_Ico.mpr ⟨by omega,by omega⟩
        have hsc : s ∈ Icc 1 M.T := mem_Icc.mpr ⟨(mem_Ico.mp hsi).1,(mem_Ico.mp hsi).2.le⟩
        have hb := native_interval_expected_bounds M I hI TB P hTB hP s hsi
          (fun ω hp => intervalHolding_eq_marginal M I hI TB hTB ω hsc hp)
          (fun ω _ hh => interval_high_bounds M I hI TB P hTB hP ω (mem_Ico.mp hsi).1 hh)
          (fun ω _ hh => interval_low_bounds M I hI TB P hTB hP ω s (lt_of_not_ge hh).le)
        simpa only [startBudget,if_neg hz] using hb
  exact three_approx_of_interval_estimates M TB P hTB.1 hP
    (fun s hs => (hlocal s hs).1) (fun s hs => (hlocal s hs).2)

end TripleBalancingProof


open MeasureTheory ProbabilityTheory

namespace LeviBalancing.TripleBalancing

/-- Theorem 6.1 (p. 301): the expected cost of the triple-balancing policy is at most three times
the expected cost of any feasible policy (in particular, of an optimal one). -/
theorem triple_balancing_three_approximation {Ω : Type*} [MeasurableSpace Ω]
    (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB)
    (P : ℕ → Ω → ℝ) (hP : IsFeasiblePolicy M P) :
    expectedCost M TB ≤ 3 * expectedCost M P := by
  exact TripleBalancingProof.full_native_result M I hI TB hTB P hP

end LeviBalancing.TripleBalancing

open LeviBalancing.TripleBalancing MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB)
    (P : ℕ → Ω → ℝ) (hP : IsFeasiblePolicy M P) :
    expectedCost M TB ≤ 3 * expectedCost M P := LeviBalancing.TripleBalancing.triple_balancing_three_approximation M I hI TB hTB P hP
