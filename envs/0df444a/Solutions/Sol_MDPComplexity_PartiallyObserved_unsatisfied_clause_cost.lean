-- Prove2me | solution 1 for MDPComplexity.PartiallyObserved.unsatisfied_clause_cost
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T05:55:33.583195+00:00
-- url     : https://prove2.me/submissions/7e8c1747-2763-42a8-9623-df56f6a99696

import Definitions.Def_MDPComplexity_PartiallyObserved_Construction
import Mathlib.Tactic.Ring

open Finset MDPComplexity.PartiallyObserved

namespace MDPStages

variable {n m : ℕ}

lemma lvlA'_eq_iff (i j : Fin m) (k : ℕ) :
    lvlA' (n := n) i k = lvlA' j k ↔ i = j := by
  unfold lvlA'
  split_ifs <;> simp

lemma trajProb_nonneg {S Z : Type} (M : POMDP S Z) [DecidableEq S] (s₀ : S) (π : M.Policy) (T : ℕ)
    (x : Fin (T + 1) → S) : 0 ≤ M.trajProb s₀ π T x := by
  unfold POMDP.trajProb
  apply mul_nonneg
  · split_ifs <;> norm_num
  · exact Finset.prod_nonneg (fun _ _ ↦ ENNReal.toReal_nonneg)

lemma trajCost_nonneg (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy) (T : ℕ)
    (x : Fin (T + 1) → St n m) : 0 ≤ (φ.toPOMDP hm).trajCost π T x := by
  unfold POMDP.trajCost
  apply sum_nonneg
  intro t _
  have hcost (z : Obs n m) (d : φ.Dec z) : 0 ≤ φ.cost z d := by
    cases z <;> simp [QBF.cost]
  exact hcost _ _

/-- The time at which a state is visited in the acyclic part of the construction. -/
def stage : St n m → ℕ
  | .s0 => 0
  | .A _ j | .A' _ j => 2 * j.val + 1
  | .T _ j | .T' _ j | .F _ j | .F' _ j => 2 * j.val + 2
  | .Aend _ | .Aend' _ => 2 * n + 1
  | .sink => horizon n

lemma stage_lvlA (i : Fin m) (k : ℕ) (hk : k ≤ n) :
    stage (lvlA (n := n) i k) = 2 * k + 1 := by
  unfold lvlA
  split_ifs with h
  · rfl
  · have : k = n := by omega
    simp [stage, this]

lemma stage_lvlA' (i : Fin m) (k : ℕ) (hk : k ≤ n) :
    stage (lvlA' (n := n) i k) = 2 * k + 1 := by
  unfold lvlA'
  split_ifs with h
  · rfl
  · have : k = n := by omega
    simp [stage, this]

lemma pure_support {s t : St n m} (h : (PMF.pure t) s ≠ 0) : s = t :=
  (PMF.mem_support_pure_iff _ _).mp h

lemma stepA_support (b : Bool) (d : DecA b) (t f s : St n m)
    (h : stepA b d t f s ≠ 0) : s = t ∨ s = f := by
  cases b with
  | false =>
    obtain ⟨c, _, hc⟩ := (PMF.mem_support_map_iff _ _ _).mp h
    cases c with
    | false => exact Or.inr hc.symm
    | true => exact Or.inl hc.symm
  | true =>
    have hs : s = cond d t f := pure_support h
    cases d with
    | false => exact Or.inr hs
    | true => exact Or.inl hs

lemma stepA_half_le (b : Bool) (d : DecA b) (t f s : St n m)
    (h : stepA b d t f s ≠ 0) : (2 : ℝ)⁻¹ ≤ (stepA b d t f s).toReal := by
  cases b with
  | false =>
    rcases stepA_support false d t f s h with hs | hs
    all_goals
      rw [hs]
      by_cases htf : t = f <;>
        norm_num [stepA, PMF.map_apply, tsum_fintype, htf, eq_comm]
  | true =>
    have hs : s = cond d t f := pure_support h
    rw [hs]
    cases d <;> norm_num [stepA, PMF.pure_apply]

lemma transition_initial (φ : QBF n m) (hm : 0 < m) (s : St n m)
    (d : φ.Dec (.s0 : St n m).obs) (h : φ.trans hm .s0 d s ≠ 0) :
    (φ.trans hm .s0 d s).toReal = 1 / (m : ℝ) := by
  obtain ⟨i, _, hi⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  rw [← hi]
  simp [QBF.trans, PMF.map_apply, tsum_fintype, lvlA'_eq_iff,
    ENNReal.toReal_inv, one_div]

lemma transition_zero_stage (φ : QBF n m) (hm : 0 < m) (s s' : St n m)
    (d : φ.Dec s.obs) (h : φ.trans hm s d s' ≠ 0) (hs : stage s = 0) :
    (φ.trans hm s d s').toReal = 1 / (m : ℝ) := by
  cases s <;> simp only [stage, horizon] at hs
  all_goals try omega
  exact transition_initial φ hm _ _ h

lemma transition_odd_lower (φ : QBF n m) (hm : 0 < m) (s s' : St n m)
    (d : φ.Dec s.obs) (h : φ.trans hm s d s' ≠ 0)
    (k : ℕ) (hk : k < n) (hs : stage s = 2 * k + 1) :
    (2 : ℝ)⁻¹ ≤ (φ.trans hm s d s').toReal := by
  cases s <;> simp only [stage, horizon] at hs
  all_goals try omega
  · exact stepA_half_le _ _ _ _ _ h
  · exact stepA_half_le _ _ _ _ _ h

lemma transition_even_one (φ : QBF n m) (hm : 0 < m) (s s' : St n m)
    (d : φ.Dec s.obs) (h : φ.trans hm s d s' ≠ 0)
    (k : ℕ) (hs : stage s = 2 * k + 2) :
    (φ.trans hm s d s').toReal = 1 := by
  cases s <;> simp only [stage, horizon] at hs
  all_goals try omega
  all_goals
    rw [pure_support h]
    simp only [QBF.trans, PMF.pure_apply_self, ENNReal.toReal_one]

lemma transition_final_one (φ : QBF n m) (hm : 0 < m) (s s' : St n m)
    (d : φ.Dec s.obs) (h : φ.trans hm s d s' ≠ 0) (hs : stage s = 2 * n + 1) :
    (φ.trans hm s d s').toReal = 1 := by
  cases s <;> simp only [stage, horizon] at hs
  all_goals try omega
  all_goals
    rw [pure_support h]
    simp only [QBF.trans, PMF.pure_apply_self, ENNReal.toReal_one]

lemma transition_stage (φ : QBF n m) (hm : 0 < m) (s s' : St n m) (d : φ.Dec s.obs)
    (h : φ.trans hm s d s' ≠ 0) :
    stage s' = min (stage s + 1) (horizon n) := by
  cases s with
  | s0 =>
    obtain ⟨i, _, hi⟩ := (PMF.mem_support_map_iff _ _ _).mp h
    rw [← hi, stage_lvlA' i 0 (Nat.zero_le n)]
    simp [stage, horizon]
  | A i j =>
    rcases stepA_support (φ.q j) d (.T i j) (.F i j) s' h with rfl | rfl <;>
      simp only [stage, horizon] <;> omega
  | A' i j =>
    rcases stepA_support (φ.q j) d (.T' i j) (.F' i j) s' h with rfl | rfl <;>
      simp only [stage, horizon] <;> omega
  | T i j =>
    rw [pure_support h, stage_lvlA i (j.val + 1) (by omega)]
    simp only [stage, horizon]
    omega
  | F i j =>
    rw [pure_support h, stage_lvlA i (j.val + 1) (by omega)]
    simp only [stage, horizon]
    omega
  | T' i j =>
    have hs : s' = if (j, true) ∈ φ.clause i then lvlA i (j.val + 1)
        else lvlA' i (j.val + 1) := pure_support h
    rw [hs]
    split_ifs
    · rw [stage_lvlA i (j.val + 1) (by omega)]
      simp only [stage, horizon]
      omega
    · rw [stage_lvlA' i (j.val + 1) (by omega)]
      simp only [stage, horizon]
      omega
  | F' i j =>
    have hs : s' = if (j, false) ∈ φ.clause i then lvlA i (j.val + 1)
        else lvlA' i (j.val + 1) := pure_support h
    rw [hs]
    split_ifs
    · rw [stage_lvlA i (j.val + 1) (by omega)]
      simp only [stage, horizon]
      omega
    · rw [stage_lvlA' i (j.val + 1) (by omega)]
      simp only [stage, horizon]
      omega
  | Aend i | Aend' i | sink =>
    rw [pure_support h]
    simp [stage, horizon]

lemma trajectory_support (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy)
    (x : Fin (horizon n + 1) → St n m)
    (hx : (φ.toPOMDP hm).trajProb .s0 π (horizon n) x ≠ 0) :
    x 0 = .s0 ∧ ∀ t : Fin (horizon n),
      φ.trans hm (x t.castSucc) ((φ.toPOMDP hm).dec π x t.castSucc) (x t.succ) ≠ 0 := by
  have h0 : x 0 = .s0 := by
    by_contra h
    simp [POMDP.trajProb, h] at hx
  refine ⟨h0, fun t ↦ ?_⟩
  have hp : (∏ t : Fin (horizon n),
      ((φ.toPOMDP hm).p (x t.castSucc)
        ((φ.toPOMDP hm).dec π x t.castSucc) (x t.succ)).toReal) ≠ 0 := by
    simpa [POMDP.trajProb, h0] using hx
  have ht := Finset.prod_ne_zero_iff.mp hp t (Finset.mem_univ t)
  intro h
  apply ht
  change (φ.trans hm (x t.castSucc)
    ((φ.toPOMDP hm).dec π x t.castSucc) (x t.succ)).toReal = 0
  rw [h]
  rfl

lemma trajectory_stage (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy)
    (x : Fin (horizon n + 1) → St n m)
    (hx : (φ.toPOMDP hm).trajProb .s0 π (horizon n) x ≠ 0)
    (k : ℕ) (hk : k < horizon n + 1) : stage (x ⟨k, hk⟩) = k := by
  obtain ⟨h0, ht⟩ := trajectory_support φ hm π x hx
  induction k with
  | zero =>
    have hz : (⟨0, hk⟩ : Fin (horizon n + 1)) = 0 := Fin.ext (by simp)
    rw [hz, h0]
    rfl
  | succ k ih =>
    have hk' : k < horizon n := by omega
    have hs := transition_stage φ hm (x (⟨k, hk'⟩ : Fin (horizon n)).castSucc)
      (x (⟨k, hk'⟩ : Fin (horizon n)).succ)
      ((φ.toPOMDP hm).dec π x (⟨k, hk'⟩ : Fin (horizon n)).castSucc) (ht ⟨k, hk'⟩)
    change stage (x ⟨k + 1, hk⟩) =
      min (stage (x ⟨k, by omega⟩) + 1) (horizon n) at hs
    rw [ih] at hs
    exact hs.trans (Nat.min_eq_left (by omega))

lemma cost_zero_of_stage_ne (φ : QBF n m) (s : St n m) (d : φ.Dec s.obs)
    (hs : stage s ≠ 2 * n + 1) : φ.cost s.obs d = 0 := by
  cases s <;> try rfl
  exact (hs rfl).elim

lemma cost_zero_iff (φ : QBF n m) (s : St n m) (d : φ.Dec s.obs) :
    φ.cost s.obs d = 0 ↔ ∀ i : Fin m, s ≠ .Aend' i := by
  cases s <;> simp [St.obs, QBF.cost]

lemma cost_one_of_unsatisfied (φ : QBF n m) (s : St n m) (d : φ.Dec s.obs)
    (i : Fin m) (hs : s = .Aend' i) : φ.cost s.obs d = 1 := by
  subst s
  rfl

/-- All nonzero cost on a supported trajectory occurs at the terminal clause test. -/
lemma trajectory_cost_at_end (φ : QBF n m) (hm : 0 < m)
    (π : (φ.toPOMDP hm).Policy) (x : Fin (horizon n + 1) → St n m)
    (hx : (φ.toPOMDP hm).trajProb .s0 π (horizon n) x ≠ 0) :
    (φ.toPOMDP hm).trajCost π (horizon n) x =
      φ.cost (x ⟨2 * n + 1, by unfold horizon; omega⟩).obs
        ((φ.toPOMDP hm).dec π x ⟨2 * n + 1, by unfold horizon; omega⟩) := by
  unfold POMDP.trajCost
  change (∑ t, φ.cost (x t).obs ((φ.toPOMDP hm).dec π x t)) = _
  refine Finset.sum_eq_single (s := Finset.univ)
    (f := fun t : Fin (horizon n + 1) ↦
      φ.cost (x t).obs ((φ.toPOMDP hm).dec π x t))
    ⟨2 * n + 1, by unfold horizon; omega⟩ ?_ ?_
  · intro t _ ht
    apply cost_zero_of_stage_ne
    rw [trajectory_stage φ hm π x hx t.val t.isLt]
    intro heq
    apply ht
    exact Fin.ext heq
  · simp

lemma zero_cost_iff_no_unsatisfied_endpoint (φ : QBF n m) (hm : 0 < m)
    (π : (φ.toPOMDP hm).Policy) :
    (φ.toPOMDP hm).expCost .s0 π (horizon n) = 0 ↔
      ∀ x : Fin (horizon n + 1) → St n m,
        (φ.toPOMDP hm).trajProb .s0 π (horizon n) x ≠ 0 →
          ∀ i : Fin m, x ⟨2 * n + 1, by unfold horizon; omega⟩ ≠ .Aend' i := by
  have hn (x : Fin (horizon n + 1) → St n m) :
      0 ≤ (φ.toPOMDP hm).trajProb .s0 π (horizon n) x *
        (φ.toPOMDP hm).trajCost π (horizon n) x :=
    mul_nonneg (trajProb_nonneg (φ.toPOMDP hm) .s0 π (horizon n) x)
      (trajCost_nonneg φ hm π (horizon n) x)
  constructor
  · intro h x hx i hi
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ ↦ hn y)).mp h
    have hcost := (mul_eq_zero.mp (hall x (mem_univ x))).resolve_left hx
    rw [trajectory_cost_at_end φ hm π x hx] at hcost
    exact (cost_zero_iff φ _ _).mp hcost i hi
  · intro h
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : (φ.toPOMDP hm).trajProb .s0 π (horizon n) x = 0
    · rw [hx, zero_mul]
    · rw [trajectory_cost_at_end φ hm π x hx]
      have hc := (cost_zero_iff φ _
        ((φ.toPOMDP hm).dec π x ⟨2 * n + 1, by unfold horizon; omega⟩)).mpr (h x hx)
      rw [hc, mul_zero]

lemma paired_product_lower (n : ℕ) (w : ℕ → ℝ) (a : ℝ) (hw : ∀ t, 0 ≤ w t)
    (hzero : w 0 = a) (hodd : ∀ k < n, (2 : ℝ)⁻¹ ≤ w (2 * k + 1))
    (heven : ∀ k < n, w (2 * k + 2) = 1) (hlast : w (2 * n + 1) = 1) :
    a * (2 : ℝ)⁻¹ ^ n ≤ ∏ t : Fin (2 * n + 2), w t := by
  have hp : ∀ k ≤ n, a * (2 : ℝ)⁻¹ ^ k ≤ ∏ t : Fin (2 * k + 1), w t := by
    intro k hk
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
      have ih' := ih (by omega)
      have hk' : k < n := by omega
      have heq : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by omega
      rw [heq, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [heven k hk', mul_one, pow_succ, ← mul_assoc]
      exact mul_le_mul ih' (hodd k hk') (by norm_num)
        (Finset.prod_nonneg (fun t _ ↦ hw t))
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, hlast, mul_one]
  exact hp n le_rfl

lemma trajectory_probability_lower (φ : QBF n m) (hm : 0 < m)
    (π : (φ.toPOMDP hm).Policy) (x : Fin (horizon n + 1) → St n m)
    (hx : (φ.toPOMDP hm).trajProb .s0 π (horizon n) x ≠ 0) :
    (2 : ℝ)⁻¹ ^ n / m ≤ (φ.toPOMDP hm).trajProb .s0 π (horizon n) x := by
  obtain ⟨h0, ht⟩ := trajectory_support φ hm π x hx
  let w : ℕ → ℝ := fun t ↦ if h : t < horizon n then
    (φ.trans hm (x (⟨t, h⟩ : Fin (horizon n)).castSucc)
      ((φ.toPOMDP hm).dec π x (⟨t, h⟩ : Fin (horizon n)).castSucc)
      (x (⟨t, h⟩ : Fin (horizon n)).succ)).toReal else 1
  have hw (t : ℕ) : 0 ≤ w t := by
    dsimp [w]
    split_ifs
    · exact ENNReal.toReal_nonneg
    · norm_num
  have hw0 : w 0 = 1 / (m : ℝ) := by
    dsimp [w]
    rw [dif_pos (by unfold horizon; omega)]
    exact transition_zero_stage φ hm _ _ _ (ht ⟨0, by unfold horizon; omega⟩)
      (trajectory_stage φ hm π x hx 0 (by unfold horizon; omega))
  have hwo (k : ℕ) (hk : k < n) : (2 : ℝ)⁻¹ ≤ w (2 * k + 1) := by
    dsimp [w]
    rw [dif_pos (by unfold horizon; omega)]
    exact transition_odd_lower φ hm _ _ _ (ht ⟨2 * k + 1, by unfold horizon; omega⟩)
      k hk (trajectory_stage φ hm π x hx _ _)
  have hwe (k : ℕ) (hk : k < n) : w (2 * k + 2) = 1 := by
    dsimp [w]
    rw [dif_pos (by unfold horizon; omega)]
    exact transition_even_one φ hm _ _ _ (ht ⟨2 * k + 2, by unfold horizon; omega⟩)
      k (trajectory_stage φ hm π x hx _ _)
  have hwl : w (2 * n + 1) = 1 := by
    dsimp [w]
    rw [dif_pos (by unfold horizon; omega)]
    exact transition_final_one φ hm _ _ _ (ht ⟨2 * n + 1, by unfold horizon; omega⟩)
      (trajectory_stage φ hm π x hx _ _)
  have heq : (φ.toPOMDP hm).trajProb .s0 π (horizon n) x =
      ∏ t : Fin (horizon n), w t := by
    unfold POMDP.trajProb
    rw [h0]
    simp only [ite_true, one_mul]
    apply Finset.prod_congr rfl
    intro t _
    dsimp [w]
    rw [dif_pos t.isLt]
    rfl
  rw [heq, show (2 : ℝ)⁻¹ ^ n / m = 1 / (m : ℝ) * (2 : ℝ)⁻¹ ^ n by ring]
  exact paired_product_lower n w (1 / (m : ℝ)) hw hw0 hwo hwe hwl

end MDPStages

/-- §4, proof of Theorem 6 (p. 449): if, under policy `π`, some trajectory of positive probability
is at `A′_{i,n+1}` at time `2n + 1`, then the expected cost is at least `2^{−n}/m`. -/
theorem solution {n m : ℕ} (φ : QBF n m) (hm : 0 < m)
    (_hqsat : φ.IsPaperQSAT)
    (π : (φ.toPOMDP hm).Policy) (i : Fin m) (x : Fin (horizon n + 1) → St n m)
    (hx : 0 < (φ.toPOMDP hm).trajProb .s0 π (horizon n) x)
    (hend : x ⟨2 * n + 1, by unfold horizon; omega⟩ = .Aend' i) :
    (2 : ℝ)⁻¹ ^ n / m ≤ (φ.toPOMDP hm).expCost .s0 π (horizon n) := by
  have hx' := ne_of_gt hx
  have hc : (φ.toPOMDP hm).trajCost π (horizon n) x = 1 := by
    rw [MDPStages.trajectory_cost_at_end φ hm π x hx']
    exact MDPStages.cost_one_of_unsatisfied φ _ _ i hend
  have hsum : (φ.toPOMDP hm).trajProb .s0 π (horizon n) x *
      (φ.toPOMDP hm).trajCost π (horizon n) x ≤
      (φ.toPOMDP hm).expCost .s0 π (horizon n) :=
    Finset.single_le_sum
      (fun y _ ↦ mul_nonneg (MDPStages.trajProb_nonneg (φ.toPOMDP hm) .s0 π (horizon n) y)
        (MDPStages.trajCost_nonneg φ hm π (horizon n) y)) (Finset.mem_univ x)
  rw [hc, mul_one] at hsum
  exact (MDPStages.trajectory_probability_lower φ hm π x hx').trans hsum
