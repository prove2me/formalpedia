-- Prove2me | solution 1 for MDPComplexity.CircuitValue.theorem1_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T17:35:22.177951+00:00
-- url     : https://prove2.me/submissions/c6560b01-13c1-4eac-b453-3536b442da02

import Mathlib
import Definitions.Def_MDPComplexity_CircuitValue_Model
import Definitions.Def_MDPComplexity_CircuitValue_Circuit
import Definitions.Def_MDPComplexity_CircuitValue_Reduction

open MDPComplexity.CircuitValue Finset

theorem cv_zero_iff {S : Type} [Fintype S] [DecidableEq S] (M : MDP S)
    (hc : ∀ s i t, 0 ≤ M.c s i t) (s₀ : S) (δ : M.Policy) (T : ℕ) :
    M.expCost s₀ δ T = 0 ↔ ∀ x : Fin (T + 1) → S, 0 < M.trajProb s₀ δ T x →
        ∀ t : Fin (T + 1), M.c (x t) (δ (x t) (t : ℕ)) (t : ℕ) = 0 := by
  have hp : ∀ x, 0 ≤ M.trajProb s₀ δ T x := fun x => by
    unfold MDP.trajProb
    apply mul_nonneg (by split_ifs <;> norm_num)
    exact Finset.prod_nonneg (fun t _ => M.p_nonneg _ _ _ _)
  have hcost : ∀ x, 0 ≤ M.trajCost δ T x := fun x => Finset.sum_nonneg (fun t _ => hc _ _ _)
  unfold MDP.expCost
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_nonneg (hp x) (hcost x))]
  constructor
  · intro h x hx t
    have h1 := h x (Finset.mem_univ _)
    have h2 : M.trajCost δ T x = 0 := by
      rcases mul_eq_zero.1 h1 with h3 | h3
      · linarith
      · exact h3
    unfold MDP.trajCost at h2
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hc _ _ _)] at h2
    exact h2 t (Finset.mem_univ _)
  · intro h x _
    rcases (hp x).lt_or_eq with hx | hx
    · have : M.trajCost δ T x = 0 := Finset.sum_eq_zero (fun t _ => h x hx t)
      rw [this, mul_zero]
    · rw [← hx, zero_mul]

section
variable {k : ℕ}

theorem cv_ff (C : Circuit k) (i : Fin k) (h : C.a i = Op.ff) : C.val i = false := by
  rw [Circuit.val]; split <;> simp_all
theorem cv_tt (C : Circuit k) (i : Fin k) (h : C.a i = Op.tt) : C.val i = true := by
  rw [Circuit.val]; split <;> simp_all
theorem cv_and (C : Circuit k) (i : Fin k) (h : C.a i = Op.and) :
    C.val i = (C.val (C.b i) && C.val (C.c i)) := by
  rw [Circuit.val]; split <;> simp_all
theorem cv_or (C : Circuit k) (i : Fin k) (h : C.a i = Op.or) :
    C.val i = (C.val (C.b i) || C.val (C.c i)) := by
  rw [Circuit.val]; split <;> simp_all

theorem cv_cost_nonneg (C : Circuit k) (s : Option (Fin k)) : 0 ≤ C.cost s := by
  cases s with
  | none => simp [Circuit.cost]
  | some i => simp only [Circuit.cost]; split_ifs <;> norm_num

theorem cv_hc (C : Circuit k) : ∀ s i t, 0 ≤ C.toMDP.c s i t :=
  fun s _ _ => cv_cost_nonneg C s

theorem cv_expCost_nonneg (C : Circuit k) (s₀ : Option (Fin k)) (δ : C.toMDP.Policy) (T : ℕ) :
    0 ≤ C.toMDP.expCost s₀ δ T := by
  unfold MDP.expCost
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg
  · unfold MDP.trajProb
    apply mul_nonneg (by split_ifs <;> norm_num)
    exact Finset.prod_nonneg (fun t _ => C.toMDP.p_nonneg _ _ _ _)
  · exact Finset.sum_nonneg (fun t _ => cv_hc C _ _ _)
end

section
variable {k : ℕ}

def cvPolT (C : Circuit k) : C.toMDP.Policy := fun s _ =>
  match s with
  | none => (⟨0, C.numDec_pos none⟩ : Fin (C.numDec none))
  | some i =>
    if h : C.a i = Op.or ∧ C.val (C.b i) = false then
      (⟨1, by simp [Circuit.numDec, h.1]⟩ : Fin (C.numDec (some i)))
    else ⟨0, C.numDec_pos (some i)⟩

theorem cv_stepT (C : Circuit k) (s s' : Option (Fin k)) (t : ℕ)
    (hs : s = none ∨ ∃ i, s = some i ∧ C.val i = true)
    (h : C.trans s (Fin.val (cvPolT C s t)) s' ≠ 0) :
    s' = none ∨ ∃ i, s' = some i ∧ C.val i = true := by
  rcases hs with rfl | ⟨i, rfl, hi⟩
  · left
    simp only [Circuit.trans] at h
    by_contra hn; exact h (if_neg hn)
  · cases ha : C.a i with
    | ff => rw [cv_ff C i ha] at hi; exact absurd hi (by simp)
    | tt =>
      left
      simp only [Circuit.trans, ha] at h
      by_contra hn; exact h (if_neg hn)
    | and =>
      rw [cv_and C i ha] at hi
      simp only [Bool.and_eq_true] at hi
      right
      simp only [Circuit.trans, ha] at h
      by_cases h1 : s' = some (C.b i)
      · exact ⟨_, h1, hi.1⟩
      · by_cases h2 : s' = some (C.c i)
        · exact ⟨_, h2, hi.2⟩
        · simp [h1, h2] at h
    | or =>
      rw [cv_or C i ha] at hi
      right
      by_cases hb : C.val (C.b i) = false
      · have hd : Fin.val (cvPolT C (some i) t) = 1 := by
          simp [cvPolT, ha, hb]
        rw [hd] at h
        simp only [Circuit.trans, ha] at h
        have hc : C.val (C.c i) = true := by simpa [hb] using hi
        by_cases h2 : s' = some (C.c i)
        · exact ⟨_, h2, hc⟩
        · simp [h2] at h
      · have hd : Fin.val (cvPolT C (some i) t) = 0 := by
          simp [cvPolT, ha, hb]
        rw [hd] at h
        simp only [Circuit.trans, ha] at h
        by_cases h2 : s' = some (C.b i)
        · exact ⟨_, h2, by simpa using hb⟩
        · simp [h2] at h

theorem cv_invT [NeZero k] (C : Circuit k) (hv : C.value = true) (x : Fin (k+1) → Option (Fin k))
    (hx : 0 < C.toMDP.trajProb (some (Circuit.lastIdx k)) (cvPolT C) k x) :
    ∀ n (hn : n < k + 1), x ⟨n, hn⟩ = none ∨ ∃ i, x ⟨n, hn⟩ = some i ∧ C.val i = true := by
  unfold MDP.trajProb at hx
  have hx0 : x 0 = some (Circuit.lastIdx k) := by
    by_contra hne; rw [if_neg hne, zero_mul] at hx; exact lt_irrefl _ hx
  rw [if_pos hx0, one_mul] at hx
  have hprod := Finset.prod_ne_zero_iff.1 hx.ne'
  intro n
  induction n with
  | zero =>
    intro hn
    right
    refine ⟨_, ?_, hv⟩
    rw [← hx0]; exact congrArg x (Fin.ext (by simp))
  | succ n ih =>
    intro hn
    have hf : C.trans (x ⟨n, by omega⟩) (Fin.val (cvPolT C (x ⟨n, by omega⟩) n)) (x ⟨n+1, hn⟩) ≠ 0 :=
      hprod ⟨n, by omega⟩ (Finset.mem_univ _)
    exact cv_stepT C _ _ n (ih (by omega)) hf

theorem cv_exists_zero [NeZero k] (C : Circuit k) (h : C.value = true) :
    ∃ δ : C.toMDP.Policy, C.toMDP.expCost (some (Circuit.lastIdx k)) δ k = 0 := by
  refine ⟨cvPolT C, (cv_zero_iff _ (cv_hc C) _ _ _).2 ?_⟩
  intro x hx t
  have := cv_invT C h x hx t.val t.isLt
  show C.cost (x t) = 0
  rcases this with h1 | ⟨i, h1, hi⟩
  · rw [show x t = none from h1]; rfl
  · rw [show x t = some i from h1]
    simp only [Circuit.cost]
    rw [if_neg]
    intro ha; rw [cv_ff C i ha] at hi; exact absurd hi (by simp)
end

section
variable {k : ℕ}

def cvNext (C : Circuit k) (δ : C.toMDP.Policy) (s : Option (Fin k)) (t : ℕ) : Option (Fin k) :=
  match s with
  | none => none
  | some i =>
    match C.a i with
    | Op.ff => none
    | Op.tt => none
    | Op.and => if C.val (C.b i) = false then some (C.b i) else some (C.c i)
    | Op.or => if Fin.val (δ (some i) t : Fin (C.numDec (some i))) = 0 then some (C.b i)
        else some (C.c i)

def cvY [NeZero k] (C : Circuit k) (δ : C.toMDP.Policy) : ℕ → Option (Fin k)
  | 0 => some (Circuit.lastIdx k)
  | t + 1 => cvNext C δ (cvY C δ t) t

theorem cv_half (C : Circuit k) (δ : C.toMDP.Policy) (s : Option (Fin k)) (t : ℕ) :
    1 / 2 ≤ C.trans s (Fin.val (δ s t : Fin (C.numDec s))) (cvNext C δ s t) := by
  cases s with
  | none => simp [Circuit.trans, cvNext]; norm_num
  | some i =>
    cases ha : C.a i with
    | ff => simp [Circuit.trans, cvNext, ha]; norm_num
    | tt => simp [Circuit.trans, cvNext, ha]; norm_num
    | and =>
      simp only [Circuit.trans, cvNext, ha]
      split_ifs <;> simp_all <;> norm_num
    | or =>
      simp only [Circuit.trans, cvNext, ha]
      split_ifs <;> simp_all <;> norm_num

theorem cv_hit [NeZero k] (C : Circuit k) (δ : C.toMDP.Policy) (hv : C.value = false) :
    ∀ t, (∃ t' ≤ t, ∃ i, cvY C δ t' = some i ∧ C.a i = Op.ff) ∨
      (∃ i, cvY C δ t = some i ∧ C.val i = false ∧ i.val + t ≤ k - 1) := by
  intro t
  induction t with
  | zero =>
    right
    exact ⟨Circuit.lastIdx k, rfl, hv, by simp [Circuit.lastIdx]⟩
  | succ t ih =>
    rcases ih with ⟨t', ht', h⟩ | ⟨i, h, hi, hle⟩
    · exact Or.inl ⟨t', by omega, h⟩
    · have hy : cvY C δ (t + 1) = cvNext C δ (some i) t := by
        show cvNext C δ (cvY C δ t) t = _; rw [h]
      cases ha : C.a i with
      | ff => exact Or.inl ⟨t, by omega, i, h, ha⟩
      | tt => rw [cv_tt C i ha] at hi; exact absurd hi (by simp)
      | and =>
        rw [cv_and C i ha] at hi
        have hb := C.b_lt i (Or.inl ha)
        have hc := C.c_lt i (Or.inl ha)
        right
        rw [hy]
        simp only [cvNext, ha]
        split_ifs with h1
        · exact ⟨_, rfl, h1, by rw [Fin.lt_def] at hb; omega⟩
        · refine ⟨_, rfl, ?_, by rw [Fin.lt_def] at hc; omega⟩
          simpa [h1] using hi
      | or =>
        rw [cv_or C i ha] at hi
        simp only [Bool.or_eq_false_iff] at hi
        have hb := C.b_lt i (Or.inr ha)
        have hc := C.c_lt i (Or.inr ha)
        right
        rw [hy]
        simp only [cvNext, ha]
        split_ifs with h1
        · exact ⟨_, rfl, hi.1, by rw [Fin.lt_def] at hb; omega⟩
        · exact ⟨_, rfl, hi.2, by rw [Fin.lt_def] at hc; omega⟩

theorem cv_lb [NeZero k] (C : Circuit k) (hv : C.value = false) (δ : C.toMDP.Policy) :
    (1 / 2 : ℝ) ^ k ≤ C.toMDP.expCost (some (Circuit.lastIdx k)) δ k := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  let x : Fin (k + 1) → Option (Fin k) := fun t => cvY C δ t.val
  have hP : (1 / 2 : ℝ) ^ k ≤ C.toMDP.trajProb (some (Circuit.lastIdx k)) δ k x := by
    unfold MDP.trajProb
    have hx0 : x 0 = some (Circuit.lastIdx k) := by
      show cvY C δ (0 : Fin (k+1)).val = _
      rw [Fin.val_zero]; rfl
    rw [if_pos hx0, one_mul]
    calc (1 / 2 : ℝ) ^ k = ∏ _t : Fin k, (1 / 2 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod (fun _ _ => by norm_num)
        intro t _
        exact cv_half C δ (cvY C δ t.val) t.val
  have hC : 1 ≤ C.toMDP.trajCost δ k x := by
    rcases cv_hit C δ hv k with ⟨t', ht', i, h, ha⟩ | ⟨i, _, _, hle⟩
    · unfold MDP.trajCost
      have hmem := Finset.single_le_sum (f := fun t : Fin (k + 1) =>
        C.toMDP.c (x t) (δ (x t) (t : ℕ)) (t : ℕ)) (fun t _ => cv_hc C _ _ _)
        (Finset.mem_univ ⟨t', by omega⟩)
      refine le_trans ?_ hmem
      show 1 ≤ C.cost (cvY C δ t')
      rw [h]; simp [Circuit.cost, ha]
    · have := i.isLt; omega
  have hsum := Finset.single_le_sum (f := fun y : Fin (k + 1) → Option (Fin k) =>
      C.toMDP.trajProb (some (Circuit.lastIdx k)) δ k y * C.toMDP.trajCost δ k y)
    (fun y _ => by
      apply mul_nonneg
      · unfold MDP.trajProb
        apply mul_nonneg (by split_ifs <;> norm_num)
        exact Finset.prod_nonneg (fun t _ => C.toMDP.p_nonneg _ _ _ _)
      · exact Finset.sum_nonneg (fun t _ => cv_hc C _ _ _)) (Finset.mem_univ x)
  unfold MDP.expCost
  refine le_trans ?_ hsum
  have : (0:ℝ) ≤ (1/2)^k := by positivity
  calc (1 / 2 : ℝ) ^ k = (1/2)^k * 1 := by ring
    _ ≤ _ := mul_le_mul hP hC (by norm_num) (le_trans this hP)
end


theorem solution {k : ℕ} [NeZero k] (C : Circuit k) :
    C.toMDP.optCost (some (Circuit.lastIdx k)) k ≤ 0 ↔ C.value = true := by
  have hne : Nonempty C.toMDP.Policy := ⟨fun s _ => (⟨0, C.numDec_pos s⟩ : Fin (C.numDec s))⟩
  unfold MDP.optCost
  constructor
  · intro h
    by_contra hv
    have hlb : (1 / 2 : ℝ) ^ k ≤ ⨅ δ : C.toMDP.Policy, C.toMDP.expCost (some (Circuit.lastIdx k)) δ k :=
      le_ciInf (fun δ => cv_lb C (by simpa using hv) δ)
    have : (0:ℝ) < (1/2)^k := by positivity
    linarith
  · intro hv
    obtain ⟨δ, hδ⟩ := cv_exists_zero C hv
    have hbdd : BddBelow (Set.range fun δ : C.toMDP.Policy =>
        C.toMDP.expCost (some (Circuit.lastIdx k)) δ k) :=
      ⟨0, by rintro _ ⟨δ', rfl⟩; exact cv_expCost_nonneg C _ δ' k⟩
    exact (ciInf_le hbdd δ).trans (le_of_eq hδ)
