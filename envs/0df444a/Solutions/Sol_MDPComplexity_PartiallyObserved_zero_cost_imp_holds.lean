-- Prove2me | solution 1 for MDPComplexity.PartiallyObserved.zero_cost_imp_holds
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T06:19:50.54077+00:00
-- url     : https://prove2.me/submissions/54aabf83-9ff7-4833-b332-fb4cb4f649ab

import Definitions.Def_MDPComplexity_PartiallyObserved_Construction

open Finset MDPComplexity.PartiallyObserved

namespace MDPZeroCostImpHolds

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

/-- Canonical all-primed trajectory for clause `i` and truth assignment `v`. -/
def primedTraj (i : Fin m) (v : Fin n → Bool) (t : Fin (horizon n + 1)) : St n m :=
  if h0 : t.val = 0 then .s0
  else if h : t.val ≤ 2 * n then
    let k : Fin n := ⟨(t.val - 1) / 2, by omega⟩
    if (t.val - 1) % 2 = 0 then .A' i k
    else if v k then .T' i k else .F' i k
  else if t.val = 2 * n + 1 then .Aend' i
  else .sink

/-- Observation sequence along an all-primed trajectory up to time `2n` (independent of `i`). -/
def primedObs (v : Fin n → Bool) (t : ℕ) : Obs n m :=
  if h0 : t = 0 then .s0
  else if h : t ≤ 2 * n then
    let k : Fin n := ⟨(t - 1) / 2, by omega⟩
    if (t - 1) % 2 = 0 then .A k
    else if v k then .T' k else .F' k
  else .sink

/-- All-primed observation history prior to choosing variable `j`. -/
def primedHist (v : Fin n → Bool) (j : Fin n) : List (Obs n m) :=
  List.ofFn (fun t : Fin (2 * j.val + 1) ↦ primedObs v t.val)

lemma primedTraj_zero (i : Fin m) (v : Fin n → Bool) :
    primedTraj i v 0 = .s0 := rfl

lemma primedTraj_odd (i : Fin m) (v : Fin n → Bool) (j : Fin n) :
    primedTraj i v ⟨2 * j.val + 1, by unfold horizon; omega⟩ = .A' i j := by
  unfold primedTraj
  dsimp
  have h2 : 2 * j.val + 1 ≤ 2 * n := by omega
  have h3 : 2 * j.val % 2 = 0 := by omega
  rw [dif_pos h2, if_pos h3]
  congr 1
  exact Fin.ext (by dsimp; omega)

lemma primedTraj_even (i : Fin m) (v : Fin n → Bool) (j : Fin n) :
    primedTraj i v ⟨2 * j.val + 2, by unfold horizon; omega⟩ =
      if v j then .T' i j else .F' i j := by
  unfold primedTraj
  dsimp
  have h2 : 2 * j.val + 2 ≤ 2 * n := by omega
  have h3 : ¬ ((2 * j.val + 1) % 2 = 0) := by omega
  rw [dif_pos h2, if_neg h3]
  have hk : (⟨(2 * j.val + 1) / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
  rw [hk]

lemma primedTraj_end (i : Fin m) (v : Fin n → Bool) :
    primedTraj i v ⟨2 * n + 1, by unfold horizon; omega⟩ = .Aend' i := by
  unfold primedTraj
  dsimp
  have h2 : ¬ (2 * n + 1 ≤ 2 * n) := by omega
  rw [dif_neg h2, if_pos rfl]

lemma primedTraj_sink (i : Fin m) (v : Fin n → Bool) :
    primedTraj i v ⟨2 * n + 2, by unfold horizon; omega⟩ = .sink := by
  unfold primedTraj
  dsimp
  have h2 : ¬ (2 * n + 2 ≤ 2 * n) := by omega
  have h3 : ¬ (2 * n + 2 = 2 * n + 1) := by omega
  rw [dif_neg h2, if_neg h3]

lemma primedTraj_lvlA' (i : Fin m) (v : Fin n → Bool) (k : ℕ) (hk : k ≤ n) :
    primedTraj i v ⟨2 * k + 1, by unfold horizon; omega⟩ = lvlA' i k := by
  unfold lvlA'
  split_ifs with h
  · exact primedTraj_odd i v ⟨k, h⟩
  · have hkn : k = n := by omega
    subst hkn
    exact primedTraj_end i v

lemma primedTraj_obs (i : Fin m) (v : Fin n → Bool) (t : Fin (horizon n + 1))
    (ht : t.val ≤ 2 * n) :
    (primedTraj i v t).obs = primedObs v t.val := by
  unfold primedTraj primedObs
  dsimp
  split_ifs <;> rfl

lemma obsHist_primedTraj (φ : QBF n m) (hm : 0 < m) (i : Fin m)
    (v : Fin n → Bool) (j : Fin n) :
    (φ.toPOMDP hm).obsHist (primedTraj i v) ⟨2 * j.val + 1, by unfold horizon; omega⟩ =
      primedHist v j := by
  unfold POMDP.obsHist primedHist
  congr 1
  funext t
  exact primedTraj_obs i v (Fin.castLE (by unfold horizon; omega) t) (by dsimp; omega)

lemma primedObs_congr {v₁ v₂ : Fin n → Bool} {j : Fin n}
    (h : ∀ k : Fin n, k.val < j.val → v₁ k = v₂ k) {t : ℕ} (ht : t < 2 * j.val + 1) :
    primedObs (m := m) v₁ t = primedObs (m := m) v₂ t := by
  unfold primedObs
  by_cases h1 : t = 0
  · simp [h1]
  · by_cases h2 : t ≤ 2 * n
    · rw [dif_neg h1, dif_neg h1, dif_pos h2, dif_pos h2]
      dsimp
      rw [h ⟨(t - 1) / 2, by omega⟩ (by dsimp; omega)]
    · simp [h1, h2]

lemma primedHist_congr {v₁ v₂ : Fin n → Bool} {j : Fin n}
    (h : ∀ k : Fin n, k.val < j.val → v₁ k = v₂ k) :
    primedHist (m := m) v₁ j = primedHist (m := m) v₂ j :=
  congrArg List.ofFn (funext fun t ↦ primedObs_congr h t.isLt)

def decABool : (b : Bool) → DecA b → Bool
  | true, d => d
  | false, _ => false

def policyChoice (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy)
    (v : Fin n → Bool) (j : Fin n) : Bool :=
  decABool (φ.q j) (π (primedHist v j) (.A j))

lemma policyChoice_congr (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy)
    {v₁ v₂ : Fin n → Bool} {j : Fin n}
    (h : ∀ k : Fin n, k.val < j.val → v₁ k = v₂ k) :
    policyChoice φ hm π v₁ j = policyChoice φ hm π v₂ j := by
  unfold policyChoice
  rw [primedHist_congr h]

def ConsistentUpTo (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy)
    (k : ℕ) (v : Fin n → Bool) : Prop :=
  ∀ j : Fin n, j.val < k → φ.q j = true → v j = policyChoice φ hm π v j

lemma consistentUpTo_zero (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy)
    (v : Fin n → Bool) : ConsistentUpTo φ hm π 0 v := by
  intro j hj
  omega

lemma consistentUpTo_update (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy)
    (k : ℕ) (hk : k < n) (v : Fin n → Bool) (b : Bool)
    (hc : ConsistentUpTo φ hm π k v)
    (hb : φ.q ⟨k, hk⟩ = true → b = policyChoice φ hm π v ⟨k, hk⟩) :
    ConsistentUpTo φ hm π (k + 1) (Function.update v ⟨k, hk⟩ b) := by
  intro j hj hq
  have hprefix : ∀ r : Fin n, r.val < j.val → Function.update v ⟨k, hk⟩ b r = v r := by
    intro r hr
    have hrne : r ≠ ⟨k, hk⟩ := fun h ↦ by
      have : r.val = k := congrArg Fin.val h
      omega
    exact Function.update_of_ne hrne b v
  rw [policyChoice_congr φ hm π hprefix]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
  · have hjne : j ≠ ⟨k, hk⟩ := fun h ↦ by
      have : j.val = k := congrArg Fin.val h
      omega
    rw [Function.update_of_ne hjne]
    exact hc j hlt hq
  · have hjeq : j = ⟨k, hk⟩ := Fin.ext heq
    subst hjeq
    rw [Function.update_self]
    exact hb hq

lemma stepA_primed_ne_zero (b : Bool) (d : DecA b) (i : Fin m) (j : Fin n) (val : Bool)
    (h : b = true → val = decABool b d) :
    stepA b d (.T' i j) (.F' i j) (if val then .T' i j else .F' i j) ≠ 0 := by
  cases b with
  | false =>
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨val, PMF.mem_support_uniformOfFintype val, rfl⟩
  | true =>
    have hval : val = d := h rfl
    subst hval
    cases val <;> simp [stepA]

lemma trans_primed_zero_ne_zero (φ : QBF n m) (hm : 0 < m)
    (i : Fin m) (s : St n m) (d : φ.Dec s.obs) (hs : s = .s0) :
    φ.trans hm s d (lvlA' i 0) ≠ 0 := by
  subst hs
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨i, PMF.mem_support_uniformOfFintype i, rfl⟩

lemma trans_primed_odd_ne_zero (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy)
    (i : Fin m) (v : Fin n → Bool) (j : Fin n)
    (hj : φ.q j = true → v j = policyChoice φ hm π v j)
    (hist : List (Obs n m)) (hhist : hist = primedHist v j)
    (s : St n m) (hs : s = .A' i j) :
    φ.trans hm s (π hist s.obs) (if v j then .T' i j else .F' i j) ≠ 0 := by
  subst hs hhist
  exact stepA_primed_ne_zero (φ.q j) (π (primedHist v j) (.A j)) i j (v j) hj

lemma trans_primed_even_ne_zero (φ : QBF n m) (hm : 0 < m)
    (i : Fin m) (j : Fin n) (b : Bool)
    (hnot : (j, b) ∉ φ.clause i)
    (s : St n m) (d : φ.Dec s.obs)
    (hs : s = if b then .T' i j else .F' i j) :
    φ.trans hm s d (lvlA' i (j.val + 1)) ≠ 0 := by
  cases b <;> subst hs <;> simp [QBF.trans, hnot]

lemma trans_primed_end_ne_zero (φ : QBF n m) (hm : 0 < m)
    (i : Fin m) (s : St n m) (d : φ.Dec s.obs) (hs : s = .Aend' i) :
    φ.trans hm s d .sink ≠ 0 := by
  subst hs
  simp [QBF.trans]

lemma trans_primedTraj_ne_zero (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy)
    (i : Fin m) (v : Fin n → Bool) (hc : ConsistentUpTo φ hm π n v)
    (hunsat : ∀ j : Fin n, (j, v j) ∉ φ.clause i)
    (t : Fin (horizon n)) :
    φ.trans hm (primedTraj i v t.castSucc)
      ((φ.toPOMDP hm).dec π (primedTraj i v) t.castSucc)
      (primedTraj i v t.succ) ≠ 0 := by
  by_cases ht0 : t.val = 0
  · have htc : t.castSucc = 0 := Fin.ext ht0
    have hts : t.succ = ⟨2 * 0 + 1, by unfold horizon; omega⟩ := Fin.ext (by dsimp; omega)
    rw [hts, primedTraj_lvlA' i v 0 (Nat.zero_le n)]
    exact trans_primed_zero_ne_zero φ hm i (primedTraj i v t.castSucc)
      ((φ.toPOMDP hm).dec π (primedTraj i v) t.castSucc)
      (by rw [htc, primedTraj_zero])
  · by_cases htle : t.val ≤ 2 * n
    · by_cases hodd : (t.val - 1) % 2 = 0
      · let j : Fin n := ⟨(t.val - 1) / 2, by omega⟩
        have htc : t.castSucc = ⟨2 * j.val + 1, by unfold horizon; omega⟩ :=
          Fin.ext (by dsimp [j]; omega)
        have hts : t.succ = ⟨2 * j.val + 2, by unfold horizon; omega⟩ :=
          Fin.ext (by dsimp [j]; omega)
        rw [hts, primedTraj_even]
        exact trans_primed_odd_ne_zero φ hm π i v j (hc j j.isLt)
          ((φ.toPOMDP hm).obsHist (primedTraj i v) t.castSucc)
          (by rw [htc]; exact obsHist_primedTraj φ hm i v j)
          (primedTraj i v t.castSucc)
          (by rw [htc]; exact primedTraj_odd i v j)
      · let j : Fin n := ⟨(t.val - 1) / 2, by omega⟩
        have htc : t.castSucc = ⟨2 * j.val + 2, by unfold horizon; omega⟩ :=
          Fin.ext (by dsimp [j]; omega)
        have hts : t.succ = ⟨2 * (j.val + 1) + 1, by unfold horizon; omega⟩ :=
          Fin.ext (by dsimp [j]; omega)
        rw [hts, primedTraj_lvlA' i v (j.val + 1) (by omega)]
        exact trans_primed_even_ne_zero φ hm i j (v j) (hunsat j)
          (primedTraj i v t.castSucc)
          ((φ.toPOMDP hm).dec π (primedTraj i v) t.castSucc)
          (by rw [htc]; exact primedTraj_even i v j)
    · have htlt : t.val < 2 * n + 2 := t.isLt
      have htend : t.val = 2 * n + 1 := by omega
      have htc : t.castSucc = ⟨2 * n + 1, by unfold horizon; omega⟩ := Fin.ext htend
      have hts : t.succ = ⟨2 * n + 2, by unfold horizon; omega⟩ := Fin.ext (by dsimp; omega)
      rw [hts, primedTraj_sink]
      exact trans_primed_end_ne_zero φ hm i (primedTraj i v t.castSucc)
        ((φ.toPOMDP hm).dec π (primedTraj i v) t.castSucc)
        (by rw [htc]; exact primedTraj_end i v)

lemma trajProb_primedTraj_ne_zero (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy)
    (i : Fin m) (v : Fin n → Bool) (hc : ConsistentUpTo φ hm π n v)
    (hunsat : ∀ j : Fin n, (j, v j) ∉ φ.clause i) :
    (φ.toPOMDP hm).trajProb .s0 π (horizon n) (primedTraj i v) ≠ 0 := by
  unfold POMDP.trajProb
  rw [primedTraj_zero, if_pos rfl, one_mul]
  rw [Finset.prod_ne_zero_iff]
  intro t _
  have htr := trans_primedTraj_ne_zero φ hm π i v hc hunsat t
  exact ENNReal.toReal_ne_zero.mpr ⟨htr, PMF.apply_ne_top _ _⟩

lemma sat_of_consistentUpTo_n (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy)
    (h0 : (φ.toPOMDP hm).expCost .s0 π (horizon n) = 0)
    (v : Fin n → Bool) (hc : ConsistentUpTo φ hm π n v) :
    φ.Sat v := by
  intro i
  by_contra hnsat
  have hunsat : ∀ j : Fin n, (j, v j) ∉ φ.clause i := by
    intro j hmem
    exact hnsat ⟨(j, v j), hmem, rfl⟩
  have hprob := trajProb_primedTraj_ne_zero φ hm π i v hc hunsat
  have hnoend := (zero_cost_iff_no_unsatisfied_endpoint φ hm π).mp h0 (primedTraj i v) hprob i
  exact hnoend (primedTraj_end i v)

lemma holdsFrom_of_consistentUpTo (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy)
    (h0 : (φ.toPOMDP hm).expCost .s0 π (horizon n) = 0) :
    ∀ d k (v : Fin n → Bool), n - k = d → ConsistentUpTo φ hm π k v → φ.holdsFrom k v := by
  intro d
  induction d with
  | zero =>
    intro k v hd hc
    have hnk : ¬ (k < n) := by omega
    rw [QBF.holdsFrom, dif_neg hnk]
    have hcn : ConsistentUpTo φ hm π n v := fun j hj ↦ hc j (by omega)
    exact sat_of_consistentUpTo_n φ hm π h0 v hcn
  | succ d ih =>
    intro k v hd hc
    have hk : k < n := by omega
    rw [QBF.holdsFrom, dif_pos hk]
    by_cases hq : φ.q ⟨k, hk⟩ = true
    · rw [if_pos hq]
      refine ⟨policyChoice φ hm π v ⟨k, hk⟩, ?_⟩
      exact ih (k + 1) _ (by omega)
        (consistentUpTo_update φ hm π k hk v _ hc (fun _ ↦ rfl))
    · rw [if_neg hq]
      intro b
      exact ih (k + 1) _ (by omega)
        (consistentUpTo_update φ hm π k hk v b hc (fun h ↦ (hq h).elim))

end MDPZeroCostImpHolds

/-- §4, proof of Theorem 6 (p. 449), "only if": if some observation-history policy has expected
cost zero over the horizon `2n + 2`, the quantified formula is true. -/
theorem solution {n m : ℕ} (φ : QBF n m) (hm : 0 < m)
    (_hqsat : φ.IsPaperQSAT)
    (π : (φ.toPOMDP hm).Policy)
    (h0 : (φ.toPOMDP hm).expCost .s0 π (horizon n) = 0) :
    φ.holds :=
  MDPZeroCostImpHolds.holdsFrom_of_consistentUpTo φ hm π h0 n 0 (fun _ ↦ false)
    (Nat.sub_zero n) (MDPZeroCostImpHolds.consistentUpTo_zero φ hm π _)
