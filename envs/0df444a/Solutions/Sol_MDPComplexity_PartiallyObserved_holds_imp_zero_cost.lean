-- Prove2me | solution 1 for MDPComplexity.PartiallyObserved.holds_imp_zero_cost
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T06:10:37.804036+00:00
-- url     : https://prove2.me/submissions/71686386-d020-44cc-a851-5107507042ad

import Definitions.Def_MDPComplexity_PartiallyObserved_Construction

open Finset MDPComplexity.PartiallyObserved

namespace MDPHoldsImpZeroCost

variable {n m : ℕ}

lemma lvlA'_eq_iff (i j : Fin m) (k : ℕ) :
    lvlA' (n := n) i k = lvlA' j k ↔ i = j := by
  unfold lvlA'
  split_ifs <;> simp

lemma lvlA'_ne_lvlA (i j : Fin m) (k l : ℕ) :
    lvlA' (n := n) i k ≠ lvlA (n := n) j l := by
  unfold lvlA' lvlA
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

/-- Extract the truth value from a `T/T'/F/F'` observation. -/
def isTrueObs : Obs n m → Bool
  | .T _ | .T' _ => true
  | _ => false

/-- Read the assignment of variable `k` from an observation history `hist`. -/
def histAssign (hist : List (Obs n m)) (k : Fin n) : Bool :=
  match hist[2 * k.val + 2]? with
  | some z => isTrueObs z
  | none => false

/-- The truth assignment realized along a trajectory `x`. -/
def trajAssign (x : Fin (horizon n + 1) → St n m) (k : Fin n) : Bool :=
  isTrueObs (x ⟨2 * k.val + 2, by unfold horizon; omega⟩).obs

/-- Prefix of an assignment `v` up to level `j` (padded with `false` from `j` onwards). -/
def prefixAssign (v : Fin n → Bool) (j : ℕ) (k : Fin n) : Bool :=
  if k.val < j then v k else false

lemma prefixAssign_zero (v : Fin n → Bool) :
    prefixAssign v 0 = fun _ ↦ false := by
  funext k
  simp [prefixAssign]

lemma prefixAssign_n (v : Fin n → Bool) :
    prefixAssign v n = v := by
  funext k
  simp [prefixAssign, k.isLt]

lemma prefixAssign_succ (v : Fin n → Bool) (j : ℕ) (hj : j < n) :
    Function.update (prefixAssign v j) ⟨j, hj⟩ (v ⟨j, hj⟩) = prefixAssign v (j + 1) := by
  funext k
  by_cases hk : k = ⟨j, hj⟩
  · subst hk
    simp [prefixAssign]
  · have hne : k.val ≠ j := fun h ↦ hk (Fin.ext h)
    have hiff : k.val < j ↔ k.val < j + 1 := by omega
    simp [Function.update, hk, prefixAssign, hiff]

lemma histAssign_obsHist (φ : QBF n m) (hm : 0 < m)
    (x : Fin (horizon n + 1) → St n m) (j : Fin n) :
    histAssign ((φ.toPOMDP hm).obsHist x ⟨2 * j.val + 1, by unfold horizon; omega⟩) =
      prefixAssign (trajAssign x) j.val := by
  funext k
  unfold histAssign prefixAssign trajAssign POMDP.obsHist
  rw [List.getElem?_ofFn]
  dsimp
  split_ifs with h1 h2
  · rfl
  · omega
  · omega
  · rfl

open Classical in
noncomputable def winChoice (φ : QBF n m) (j : Fin n) (u : Fin n → Bool) : Bool :=
  if h : ∃ b : Bool, φ.holdsFrom (j.val + 1) (Function.update u j b) then
    Classical.choose h
  else false

noncomputable def winDecA (φ : QBF n m) (j : Fin n) (u : Fin n → Bool) :
    (b : Bool) → DecA b
  | true => winChoice φ j u
  | false => ()

noncomputable def winPolicy (φ : QBF n m) (hm : 0 < m) : (φ.toPOMDP hm).Policy :=
  fun hist z ↦ match z with
  | .A j => winDecA φ j (histAssign hist) (φ.q j)
  | .s0 | .T _ | .T' _ | .F _ | .F' _ | .Aend _ | .Aend' _ | .sink => ()

lemma stepA_true_isTrueObs (b : Bool) (i : Fin m) (j : Fin n) (s : St n m)
    (h : stepA true b (.T i j) (.F i j) s ≠ 0) :
    isTrueObs s.obs = b := by
  have hs : s = cond b (.T i j) (.F i j) := pure_support h
  subst hs
  cases b <;> rfl

lemma stepA_true_isTrueObs' (b : Bool) (i : Fin m) (j : Fin n) (s : St n m)
    (h : stepA true b (.T' i j) (.F' i j) s ≠ 0) :
    isTrueObs s.obs = b := by
  have hs : s = cond b (.T' i j) (.F' i j) := pure_support h
  subst hs
  cases b <;> rfl

lemma trans_existential_isTrueObs (φ : QBF n m) (hm : 0 < m)
    (hist : List (Obs n m)) (s s' : St n m) (j : Fin n)
    (hst : stage s = 2 * j.val + 1) (hq : φ.q j = true)
    (htr : φ.trans hm s (winPolicy φ hm hist s.obs) s' ≠ 0) :
    isTrueObs s'.obs = winChoice φ j (histAssign hist) := by
  cases s with
  | A i j' =>
    have hj : j' = j := Fin.ext (by simp only [stage] at hst; omega)
    subst hj
    change stepA (φ.q j') (winDecA φ j' (histAssign hist) (φ.q j')) (.T i j') (.F i j') s' ≠ 0 at htr
    rw [hq] at htr
    exact stepA_true_isTrueObs _ i j' s' htr
  | A' i j' =>
    have hj : j' = j := Fin.ext (by simp only [stage] at hst; omega)
    subst hj
    change stepA (φ.q j') (winDecA φ j' (histAssign hist) (φ.q j')) (.T' i j') (.F' i j') s' ≠ 0 at htr
    rw [hq] at htr
    exact stepA_true_isTrueObs' _ i j' s' htr
  | s0 | T _ _ | T' _ _ | F _ _ | F' _ _ | Aend _ | Aend' _ | sink =>
    simp only [stage, horizon] at hst; omega

lemma winPolicy_existential_step (φ : QBF n m) (hm : 0 < m)
    (x : Fin (horizon n + 1) → St n m)
    (hx : (φ.toPOMDP hm).trajProb .s0 (winPolicy φ hm) (horizon n) x ≠ 0)
    (j : Fin n) (hq : φ.q j = true) :
    trajAssign x j = winChoice φ j (prefixAssign (trajAssign x) j.val) := by
  obtain ⟨_, ht⟩ := trajectory_support φ hm (winPolicy φ hm) x hx
  let t : Fin (horizon n) := ⟨2 * j.val + 1, by unfold horizon; omega⟩
  have htr := ht t
  have hst := trajectory_stage φ hm (winPolicy φ hm) x hx (2 * j.val + 1)
    (by unfold horizon; omega)
  rw [← histAssign_obsHist φ hm x j]
  exact trans_existential_isTrueObs φ hm
    ((φ.toPOMDP hm).obsHist x t.castSucc) (x t.castSucc) (x t.succ) j hst hq htr

lemma holdsFrom_prefixAssign (φ : QBF n m) (hm : 0 < m) (h : φ.holds)
    (x : Fin (horizon n + 1) → St n m)
    (hx : (φ.toPOMDP hm).trajProb .s0 (winPolicy φ hm) (horizon n) x ≠ 0) :
    ∀ k ≤ n, φ.holdsFrom k (prefixAssign (trajAssign x) k) := by
  intro k hk
  induction k with
  | zero =>
    rw [prefixAssign_zero]
    exact h
  | succ k ih =>
    have hk' : k < n := by omega
    have ih' := ih (by omega)
    rw [QBF.holdsFrom, dif_pos hk'] at ih'
    let j : Fin n := ⟨k, hk'⟩
    rw [← prefixAssign_succ (trajAssign x) k hk']
    by_cases hq : φ.q j = true
    · rw [if_pos hq] at ih'
      have hwin : φ.holdsFrom (k + 1)
          (Function.update (prefixAssign (trajAssign x) k) j
            (winChoice φ j (prefixAssign (trajAssign x) k))) := by
        unfold winChoice
        rw [dif_pos ih']
        exact Classical.choose_spec ih'
      rwa [winPolicy_existential_step φ hm x hx j hq]
    · rw [if_neg hq] at ih'
      exact ih' (trajAssign x j)

lemma sat_trajAssign (φ : QBF n m) (hm : 0 < m) (h : φ.holds)
    (x : Fin (horizon n + 1) → St n m)
    (hx : (φ.toPOMDP hm).trajProb .s0 (winPolicy φ hm) (horizon n) x ≠ 0) :
    φ.Sat (trajAssign x) := by
  have hn := holdsFrom_prefixAssign φ hm h x hx n le_rfl
  rw [QBF.holdsFrom, dif_neg (Nat.lt_irrefl n), prefixAssign_n] at hn
  exact hn

lemma trans_to_T'_or_F' (φ : QBF n m) (hm : 0 < m) (s₁ : St n m) (d₁ : φ.Dec s₁.obs)
    (i : Fin m) (k : ℕ) (hk : k < n) (hst₁ : stage s₁ = 2 * k + 1)
    (htr₁ : φ.trans hm s₁ d₁ (.T' i ⟨k, hk⟩) ≠ 0 ∨ φ.trans hm s₁ d₁ (.F' i ⟨k, hk⟩) ≠ 0) :
    s₁ = lvlA' i k := by
  cases s₁ with
  | A i'' j' =>
    rcases htr₁ with h1 | h1
    · rcases stepA_support (φ.q j') d₁ (.T i'' j') (.F i'' j') (.T' i ⟨k, hk⟩) h1 with h | h <;>
        cases h
    · rcases stepA_support (φ.q j') d₁ (.T i'' j') (.F i'' j') (.F' i ⟨k, hk⟩) h1 with h | h <;>
        cases h
  | A' i'' j' =>
    have hj' : j' = ⟨k, hk⟩ := Fin.ext (by simp only [stage] at hst₁; dsimp; omega)
    subst hj'
    rcases htr₁ with h1 | h1
    · rcases stepA_support (φ.q ⟨k, hk⟩) d₁ (.T' i'' ⟨k, hk⟩) (.F' i'' ⟨k, hk⟩)
        (.T' i ⟨k, hk⟩) h1 with h | h
      · cases h
        unfold lvlA'
        rw [dif_pos hk]
      · cases h
    · rcases stepA_support (φ.q ⟨k, hk⟩) d₁ (.T' i'' ⟨k, hk⟩) (.F' i'' ⟨k, hk⟩)
        (.F' i ⟨k, hk⟩) h1 with h | h
      · cases h
      · cases h
        unfold lvlA'
        rw [dif_pos hk]
  | s0 | T _ _ | T' _ _ | F _ _ | F' _ _ | Aend _ | Aend' _ | sink =>
    simp only [stage, horizon] at hst₁; omega

lemma trans_to_lvlA' (φ : QBF n m) (hm : 0 < m)
    (s₁ s₂ : St n m) (d₁ : φ.Dec s₁.obs) (d₂ : φ.Dec s₂.obs)
    (i : Fin m) (k : ℕ) (hk : k < n)
    (hst₁ : stage s₁ = 2 * k + 1) (hst₂ : stage s₂ = 2 * k + 2)
    (htr₁ : φ.trans hm s₁ d₁ s₂ ≠ 0)
    (htr₂ : φ.trans hm s₂ d₂ (lvlA' i (k + 1)) ≠ 0) :
    s₁ = lvlA' i k ∧ (⟨k, hk⟩, isTrueObs s₂.obs) ∉ φ.clause i := by
  cases s₂ with
  | T i' j =>
    have hp := pure_support htr₂
    exact (lvlA'_ne_lvlA i i' (k + 1) (j.val + 1) hp).elim
  | F i' j =>
    have hp := pure_support htr₂
    exact (lvlA'_ne_lvlA i i' (k + 1) (j.val + 1) hp).elim
  | T' i' j =>
    have hj : j = ⟨k, hk⟩ := Fin.ext (by simp only [stage] at hst₂; dsimp; omega)
    subst hj
    have hp : lvlA' i (k + 1) = if (⟨k, hk⟩, true) ∈ φ.clause i' then
        lvlA i' (k + 1) else lvlA' i' (k + 1) := pure_support htr₂
    have hnotmem : (⟨k, hk⟩, true) ∉ φ.clause i' := by
      intro hmem
      rw [if_pos hmem] at hp
      exact lvlA'_ne_lvlA i i' (k + 1) (k + 1) hp
    rw [if_neg hnotmem] at hp
    have hi : i = i' := (lvlA'_eq_iff i i' (k + 1)).mp hp
    subst hi
    exact ⟨trans_to_T'_or_F' φ hm s₁ d₁ i k hk hst₁ (Or.inl htr₁), hnotmem⟩
  | F' i' j =>
    have hj : j = ⟨k, hk⟩ := Fin.ext (by simp only [stage] at hst₂; dsimp; omega)
    subst hj
    have hp : lvlA' i (k + 1) = if (⟨k, hk⟩, false) ∈ φ.clause i' then
        lvlA i' (k + 1) else lvlA' i' (k + 1) := pure_support htr₂
    have hnotmem : (⟨k, hk⟩, false) ∉ φ.clause i' := by
      intro hmem
      rw [if_pos hmem] at hp
      exact lvlA'_ne_lvlA i i' (k + 1) (k + 1) hp
    rw [if_neg hnotmem] at hp
    have hi : i = i' := (lvlA'_eq_iff i i' (k + 1)).mp hp
    subst hi
    exact ⟨trans_to_T'_or_F' φ hm s₁ d₁ i k hk hst₁ (Or.inr htr₁), hnotmem⟩
  | s0 | A _ _ | A' _ _ | Aend _ | Aend' _ | sink =>
    simp only [stage, horizon] at hst₂; omega

lemma lvlA'_pred (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy)
    (x : Fin (horizon n + 1) → St n m)
    (hx : (φ.toPOMDP hm).trajProb .s0 π (horizon n) x ≠ 0)
    (i : Fin m) (k : ℕ) (hk : k < n)
    (hnext : x ⟨2 * (k + 1) + 1, by unfold horizon; omega⟩ = lvlA' i (k + 1)) :
    x ⟨2 * k + 1, by unfold horizon; omega⟩ = lvlA' i k ∧
      (⟨k, hk⟩, trajAssign x ⟨k, hk⟩) ∉ φ.clause i := by
  obtain ⟨_, ht⟩ := trajectory_support φ hm π x hx
  let t₁ : Fin (horizon n) := ⟨2 * k + 1, by unfold horizon; omega⟩
  let t₂ : Fin (horizon n) := ⟨2 * k + 2, by unfold horizon; omega⟩
  have htr₁ := ht t₁
  have htr₂ := ht t₂
  have hst₁ := trajectory_stage φ hm π x hx (2 * k + 1) (by unfold horizon; omega)
  have hst₂ := trajectory_stage φ hm π x hx (2 * k + 2) (by unfold horizon; omega)
  have hsucc₁ : t₁.succ = t₂.castSucc := Fin.ext rfl
  have hsucc₂ : t₂.succ = ⟨2 * (k + 1) + 1, by unfold horizon; omega⟩ := Fin.ext (by dsimp [t₂]; omega)
  rw [hsucc₁] at htr₁
  rw [hsucc₂, hnext] at htr₂
  exact trans_to_lvlA' φ hm (x t₁.castSucc) (x t₂.castSucc)
    ((φ.toPOMDP hm).dec π x t₁.castSucc) ((φ.toPOMDP hm).dec π x t₂.castSucc)
    i k hk hst₁ hst₂ htr₁ htr₂

lemma unsatisfied_prefix_of_lvlA' (φ : QBF n m) (hm : 0 < m) (π : (φ.toPOMDP hm).Policy)
    (x : Fin (horizon n + 1) → St n m)
    (hx : (φ.toPOMDP hm).trajProb .s0 π (horizon n) x ≠ 0)
    (i : Fin m) (r : ℕ) :
    ∀ hr : r ≤ n, x ⟨2 * r + 1, by unfold horizon; omega⟩ = lvlA' i r →
      ∀ k : Fin n, k.val < r → (k, trajAssign x k) ∉ φ.clause i := by
  induction r with
  | zero =>
    intro _ _ k hk
    omega
  | succ r ih =>
    intro hr hnext k hk
    have hr' : r < n := by omega
    obtain ⟨hprev, hnot⟩ := lvlA'_pred φ hm π x hx i r hr' hnext
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
    · exact ih (by omega) hprev k hlt
    · have hk_eq : k = ⟨r, hr'⟩ := Fin.ext heq
      rwa [hk_eq]

end MDPHoldsImpZeroCost

/-- §4, proof of Theorem 6 (p. 449), "if": if the quantified formula is true, some
observation-history policy has expected cost zero over the horizon `2n + 2`. -/
theorem solution {n m : ℕ} (φ : QBF n m) (hm : 0 < m)
    (_hqsat : φ.IsPaperQSAT) (h : φ.holds) :
    ∃ π : (φ.toPOMDP hm).Policy, (φ.toPOMDP hm).expCost .s0 π (horizon n) = 0 := by
  refine ⟨MDPHoldsImpZeroCost.winPolicy φ hm, ?_⟩
  rw [MDPHoldsImpZeroCost.zero_cost_iff_no_unsatisfied_endpoint]
  intro x hx i hend
  have hsat := MDPHoldsImpZeroCost.sat_trajAssign φ hm h x hx
  have hlvl : x ⟨2 * n + 1, by unfold horizon; omega⟩ = lvlA' i n := by
    rw [hend]
    unfold lvlA'
    rw [dif_neg (Nat.lt_irrefl n)]
  have hunsat := MDPHoldsImpZeroCost.unsatisfied_prefix_of_lvlA' φ hm
    (MDPHoldsImpZeroCost.winPolicy φ hm) x hx i n le_rfl hlvl
  obtain ⟨⟨k, b⟩, hmem, heq⟩ := hsat i
  dsimp at heq
  subst heq
  exact hunsat k k.isLt hmem
