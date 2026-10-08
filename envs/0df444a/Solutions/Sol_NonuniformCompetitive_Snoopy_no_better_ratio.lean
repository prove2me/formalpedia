-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.no_better_ratio
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T08:45:39.525134+00:00
-- url     : https://prove2.me/submissions/b41d3e53-9234-4151-9afe-0d35ddc6e9dd

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_ep
import Definitions.Def_NonuniformCompetitive_Snoopy_model
import Definitions.Def_NonuniformCompetitive_Snoopy_randomized



namespace NonuniformCompetitive.Snoopy

namespace NBR
open scoped ENNReal

/-- ratio r = p/(p+1) -/
noncomputable def rr (p : ℕ) : ℝ := (p : ℝ) / (p + 1)

noncomputable def qq (p k : ℕ) : ℝ := if k < p then rr p ^ k / (p + 1) else rr p ^ p

lemma rr_nonneg (p : ℕ) : 0 ≤ rr p := by unfold rr; positivity

lemma qq_nonneg (p k : ℕ) : 0 ≤ qq p k := by
  unfold qq; have := rr_nonneg p; split_ifs <;> positivity

lemma sumA (p : ℕ) : ∀ s : ℕ, ∑ k ∈ Finset.range s, (k : ℝ) * rr p ^ k / (p + 1)
    = p - (s + p) * rr p ^ s := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    unfold rr
    have : (p : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    push_cast
    ring

lemma sumB (p : ℕ) : ∀ s : ℕ, ∑ k ∈ Finset.range s, rr p ^ k / (p + 1) = 1 - rr p ^ s := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    unfold rr
    have : (p : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

lemma sumIco (p s : ℕ) (hs : s ≤ p) :
    ∑ k ∈ Finset.Ico s p, rr p ^ k / (p + 1) = rr p ^ s - rr p ^ p := by
  have h := Finset.sum_range_add_sum_Ico (fun k => rr p ^ k / (p + 1)) hs
  rw [sumB, sumB] at h
  linarith

lemma sum_qq (p : ℕ) : ∑ k ∈ Finset.range (p + 1), qq p k = 1 := by
  rw [Finset.sum_range_succ]
  unfold qq
  rw [Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))]
  simp only [lt_irrefl, if_false]
  rw [sumB]; ring

/-- G k s -/
def GG (p k s : ℕ) : ℕ := if k < p then min s k + (if s ≤ k then p else 0) else s + p

lemma sum_qq_GG (p s : ℕ) (hs : s ≤ p) :
    ∑ k ∈ Finset.range (p + 1), qq p k * (GG p k s : ℝ) = p := by
  rw [Finset.sum_range_succ, ← Finset.sum_range_add_sum_Ico _ hs]
  have e1 : ∑ k ∈ Finset.range s, qq p k * (GG p k s : ℝ)
      = ∑ k ∈ Finset.range s, (k : ℝ) * rr p ^ k / (p + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    unfold qq GG
    rw [if_pos (by omega), if_pos (by omega), min_eq_right (by omega), if_neg (by omega)]
    push_cast; ring
  have e2 : ∑ k ∈ Finset.Ico s p, qq p k * (GG p k s : ℝ)
      = (s + p) * ∑ k ∈ Finset.Ico s p, rr p ^ k / (p + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    unfold qq GG
    rw [if_pos (by omega), if_pos (by omega), min_eq_left (by omega), if_pos (by omega)]
    push_cast; ring
  rw [e1, e2, sumA, sumIco p s hs]
  unfold qq GG
  simp only [lt_irrefl, if_false]
  push_cast; ring

/-- mean of opt -/
lemma sum_qq_k (p : ℕ) :
    ∑ k ∈ Finset.range (p + 1), qq p k * (k : ℝ) = p * (1 - rr p ^ p) := by
  rw [Finset.sum_range_succ]
  have e1 : ∑ k ∈ Finset.range p, qq p k * (k : ℝ)
      = ∑ k ∈ Finset.range p, (k : ℝ) * rr p ^ k / (p + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    unfold qq
    rw [if_pos (Finset.mem_range.mp hk)]; ring
  rw [e1, sumA]
  unfold qq
  simp only [lt_irrefl, if_false]
  ring

lemma rr_pow_ep (p : ℕ) (hp : 1 ≤ p) : rr p ^ p * ep p = 1 := by
  unfold rr ep
  rw [← mul_pow]
  have : (p : ℝ) ≠ 0 := by positivity
  have h2 : (p : ℝ) + 1 ≠ 0 := by positivity
  rw [show (p : ℝ) / (p + 1) * (1 + 1 / p) = 1 by field_simp]
  simp


def ww (p k : ℕ) : ℕ := if k < p then k else 2 * p

open Classical in
noncomputable def LL (p : ℕ) (B : ℕ → Bool) (k : ℕ) : ℕ :=
  ((Finset.range (ww p k)).filter (fun j => B j = false)).card +
    (if ∃ j < ww p k + 1, B j = true then p else 0)

lemma card_ge_of_sub {B : ℕ → Bool} {a b : ℕ} (hab : a ≤ b) (h : ∀ j < a, B j = false) :
    a ≤ ((Finset.range b).filter (fun j => B j = false)).card := by
  have : Finset.range a ⊆ (Finset.range b).filter (fun j => B j = false) := by
    intro j hj
    have := Finset.mem_range.mp hj
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, h j this⟩
  simpa using Finset.card_le_card this

lemma exists_s (p : ℕ) (B : ℕ → Bool) : ∃ s ≤ p, ∀ k ≤ p, GG p k s ≤ LL p B k := by
  classical
  by_cases hex : ∃ j ≤ p, B j = true
  · let T := Nat.find hex
    have hT : T ≤ p ∧ B T = true := Nat.find_spec hex
    have hmin : ∀ j < T, B j = false := by
      intro j hj
      have := Nat.find_min hex hj
      simp only [not_and] at this
      cases h : B j
      · rfl
      · exact absurd h (this (by omega))
    refine ⟨T, hT.1, ?_⟩
    intro k hk
    unfold GG LL ww
    by_cases hkp : k < p
    · rw [if_pos hkp, if_pos hkp]
      have hc := card_ge_of_sub (B := B) (a := min T k) (b := k) (min_le_right _ _)
        (fun j hj => hmin j (by omega))
      by_cases hTk : T ≤ k
      · rw [if_pos hTk, if_pos ⟨T, by omega, hT.2⟩]; omega
      · rw [if_neg hTk]; omega
    · rw [if_neg hkp, if_neg hkp]
      have hc := card_ge_of_sub (B := B) (a := T) (b := 2 * p) (by omega) hmin
      rw [if_pos ⟨T, by omega, hT.2⟩]; omega
  · push_neg at hex
    have hf : ∀ j ≤ p, B j = false := fun j hj => by
      cases h : B j
      · rfl
      · exact absurd h (hex j hj)
    refine ⟨p, le_rfl, ?_⟩
    intro k hk
    unfold GG LL ww
    by_cases hkp : k < p
    · rw [if_pos hkp, if_pos hkp, if_neg (by omega), min_eq_right (by omega)]
      have hc := card_ge_of_sub (B := B) (a := k) (b := k) le_rfl (fun j hj => hf j (by omega))
      omega
    · rw [if_neg hkp, if_neg hkp]
      by_cases h2 : ∃ j < 2 * p + 1, B j = true
      · rw [if_pos h2]
        have hc := card_ge_of_sub (B := B) (a := p) (b := 2 * p) (by omega)
          (fun j hj => hf j (by omega))
        omega
      · rw [if_neg h2]
        push_neg at h2
        have hc := card_ge_of_sub (B := B) (a := 2 * p) (b := 2 * p) le_rfl
          (fun j hj => by
            cases h : B j
            · rfl
            · exact absurd h (h2 j (by omega)))
        omega

lemma sum_qq_LL (p : ℕ) (B : ℕ → Bool) :
    (p : ℝ) ≤ ∑ k ∈ Finset.range (p + 1), qq p k * (LL p B k : ℝ) := by
  obtain ⟨s, hs, h⟩ := exists_s p B
  rw [← sum_qq_GG p s hs]
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (qq_nonneg p k)
  exact_mod_cast h k (by have := Finset.mem_range.mp hk; omega)


lemma comb (p : ℕ) (B : ℕ → Bool) : ∀ w : ℕ,
    ((Finset.range w).filter (fun j => B j = false)).card +
      (if ∃ j < w + 1, B j = true then p else 0) ≤
    ∑ j ∈ Finset.range w, ((if B j = false then 1 else 0) +
      (if B j = true ∧ B (j + 1) = false then p else 0)) + (if B w = true then p else 0) := by
  intro w
  induction w with
  | zero =>
    simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty, Finset.sum_empty,
      zero_add]
    by_cases h : B 0 = true
    · rw [if_pos ⟨0, by omega, h⟩, if_pos h]
    · rw [if_neg h, if_neg (by
        rintro ⟨j, hj, hb⟩
        have : j = 0 := by omega
        subst this; exact h hb)]
  | succ w ih =>
    rw [Finset.range_add_one, Finset.filter_insert, Finset.sum_insert (by simp)]
    have hcard : ∀ (s : Finset ℕ), w ∉ s → (if B w = false then insert w s else s).card
        = s.card + (if B w = false then 1 else 0) := by
      intro s hs
      split_ifs
      · rw [Finset.card_insert_of_notMem hs]
      · simp
    rw [hcard _ (by simp)]
    have hE : (∃ j < w + 1 + 1, B j = true) ↔ (∃ j < w + 1, B j = true) ∨ B (w + 1) = true := by
      constructor
      · rintro ⟨j, hj, hb⟩
        by_cases hjw : j = w + 1
        · subst hjw; exact Or.inr hb
        · exact Or.inl ⟨j, by omega, hb⟩
      · rintro (⟨j, hj, hb⟩ | hb)
        · exact ⟨j, by omega, hb⟩
        · exact ⟨w + 1, by omega, hb⟩
    have hBw : B w = true → (∃ j < w + 1, B j = true) := fun h => ⟨w, by omega, h⟩
    by_cases h1 : B (w + 1) = true
    · rw [if_pos (hE.mpr (Or.inr h1)), if_pos h1]
      split_ifs at ih ⊢ <;> simp_all <;> omega
    · rw [if_neg h1]
      have : (∃ j < w + 1 + 1, B j = true) ↔ (∃ j < w + 1, B j = true) := by
        rw [hE]; simp [h1]
      simp only [this]
      split_ifs at ih ⊢ <;> simp_all <;> omega


lemma fin_sum_eq_range {n : ℕ} (σ : List (Req n)) (f : Req n → ℕ → ℝ≥0∞) :
    ∑ j : Fin σ.length, f σ[j] j = ∑ j ∈ Finset.range σ.length, ((σ[j]?).map (fun r => f r j)).getD 0 := by
  rw [Finset.sum_range (fun j => ((σ[j]?).map (fun r => f r j)).getD 0)]
  apply Finset.sum_congr rfl
  intro j _
  simp [List.getElem?_eq_getElem j.isLt]

lemma cost_eq {n : ℕ} (A : OnlineAlgorithm n) (p : ℕ) (σ : List (Req n)) :
    A.cost p σ = ∑ j ∈ Finset.range σ.length, ((σ[j]?).map (fun r =>
      stepCost p r (A.after (σ.take j)) (A.moment (σ.take (j + 1))) (A.after (σ.take (j + 1))))).getD 0 :=
  fin_sum_eq_range σ (fun r j =>
      stepCost p r (A.after (σ.take j)) (A.moment (σ.take (j + 1))) (A.after (σ.take (j + 1))))

lemma cost_snoc {n : ℕ} (A : OnlineAlgorithm n) (p : ℕ) (pre : List (Req n)) (r : Req n) :
    A.cost p (pre ++ [r]) = A.cost p pre +
      stepCost p r (A.after pre) (A.moment (pre ++ [r])) (A.after (pre ++ [r])) := by
  rw [cost_eq, cost_eq, List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [List.getElem?_append_left hj', List.take_append_of_le_length (by omega),
      List.take_append_of_le_length (by omega)]
  · rw [List.getElem?_append_right le_rfl]
    have : List.take (pre.length + 1) (pre ++ [r]) = pre ++ [r] :=
      List.take_of_length_le (by simp)
    simp [this]


def ph {n : ℕ} (i0 i1 : Fin n) (w : ℕ) : List (Req n) :=
  Req.read i1 :: (List.replicate w (Req.write i1) ++ [Req.read i0])

def PP {n : ℕ} (i1 : Fin n) (pre : List (Req n)) (j : ℕ) : List (Req n) :=
  pre ++ Req.read i1 :: List.replicate j (Req.write i1)

lemma PP_succ {n : ℕ} (i1 : Fin n) (pre : List (Req n)) (j : ℕ) :
    PP i1 pre (j + 1) = PP i1 pre j ++ [Req.write i1] := by
  simp [PP, List.replicate_succ']

lemma cost_writes {n : ℕ} (A : OnlineAlgorithm n) (p : ℕ) (i1 : Fin n) (pre : List (Req n)) :
    ∀ w, A.cost p pre + ∑ j ∈ Finset.range w,
      (taskCost (Req.write i1) (A.after (PP i1 pre j)) +
        transCost p (A.after (PP i1 pre j)) (A.after (PP i1 pre (j + 1)))) ≤ A.cost p (PP i1 pre w) := by
  intro w
  induction w with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    have : PP i1 pre 0 = pre ++ [Req.read i1] := by simp [PP]
    rw [this, cost_snoc]
    exact le_self_add
  | succ w ih =>
    rw [Finset.sum_range_succ, ← add_assoc]
    calc _ ≤ A.cost p (PP i1 pre w) + (taskCost (Req.write i1) (A.after (PP i1 pre w)) +
        transCost p (A.after (PP i1 pre w)) (A.after (PP i1 pre (w + 1)))) := by gcongr
      _ = A.cost p (PP i1 pre (w + 1)) := by
        rw [PP_succ i1 pre w, cost_snoc, A.lookaheadZero, ← PP_succ]
        unfold stepCost
        simp [transCost]

lemma last_read {n : ℕ} (A : OnlineAlgorithm n) (p : ℕ) (i0 i1 : Fin n) (hne : i0 ≠ i1)
    (pre : List (Req n)) :
    A.cost p pre + (if A.after pre = some i1 then (p : ℝ≥0∞) else 0) ≤
      A.cost p (pre ++ [Req.read i0]) := by
  rw [cost_snoc]
  gcongr
  split_ifs with h
  · unfold stepCost
    rw [h]
    by_cases hm : A.moment (pre ++ [Req.read i0]) = some i1
    · rw [hm]
      have : taskCost (Req.read i0) (some i1 : State n) = ⊤ := by
        simp [taskCost, Ne.symm hne]
      rw [this]; simp
    · have : transCost p (some i1 : State n) (A.moment (pre ++ [Req.read i0])) = p := by
        simp [transCost, hm]
      rw [this, add_assoc]; exact le_self_add
  · exact zero_le'

lemma task_ge {n : ℕ} (i1 : Fin n) (x : State n) :
    (if decide (x = some i1) = false then (1 : ℝ≥0∞) else 0) ≤ taskCost (Req.write i1) x := by
  by_cases h : x = some i1
  · simp [h]
  · simp only [h, decide_false, if_true]
    simp only [taskCost, if_neg h]
    split_ifs <;> simp

lemma trans_ge {n : ℕ} (p : ℕ) (i1 : Fin n) (x y : State n) :
    (if decide (x = some i1) = true ∧ decide (y = some i1) = false then (p : ℝ≥0∞) else 0)
      ≤ transCost p x y := by
  split_ifs with h
  · simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    simp [transCost, h2]
  · exact zero_le'

open Classical in
/-- phase lemma -/
lemma phase_cost {n : ℕ} (A : OnlineAlgorithm n) (p : ℕ) (i0 i1 : Fin n) (hne : i0 ≠ i1)
    (pre : List (Req n)) (k : ℕ) :
    A.cost p pre + (LL p (fun j => decide (A.after (PP i1 pre j) = some i1)) k : ℝ≥0∞)
      ≤ A.cost p (pre ++ ph i0 i1 (ww p k)) := by
  set B : ℕ → Bool := fun j => decide (A.after (PP i1 pre j) = some i1) with hB
  have hc := comb p B (ww p k)
  have e : pre ++ ph i0 i1 (ww p k) = PP i1 pre (ww p k) ++ [Req.read i0] := by
    simp [PP, ph]
  rw [e]
  refine le_trans ?_ (last_read A p i0 i1 hne _)
  refine le_trans ?_ (add_le_add (cost_writes A p i1 pre (ww p k)) le_rfl)
  rw [add_assoc]
  gcongr
  calc (LL p B k : ℝ≥0∞)
      ≤ ((∑ j ∈ Finset.range (ww p k), ((if B j = false then 1 else 0) +
        (if B j = true ∧ B (j + 1) = false then p else 0)) + (if B (ww p k) = true then p else 0) : ℕ)
          : ℝ≥0∞) := by
        unfold LL; exact_mod_cast hc
    _ = ∑ j ∈ Finset.range (ww p k), ((if B j = false then (1 : ℝ≥0∞) else 0) +
        (if B j = true ∧ B (j + 1) = false then (p : ℝ≥0∞) else 0)) +
          (if B (ww p k) = true then (p : ℝ≥0∞) else 0) := by
        push_cast
        rfl
    _ ≤ _ := by
        gcongr with j hj
        · exact task_ge i1 _
        · exact trans_ge p i1 _ _
        · simp only [hB, decide_eq_true_eq]
          split_ifs <;> simp


/-! ### Offline schedules -/

def RW' {n : ℕ} (σ : List (Req n)) (m s : ℕ → State n) : Prop :=
  ∀ j r, σ[j]? = some r → r.isWrite = true → m (j + 1) = s j

def Sched {n : ℕ} (p : ℕ) (σ : List (Req n)) (a : State n) (C : ℝ≥0∞) : Prop :=
  ∃ m s : ℕ → State n, s 0 = a ∧ RW' σ m s ∧ scheduleCost p σ m s ≤ C

def SchedN {n : ℕ} (p : ℕ) (σ : List (Req n)) (a : State n) (C : ℝ≥0∞) : Prop :=
  ∃ m s : ℕ → State n, s 0 = a ∧ s σ.length = none ∧ RW' σ m s ∧ scheduleCost p σ m s ≤ C

lemma sched_eq {n : ℕ} (p : ℕ) (σ : List (Req n)) (m s : ℕ → State n) :
    scheduleCost p σ m s = ∑ j ∈ Finset.range σ.length,
      ((σ[j]?).map (fun r => stepCost p r (s j) (m (j + 1)) (s (j + 1)))).getD 0 :=
  fin_sum_eq_range σ (fun r j => stepCost p r (s j) (m (j + 1)) (s (j + 1)))

lemma offline_le {n : ℕ} (p : ℕ) (σ : List (Req n)) (a : State n) (C : ℝ≥0∞)
    (h : Sched p σ a C) : offlineCost p a σ ≤ C := by
  obtain ⟨m, s, h0, hR, hC⟩ := h
  have hR' : RespectsWrites σ m s := by
    intro j hj
    exact hR j σ[j] (List.getElem?_eq_getElem j.isLt) hj
  unfold offlineCost
  exact iInf_le_of_le m (iInf_le_of_le s (iInf_le_of_le h0 (iInf_le_of_le hR' hC)))

lemma sched_nil {n : ℕ} (p : ℕ) (a : State n) : Sched p ([] : List (Req n)) a 0 := by
  refine ⟨fun _ => a, fun _ => a, rfl, ?_, ?_⟩
  · intro j r h; simp at h
  · simp [scheduleCost]

lemma splice {n : ℕ} (p : ℕ) (σ1 σ2 : List (Req n)) (a : State n) (C1 C2 : ℝ≥0∞)
    (h1 : SchedN p σ1 a C1) (h2 : Sched p σ2 none C2) : Sched p (σ1 ++ σ2) a (C1 + C2) := by
  obtain ⟨m1, s1, h10, h1L, hR1, hC1⟩ := h1
  obtain ⟨m2, s2, h20, hR2, hC2⟩ := h2
  set L := σ1.length with hL
  let m : ℕ → State n := fun j => if j ≤ L then m1 j else m2 (j - L)
  let s : ℕ → State n := fun j => if j ≤ L then s1 j else s2 (j - L)
  have hs2 : ∀ j, s (L + j) = s2 j := by
    intro j
    simp only [s]
    split_ifs with h
    · have : j = 0 := by omega
      subst this; simp [h1L, h20]
    · congr 1; omega
  have hm2 : ∀ j, m (L + j + 1) = m2 (j + 1) := by
    intro j
    simp only [m]
    rw [if_neg (by omega)]; congr 1; omega
  have hs1 : ∀ j ≤ L, s j = s1 j := fun j hj => by simp only [s]; rw [if_pos hj]
  have hm1 : ∀ j ≤ L, m j = m1 j := fun j hj => by simp only [m]; rw [if_pos hj]
  refine ⟨m, s, ?_, ?_, ?_⟩
  · rw [hs1 0 (by omega), h10]
  · intro j r hj hw
    by_cases hjL : j < L
    · rw [List.getElem?_append_left hjL] at hj
      rw [hm1 _ (by omega), hs1 _ (by omega)]
      exact hR1 j r hj hw
    · rw [List.getElem?_append_right (by omega)] at hj
      have := hR2 (j - L) r hj hw
      have e : j = L + (j - L) := by omega
      rw [e, hm2, hs2, this]
  · rw [sched_eq, List.length_append, Finset.sum_range_add]
    rw [sched_eq] at hC1 hC2
    refine le_trans (le_of_eq ?_) (add_le_add hC1 hC2)
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [List.getElem?_append_left hj', hs1 _ (by omega), hm1 _ (by omega), hs1 _ (by omega)]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, hs2, hm2, add_assoc, hs2]

lemma ph_get {n : ℕ} (i0 i1 : Fin n) (w j : ℕ) :
    (ph i0 i1 w)[j]? = if j = 0 then some (Req.read i1) else if j ≤ w then some (Req.write i1)
      else if j = w + 1 then some (Req.read i0) else none := by
  unfold ph
  rcases j with _ | j
  · simp
  · simp only [List.getElem?_cons_succ, Nat.add_one_ne_zero, if_false]
    by_cases hj : j < w
    · rw [List.getElem?_append_left (by simpa using hj), if_pos (by omega)]
      simp [hj]
    · rw [List.getElem?_append_right (by simp; omega), if_neg (by omega)]
      simp only [List.length_replicate]
      by_cases hjw : j = w
      · subst hjw; simp
      · rw [if_neg (by omega)]
        rw [List.getElem?_eq_none (by simp; omega)]

lemma trans_none_le {n : ℕ} (p : ℕ) (a : State n) :
    transCost p a none ≤ (if a = none then 0 else (p : ℝ≥0∞)) := by
  rcases a with _ | a <;> simp [transCost]

lemma ph_length {n : ℕ} (i0 i1 : Fin n) (w : ℕ) : (ph i0 i1 w).length = w + 2 := by
  simp [ph]

lemma sched_short {n : ℕ} (p : ℕ) (i0 i1 : Fin n) (w : ℕ) (a : State n) :
    SchedN p (ph i0 i1 w) a ((if a = none then 0 else (p : ℝ≥0∞)) + w) := by
  refine ⟨fun _ => none, fun j => if j = 0 then a else none, rfl, ?_, ?_, ?_⟩
  · simp [ph_length]
  · intro j r hj hw
    rw [ph_get] at hj
    split_ifs at hj with h0 h1 h2
    · cases hj; simp [Req.isWrite] at hw
    · simp [h0]
    · cases hj; simp [Req.isWrite] at hw
  · rw [sched_eq, ph_length, Finset.sum_range_succ, Finset.sum_range_succ']
    have hmid : ∀ j ∈ Finset.range w, ((ph i0 i1 w)[j + 1]?.map (fun r => stepCost p r
        ((fun j => if j = 0 then a else none) (j + 1)) ((fun _ => (none : State n)) (j + 1 + 1))
        ((fun j => if j = 0 then a else none) (j + 1 + 1)))).getD 0 = 1 := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      simp only [ph_get, show j + 1 ≠ 0 by omega, show j + 1 ≤ w by omega, show j + 1 + 1 ≠ 0 by omega,
        if_true, if_false, Option.map_some, Option.getD_some]
      simp [stepCost, taskCost, transCost]
    rw [Finset.sum_congr rfl hmid]
    have h0 : ((ph i0 i1 w)[0]?.map (fun r => stepCost p r
        ((fun j => if j = 0 then a else none) 0) ((fun _ => (none : State n)) (0 + 1))
        ((fun j => if j = 0 then a else none) (0 + 1)))).getD 0 ≤ (if a = none then 0 else (p : ℝ≥0∞)) := by
      simp only [ph_get, if_true, Option.map_some, Option.getD_some, show (0 + 1 : ℕ) ≠ 0 by omega,
        if_false]
      simp only [stepCost]
      have : taskCost (Req.read i1) (none : State n) = 0 := by simp [taskCost]
      rw [this]
      simp [transCost]
      exact trans_none_le p a
    have hl : ((ph i0 i1 w)[w + 1]?.map (fun r => stepCost p r
        ((fun j => if j = 0 then a else none) (w + 1)) ((fun _ => (none : State n)) (w + 1 + 1))
        ((fun j => if j = 0 then a else none) (w + 1 + 1)))).getD 0 = 0 := by
      simp only [ph_get, show w + 1 ≠ 0 by omega, show ¬ w + 1 ≤ w by omega, if_true, if_false,
        Option.map_some, Option.getD_some, show w + 1 + 1 ≠ 0 by omega]
      simp [stepCost, taskCost, transCost]
    rw [hl]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, add_zero]
    rw [add_comm]
    exact add_le_add h0 le_rfl

lemma sched_long {n : ℕ} (p : ℕ) (i0 i1 : Fin n) (hne : i0 ≠ i1) (w : ℕ) (a : State n) :
    SchedN p (ph i0 i1 w) a ((if a = none then 0 else (p : ℝ≥0∞)) + p) := by
  set m : ℕ → State n := fun j => if j = 1 then none else if j ≤ w + 1 then some i1 else none with hm
  set s : ℕ → State n := fun j => if j = 0 then a else if j ≤ w + 1 then some i1 else none with hs
  refine ⟨m, s, rfl, ?_, ?_, ?_⟩
  · simp [ph_length, hs]
  · intro j r hj hw
    rw [ph_get] at hj
    split_ifs at hj with h0 h1 h2
    · cases hj; simp [Req.isWrite] at hw
    · simp only [hm, hs]
      rw [if_neg (by omega), if_pos (by omega), if_neg h0, if_pos (by omega)]
    · cases hj; simp [Req.isWrite] at hw
  · rw [sched_eq, ph_length, Finset.sum_range_succ, Finset.sum_range_succ']
    have hmid : ∀ j ∈ Finset.range w, ((ph i0 i1 w)[j + 1]?.map (fun r => stepCost p r
        (s (j + 1)) (m (j + 1 + 1)) (s (j + 1 + 1)))).getD 0 = 0 := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have e1 : s (j + 1) = some i1 := by
        simp only [hs]; rw [if_neg (by omega), if_pos (by omega)]
      have e2 : s (j + 1 + 1) = some i1 := by
        simp only [hs]; rw [if_neg (by omega), if_pos (by omega)]
      have e3 : m (j + 1 + 1) = some i1 := by
        simp only [hm]; rw [if_neg (by omega), if_pos (by omega)]
      rw [e1, e2, e3]
      simp only [ph_get, show j + 1 ≠ 0 by omega, show j + 1 ≤ w by omega,
        if_true, if_false, Option.map_some, Option.getD_some]
      simp [stepCost, taskCost, transCost]
    rw [Finset.sum_congr rfl hmid]
    have h0 : ((ph i0 i1 w)[0]?.map (fun r => stepCost p r
        (s 0) (m (0 + 1)) (s (0 + 1)))).getD 0 ≤ (if a = none then 0 else (p : ℝ≥0∞)) := by
      have e1 : s 0 = a := by simp [hs]
      have e2 : s (0 + 1) = some i1 := by
        simp only [hs]; rw [if_neg (by omega), if_pos (by omega)]
      have e3 : m (0 + 1) = none := by simp [hm]
      rw [e1, e2, e3]
      simp only [ph_get, if_true, Option.map_some, Option.getD_some]
      simp only [stepCost]
      have : taskCost (Req.read i1) (none : State n) = 0 := by simp [taskCost]
      rw [this]
      simp [transCost]
      exact trans_none_le p a
    have hl : ((ph i0 i1 w)[w + 1]?.map (fun r => stepCost p r
        (s (w + 1)) (m (w + 1 + 1)) (s (w + 1 + 1)))).getD 0 = p := by
      have e1 : s (w + 1) = some i1 := by
        simp only [hs]; rw [if_neg (by omega), if_pos (by omega)]
      have e2 : s (w + 1 + 1) = none := by
        simp only [hs]; rw [if_neg (by omega), if_neg (by omega)]
      have e3 : m (w + 1 + 1) = none := by
        simp only [hm]; rw [if_neg (by omega), if_neg (by omega)]
      rw [e1, e2, e3]
      simp only [ph_get, show w + 1 ≠ 0 by omega, show ¬ w + 1 ≤ w by omega, if_true, if_false,
        Option.map_some, Option.getD_some]
      simp [stepCost, taskCost, transCost]
    rw [hl]
    simp only [Finset.sum_const_zero, zero_add]
    exact add_le_add h0 le_rfl


/-! ### sequences -/

def sq {n : ℕ} (i0 i1 : Fin n) (p : ℕ) (ks : List ℕ) : List (Req n) :=
  ks.flatMap (fun k => ph i0 i1 (ww p k))

lemma sq_snoc {n : ℕ} (i0 i1 : Fin n) (p : ℕ) (ks : List ℕ) (k : ℕ) :
    sq i0 i1 p (ks ++ [k]) = sq i0 i1 p ks ++ ph i0 i1 (ww p k) := by
  simp [sq]

lemma sched_mono {n : ℕ} {p : ℕ} {σ : List (Req n)} {a : State n} {C C' : ℝ≥0∞}
    (h : Sched p σ a C) (hC : C ≤ C') : Sched p σ a C' := by
  obtain ⟨m, s, h0, hR, hc⟩ := h
  exact ⟨m, s, h0, hR, hc.trans hC⟩

lemma schedN_mono {n : ℕ} {p : ℕ} {σ : List (Req n)} {a : State n} {C C' : ℝ≥0∞}
    (h : SchedN p σ a C) (hC : C ≤ C') : SchedN p σ a C' := by
  obtain ⟨m, s, h0, h1, hR, hc⟩ := h
  exact ⟨m, s, h0, h1, hR, hc.trans hC⟩

lemma sched_phase {n : ℕ} (p : ℕ) (i0 i1 : Fin n) (hne : i0 ≠ i1) (k : ℕ) (hk : k ≤ p)
    (a : State n) :
    SchedN p (ph i0 i1 (ww p k)) a ((if a = none then 0 else (p : ℝ≥0∞)) + k) := by
  by_cases h : k < p
  · have e : ww p k = k := by simp [ww, h]
    rw [e]; exact sched_short p i0 i1 k a
  · have : k = p := by omega
    subst this
    exact sched_long k i0 i1 hne _ a

lemma sched_seq {n : ℕ} (p : ℕ) (i0 i1 : Fin n) (hne : i0 ≠ i1) : ∀ (ks : List ℕ) (a : State n),
    (∀ k ∈ ks, k ≤ p) →
    Sched p (sq i0 i1 p ks) a ((if a = none then 0 else (p : ℝ≥0∞)) + ((ks.sum : ℕ) : ℝ≥0∞)) := by
  intro ks
  induction ks with
  | nil =>
    intro a _
    simp only [sq, List.flatMap_nil, List.sum_nil, Nat.cast_zero, add_zero]
    exact sched_mono (sched_nil p a) (zero_le')
  | cons k ks ih =>
    intro a hks
    have h1 := sched_phase p i0 i1 hne k (hks k (by simp)) a
    have h2 := ih none (fun k' hk' => hks k' (by simp [hk']))
    have := splice p _ _ a _ _ h1 h2
    have e : sq i0 i1 p (k :: ks) = ph i0 i1 (ww p k) ++ sq i0 i1 p ks := by simp [sq]
    rw [e]
    refine sched_mono this (le_of_eq ?_)
    simp only [if_true, zero_add, List.sum_cons, Nat.cast_add]
    ring

lemma adm_append {n : ℕ} (σ1 σ2 : List (Req n)) (h1 : Admissible σ1) (h2 : Admissible σ2)
    (h0 : ∀ i, σ2[0]? ≠ some (Req.write i)) : Admissible (σ1 ++ σ2) := by
  intro j i h
  by_cases hj : j < σ1.length
  · rw [List.getElem?_append_left hj] at h
    obtain ⟨hpos, hprev⟩ := h1 j i h
    refine ⟨hpos, ?_⟩
    rw [List.getElem?_append_left (by omega)]
    exact hprev
  · rw [List.getElem?_append_right (by omega)] at h
    by_cases hjL : j = σ1.length
    · subst hjL; simp at h; exact absurd h (h0 i)
    · obtain ⟨hpos, hprev⟩ := h2 _ i h
      refine ⟨by omega, ?_⟩
      rw [List.getElem?_append_right (by omega)]
      rw [show j - 1 - σ1.length = j - σ1.length - 1 by omega]
      exact hprev

lemma adm_ph {n : ℕ} (i0 i1 : Fin n) (w : ℕ) : Admissible (ph i0 i1 w) := by
  intro j i h
  rw [ph_get] at h
  split_ifs at h with h0 h1 h2
  · simp at h
  · simp only [Option.some.injEq, Req.write.injEq] at h
    subst h
    refine ⟨by omega, ?_⟩
    rw [ph_get]
    by_cases hj : j - 1 = 0
    · left; simp [hj]
    · right; rw [if_neg hj, if_pos (by omega)]
  · simp at h

lemma adm_sq {n : ℕ} (i0 i1 : Fin n) (p : ℕ) : ∀ ks : List ℕ, Admissible (sq i0 i1 p ks) := by
  intro ks
  induction ks with
  | nil => intro j i h; simp [sq] at h
  | cons k ks ih =>
    have e : sq i0 i1 p (k :: ks) = ph i0 i1 (ww p k) ++ sq i0 i1 p ks := by simp [sq]
    rw [e]
    apply adm_append _ _ (adm_ph i0 i1 _) ih
    intro i
    cases ks with
    | nil => simp [sq]
    | cons k' ks' =>
      have e' : sq i0 i1 p (k' :: ks') = ph i0 i1 (ww p k') ++ sq i0 i1 p ks' := by simp [sq]
      rw [e', List.getElem?_append_left (by simp [ph_length]), ph_get]
      simp


/-! ### weighted trees -/

noncomputable def Wt (p : ℕ) (f : List ℕ → ℝ≥0∞) : ℕ → List ℕ → ℝ≥0∞
  | 0, ks => f ks
  | N + 1, ks => ∑ k ∈ Finset.range (p + 1), ENNReal.ofReal (qq p k) * Wt p f N (ks ++ [k])

lemma sum_ofReal_qq (p : ℕ) : ∑ k ∈ Finset.range (p + 1), ENNReal.ofReal (qq p k) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => qq_nonneg p k), sum_qq]; simp

lemma Wt_mono (p : ℕ) (f g : List ℕ → ℝ≥0∞) (hfg : ∀ ks, f ks ≤ g ks) :
    ∀ N ks, Wt p f N ks ≤ Wt p g N ks := by
  intro N
  induction N with
  | zero => intro ks; exact hfg ks
  | succ N ih =>
    intro ks
    simp only [Wt]
    gcongr with k hk
    exact ih _

lemma Wt_lower {n : ℕ} (A : OnlineAlgorithm n) (p : ℕ) (i0 i1 : Fin n) (hne : i0 ≠ i1) :
    ∀ (N : ℕ) ks, A.cost p (sq i0 i1 p ks) + (N : ℝ≥0∞) * p ≤
      Wt p (fun ks => A.cost p (sq i0 i1 p ks)) N ks := by
  intro N
  induction N with
  | zero => intro ks; simp [Wt]
  | succ N ih =>
    intro ks
    simp only [Wt]
    set B : ℕ → Bool := fun j => decide (A.after (PP i1 (sq i0 i1 p ks) j) = some i1)
    have h1 : ∀ k ∈ Finset.range (p + 1),
        ENNReal.ofReal (qq p k) * (A.cost p (sq i0 i1 p ks) + (N : ℝ≥0∞) * p +
          (LL p B k : ℝ≥0∞)) ≤
        ENNReal.ofReal (qq p k) * Wt p (fun ks => A.cost p (sq i0 i1 p ks)) N (ks ++ [k]) := by
      intro k _
      gcongr
      refine le_trans ?_ (ih _)
      rw [sq_snoc]
      have := phase_cost A p i0 i1 hne (sq i0 i1 p ks) k
      calc _ = A.cost p (sq i0 i1 p ks) + (LL p B k : ℝ≥0∞) + (N : ℝ≥0∞) * p := by ring
        _ ≤ _ := by gcongr
    refine le_trans ?_ (Finset.sum_le_sum h1)
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, sum_ofReal_qq, one_mul]
    have h2 : (p : ℝ≥0∞) ≤ ∑ k ∈ Finset.range (p + 1), ENNReal.ofReal (qq p k) * (LL p B k : ℝ≥0∞) := by
      have e : ∑ k ∈ Finset.range (p + 1), ENNReal.ofReal (qq p k) * (LL p B k : ℝ≥0∞)
          = ENNReal.ofReal (∑ k ∈ Finset.range (p + 1), qq p k * (LL p B k : ℝ)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (qq_nonneg p k) (by positivity))]
        apply Finset.sum_congr rfl; intro k _
        rw [ENNReal.ofReal_mul (qq_nonneg p k)]; simp
      rw [e]
      have := sum_qq_LL p B
      calc (p : ℝ≥0∞) = ENNReal.ofReal (p : ℝ) := by simp
        _ ≤ _ := ENNReal.ofReal_le_ofReal this
    push_cast
    calc A.cost p (sq i0 i1 p ks) + (N + 1 : ℝ≥0∞) * p
        = A.cost p (sq i0 i1 p ks) + (N : ℝ≥0∞) * p + p := by ring
      _ ≤ _ := by
        gcongr
        rw [← Finset.sum_mul, sum_ofReal_qq, one_mul]

lemma Wt_upper (p : ℕ) (f : List ℕ → ℝ≥0∞) (c a : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hf : ∀ ks, (∀ k ∈ ks, k ≤ p) → f ks ≤ ENNReal.ofReal (c * (p + (ks.sum : ℝ)) + a)) :
    ∀ (N : ℕ) ks, (∀ k ∈ ks, k ≤ p) → Wt p f N ks ≤
      ENNReal.ofReal (c * (p + (ks.sum : ℝ) + N * (p * (1 - rr p ^ p))) + a) := by
  intro N
  induction N with
  | zero => intro ks hks; simpa [Wt] using hf ks hks
  | succ N ih =>
    intro ks hks
    simp only [Wt]
    have h1 : ∀ k ∈ Finset.range (p + 1), ENNReal.ofReal (qq p k) * Wt p f N (ks ++ [k]) ≤
        ENNReal.ofReal (qq p k * (c * (p + (ks.sum : ℝ) + N * (p * (1 - rr p ^ p))) + a + c * k)) := by
      intro k hk
      have hk' : k ≤ p := by have := Finset.mem_range.mp hk; omega
      rw [ENNReal.ofReal_mul (qq_nonneg p k)]
      gcongr
      refine le_trans (ih (ks ++ [k]) ?_) (le_of_eq ?_)
      · intro k' hk'; simp at hk'; rcases hk' with h | h
        · exact hks k' h
        · omega
      · congr 1; simp; ring
    refine le_trans (Finset.sum_le_sum h1) ?_
    have hnn : ∀ k ∈ Finset.range (p + 1), 0 ≤ qq p k * (c * (p + (ks.sum : ℝ) + N * (p * (1 - rr p ^ p))) + a + c * k) := by
      intro k _
      apply mul_nonneg (qq_nonneg p k)
      have : 0 ≤ 1 - rr p ^ p := by
        have h0 := rr_nonneg p
        have h1 : rr p ≤ 1 := by unfold rr; rw [div_le_one (by positivity)]; linarith
        linarith [pow_le_one₀ h0 h1 (n := p)]
      positivity
    rw [← ENNReal.ofReal_sum_of_nonneg hnn]
    apply le_of_eq
    congr 1
    have e1 := sum_qq p
    have e2 := sum_qq_k p
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [e1]
    have e3 : ∑ k ∈ Finset.range (p + 1), qq p k * (c * (k : ℝ)) = c * (p * (1 - rr p ^ p)) := by
      rw [← e2, Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    rw [e3]; push_cast; ring


open MeasureTheory

lemma Wt_meas {n p : ℕ} (A : RandomizedAlgorithm n p) (i0 i1 : Fin n) :
    ∀ (N : ℕ) ks, @Measurable A.ι ℝ≥0∞ A.ms _
      (fun ω => Wt p (fun ks => (A.alg ω).cost p (sq i0 i1 p ks)) N ks) := by
  letI := A.ms
  intro N
  induction N with
  | zero => intro ks; exact A.meas _
  | succ N ih =>
    intro ks
    simp only [Wt]
    exact Finset.measurable_sum _ (fun k _ => (ih _).const_mul _)

lemma Wt_lint {n p : ℕ} (A : RandomizedAlgorithm n p) (i0 i1 : Fin n) :
    ∀ (N : ℕ) ks, @lintegral A.ι A.ms A.μ
      (fun ω => Wt p (fun ks => (A.alg ω).cost p (sq i0 i1 p ks)) N ks) =
      Wt p (fun ks => A.expCost (sq i0 i1 p ks)) N ks := by
  letI := A.ms
  intro N
  induction N with
  | zero => intro ks; simp [Wt, RandomizedAlgorithm.expCost]
  | succ N ih =>
    intro ks
    simp only [Wt]
    rw [lintegral_finsetSum _ (fun k _ => (Wt_meas A i0 i1 N _).const_mul _)]
    apply Finset.sum_congr rfl
    intro k _
    rw [lintegral_const_mul _ (Wt_meas A i0 i1 N _), ih]

theorem nbr_core (n p : ℕ) (hn : 2 ≤ n) (hp : 1 ≤ p) (s₀ : State n)
    (A : RandomizedAlgorithm n p) (c : ℝ) (hA : A.IsCompetitiveFrom s₀ c) :
    ep p / (ep p - 1) ≤ c := by
  letI := A.ms
  haveI := A.prob
  obtain ⟨_, a, ha⟩ := hA
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set c' := max c 0
  set a' := max a 0
  have hc' : 0 ≤ c' := le_max_right _ _
  have ha' : 0 ≤ a' := le_max_right _ _
  set m : ℝ := p * (1 - rr p ^ p)
  -- bound function
  have hf : ∀ ks : List ℕ, (∀ k ∈ ks, k ≤ p) → A.expCost (sq i0 i1 p ks) ≤
      ENNReal.ofReal (c' * (p + (ks.sum : ℝ)) + a') := by
    intro ks hks
    refine le_trans (ha _ (adm_sq i0 i1 p ks)) ?_
    apply ENNReal.ofReal_le_ofReal
    have hopt := offline_le p _ s₀ _ (sched_seq p i0 i1 hne ks s₀ hks)
    have hle : (offlineCost p s₀ (sq i0 i1 p ks)).toReal ≤ p + (ks.sum : ℝ) := by
      have : (if s₀ = none then 0 else (p : ℝ≥0∞)) + ((ks.sum : ℕ) : ℝ≥0∞)
          ≤ ENNReal.ofReal (p + (ks.sum : ℝ)) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        simp only [ENNReal.ofReal_natCast]
        gcongr
        split_ifs <;> simp
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hopt.trans this)
    have h0 : 0 ≤ (offlineCost p s₀ (sq i0 i1 p ks)).toReal := ENNReal.toReal_nonneg
    calc c * (offlineCost p s₀ (sq i0 i1 p ks)).toReal + a
        ≤ c' * (offlineCost p s₀ (sq i0 i1 p ks)).toReal + a' := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_left _ _
      _ ≤ _ := by gcongr
  have key : ∀ N : ℕ, (N : ℝ) * p ≤ c' * (p + N * m) + a' := by
    intro N
    have h1 : ∀ ω, (N : ℝ≥0∞) * p ≤
        Wt p (fun ks => (A.alg ω).cost p (sq i0 i1 p ks)) N [] :=
      fun ω => le_trans le_add_self (Wt_lower (A.alg ω) p i0 i1 hne N [])
    have h2 : (N : ℝ≥0∞) * p ≤ ∫⁻ ω, Wt p (fun ks => (A.alg ω).cost p (sq i0 i1 p ks)) N [] ∂A.μ := by
      calc (N : ℝ≥0∞) * p = ∫⁻ _ω, (N : ℝ≥0∞) * p ∂A.μ := by simp
        _ ≤ _ := lintegral_mono h1
    rw [Wt_lint] at h2
    have hmono := Wt_mono p (fun ks => A.expCost (sq i0 i1 p ks))
      (fun ks => if ∀ k ∈ ks, k ≤ p then A.expCost (sq i0 i1 p ks) else ⊤)
      (fun ks => by split_ifs <;> simp) N []
    have h3 := le_trans hmono (Wt_upper p
      (fun ks => if ∀ k ∈ ks, k ≤ p then A.expCost (sq i0 i1 p ks) else ⊤) c' a' hc' ha'
      (fun ks hks => (if_pos hks).trans_le (hf ks hks)) N [] (by simp))
    have h4 := h2.trans h3
    simp only [List.sum_nil, Nat.cast_zero, add_zero] at h4
    have hpos : 0 ≤ c' * (p + N * m) + a' := by
      have : 0 ≤ m := by
        have h0 := rr_nonneg p
        have h1 : rr p ≤ 1 := by unfold rr; rw [div_le_one (by positivity)]; linarith
        have := pow_le_one₀ h0 h1 (n := p)
        simp only [m]; apply mul_nonneg (by positivity); linarith
      positivity
    rw [ENNReal.le_ofReal_iff_toReal_le (ENNReal.mul_ne_top (by simp) (by simp)) hpos] at h4
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h4
    exact h4
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hcm : (p : ℝ) ≤ c' * m := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨N, hN⟩ := exists_nat_gt ((c' * p + a') / (p - c' * m))
    have hd : 0 < (p : ℝ) - c' * m := by linarith
    have := key N
    rw [div_lt_iff₀ hd] at hN
    nlinarith
  have hr0 : 0 < rr p := by unfold rr; positivity
  have hr1 : rr p < 1 := by unfold rr; rw [div_lt_one (by positivity)]; linarith
  have hrp : rr p ^ p < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have hrp0 : 0 < rr p ^ p := pow_pos hr0 p
  have hep := rr_pow_ep p hp
  have hep1 : 1 < ep p := by
    by_contra h; push_neg at h
    nlinarith
  have hc'1 : 1 ≤ c' * (1 - rr p ^ p) := by
    simp only [m] at hcm
    have : (p : ℝ) * 1 ≤ p * (c' * (1 - rr p ^ p)) := by nlinarith
    exact le_of_mul_le_mul_left this (by linarith)
  have hfin : ep p / (ep p - 1) ≤ c' := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hpos : 0 < ep p / (ep p - 1) := div_pos (by linarith) (by linarith)
  rcases le_total c 0 with h | h
  · have : c' = 0 := max_eq_right h
    linarith
  · have : c' = c := max_eq_left h
    linarith

end NBR
end NonuniformCompetitive.Snoopy

open NonuniformCompetitive.Snoopy


theorem solution (n p : ℕ) (hn : 2 ≤ n) (hp : 1 ≤ p) (s₀ : State n)
    (A : RandomizedAlgorithm n p) (c : ℝ) (hA : A.IsCompetitiveFrom s₀ c) :
    ep p / (ep p - 1) ≤ c := by
  exact NBR.nbr_core n p hn hp s₀ A c hA
