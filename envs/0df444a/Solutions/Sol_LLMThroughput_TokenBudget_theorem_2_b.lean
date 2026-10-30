-- Prove2me | solution 1 for LLMThroughput.TokenBudget.theorem_2_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T14:02:25.581975+00:00
-- url     : https://prove2.me/submissions/973d3259-a3fc-4110-b619-5b4987c74041

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Model

namespace LLMThroughput.TokenBudget.Core
open LLMThroughput.TokenBudget

/-! ### Fresh arrivals -/

def freshList : ℕ → List (ℕ × ℕ) → List Req
  | _, [] => []
  | n, s :: l => ({ label := n, P := s.1, D := s.2 } : Req) :: freshList (n + 1) l

theorem mapIdx_fresh (n : ℕ) (arr : List (ℕ × ℕ)) :
    arr.mapIdx (fun k s => ({ label := n + k, P := s.1, D := s.2 } : Req)) = freshList n arr := by
  induction arr generalizing n with
  | nil => simp [freshList]
  | cons s l ih =>
    rw [List.mapIdx_cons, freshList]
    have : (fun i (s : ℕ × ℕ) => ({ label := n + (i + 1), P := s.1, D := s.2 } : Req)) =
        (fun k (s : ℕ × ℕ) => ({ label := (n + 1) + k, P := s.1, D := s.2 } : Req)) := by
      funext i s; congr 1; omega
    simp only [Nat.add_zero]
    rw [this, ih]

theorem freshList_mem (n : ℕ) (arr : List (ℕ × ℕ)) :
    ∀ r ∈ freshList n arr, n ≤ r.label ∧ r.label < n + arr.length ∧ (r.P, r.D) ∈ arr := by
  induction arr generalizing n with
  | nil => simp [freshList]
  | cons s l ih =>
    intro r hr
    simp only [freshList, List.mem_cons] at hr
    rcases hr with rfl | hr
    · simp
    · have := ih (n + 1) r hr
      simp only [List.length_cons, List.mem_cons]
      refine ⟨by omega, by omega, Or.inr this.2.2⟩

theorem freshList_pairwise (n : ℕ) (arr : List (ℕ × ℕ)) :
    (freshList n arr).Pairwise (fun r s => r.label < s.label) := by
  induction arr generalizing n with
  | nil => simp [freshList]
  | cons s l ih =>
    simp only [freshList, List.pairwise_cons]
    refine ⟨fun r hr => ?_, ih (n + 1)⟩
    have := (freshList_mem (n + 1) l r hr).1
    omega

theorem freshList_tokens (n : ℕ) (arr : List (ℕ × ℕ)) :
    ((freshList n arr).map fun r => r.P + r.D).sum = (arr.map fun s => s.1 + s.2).sum := by
  induction arr generalizing n with
  | nil => simp [freshList]
  | cons s l ih => simp [freshList, ih]

theorem freshList_length (n : ℕ) (arr : List (ℕ × ℕ)) :
    (freshList n arr).length = arr.length := by
  induction arr generalizing n with
  | nil => simp [freshList]
  | cons s l ih => simp [freshList, ih]

/-! ### applyAlloc -/

theorem applyAlloc_cons (r : Req) (rs : List Req) (d : ℕ × ℕ) (ds : Alloc) :
    applyAlloc (r :: rs) (d :: ds) = { r with P := r.P - d.1, D := r.D - d.2 } :: applyAlloc rs ds := by
  simp [applyAlloc]

theorem applyAlloc_labels {F : Req → ℕ × ℕ → Prop} {reqs : List Req} {δ : Alloc}
    (h : List.Forall₂ F reqs δ) : (applyAlloc reqs δ).map Req.label = reqs.map Req.label := by
  induction h with
  | nil => simp [applyAlloc]
  | cons _ _ ih => rw [applyAlloc_cons]; simp [ih]

theorem applyAlloc_mem {F : Req → ℕ × ℕ → Prop} {reqs : List Req} {δ : Alloc}
    (h : List.Forall₂ F reqs δ) :
    ∀ r' ∈ applyAlloc reqs δ, ∃ r ∈ reqs, ∃ d : ℕ × ℕ, F r d ∧
      r' = { r with P := r.P - d.1, D := r.D - d.2 } := by
  induction h with
  | nil => simp [applyAlloc]
  | @cons r d rs ds hrd _ ih =>
    intro r' hr'
    rw [applyAlloc_cons, List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · exact ⟨r, by simp, d, hrd, rfl⟩
    · obtain ⟨r0, hr0, d0, h0, e⟩ := ih r' hr'
      exact ⟨r0, by simp [hr0], d0, h0, e⟩

theorem applyAlloc_countD {F : Req → ℕ × ℕ → Prop} {reqs : List Req} {δ : Alloc}
    (h : List.Forall₂ F reqs δ) (hF : ∀ r d, F r d → d.2 ≤ r.D) (hall : ∀ r ∈ reqs, 1 ≤ r.D) :
    ((applyAlloc reqs δ).filter fun r => r.D = 0).length ≤ decodeLoad δ := by
  induction h with
  | nil => simp [applyAlloc]
  | @cons r d rs ds hrd _ ih =>
    have ih := ih (fun r hr => hall r (by simp [hr]))
    have h1 := hall r (by simp)
    have h2 := hF r d hrd
    rw [applyAlloc_cons, List.filter_cons]
    simp only [decodeLoad, List.map_cons, List.sum_cons] at ih ⊢
    split
    · rename_i hd
      simp only [decide_eq_true_eq] at hd
      simp only [List.length_cons]; omega
    · omega

theorem applyAlloc_tokens {reqs : List Req} {δ : Alloc}
    (h : List.Forall₂ (fun r d => d.1 ≤ r.P ∧ d.2 ≤ r.D) reqs δ) :
    ((applyAlloc reqs δ).map fun r => r.P + r.D).sum + load δ = (reqs.map fun r => r.P + r.D).sum := by
  induction h with
  | nil => simp [applyAlloc, load]
  | @cons r d rs ds hrd _ ih =>
    rw [applyAlloc_cons]
    simp only [load, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem decodeLoad_le_load (δ : Alloc) : decodeLoad δ ≤ load δ := by
  induction δ with
  | nil => simp [decodeLoad, load]
  | cons d ds ih => simp only [decodeLoad, load, List.map_cons, List.sum_cons] at ih ⊢; omega

theorem prefillLoad_le_load (δ : Alloc) : prefillLoad δ ≤ load δ := by
  induction δ with
  | nil => simp [prefillLoad, load]
  | cons d ds ih => simp only [prefillLoad, load, List.map_cons, List.sum_cons] at ih ⊢; omega

theorem load_eq_zero {δ : Alloc} (h : load δ = 0) : ∀ d ∈ δ, d = (0, 0) := by
  induction δ with
  | nil => simp
  | cons d ds ih =>
    simp only [load, List.map_cons, List.sum_cons] at h
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · ext <;> simp <;> omega
    · exact ih (by simp only [load]; omega) e he

theorem applyAlloc_zero {F : Req → ℕ × ℕ → Prop} {reqs : List Req} {δ : Alloc}
    (h : List.Forall₂ F reqs δ) (hz : load δ = 0) : applyAlloc reqs δ = reqs := by
  induction h with
  | nil => simp [applyAlloc]
  | @cons r d rs ds hrd _ ih =>
    rw [applyAlloc_cons]
    have h0 := load_eq_zero hz d (by simp)
    have hz' : load ds = 0 := by simp only [load, List.map_cons, List.sum_cons] at hz ⊢; omega
    rw [ih hz', h0]
    simp

/-! ### Parameters -/

theorem t_zero_load (P : Params) (hP : P.Valid) (b : ℕ) (h : P.t b = 0) : b = 0 := by
  obtain ⟨hb0, ⟨k, hk⟩, hbm, ht⟩ := hP
  unfold Params.t at h ht
  by_contra hb
  have h1 : 1 ≤ (b + P.b0 - 1) / P.b0 := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hc : P.c = 0 := by omega
  have ha : P.a = 0 := by
    rcases Nat.eq_zero_or_pos P.a with h' | h'
    · exact h'
    · have : 0 < P.a * ((b + P.b0 - 1) / P.b0) := Nat.mul_pos h' h1
      omega
  rw [hc, ha] at ht; simp at ht

theorem t_mono (P : Params) {b b' : ℕ} (h : b ≤ b') : P.t b ≤ P.t b' := by
  unfold Params.t
  have : (b + P.b0 - 1) / P.b0 ≤ (b' + P.b0 - 1) / P.b0 := Nat.div_le_div_right (by omega)
  have := Nat.mul_le_mul_left P.a this
  omega

/-! ### One step -/

theorem step_R (P : Params) (π : Policy) (x : State) (arr : List (ℕ × ℕ)) :
    (step P π x arr).R = if 0 < x.R then x.R - 1
      else if 0 < P.t (load (π x)) then P.t (load (π x)) - 1 else 0 := by
  by_cases h : x.R = 0
  · simp [step, batchOf, h]
  · have : 0 < x.R := Nat.pos_of_ne_zero h
    simp [step, h, this]

theorem step_next (P : Params) (π : Policy) (x : State) (arr : List (ℕ × ℕ)) :
    (step P π x arr).next = x.next + arr.length := by
  simp [step]

/-- Generic shape of the requests after one step. -/
theorem step_reqs (P : Params) (π : Policy) (x : State) (arr : List (ℕ × ℕ)) :
    ∃ L : List Req, (step P π x arr).reqs = L ++ freshList x.next arr ∧
      ((x.R = 0 → L = applyAlloc x.reqs (π x) ∨
          L = (applyAlloc x.reqs (π x)).filter (fun r => decide (r.D ≠ 0))) ∧
       (0 < x.R → L = x.reqs ∨ L = x.reqs.filter (fun r => decide (r.D ≠ 0)))) ∧
      ((step P π x arr).R = 0 → (0 < x.R ∨ 0 < P.t (load (π x))) →
        ∀ r ∈ L, r.D ≠ 0) := by
  by_cases h : x.R = 0
  · by_cases hd : (0 < P.t (load (π x)) ∧ P.t (load (π x)) - 1 = 0)
    · refine ⟨(applyAlloc x.reqs (π x)).filter (fun r => decide (r.D ≠ 0)), ?_, ?_, ?_⟩
      · simp [step, batchOf, h, hd, mapIdx_fresh]
      · exact ⟨fun _ => Or.inr rfl, fun h' => by omega⟩
      · intro _ _ r hr; simpa using (List.mem_filter.1 hr).2
    · refine ⟨applyAlloc x.reqs (π x), ?_, ?_, ?_⟩
      · simp only [step, batchOf, h, if_true, mapIdx_fresh]
        congr 1
        rw [if_neg]
        simp only [decide_eq_true_eq, lt_irrefl, false_or, not_and]
        intro h1
        have : ¬ (if 0 < 0 then 0 - 1 else if 0 < P.t (load (π x)) then P.t (load (π x)) - 1 else 0) = 0 := by
          simp only [lt_irrefl, if_false, if_pos h1]; exact fun h2 => hd ⟨h1, h2⟩
        exact this
      · exact ⟨fun _ => Or.inl rfl, fun h' => by omega⟩
      · intro hR hpos
        rw [step_R] at hR
        simp only [h, lt_irrefl, if_false, false_or] at hR hpos
        rw [if_pos hpos] at hR
        exact absurd ⟨hpos, hR⟩ hd
  · have hpos : 0 < x.R := Nat.pos_of_ne_zero h
    by_cases hd : x.R - 1 = 0
    · refine ⟨x.reqs.filter (fun r => decide (r.D ≠ 0)), ?_, ?_, ?_⟩
      · simp [step, batchOf, h, hd, hpos, mapIdx_fresh]
      · exact ⟨fun h' => absurd h' h, fun _ => Or.inr rfl⟩
      · intro _ _ r hr; simpa using (List.mem_filter.1 hr).2
    · refine ⟨x.reqs, ?_, ?_, ?_⟩
      · simp [step, batchOf, h, hd, hpos, mapIdx_fresh]
      · exact ⟨fun h' => absurd h' h, fun _ => Or.inl rfl⟩
      · intro hR; rw [step_R] at hR; simp [hpos] at hR; omega

/-! ### Admissibility is invariant -/

def GoodL (bmax next : ℕ) (L : List Req) : Prop :=
  L.Pairwise (fun r s => r.label < s.label) ∧ (∀ r ∈ L, r.label < next) ∧
  (∀ r ∈ L, 0 < r.P → 1 ≤ r.D) ∧ (L.filter fun r => r.D = 0).length ≤ bmax

theorem GoodL_filter {bmax next : ℕ} {L : List Req} (h : GoodL bmax next L) :
    GoodL bmax next (L.filter fun r => decide (r.D ≠ 0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1.filter _, fun r hr => h2 r (List.mem_filter.1 hr).1,
    fun r hr => h3 r (List.mem_filter.1 hr).1, ?_⟩
  rw [List.filter_filter]
  have : (L.filter fun r => decide (r.D = 0) && decide (r.D ≠ 0)) = [] := by
    rw [List.filter_eq_nil_iff]; intro r _; simp
  rw [this]; simp

theorem GoodL_of_adm {bmax : ℕ} {x : State} (hx : Admissible bmax x) : GoodL bmax x.next x.reqs :=
  ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.2⟩

theorem GoodL_applyAlloc (P : Params) (π : Policy) (hπ : IsScheduler P π) (x : State)
    (hx : Admissible P.bmax x) (hR : x.R = 0) :
    GoodL P.bmax x.next (applyAlloc x.reqs (π x)) := by
  have hf := hπ x hx hR
  obtain ⟨h2, hload⟩ := hf
  have hlab := applyAlloc_labels h2
  have hmem := applyAlloc_mem h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← List.pairwise_map (R := fun a b => a < b), hlab, List.pairwise_map]; exact hx.1
  · intro r' hr'
    obtain ⟨r, hr, d, _, rfl⟩ := hmem r' hr'
    exact hx.2.1 r hr
  · intro r' hr' hP'
    obtain ⟨r, hr, d, hF, rfl⟩ := hmem r' hr'
    simp only at hP' ⊢
    have hrP : 0 < r.P := by omega
    have := hF.1 hrP
    have := hx.2.2.2.1 hR r hr
    omega
  · have := applyAlloc_countD h2 (fun r d h => h.2.2.2) (hx.2.2.2.1 hR)
    have := decodeLoad_le_load (π x)
    omega

theorem step_adm (P : Params) (hP : P.Valid) (π : Policy) (hπ : IsScheduler P π) (x : State)
    (hx : Admissible P.bmax x) (arr : List (ℕ × ℕ)) (harr : ∀ s ∈ arr, 1 ≤ s.2) :
    Admissible P.bmax (step P π x arr) := by
  obtain ⟨L, hreq, ⟨hL0, hL1⟩, hzero⟩ := step_reqs P π x arr
  have hG : GoodL P.bmax x.next L := by
    by_cases hR : x.R = 0
    · rcases hL0 hR with rfl | rfl
      · exact GoodL_applyAlloc P π hπ x hx hR
      · exact GoodL_filter (GoodL_applyAlloc P π hπ x hx hR)
    · rcases hL1 (Nat.pos_of_ne_zero hR) with rfl | rfl
      · exact GoodL_of_adm hx
      · exact GoodL_filter (GoodL_of_adm hx)
  obtain ⟨g1, g2, g3, g4⟩ := hG
  have hfr := freshList_mem x.next arr
  have hfrD : ∀ r ∈ freshList x.next arr, 1 ≤ r.D := fun r hr => harr _ (hfr r hr).2.2
  rw [Admissible, hreq, step_next]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨g1, freshList_pairwise _ _, fun r hr s hs => ?_⟩
    have := g2 r hr; have := (hfr s hs).1; omega
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · have := g2 r hr; omega
    · exact (hfr r hr).2.1
  · intro r hr hp
    rcases List.mem_append.1 hr with hr | hr
    · exact g3 r hr hp
    · exact hfrD r hr
  · intro hR r hr
    rcases List.mem_append.1 hr with hr | hr
    · by_cases hcase : 0 < x.R ∨ 0 < P.t (load (π x))
      · have := hzero hR hcase r hr
        omega
      · push Not at hcase
        have hx0 : x.R = 0 := by omega
        have ht0 : P.t (load (π x)) = 0 := by omega
        have hb := t_zero_load P hP _ ht0
        rcases hL0 hx0 with rfl | rfl
        · rw [applyAlloc_zero (hπ x hx hx0).1 hb] at hr
          exact hx.2.2.2.1 hx0 r hr
        · have := (List.mem_filter.1 hr).2
          simp at this; omega
    · exact hfrD r hr
  · rw [List.filter_append]
    have : ((freshList x.next arr).filter fun r => r.D = 0) = [] := by
      rw [List.filter_eq_nil_iff]; intro r hr; have := hfrD r hr; simp; omega
    rw [this]; simpa using g4

theorem run_adm (P : Params) (hP : P.Valid) (π : Policy) (hπ : IsScheduler P π) (x : State)
    (hx : Admissible P.bmax x) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ) (hv : ∀ i, 1 ≤ (v i).2) :
    ∀ n, Admissible P.bmax (run P π x a v n) := by
  intro n
  induction n with
  | zero => exact hx
  | succ n ih =>
    refine step_adm P hP π hπ _ ih _ ?_
    intro s hs
    simp only [slotArrivals, List.mem_map] at hs
    obtain ⟨k, _, rfl⟩ := hs
    exact hv _

/-! ### Abstract batch timing -/

section Timing

variable (R τ : ℕ → ℕ)

def RDyn : Prop := ∀ m, R (m + 1) = if 0 < R m then R m - 1 else if 0 < τ m then τ m - 1 else 0

variable {R τ}

theorem busy (hR : RDyn R τ) {m : ℕ} (h0 : R m = 0) (hτ : 0 < τ m) :
    ∀ j, 1 ≤ j → j ≤ τ m → R (m + j) = τ m - j := by
  intro j hj1 hj2
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hR, h0]; simp [hτ]
    · have := ih hj (by omega)
      rw [← Nat.add_assoc, hR, this, if_pos (by omega)]
      omega

theorem gap (hR : RDyn R τ) {m m' : ℕ} (h0 : R m = 0) (hτ : 0 < τ m) (h0' : R m' = 0)
    (hlt : m < m') : m + τ m ≤ m' := by
  by_contra hc
  have := busy hR h0 hτ (m' - m) (by omega) (by omega)
  rw [show m + (m' - m) = m' by omega, h0'] at this
  omega

theorem interval_sum (hR : RDyn R τ) (N2 : ℕ) :
    ∀ N1, N1 ≤ N2 → ∑ m ∈ Finset.Ico N1 N2,
      (if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ N2 then τ m else 0) ≤ N2 - N1 := by
  intro N1
  induction h : N2 - N1 using Nat.strong_induction_on generalizing N1 with
  | _ k ih =>
    intro hN
    rcases Nat.eq_or_lt_of_le hN with rfl | hlt
    · simp
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
    split
    · rename_i hc
      obtain ⟨h0, hτ, hle⟩ := hc
      rw [← Finset.sum_Ico_consecutive _ (show N1 + 1 ≤ N1 + τ N1 by omega) hle]
      have hz : ∑ m ∈ Finset.Ico (N1 + 1) (N1 + τ N1),
          (if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ N2 then τ m else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        rw [Finset.mem_Ico] at hm
        rw [if_neg]
        rintro ⟨hm0, -, -⟩
        have := gap hR h0 hτ hm0 (by omega)
        omega
      rw [hz]
      have := ih (N2 - (N1 + τ N1)) (by omega) (N1 + τ N1) rfl hle
      omega
    · have := ih (N2 - (N1 + 1)) (by omega) (N1 + 1) rfl (by omega)
      omega

/-- Abstract form of (43). -/
theorem abstract_43 (hR : RDyn R τ) (tok : ℕ → ℕ) (bmax T : ℕ) (hT : 0 < T)
    (h1 : ∀ m, R m = 0 → tok m * T ≤ bmax * τ m) (h2 : ∀ m, R m = 0 → tok m ≤ bmax)
    (n1 n2 : ℕ) (hn : n1 ≤ n2) :
    (∑ m ∈ Finset.range (n2 * T), if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ n2 * T then tok m else 0)
      ≤ (∑ m ∈ Finset.range (n1 * T), if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ n1 * T then tok m else 0)
        + (n2 - n1 + 1) * bmax := by
  set N1 := n1 * T
  set N2 := n2 * T
  have hN : N1 ≤ N2 := Nat.mul_le_mul_right _ hn
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le N1) hN, ← Finset.range_eq_Ico]
  -- part 1: batches formed before N1
  have p1 : (∑ m ∈ Finset.range N1, if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ N2 then tok m else 0)
      ≤ (∑ m ∈ Finset.range N1, if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ N1 then tok m else 0) + bmax := by
    let h : ℕ → ℕ := fun m => if R m = 0 ∧ 0 < τ m ∧ N1 < m + τ m then tok m else 0
    have hle : ∀ m, (if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ N2 then tok m else 0)
        ≤ (if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ N1 then tok m else 0) + h m := by
      intro m
      simp only [h]
      split_ifs <;> omega
    have hsum : ∑ m ∈ Finset.range N1, h m ≤ bmax := by
      by_cases hex : ∃ m0 ∈ Finset.range N1, h m0 ≠ 0
      · obtain ⟨m0, hm0, hne⟩ := hex
        have hc0 : R m0 = 0 ∧ 0 < τ m0 ∧ N1 < m0 + τ m0 := by
          by_contra hc; exact hne (by simp only [h]; rw [if_neg hc])
        rw [Finset.sum_eq_single_of_mem m0 hm0]
        · simp only [h]; rw [if_pos hc0]; exact h2 m0 hc0.1
        · intro m hm hmne
          simp only [h]
          rw [if_neg]
          rintro ⟨hm1, hm2, hm3⟩
          rw [Finset.mem_range] at hm hm0
          rcases Nat.lt_or_gt_of_ne hmne with hlt | hlt
          · have := gap hR hm1 hm2 hc0.1 hlt; omega
          · have := gap hR hc0.1 hc0.2.1 hm1 hlt; omega
      · push Not at hex
        rw [Finset.sum_eq_zero hex]; exact Nat.zero_le _
    calc _ ≤ ∑ m ∈ Finset.range N1, ((if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ N1 then tok m else 0) + h m) :=
          Finset.sum_le_sum fun m _ => hle m
      _ = _ + _ := Finset.sum_add_distrib
      _ ≤ _ := by omega
  -- part 2: batches formed in [N1, N2)
  have p2 : (∑ m ∈ Finset.Ico N1 N2, if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ N2 then tok m else 0)
      ≤ (n2 - n1) * bmax := by
    have hI := interval_sum hR N2 N1 hN
    have hmul : (∑ m ∈ Finset.Ico N1 N2, if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ N2 then tok m else 0) * T
        ≤ bmax * ∑ m ∈ Finset.Ico N1 N2, (if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ N2 then τ m else 0) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m _
      split_ifs with hc
      · exact h1 m hc.1
      · simp
    have : N2 - N1 = (n2 - n1) * T := by simp only [N1, N2]; rw [Nat.sub_mul]
    rw [this] at hI
    have h3 := le_trans hmul (Nat.mul_le_mul_left bmax hI)
    rw [show bmax * ((n2 - n1) * T) = ((n2 - n1) * bmax) * T by ring] at h3
    exact Nat.le_of_mul_le_mul_right h3 hT
  have : (n2 - n1 + 1) * bmax = (n2 - n1) * bmax + bmax := by ring
  omega

end Timing

theorem rate_bound_nat (P : Params) (hP : P.Valid) (b : ℕ) (hb : b ≤ P.bmax) :
    b * P.t P.bmax ≤ P.bmax * P.t b := by
  obtain ⟨hb0, ⟨k, hk⟩, _, _⟩ := hP
  have hkmax : (P.bmax + P.b0 - 1) / P.b0 = k := by
    rw [hk]
    have : P.b0 * k + P.b0 - 1 = (P.b0 - 1) + P.b0 * k := by omega
    rw [this, Nat.add_mul_div_left _ _ (by omega)]
    rw [Nat.div_eq_of_lt (by omega)]; simp
  set j := (b + P.b0 - 1) / P.b0 with hj
  have hbj : b ≤ P.b0 * j := by
    have := Nat.lt_mul_div_succ (b + P.b0 - 1) (show 0 < P.b0 by omega)
    rw [← hj, Nat.mul_succ] at this
    generalize P.b0 * j = m at this ⊢
    omega
  have hjk : j ≤ k := by
    rw [hj, ← hkmax]
    exact Nat.div_le_div_right (by omega)
  unfold Params.t
  rw [hkmax, ← hj, hk]
  calc b * (P.c + P.a * k) ≤ (P.b0 * j) * (P.c + P.a * k) := Nat.mul_le_mul_right _ hbj
    _ = P.b0 * (j * P.c + P.a * j * k) := by ring
    _ ≤ P.b0 * (k * P.c + P.a * j * k) := by
        apply Nat.mul_le_mul_left; apply Nat.add_le_add_right; exact Nat.mul_le_mul_right _ hjk
    _ = P.b0 * k * (P.c + P.a * j) := by ring

theorem run_RDyn (P : Params) (π : Policy) (x : State) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ) :
    RDyn (fun m => (run P π x a v m).R) (fun m => P.t (load (π (run P π x a v m)))) := by
  intro m
  show (step P π (run P π x a v m) (slotArrivals a v m)).R = _
  rw [step_R]

theorem run_load_le (P : Params) (hP : P.Valid) (π : Policy) (hπ : IsScheduler P π) (x : State)
    (hx : Admissible P.bmax x) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ) (hv : ∀ i, 1 ≤ (v i).2) (m : ℕ)
    (h0 : (run P π x a v m).R = 0) : load (π (run P π x a v m)) ≤ P.bmax :=
  (hπ _ (run_adm P hP π hπ x hx a v hv m) h0).2

theorem eq_43_gen (P : Params) (hP : P.Valid) (π : Policy) (hπ : IsScheduler P π)
    (x : State) (hx : Admissible P.bmax x) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ)
    (hv : ∀ i, 1 ≤ (v i).2) (tok : Alloc → ℕ) (htok : ∀ δ, tok δ ≤ load δ) (n₁ n₂ : ℕ)
    (hn : n₁ ≤ n₂) :
    completedTokens P π x a v tok (n₂ * P.t P.bmax)
        ≤ completedTokens P π x a v tok (n₁ * P.t P.bmax) + (n₂ - n₁ + 1) * P.bmax := by
  unfold completedTokens
  refine abstract_43 (run_RDyn P π x a v) (fun m => tok (π (run P π x a v m))) P.bmax
    (P.t P.bmax) hP.2.2.2 ?_ ?_ n₁ n₂ hn
  · intro m h0
    have hl := run_load_le P hP π hπ x hx a v hv m h0
    have := rate_bound_nat P hP _ hl
    have := Nat.mul_le_mul_right (P.t P.bmax) (htok (π (run P π x a v m)))
    exact le_trans this (by simpa using ‹load (π (run P π x a v m)) * P.t P.bmax ≤ _›)
  · intro m h0
    exact le_trans (htok _) (run_load_le P hP π hπ x hx a v hv m h0)

/-! ### Token accounting -/

theorem tokens_filter (L : List Req) (h : ∀ r ∈ L, 0 < r.P → 1 ≤ r.D) :
    ((L.filter fun r => decide (r.D ≠ 0)).map fun r => r.P + r.D).sum = (L.map fun r => r.P + r.D).sum := by
  induction L with
  | nil => simp
  | cons r rs ih =>
    have ih := ih (fun s hs => h s (by simp [hs]))
    rw [List.filter_cons]
    split
    · rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
    · rename_i hd
      simp only [decide_eq_true_eq, ne_eq, not_not] at hd
      have : r.P = 0 := by
        by_contra hp; have := h r (by simp) (Nat.pos_of_ne_zero hp); omega
      rw [ih, List.map_cons, List.sum_cons, hd, this]; simp

theorem step_tokens (P : Params) (π : Policy) (hπ : IsScheduler P π) (x : State)
    (hx : Admissible P.bmax x) (arr : List (ℕ × ℕ)) :
    totalTokens x + (arr.map fun s => s.1 + s.2).sum ≤
      totalTokens (step P π x arr) + (if x.R = 0 then load (π x) else 0) := by
  obtain ⟨L, hreq, ⟨hL0, hL1⟩, -⟩ := step_reqs P π x arr
  have hL : (L.map fun r => r.P + r.D).sum + (if x.R = 0 then load (π x) else 0) =
      totalTokens x := by
    unfold totalTokens
    by_cases hR : x.R = 0
    · have hF := (hπ x hx hR).1
      have hF' : List.Forall₂ (fun r d => d.1 ≤ r.P ∧ d.2 ≤ r.D) x.reqs (π x) :=
        hF.imp (fun r d h => ⟨h.2.1, h.2.2.2⟩)
      have ht := applyAlloc_tokens hF'
      rw [if_pos hR]
      rcases hL0 hR with rfl | rfl
      · exact ht
      · rw [tokens_filter _ (GoodL_applyAlloc P π hπ x hx hR).2.2.1]; exact ht
    · rw [if_neg hR]
      rcases hL1 (Nat.pos_of_ne_zero hR) with rfl | rfl
      · simp
      · rw [tokens_filter _ hx.2.2.1]; simp
  rw [← hL]
  unfold totalTokens
  rw [hreq, List.map_append, List.sum_append, freshList_tokens]
  omega

theorem list_range_sum (g : ℕ → ℕ) (k : ℕ) :
    ((List.range k).map g).sum = ∑ i ∈ Finset.range k, g i := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem slot_sum (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ) (f : ℕ × ℕ → ℕ) (n : ℕ) :
    ∑ m ∈ Finset.range n, ((slotArrivals a v m).map f).sum =
      ∑ i ∈ Finset.range (arrivalsBefore a n), f (v i) := by
  induction n with
  | zero => simp [arrivalsBefore]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have : arrivalsBefore a (n + 1) = arrivalsBefore a n + a n := by
      simp [arrivalsBefore, Finset.sum_range_succ]
    rw [this, Finset.sum_range_add]
    congr 1
    simp only [slotArrivals, List.map_map]
    exact list_range_sum _ _

theorem run_tokens (P : Params) (hP : P.Valid) (π : Policy) (hπ : IsScheduler P π) (x : State)
    (hx : Admissible P.bmax x) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ) (hv : ∀ i, 1 ≤ (v i).2) (n : ℕ) :
    totalTokens x + ∑ i ∈ Finset.range (arrivalsBefore a n), ((v i).1 + (v i).2) ≤
      totalTokens (run P π x a v n) + ∑ m ∈ Finset.range n,
        (if (run P π x a v m).R = 0 then load (π (run P π x a v m)) else 0) := by
  rw [← slot_sum a v (fun s => s.1 + s.2) n]
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have := step_tokens P π hπ (run P π x a v n) (run_adm P hP π hπ x hx a v hv n)
      (slotArrivals a v n)
    have e : run P π x a v (n + 1) = step P π (run P π x a v n) (slotArrivals a v n) := rfl
    rw [e]
    omega

theorem processed_bound (P : Params) (hP : P.Valid) (π : Policy) (hπ : IsScheduler P π)
    (x : State) (hx : Admissible P.bmax x) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ) (hv : ∀ i, 1 ≤ (v i).2)
    (n : ℕ) :
    (∑ m ∈ Finset.range n, (if (run P π x a v m).R = 0 then load (π (run P π x a v m)) else 0))
      * P.t P.bmax ≤ P.bmax * (n + P.t P.bmax) := by
  set R := fun m => (run P π x a v m).R
  set τ := fun m => P.t (load (π (run P π x a v m)))
  have hI := interval_sum (run_RDyn P π x a v) (n + P.t P.bmax) 0 (Nat.zero_le _)
  rw [Nat.sub_zero, ← Finset.range_eq_Ico] at hI
  have hsub : Finset.range n ⊆ Finset.range (n + P.t P.bmax) := Finset.range_mono (by omega)
  calc _ = ∑ m ∈ Finset.range n,
        (if (run P π x a v m).R = 0 then load (π (run P π x a v m)) else 0) * P.t P.bmax :=
        Finset.sum_mul _ _ _
    _ ≤ ∑ m ∈ Finset.range n, P.bmax *
        (if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ n + P.t P.bmax then τ m else 0) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_range] at hm
        by_cases h0 : (run P π x a v m).R = 0
        · rw [if_pos h0]
          have hl := run_load_le P hP π hπ x hx a v hv m h0
          rcases Nat.eq_zero_or_pos (τ m) with ht | ht
          · have := t_zero_load P hP _ ht
            rw [this]; simp
          · have htT : τ m ≤ P.t P.bmax := t_mono P hl
            rw [if_pos ⟨h0, ht, by omega⟩]
            exact rate_bound_nat P hP _ hl
        · rw [if_neg h0]; simp
    _ = P.bmax * ∑ m ∈ Finset.range n,
        (if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ n + P.t P.bmax then τ m else 0) := by
        rw [Finset.mul_sum]
    _ ≤ P.bmax * ∑ m ∈ Finset.range (n + P.t P.bmax),
        (if R m = 0 ∧ 0 < τ m ∧ m + τ m ≤ n + P.t P.bmax then τ m else 0) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset hsub)
    _ ≤ _ := Nat.mul_le_mul_left _ hI

end LLMThroughput.TokenBudget.Core


namespace LLMThroughput.TokenBudget.Core
open LLMThroughput.TokenBudget
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- The arrival counts and request sizes as one family indexed by `ℕ ⊕ ℕ`. -/
def Zc {Ω : Type*} (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ) : ℕ ⊕ ℕ → Ω → ℕ × ℕ
  | Sum.inl n => fun ω => (a n ω, 0)
  | Sum.inr i => v i

theorem allMeas {β : Type*} [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    (s : Set β) : MeasurableSet s := (Set.to_countable s).measurableSet

theorem Zc_indep {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {vpmax vdmax : ℕ} {a : ℕ → Ω → ℕ} {v : ℕ → Ω → ℕ × ℕ}
    (hA : IIDArrivals μ a v vpmax vdmax) : iIndepFun (Zc a v) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  set Sa := S.toLeft
  set Sv := S.toRight
  set A1 : Set (ℕ → ℕ) := {α | ∀ n ∈ Sa, (α n, 0) ∈ sets (Sum.inl n)}
  set A2 : Set (ℕ → ℕ × ℕ) := {β | ∀ i ∈ Sv, β i ∈ sets (Sum.inr i)}
  have hA1 : MeasurableSet A1 := by
    have : A1 = ⋂ n ∈ Sa, (fun α : ℕ → ℕ => α n) ⁻¹' {k | (k, 0) ∈ sets (Sum.inl n)} := by
      ext α; simp [A1]
    rw [this]
    exact Finset.measurableSet_biInter _ fun n _ => (measurable_pi_apply n) (allMeas _)
  have hA2 : MeasurableSet A2 := by
    have : A2 = ⋂ i ∈ Sv, (fun β : ℕ → ℕ × ℕ => β i) ⁻¹' (sets (Sum.inr i)) := by
      ext β; simp [A2]
    rw [this]
    exact Finset.measurableSet_biInter _ fun i _ => (measurable_pi_apply i) (allMeas _)
  have hset : (⋂ s ∈ S, Zc a v s ⁻¹' sets s) =
      (fun ω n => a n ω) ⁻¹' A1 ∩ (fun ω i => v i ω) ⁻¹' A2 := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_inter_iff, A1, A2, Set.mem_setOf_eq,
      Sa, Sv, Finset.mem_toLeft, Finset.mem_toRight]
    constructor
    · intro h
      exact ⟨fun n hn => h _ hn, fun i hi => h _ hi⟩
    · rintro ⟨h1, h2⟩ s hs
      cases s with
      | inl n => exact h1 n hs
      | inr i => exact h2 i hs
  rw [hset, hA.indep_av.measure_inter_preimage_eq_mul _ _ hA1 hA2,
    Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  congr 1
  · have e : (fun ω n => a n ω) ⁻¹' A1 = ⋂ n ∈ Sa, a n ⁻¹' {k | (k, 0) ∈ sets (Sum.inl n)} := by
      ext ω; simp [A1]
    rw [e, hA.indep_a.measure_inter_preimage_eq_mul Sa (fun n _ => allMeas _)]
    rfl
  · have e : (fun ω i => v i ω) ⁻¹' A2 = ⋂ i ∈ Sv, v i ⁻¹' sets (Sum.inr i) := by
      ext ω; simp [A2]
    rw [e, hA.indep_v.measure_inter_preimage_eq_mul Sv (fun i _ => allMeas _)]
    rfl

/-- σ-algebra of one coordinate of the combined family. -/
def mZ {Ω : Type*} (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ) (s : ℕ ⊕ ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (Zc a v s) inferInstance

theorem meas_of_mZ {Ω : Type*} {a : ℕ → Ω → ℕ} {v : ℕ → Ω → ℕ × ℕ} {M : MeasurableSpace Ω}
    {s : ℕ ⊕ ℕ} (h : mZ a v s ≤ M) : Measurable[M] (Zc a v s) := fun t ht => h _ ⟨t, ht, rfl⟩

theorem meas_pi_helper {Ω ι X : Type*} [MeasurableSpace X] {M : MeasurableSpace Ω}
    (f : Ω → ι → X) (hf : ∀ i, Measurable[M] (fun ω => f ω i)) : Measurable[M] f :=
  measurable_pi_lambda f hf

section ThreeIndep

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {vpmax vdmax : ℕ} {a : ℕ → Ω → ℕ} {v : ℕ → Ω → ℕ × ℕ}

theorem Zc_meas (hA : IIDArrivals μ a v vpmax vdmax) (s : ℕ ⊕ ℕ) : Measurable (Zc a v s) := by
  cases s with
  | inl n => exact (hA.meas_a n).prodMk measurable_const
  | inr i => exact hA.meas_v i

theorem mZ_le (hA : IIDArrivals μ a v vpmax vdmax) (s : ℕ ⊕ ℕ) :
    mZ a v s ≤ (inferInstance : MeasurableSpace Ω) :=
  (Zc_meas hA s).comap_le

theorem iSup_le_of {S : Set (ℕ ⊕ ℕ)} (hA : IIDArrivals μ a v vpmax vdmax) :
    (⨆ s ∈ S, mZ a v s) ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => mZ_le hA s

theorem three_lintegral (hA : IIDArrivals μ a v vpmax vdmax) (n n' j i : ℕ) (hji : j ≤ i)
    (Φ : Set ((Fin n → ℕ) × (Fin j → ℕ × ℕ))) (g : (Fin n' → ℕ) → ℝ≥0∞) (h : ℕ × ℕ → ℝ≥0∞) :
    ∫⁻ ω, ((fun ω => ((fun m : Fin n => a m ω), (fun k : Fin j => v k ω))) ⁻¹' Φ).indicator 1 ω *
        (g (fun m : Fin n' => a (n + m) ω) * h (v i ω)) ∂μ =
      μ ((fun ω => ((fun m : Fin n => a m ω), (fun k : Fin j => v k ω))) ⁻¹' Φ) *
        ((∫⁻ ω, g (fun m : Fin n' => a (n + m) ω) ∂μ) * ∫⁻ ω, h (v i ω) ∂μ) := by
  have hind : iIndep (mZ a v) μ := (iIndepFun_iff_iIndep _ _ _).1 (Zc_indep hA)
  let S1 : Set (ℕ ⊕ ℕ) := {s | ∃ m < n, s = Sum.inl m} ∪ {s | ∃ k < j, s = Sum.inr k}
  let S2 : Set (ℕ ⊕ ℕ) := {s | ∃ m, n ≤ m ∧ s = Sum.inl m}
  let S3 : Set (ℕ ⊕ ℕ) := {Sum.inr i}
  have d1 : Disjoint S1 (S2 ∪ S3) := by
    rw [Set.disjoint_left]
    rintro s (⟨m, hm, rfl⟩ | ⟨k, hk, rfl⟩) (⟨m', hm', he⟩ | he)
    · simp at he; omega
    · simp [S3] at he
    · simp at he
    · simp [S3] at he; omega
  have d2 : Disjoint S2 S3 := by
    rw [Set.disjoint_left]
    rintro s ⟨m, _, rfl⟩ he
    simp [S3] at he
  have I1 := indep_iSup_of_disjoint (mZ_le hA) hind d1
  have I2 := indep_iSup_of_disjoint (mZ_le hA) hind d2
  -- measurability of the three factors
  have hmap : Measurable[⨆ s ∈ S1, mZ a v s]
      (fun ω => ((fun m : Fin n => a m ω), (fun k : Fin j => v k ω))) := by
    refine Measurable.prodMk ?_ ?_
    · refine meas_pi_helper _ fun m => ?_
      have : mZ a v (Sum.inl (m : ℕ)) ≤ ⨆ s ∈ S1, mZ a v s :=
        le_iSup₂ (f := fun s _ => mZ a v s) (Sum.inl (m : ℕ)) (Or.inl ⟨m, m.2, rfl⟩)
      exact measurable_fst.comp (meas_of_mZ this)
    · refine meas_pi_helper _ fun k => ?_
      have : mZ a v (Sum.inr (k : ℕ)) ≤ ⨆ s ∈ S1, mZ a v s :=
        le_iSup₂ (f := fun s _ => mZ a v s) (Sum.inr (k : ℕ)) (Or.inr ⟨k, k.2, rfl⟩)
      exact meas_of_mZ this
  have mf : Measurable[⨆ s ∈ S1, mZ a v s]
      (((fun ω => ((fun m : Fin n => a m ω), (fun k : Fin j => v k ω))) ⁻¹' Φ).indicator
        (1 : Ω → ℝ≥0∞)) :=
    Measurable.indicator measurable_const (hmap (allMeas Φ))
  have mg : Measurable[⨆ s ∈ S2, mZ a v s] (fun ω => g (fun m : Fin n' => a (n + m) ω)) := by
    refine Measurable.of_discrete.comp ?_
    refine meas_pi_helper _ fun m => ?_
    have : mZ a v (Sum.inl (n + m)) ≤ ⨆ s ∈ S2, mZ a v s :=
      le_iSup₂ (f := fun s _ => mZ a v s) (Sum.inl (n + m)) ⟨n + m, by omega, rfl⟩
    exact measurable_fst.comp (meas_of_mZ this)
  have mh : Measurable[⨆ s ∈ S3, mZ a v s] (fun ω => h (v i ω)) := by
    refine Measurable.of_discrete.comp ?_
    have : mZ a v (Sum.inr i) ≤ ⨆ s ∈ S3, mZ a v s :=
      le_iSup₂ (f := fun s _ => mZ a v s) (Sum.inr i) rfl
    exact meas_of_mZ this
  have l23 : (⨆ s ∈ S2, mZ a v s) ≤ ⨆ s ∈ S2 ∪ S3, mZ a v s :=
    iSup₂_le fun s hs => le_iSup₂ (f := fun s _ => mZ a v s) s (Or.inl hs)
  have l33 : (⨆ s ∈ S3, mZ a v s) ≤ ⨆ s ∈ S2 ∪ S3, mZ a v s :=
    iSup₂_le fun s hs => le_iSup₂ (f := fun s _ => mZ a v s) s (Or.inr hs)
  have mgh : Measurable[⨆ s ∈ S2 ∪ S3, mZ a v s]
      (fun ω => g (fun m : Fin n' => a (n + m) ω) * h (v i ω)) :=
    (mg.mono l23 le_rfl).mul (mh.mono l33 le_rfl)
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (iSup_le_of hA) (iSup_le_of hA) I1 mf mgh,
    lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (iSup_le_of hA) (iSup_le_of hA) I2 mg mh]
  congr 1
  rw [lintegral_indicator_one ((hmap.mono (iSup_le_of hA) le_rfl) (allMeas Φ))]

end ThreeIndep

/-! ### The accumulated-work walk -/

section Walk

variable {Ω : Type*}

/-- Work (prefill + decode tokens) of the requests arrived before slot `N`. -/
def Acc (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ) (ω : Ω) (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (arrivalsBefore (fun m => a m ω) N), ((v i ω).1 + (v i ω).2)

def Gset (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ) (D T B W0 k : ℕ) : Set Ω :=
  {ω | ∀ k' ≤ k, k' * B < W0 + Acc a v ω (D + k' * T)}

noncomputable def kappa (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ) (D T B W0 : ℕ) (ω : Ω) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : W0 + Acc a v ω (D + k * T) ≤ k * B), (k : ℕ∞)

theorem kappa_gt_iff (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ) (D T B W0 k : ℕ) (ω : Ω) :
    (k : ℕ∞) < kappa a v D T B W0 ω ↔ ω ∈ Gset a v D T B W0 k := by
  constructor
  · intro h k' hk'
    by_contra hc
    push Not at hc
    have : kappa a v D T B W0 ω ≤ k' := iInf₂_le k' hc
    have : (k : ℕ∞) < k' := lt_of_lt_of_le h this
    exact absurd (by exact_mod_cast this : k < k') (by omega)
  · intro h
    have : ((k + 1 : ℕ) : ℕ∞) ≤ kappa a v D T B W0 ω := by
      refine le_iInf₂ fun k' hk' => ?_
      by_contra hc
      push Not at hc
      have hk : k' ≤ k := by exact_mod_cast Order.lt_succ_iff.mp (by exact_mod_cast hc)
      have := h k' hk
      omega
    refine lt_of_lt_of_le ?_ this
    exact_mod_cast Nat.lt_succ_self k

theorem arrivalsBefore_mono (a : ℕ → ℕ) {n n' : ℕ} (h : n ≤ n') :
    arrivalsBefore a n ≤ arrivalsBefore a n' :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem Acc_mono (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ) (ω : Ω) {n n' : ℕ} (h : n ≤ n') :
    Acc a v ω n ≤ Acc a v ω n' :=
  Finset.sum_le_sum_of_subset (Finset.range_mono (arrivalsBefore_mono _ h))

theorem arrivalsBefore_add (a : ℕ → ℕ) (n T : ℕ) :
    arrivalsBefore a (n + T) = arrivalsBefore a n + ∑ m ∈ Finset.range T, a (n + m) := by
  simp [arrivalsBefore, Finset.sum_range_add]

theorem Acc_add (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ) (ω : Ω) (n T : ℕ) :
    Acc a v ω (n + T) = Acc a v ω n + ∑ l ∈ Finset.range (∑ m ∈ Finset.range T, a (n + m) ω),
      ((v (arrivalsBefore (fun m => a m ω) n + l) ω).1 +
        (v (arrivalsBefore (fun m => a m ω) n + l) ω).2) := by
  simp only [Acc]
  rw [arrivalsBefore_add, Finset.sum_range_add]

/-- Extend a finite tuple by zero. -/
def extA {n : ℕ} (α : Fin n → ℕ) (m : ℕ) : ℕ := if h : m < n then α ⟨m, h⟩ else 0

def extW {j : ℕ} (β : Fin j → ℕ × ℕ) (i : ℕ) : ℕ := if h : i < j then (β ⟨i, h⟩).1 + (β ⟨i, h⟩).2 else 0

def PhiSet (D T B W0 k j : ℕ) : Set ((Fin (D + k * T) → ℕ) × (Fin j → ℕ × ℕ)) :=
  {p | ∑ m ∈ Finset.range (D + k * T), extA p.1 m = j ∧
      ∀ k' ≤ k, k' * B < W0 + ∑ i ∈ Finset.range (∑ m ∈ Finset.range (D + k' * T), extA p.1 m),
        extW p.2 i}

theorem Gset_inter_eq (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ) (D T B W0 k j : ℕ) :
    Gset a v D T B W0 k ∩ {ω | arrivalsBefore (fun m => a m ω) (D + k * T) = j} =
      (fun ω => ((fun m : Fin (D + k * T) => a m ω), (fun i : Fin j => v i ω))) ⁻¹'
        PhiSet D T B W0 k j := by
  ext ω
  simp only [Set.mem_inter_iff, Gset, Set.mem_setOf_eq, Set.mem_preimage, PhiSet]
  have hA : ∀ N ≤ D + k * T, ∑ m ∈ Finset.range N, extA (fun m : Fin (D + k * T) => a m ω) m =
      arrivalsBefore (fun m => a m ω) N := by
    intro N hN
    simp only [arrivalsBefore]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    simp [extA, show m < D + k * T by omega]
  rw [hA _ le_rfl]
  constructor
  · rintro ⟨hG, hj⟩
    refine ⟨hj, fun k' hk' => ?_⟩
    have hle : D + k' * T ≤ D + k * T := by have := Nat.mul_le_mul_right T hk'; omega
    rw [hA _ hle]
    have hEj : arrivalsBefore (fun m => a m ω) (D + k' * T) ≤ j := hj ▸ arrivalsBefore_mono _ hle
    have := hG k' hk'
    simp only [Acc] at this
    convert this using 2
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    simp [extW, show i < j by omega]
  · rintro ⟨hj, hG⟩
    refine ⟨fun k' hk' => ?_, hj⟩
    have hle : D + k' * T ≤ D + k * T := by have := Nat.mul_le_mul_right T hk'; omega
    have := hG k' hk'
    rw [hA _ hle] at this
    have hEj : arrivalsBefore (fun m => a m ω) (D + k' * T) ≤ j := hj ▸ arrivalsBefore_mono _ hle
    simp only [Acc]
    convert this using 2
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    simp [extW, show i < j by omega]

end Walk

section Wald

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {vpmax vdmax : ℕ} {a : ℕ → Ω → ℕ} {v : ℕ → Ω → ℕ × ℕ}

theorem trunc_meas (hA : IIDArrivals μ a v vpmax vdmax) (n j : ℕ) :
    Measurable (fun ω => ((fun m : Fin n => a m ω), (fun i : Fin j => v i ω))) :=
  (measurable_pi_lambda (fun ω (m : Fin n) => a m ω) fun m => hA.meas_a m).prodMk
    (measurable_pi_lambda (fun ω (i : Fin j) => v i ω) fun i => hA.meas_v i)

theorem Gj_meas (hA : IIDArrivals μ a v vpmax vdmax) (D T B W0 k j : ℕ) :
    MeasurableSet (Gset a v D T B W0 k ∩ {ω | arrivalsBefore (fun m => a m ω) (D + k * T) = j}) := by
  rw [Gset_inter_eq]; exact trunc_meas hA _ _ (allMeas _)

theorem G_meas (hA : IIDArrivals μ a v vpmax vdmax) (D T B W0 k : ℕ) :
    MeasurableSet (Gset a v D T B W0 k) := by
  have : Gset a v D T B W0 k =
      ⋃ j, (Gset a v D T B W0 k ∩ {ω | arrivalsBefore (fun m => a m ω) (D + k * T) = j}) := by
    ext ω; simp
  rw [this]; exact MeasurableSet.iUnion fun j => Gj_meas hA D T B W0 k j

theorem lintegral_a (hA : IIDArrivals μ a v vpmax vdmax) (m : ℕ) :
    ∫⁻ ω, (a m ω : ℝ≥0∞) ∂μ = ∫⁻ ω, (a 0 ω : ℝ≥0∞) ∂μ :=
  ((hA.ident_a m).comp (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ≥0∞)))).lintegral_eq

theorem lintegral_w (hA : IIDArrivals μ a v vpmax vdmax) (i : ℕ) :
    ∫⁻ ω, (((v i ω).1 + (v i ω).2 : ℕ) : ℝ≥0∞) ∂μ = ∫⁻ ω, (((v 0 ω).1 + (v 0 ω).2 : ℕ) : ℝ≥0∞) ∂μ :=
  ((hA.ident_v i).comp (Measurable.of_discrete
    (f := fun p : ℕ × ℕ => ((p.1 + p.2 : ℕ) : ℝ≥0∞)))).lintegral_eq

theorem wald_step (hA : IIDArrivals μ a v vpmax vdmax) (D T B W0 k : ℕ) :
    ∫⁻ ω, (Gset a v D T B W0 k).indicator 1 ω *
        ((Acc a v ω (D + k * T + T) - Acc a v ω (D + k * T) : ℕ) : ℝ≥0∞) ∂μ =
      μ (Gset a v D T B W0 k) * ((T : ℝ≥0∞) * ∫⁻ ω, (a 0 ω : ℝ≥0∞) ∂μ) *
        ∫⁻ ω, (((v 0 ω).1 + (v 0 ω).2 : ℕ) : ℝ≥0∞) ∂μ := by
  set n := D + k * T with hn
  set G := Gset a v D T B W0 k
  let Gj : ℕ → Set Ω := fun j => G ∩ {ω | arrivalsBefore (fun m => a m ω) n = j}
  let g : ℕ → (Fin T → ℕ) → ℝ≥0∞ := fun l β => if l < ∑ m : Fin T, β m then 1 else 0
  let h : ℕ × ℕ → ℝ≥0∞ := fun p => ((p.1 + p.2 : ℕ) : ℝ≥0∞)
  let F : ℕ → ℕ → Ω → ℝ≥0∞ := fun j l ω =>
    (Gj j).indicator 1 ω * (g l (fun m : Fin T => a (n + m) ω) * h (v (j + l) ω))
  have hS : ∀ ω, ∑ m : Fin T, a (n + m) ω = ∑ m ∈ Finset.range T, a (n + m) ω := fun ω =>
    Fin.sum_univ_eq_sum_range (fun m => a (n + m) ω) T
  have hFm : ∀ j l, Measurable (F j l) := by
    intro j l
    refine Measurable.mul (Measurable.indicator measurable_const (Gj_meas hA D T B W0 k j))
      (Measurable.mul ?_ ?_)
    · exact (Measurable.of_discrete (f := g l)).comp
        (measurable_pi_lambda (fun ω (m : Fin T) => a (n + m) ω) fun m => hA.meas_a _)
    · exact (Measurable.of_discrete (f := h)).comp (hA.meas_v (j + l))
  have key : ∀ ω, G.indicator 1 ω * ((Acc a v ω (n + T) - Acc a v ω n : ℕ) : ℝ≥0∞) =
      ∑' j, ∑' l, F j l ω := by
    intro ω
    set j0 := arrivalsBefore (fun m => a m ω) n
    rw [tsum_eq_single j0]
    · rw [tsum_eq_sum (s := Finset.range (∑ m ∈ Finset.range T, a (n + m) ω))]
      · rw [Acc_add, Nat.add_sub_cancel_left, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [Finset.mem_range] at hl
        have hind : (Gj j0).indicator (1 : Ω → ℝ≥0∞) ω = G.indicator 1 ω := by
          by_cases hG : ω ∈ G
          · rw [Set.indicator_of_mem hG, Set.indicator_of_mem]; exact ⟨hG, rfl⟩
          · rw [Set.indicator_of_notMem hG, Set.indicator_of_notMem]; exact fun h => hG h.1
        simp only [F, g, h, hind, hS, if_pos hl, one_mul]
        rfl
      · intro l hl
        rw [Finset.mem_range, not_lt] at hl
        simp only [F, g, hS, if_neg (not_lt.2 hl), zero_mul, mul_zero]
    · intro j hj
      refine ENNReal.tsum_eq_zero.2 fun l => ?_
      simp only [F]
      rw [Set.indicator_of_notMem, zero_mul]
      exact fun hm => hj hm.2.symm
  simp_rw [key]
  rw [lintegral_tsum fun j => (Measurable.ennreal_tsum fun l => hFm j l).aemeasurable]
  simp_rw [lintegral_tsum fun l => (hFm _ l).aemeasurable]
  have h3 : ∀ j l, ∫⁻ ω, F j l ω ∂μ = μ (Gj j) * ((∫⁻ ω, g l (fun m : Fin T => a (n + m) ω) ∂μ) *
      ∫⁻ ω, (((v 0 ω).1 + (v 0 ω).2 : ℕ) : ℝ≥0∞) ∂μ) := by
    intro j l
    have e := three_lintegral hA n T j (j + l) (by omega) (PhiSet D T B W0 k j) (g l) h
    rw [← Gset_inter_eq] at e
    simp only [F]
    rw [e, lintegral_w hA]
  simp_rw [h3]
  -- sum over l
  have hl : ∑' l, ∫⁻ ω, g l (fun m : Fin T => a (n + m) ω) ∂μ = (T : ℝ≥0∞) * ∫⁻ ω, (a 0 ω : ℝ≥0∞) ∂μ := by
    rw [← lintegral_tsum (f := fun l ω => g l (fun m : Fin T => a (n + m) ω)) fun l =>
      ((Measurable.of_discrete (f := g l)).comp
        (measurable_pi_lambda (fun ω (m : Fin T) => a (n + m) ω) fun m => hA.meas_a _)).aemeasurable]
    have : ∀ ω, ∑' l, g l (fun m : Fin T => a (n + m) ω) =
        ∑ m ∈ Finset.range T, (a (n + m) ω : ℝ≥0∞) := by
      intro ω
      rw [tsum_eq_sum (s := Finset.range (∑ m ∈ Finset.range T, a (n + m) ω))]
      · simp only [g, hS]
        rw [Finset.sum_congr rfl fun l hl => if_pos (Finset.mem_range.1 hl)]
        simp
      · intro l hl
        rw [Finset.mem_range, not_lt] at hl
        simp only [g, hS, if_neg (not_lt.2 hl)]
    simp_rw [this]
    rw [lintegral_finsetSum (f := fun m ω => (a (n + m) ω : ℝ≥0∞)) _ fun m _ =>
      (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ≥0∞))).comp (hA.meas_a _)]
    simp_rw [lintegral_a hA]
    simp
  -- sum over j
  have hj : ∑' j, μ (Gj j) = μ G := by
    rw [← measure_iUnion]
    · congr 1; ext ω; simp [Gj]
    · intro i j hij
      exact Set.disjoint_left.2 fun ω hi hj' => hij (hi.2.symm.trans hj'.2)
    · exact fun j => Gj_meas hA D T B W0 k j
  simp_rw [← mul_assoc, ENNReal.tsum_mul_right]
  congr 1
  simp_rw [ENNReal.tsum_mul_left, hl]
  rw [ENNReal.tsum_mul_right, hj, mul_assoc]

theorem E_meas (hA : IIDArrivals μ a v vpmax vdmax) (N : ℕ) :
    Measurable (fun ω => arrivalsBefore (fun m => a m ω) N) := by
  simp only [arrivalsBefore]
  exact Finset.measurable_sum _ fun m _ => hA.meas_a m

theorem Acc_meas (hA : IIDArrivals μ a v vpmax vdmax) (N : ℕ) :
    Measurable (fun ω => Acc a v ω N) := by
  let f : ℕ × Ω → ℕ := fun p => ∑ i ∈ Finset.range p.1, ((v i p.2).1 + (v i p.2).2)
  have hf : Measurable f := by
    refine measurable_from_prod_countable_right fun j => ?_
    change Measurable (fun ω => ∑ i ∈ Finset.range j, ((v i ω).1 + (v i ω).2))
    exact Finset.measurable_sum (f := fun i ω => (v i ω).1 + (v i ω).2) _ fun i _ =>
      ((measurable_fst.comp (hA.meas_v i)).add (measurable_snd.comp (hA.meas_v i)))
  exact hf.comp ((E_meas hA N).prodMk measurable_id)

theorem lintegral_a_lt_top (hA : IIDArrivals μ a v vpmax vdmax) :
    ∫⁻ ω, (a 0 ω : ℝ≥0∞) ∂μ < ⊤ := by
  have := hA.integrable_a.lintegral_lt_top
  simpa using this

theorem Acc_lintegral_lt_top (hA : IIDArrivals μ a v vpmax vdmax) (N : ℕ) :
    ∫⁻ ω, (Acc a v ω N : ℝ≥0∞) ∂μ < ⊤ := by
  have hle : ∀ ω, (Acc a v ω N : ℝ≥0∞) ≤
      ((vpmax + vdmax : ℕ) : ℝ≥0∞) * ∑ m ∈ Finset.range N, (a m ω : ℝ≥0∞) := by
    intro ω
    have : Acc a v ω N ≤ (vpmax + vdmax) * arrivalsBefore (fun m => a m ω) N := by
      simp only [Acc]
      calc _ ≤ ∑ i ∈ Finset.range (arrivalsBefore (fun m => a m ω) N), (vpmax + vdmax) :=
            Finset.sum_le_sum fun i _ => by
              have := hA.size_bounds i ω; omega
        _ = _ := by simp [mul_comm]
    have h2 : ((arrivalsBefore (fun m => a m ω) N : ℕ) : ℝ≥0∞) =
        ∑ m ∈ Finset.range N, (a m ω : ℝ≥0∞) := by simp [arrivalsBefore]
    rw [← h2]; exact_mod_cast this
  calc _ ≤ ∫⁻ ω, ((vpmax + vdmax : ℕ) : ℝ≥0∞) * ∑ m ∈ Finset.range N, (a m ω : ℝ≥0∞) ∂μ :=
        lintegral_mono hle
    _ = ((vpmax + vdmax : ℕ) : ℝ≥0∞) * ∑ m ∈ Finset.range N, ∫⁻ ω, (a m ω : ℝ≥0∞) ∂μ := by
        rw [lintegral_const_mul _ (Finset.measurable_sum (f := fun m ω => (a m ω : ℝ≥0∞)) _
          fun m _ => (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ≥0∞))).comp (hA.meas_a m))]
        rw [lintegral_finsetSum (f := fun m ω => (a m ω : ℝ≥0∞)) _ fun m _ =>
          (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ≥0∞))).comp (hA.meas_a _)]
    _ < ⊤ := by
        simp_rw [lintegral_a hA]
        refine ENNReal.mul_lt_top (by simp) ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (by simp) (lintegral_a_lt_top hA)

end Wald

section Final

variable {Ω : Type*}

theorem G_nested (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ) (D T B W0 : ℕ) {ω : Ω} {k k' : ℕ}
    (h : ω ∈ Gset a v D T B W0 k) (hk : k' ≤ k) : ω ∈ Gset a v D T B W0 k' :=
  fun k'' hk'' => h k'' (le_trans hk'' hk)

open Classical in
/-- Number of the first `K` events `G_k` containing `ω`, and the telescoped work. -/
theorem lemmaA (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ) (D T B W0 : ℕ) (ω : Ω) (K' : ℕ)
    (h : ω ∈ Gset a v D T B W0 K') : ∀ K ≤ K' + 1,
    (∑ k ∈ Finset.range K, if ω ∈ Gset a v D T B W0 k then 1 else 0) = K ∧
    (∑ k ∈ Finset.range K, if ω ∈ Gset a v D T B W0 k then
        (Acc a v ω (D + k * T + T) - Acc a v ω (D + k * T)) else 0) + Acc a v ω D =
      Acc a v ω (D + K * T) := by
  intro K
  induction K with
  | zero => intro _; simp
  | succ K ih =>
    intro hK
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hG : ω ∈ Gset a v D T B W0 K := G_nested a v D T B W0 h (by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, if_pos hG, if_pos hG, ih1]
    refine ⟨rfl, ?_⟩
    have hmono := Acc_mono a v ω (show D + K * T ≤ D + K * T + T by omega)
    rw [show D + (K + 1) * T = D + K * T + T by ring]
    omega

open Classical in
theorem lemmaB (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ) (D T B W0 : ℕ) (ω : Ω) (K : ℕ) :
    (∑ k ∈ Finset.range K, if ω ∈ Gset a v D T B W0 k then 1 else 0) * B ≤
      W0 + B + Acc a v ω D + ∑ k ∈ Finset.range K, if ω ∈ Gset a v D T B W0 k then
        (Acc a v ω (D + k * T + T) - Acc a v ω (D + k * T)) else 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
    by_cases hG : ω ∈ Gset a v D T B W0 K
    · obtain ⟨h1, h2⟩ := lemmaA a v D T B W0 ω K hG (K + 1) le_rfl
      rw [h1]
      have h3 := hG K le_rfl
      have hmono := Acc_mono a v ω (show D + K * T ≤ D + (K + 1) * T from
        Nat.add_le_add_left (Nat.mul_le_mul_right T (Nat.le_succ K)) D)
      set S := ∑ k ∈ Finset.range (K + 1), if ω ∈ Gset a v D T B W0 k then
        (Acc a v ω (D + k * T + T) - Acc a v ω (D + k * T)) else 0
      have e : (K + 1) * B = K * B + B := by ring
      rw [e]
      generalize K * B = KB at h3 ⊢
      calc KB + B ≤ W0 + Acc a v ω (D + K * T) + B := by omega
        _ ≤ W0 + Acc a v ω (D + (K + 1) * T) + B := by omega
        _ = W0 + B + Acc a v ω D + S := by omega
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, if_neg hG, if_neg hG]
      simpa using ih

end Final

section Final2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {vpmax vdmax : ℕ} {a : ℕ → Ω → ℕ} {v : ℕ → Ω → ℕ × ℕ}

theorem kappa_eq_tsum (D T B W0 : ℕ) (ω : Ω) :
    ((kappa a v D T B W0 ω : ℕ∞) : ℝ≥0∞) = ∑' k, (Gset a v D T B W0 k).indicator 1 ω := by
  have hiff := fun k => kappa_gt_iff a v D T B W0 k ω
  rcases eq_top_or_lt_top (kappa a v D T B W0 ω) with htop | hfin
  · rw [htop]
    have : ∀ k, (Gset a v D T B W0 k).indicator (1 : Ω → ℝ≥0∞) ω = 1 := by
      intro k
      rw [Set.indicator_of_mem ((hiff k).1 (by rw [htop]; exact ENat.coe_lt_top k))]; rfl
    simp_rw [this]
    rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]; simp
  · obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hfin.ne
    rw [← hN]
    rw [tsum_eq_sum (s := Finset.range N)]
    · rw [Finset.sum_congr rfl fun k hk => by
        rw [Set.indicator_of_mem ((hiff k).1 (by rw [← hN]; exact_mod_cast Finset.mem_range.1 hk))]]
      simp
    · intro k hk
      rw [Finset.mem_range, not_lt] at hk
      rw [Set.indicator_of_notMem]
      intro hm
      have := (hiff k).2 hm
      rw [← hN] at this
      have : k < N := by exact_mod_cast this
      omega

theorem kappa_lintegral_lt_top (hA : IIDArrivals μ a v vpmax vdmax) (D T B W0 : ℕ)
    (hB : (T : ℝ≥0∞) * (∫⁻ ω, (a 0 ω : ℝ≥0∞) ∂μ) *
      (∫⁻ ω, (((v 0 ω).1 + (v 0 ω).2 : ℕ) : ℝ≥0∞) ∂μ) < B) :
    ∫⁻ ω, ((kappa a v D T B W0 ω : ℕ∞) : ℝ≥0∞) ∂μ < ⊤ := by
  classical
  set c := (T : ℝ≥0∞) * (∫⁻ ω, (a 0 ω : ℝ≥0∞) ∂μ) *
      (∫⁻ ω, (((v 0 ω).1 + (v 0 ω).2 : ℕ) : ℝ≥0∞) ∂μ) with hc
  set C0 : ℝ≥0∞ := (W0 : ℝ≥0∞) + B + ∫⁻ ω, (Acc a v ω D : ℝ≥0∞) ∂μ with hC0
  have hC0fin : C0 < ⊤ := by
    simp only [hC0]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨by simp, by simp⟩, Acc_lintegral_lt_top hA D⟩
  set G := fun k => Gset a v D T B W0 k
  have hGm : ∀ k, MeasurableSet (G k) := fun k => G_meas hA D T B W0 k
  -- partial sums are bounded
  have hpart : ∀ K, (∑ k ∈ Finset.range K, μ (G k)) ≤ C0 / (B - c) := by
    intro K
    set x := ∑ k ∈ Finset.range K, μ (G k)
    have hx : x < ⊤ := ENNReal.sum_lt_top.2 fun k _ => measure_lt_top μ _
    -- integrate lemma B
    have hB' := fun ω => lemmaB a v D T B W0 ω K
    have hint : (B : ℝ≥0∞) * x ≤ C0 + x * c := by
      have e1 : ∫⁻ ω, ((∑ k ∈ Finset.range K, if ω ∈ G k then 1 else 0 : ℕ) : ℝ≥0∞) * B ∂μ =
          (B : ℝ≥0∞) * x := by
        rw [lintegral_mul_const _ ?_]
        · simp only [x, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
          rw [lintegral_finsetSum _ fun k _ => ?_]
          · rw [mul_comm]
            congr 1
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← lintegral_indicator_one (hGm k)]
            rfl
          · exact Measurable.ite (p := fun ω => ω ∈ G k) (hGm k) measurable_const measurable_const
        · exact (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ≥0∞))).comp
            (Finset.measurable_sum _ fun k _ =>
              Measurable.ite (p := fun ω => ω ∈ G k) (hGm k) measurable_const measurable_const)
      have e2 : ∫⁻ ω, ((W0 + B + Acc a v ω D + ∑ k ∈ Finset.range K, if ω ∈ G k then
          (Acc a v ω (D + k * T + T) - Acc a v ω (D + k * T)) else 0 : ℕ) : ℝ≥0∞) ∂μ =
          C0 + x * c := by
        simp only [Nat.cast_add, Nat.cast_sum]
        have mAcc : ∀ N, Measurable (fun ω => (Acc a v ω N : ℝ≥0∞)) := fun N =>
          (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ≥0∞))).comp (Acc_meas hA N)
        have mterm : ∀ k, Measurable (fun ω => ((if ω ∈ G k then
            (Acc a v ω (D + k * T + T) - Acc a v ω (D + k * T)) else 0 : ℕ) : ℝ≥0∞)) := by
          intro k
          exact (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ≥0∞))).comp
            (Measurable.ite (p := fun ω => ω ∈ G k) (hGm k)
              ((Acc_meas hA _).sub (Acc_meas hA _)) measurable_const)
        rw [lintegral_add_right _ (Finset.measurable_sum _ fun k _ => mterm k),
          lintegral_add_right _ (mAcc D)]
        simp only [lintegral_const, measure_univ, mul_one]
        rw [lintegral_finsetSum _ fun k _ => mterm k]
        congr 1
        simp only [x, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        have := wald_step hA D T B W0 k
        rw [hc, ← mul_assoc, ← this]
        refine lintegral_congr fun ω => ?_
        by_cases hω : ω ∈ G k
        · simp only [G] at hω
          simp [hω, G]
        · simp only [G] at hω
          simp [hω, G]
      calc (B : ℝ≥0∞) * x = _ := e1.symm
        _ ≤ _ := lintegral_mono fun ω => by rw [← Nat.cast_mul]; exact Nat.cast_le.2 (hB' ω)
        _ = _ := e2
    have hcB : c < B := hB
    have hpos : B - c ≠ 0 := (tsub_pos_of_lt hcB).ne'
    rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inr hC0fin.ne), ENNReal.mul_sub
      (fun _ _ => hx.ne)]
    rw [tsub_le_iff_right]
    calc x * B = B * x := mul_comm _ _
      _ ≤ C0 + x * c := hint
  -- the integral of kappa is the sum of the measures
  have hk : ∫⁻ ω, ((kappa a v D T B W0 ω : ℕ∞) : ℝ≥0∞) ∂μ = ∑' k, μ (G k) := by
    simp_rw [kappa_eq_tsum]
    rw [lintegral_tsum fun k => (measurable_one.indicator (hGm k)).aemeasurable]
    congr 1; funext k
    exact lintegral_indicator_one (hGm k)
  rw [hk, ENNReal.tsum_eq_iSup_nat]
  refine lt_of_le_of_lt (iSup_le hpart) ?_
  exact ENNReal.div_lt_top hC0fin.ne (tsub_pos_of_lt hB).ne'

end Final2

end LLMThroughput.TokenBudget.Core


namespace LLMThroughput.TokenBudget.Core
open LLMThroughput.TokenBudget
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-! ### Exact token balance -/

theorem step_tokens_eq (P : Params) (π : Policy) (hπ : IsScheduler P π) (x : State)
    (hx : Admissible P.bmax x) (arr : List (ℕ × ℕ)) :
    totalTokens (step P π x arr) + (if x.R = 0 then load (π x) else 0) =
      totalTokens x + (arr.map fun s => s.1 + s.2).sum := by
  obtain ⟨L, hreq, ⟨hL0, hL1⟩, -⟩ := step_reqs P π x arr
  have hL : (L.map fun r => r.P + r.D).sum + (if x.R = 0 then load (π x) else 0) =
      totalTokens x := by
    unfold totalTokens
    by_cases hR : x.R = 0
    · have hF := (hπ x hx hR).1
      have hF' : List.Forall₂ (fun r d => d.1 ≤ r.P ∧ d.2 ≤ r.D) x.reqs (π x) :=
        hF.imp (fun r d h => ⟨h.2.1, h.2.2.2⟩)
      have ht := applyAlloc_tokens hF'
      rw [if_pos hR]
      rcases hL0 hR with rfl | rfl
      · exact ht
      · rw [tokens_filter _ (GoodL_applyAlloc P π hπ x hx hR).2.2.1]; exact ht
    · rw [if_neg hR]
      rcases hL1 (Nat.pos_of_ne_zero hR) with rfl | rfl
      · simp
      · rw [tokens_filter _ hx.2.2.1]; simp
  rw [← hL]
  unfold totalTokens
  rw [hreq, List.map_append, List.sum_append, freshList_tokens]
  omega

theorem run_tokens_eq (P : Params) (hP : P.Valid) (π : Policy) (hπ : IsScheduler P π)
    (x : State) (hx : Admissible P.bmax x) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ) (hv : ∀ i, 1 ≤ (v i).2)
    (n : ℕ) :
    totalTokens (run P π x a v n) + ∑ m ∈ Finset.range n,
        (if (run P π x a v m).R = 0 then load (π (run P π x a v m)) else 0) =
      totalTokens x + ∑ i ∈ Finset.range (arrivalsBefore a n), ((v i).1 + (v i).2) := by
  rw [← slot_sum a v (fun s => s.1 + s.2) n]
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have := step_tokens_eq P π hπ (run P π x a v n) (run_adm P hP π hπ x hx a v hv n)
      (slotArrivals a v n)
    have e : run P π x a v (n + 1) = step P π (run P π x a v n) (slotArrivals a v n) := rfl
    rw [e]
    omega

/-! ### Size bounds are invariant -/

def SizeOK (vpmax vdmax : ℕ) (x : State) : Prop := ∀ r ∈ x.reqs, r.P ≤ vpmax ∧ r.D ≤ vdmax

theorem step_size (P : Params) (π : Policy) (hπ : IsScheduler P π) (vpmax vdmax : ℕ) (x : State)
    (hx : Admissible P.bmax x) (hs : SizeOK vpmax vdmax x) (arr : List (ℕ × ℕ))
    (harr : ∀ s ∈ arr, s.1 ≤ vpmax ∧ s.2 ≤ vdmax) : SizeOK vpmax vdmax (step P π x arr) := by
  obtain ⟨L, hreq, ⟨hL0, hL1⟩, -⟩ := step_reqs P π x arr
  have hLs : ∀ r ∈ L, r.P ≤ vpmax ∧ r.D ≤ vdmax := by
    by_cases hR : x.R = 0
    · have hmem := applyAlloc_mem (hπ x hx hR).1
      have h0 : ∀ r ∈ applyAlloc x.reqs (π x), r.P ≤ vpmax ∧ r.D ≤ vdmax := by
        intro r' hr'
        obtain ⟨r, hr, d, _, rfl⟩ := hmem r' hr'
        have := hs r hr
        simp only; omega
      rcases hL0 hR with rfl | rfl
      · exact h0
      · exact fun r hr => h0 r (List.mem_filter.1 hr).1
    · rcases hL1 (Nat.pos_of_ne_zero hR) with rfl | rfl
      · exact hs
      · exact fun r hr => hs r (List.mem_filter.1 hr).1
  intro r hr
  rw [hreq] at hr
  rcases List.mem_append.1 hr with hr | hr
  · exact hLs r hr
  · exact harr _ (freshList_mem _ _ r hr).2.2

theorem run_size (P : Params) (hP : P.Valid) (π : Policy) (hπ : IsScheduler P π)
    (vpmax vdmax : ℕ) (x : State) (hx : Admissible P.bmax x) (hs : SizeOK vpmax vdmax x)
    (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ) (hv : ∀ i, 1 ≤ (v i).2 ∧ (v i).1 ≤ vpmax ∧ (v i).2 ≤ vdmax) :
    ∀ n, SizeOK vpmax vdmax (run P π x a v n) := by
  intro n
  induction n with
  | zero => exact hs
  | succ n ih =>
    refine step_size P π hπ vpmax vdmax _ (run_adm P hP π hπ x hx a v (fun i => (hv i).1) n) ih _ ?_
    intro s hs'
    simp only [slotArrivals, List.mem_map] at hs'
    obtain ⟨k, _, rfl⟩ := hs'
    exact ⟨(hv _).2.1, (hv _).2.2⟩

/-! ### Remaining time -/

theorem run_countdown (P : Params) (π : Policy) (x : State) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ) :
    ∀ n ≤ x.R, (run P π x a v n).R = x.R - n := by
  intro n
  induction n with
  | zero => intro _; simp [run]
  | succ n ih =>
    intro hn
    have := ih (by omega)
    have e := run_RDyn P π x a v n
    simp only at e
    rw [e, this, if_pos (by omega)]
    omega

theorem run_R_bound (P : Params) (hP : P.Valid) (π : Policy) (hπ : IsScheduler P π) (x : State)
    (hx : Admissible P.bmax x) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ) (hv : ∀ i, 1 ≤ (v i).2) :
    ∀ n, x.R + 1 ≤ n → (run P π x a v n).R < P.t P.bmax := by
  have hT := hP.2.2.2
  have key : ∀ n, (run P π x a v n).R < P.t P.bmax ∨ (run P π x a v n).R + n = x.R := by
    intro n
    induction n with
    | zero => right; simp [run]
    | succ n ih =>
      have e := run_RDyn P π x a v n
      simp only at e
      rw [e]
      by_cases h0 : (run P π x a v n).R = 0
      · left
        rw [if_neg (by omega)]
        have hl := run_load_le P hP π hπ x hx a v hv n h0
        have := t_mono P hl
        split_ifs <;> omega
      · rw [if_pos (by omega)]
        omega
  intro n hn
  rcases key n with h | h
  · exact h
  · omega

/-! ### Supply and request counts -/

theorem supply_ge_length (x : State) : x.reqs.length ≤ supply x := by
  unfold supply
  generalize x.reqs = L
  induction L with
  | nil => simp
  | cons r rs ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    split_ifs with h <;> omega

theorem exists_D_pos {L : List Req} (h : (L.filter fun r => r.D = 0).length < L.length) :
    ∃ r ∈ L, r.D ≠ 0 := by
  by_contra hc
  push Not at hc
  have : L.filter (fun r => r.D = 0) = L := List.filter_eq_self.2 (fun r hr => by simp [hc r hr])
  rw [this] at h
  exact lt_irrefl _ h

theorem tokens_pos {L : List Req} {r : Req} (hr : r ∈ L) (hD : r.D ≠ 0) :
    1 ≤ (L.map fun r => r.P + r.D).sum := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun r : Req => r.P + r.D) hr)
  omega

/-! ### The finite target set -/

def FS (T bmax vpmax vdmax : ℕ) : Set (ℕ × List (ℕ × ℕ)) :=
  {c | c.1 < T ∧ c.2.length ≤ bmax ∧ ∀ e ∈ c.2, e.1 ≤ vpmax ∧ e.2 ≤ vdmax}

theorem FS_finite (T bmax vpmax vdmax : ℕ) : (FS T bmax vpmax vdmax).Finite := by
  let α := Fin (vpmax + 1) × Fin (vdmax + 1)
  let toN : List α → List (ℕ × ℕ) := List.map fun e => ((e.1 : ℕ), (e.2 : ℕ))
  have hL : {l : List (ℕ × ℕ) | l.length ≤ bmax ∧ ∀ e ∈ l, e.1 ≤ vpmax ∧ e.2 ≤ vdmax}.Finite := by
    refine ((List.finite_length_le α bmax).image toN).subset ?_
    intro l ⟨hlen, hent⟩
    refine ⟨l.pmap (fun e (he : e.1 ≤ vpmax ∧ e.2 ≤ vdmax) =>
      ((⟨e.1, by omega⟩ : Fin (vpmax + 1)), (⟨e.2, by omega⟩ : Fin (vdmax + 1)))) hent, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, List.length_pmap]; exact hlen
    · simp only [toN, List.map_pmap]
      exact List.pmap_eq_self.2 (fun e _ => rfl)
  refine ((Set.finite_Iio T).prod hL).subset ?_
  intro c ⟨h1, h2, h3⟩
  exact ⟨h1, h2, h3⟩

/-! ### The key deterministic bound -/

theorem no_hit_bound (P : Params) (hP : P.Valid) (π : Policy) (hπ : IsScheduler P π)
    (hWC : IsWorkConserving P π) (vpmax vdmax : ℕ) (x : State) (hx : Admissible P.bmax x)
    (hs : SizeOK vpmax vdmax x) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ)
    (hv : ∀ i, 1 ≤ (v i).2 ∧ (v i).1 ≤ vpmax ∧ (v i).2 ≤ vdmax) (k : ℕ)
    (hno : ∀ n, 1 ≤ n → n ≤ x.R + P.t P.bmax + k * P.t P.bmax →
      config (run P π x a v n) ∉ FS (P.t P.bmax) P.bmax vpmax vdmax) :
    k * P.bmax + 1 ≤ totalTokens x +
      ∑ i ∈ Finset.range (arrivalsBefore a (x.R + P.t P.bmax + k * P.t P.bmax)), ((v i).1 + (v i).2) := by
  have hT : 1 ≤ P.t P.bmax := hP.2.2.2
  have hv2 : ∀ i, 1 ≤ (v i).2 := fun i => (hv i).1
  have hdyn := run_RDyn P π x a v
  have hadm := run_adm P hP π hπ x hx a v hv2
  have hsz := run_size P hP π hπ vpmax vdmax x hx hs a v hv
  -- not in `F` with small `R` forces more than `b_max` requests
  have hlong : ∀ n, 1 ≤ n → n ≤ x.R + P.t P.bmax + k * P.t P.bmax →
      (run P π x a v n).R < P.t P.bmax → P.bmax < (run P π x a v n).reqs.length := by
    intro n h1 h2 hR
    by_contra hc
    push Not at hc
    apply hno n h1 h2
    refine ⟨hR, by simpa [config] using hc, ?_⟩
    intro e he
    simp only [config, List.mem_map] at he
    obtain ⟨r, hr, rfl⟩ := he
    exact hsz n r hr
  -- a scheduling instant with a long queue schedules a full batch
  have hfull : ∀ n, 1 ≤ n → n ≤ x.R + P.t P.bmax + k * P.t P.bmax → (run P π x a v n).R = 0 →
      load (π (run P π x a v n)) = P.bmax := by
    intro n h1 h2 h0
    have hl := hlong n h1 h2 (by rw [h0]; omega)
    have hsup := supply_ge_length (run P π x a v n)
    exact hWC _ (hadm n) h0 (by omega)
  -- the first scheduling instant after the initial countdown
  have hR0 : (run P π x a v x.R).R = 0 := by
    rw [run_countdown P π x a v x.R le_rfl, Nat.sub_self]
  have hτ0 : P.t (load (π (run P π x a v x.R))) ≤ P.t P.bmax :=
    t_mono P (run_load_le P hP π hπ x hx a v hv2 x.R hR0)
  obtain ⟨s1, hs1a, hs1b, hs1R⟩ : ∃ s1, x.R + 1 ≤ s1 ∧ s1 ≤ x.R + P.t P.bmax ∧
      (run P π x a v s1).R = 0 := by
    rcases Nat.eq_zero_or_pos (P.t (load (π (run P π x a v x.R)))) with h0 | hpos
    · refine ⟨x.R + 1, le_rfl, by omega, ?_⟩
      have e := hdyn x.R
      simp only at e
      rw [e, hR0, h0]; simp
    · refine ⟨x.R + P.t (load (π (run P π x a v x.R))), by omega, by omega, ?_⟩
      have := busy hdyn (m := x.R) hR0 hpos _ hpos le_rfl
      rw [this, Nat.sub_self]
  -- full batches every `T` slots
  have hchain : ∀ j, j < k → (run P π x a v (s1 + j * P.t P.bmax)).R = 0 ∧
      load (π (run P π x a v (s1 + j * P.t P.bmax))) = P.bmax := by
    intro j
    induction j with
    | zero =>
      intro hk
      have e : s1 + 0 * P.t P.bmax = s1 := by simp
      rw [e]
      exact ⟨hs1R, hfull s1 (by omega) (by nlinarith) hs1R⟩
    | succ j ih =>
      intro hk
      obtain ⟨h0, hl⟩ := ih (by omega)
      have hτ : P.t (load (π (run P π x a v (s1 + j * P.t P.bmax)))) = P.t P.bmax := by rw [hl]
      have hR' : (run P π x a v (s1 + (j + 1) * P.t P.bmax)).R = 0 := by
        have := busy hdyn (m := s1 + j * P.t P.bmax) h0 (by rw [hτ]; omega) (P.t P.bmax)
          (by omega) (by rw [hτ])
        rw [show s1 + (j + 1) * P.t P.bmax = s1 + j * P.t P.bmax + P.t P.bmax by ring, this, hτ,
          Nat.sub_self]
      refine ⟨hR', ?_⟩
      have hle : s1 + (j + 1) * P.t P.bmax ≤ x.R + P.t P.bmax + k * P.t P.bmax := by
        have : (j + 1) * P.t P.bmax ≤ k * P.t P.bmax := Nat.mul_le_mul_right _ (by omega)
        omega
      exact hfull _ (by omega) hle hR'
  -- processed tokens
  have hproc : k * P.bmax ≤ ∑ m ∈ Finset.range (x.R + P.t P.bmax + k * P.t P.bmax),
      (if (run P π x a v m).R = 0 then load (π (run P π x a v m)) else 0) := by
    have himg : (Finset.range k).image (fun j => s1 + j * P.t P.bmax) ⊆
        Finset.range (x.R + P.t P.bmax + k * P.t P.bmax) := by
      intro m hm
      simp only [Finset.mem_image, Finset.mem_range] at hm ⊢
      obtain ⟨j, hj, rfl⟩ := hm
      have : (j + 1) * P.t P.bmax ≤ k * P.t P.bmax := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
    have hinj : Set.InjOn (fun j => s1 + j * P.t P.bmax) (Finset.range k) := by
      intro i _ j _ h
      have h2 : s1 + i * P.t P.bmax = s1 + j * P.t P.bmax := h
      exact Nat.eq_of_mul_eq_mul_right (m := P.t P.bmax) (by omega) (by omega)
    have hsum : ∑ m ∈ (Finset.range k).image (fun j => s1 + j * P.t P.bmax),
        (if (run P π x a v m).R = 0 then load (π (run P π x a v m)) else 0) = k * P.bmax := by
      rw [Finset.sum_image hinj]
      rw [Finset.sum_congr rfl fun j hj => by
        rw [if_pos (hchain j (Finset.mem_range.1 hj)).1, (hchain j (Finset.mem_range.1 hj)).2]]
      simp
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset himg
  -- tokens left at the end
  have hpos : 1 ≤ totalTokens (run P π x a v (x.R + P.t P.bmax + k * P.t P.bmax)) := by
    have hRN := run_R_bound P hP π hπ x hx a v hv2 (x.R + P.t P.bmax + k * P.t P.bmax) (by omega)
    have hlen := hlong _ (by omega) le_rfl hRN
    have hD := (hadm (x.R + P.t P.bmax + k * P.t P.bmax)).2.2.2.2
    obtain ⟨r, hr, hr0⟩ := exists_D_pos
      (L := (run P π x a v (x.R + P.t P.bmax + k * P.t P.bmax)).reqs) (by omega)
    exact tokens_pos hr hr0
  have heq := run_tokens_eq P hP π hπ x hx a v hv2 (x.R + P.t P.bmax + k * P.t P.bmax)
  omega

end LLMThroughput.TokenBudget.Core


open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open LLMThroughput.TokenBudget

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Params) (hP : P.Valid) (vpmax vdmax : ℕ) (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ)
    (hA : IIDArrivals μ a v vpmax vdmax)
    (hload : arrivalRate μ a * (meanPrefill μ v + meanDecode μ v) < (P.bmax : ℝ) / (P.t P.bmax : ℝ)) :
    ∀ (K : ℕ) (π : Policy), IsScheduler P π → IsWorkConserving P π → IsKFCFS P K π →
      ∃ F : Finset (ℕ × List (ℕ × ℕ)), ∀ x : State, Admissible P.bmax x →
        (∀ r ∈ x.reqs, r.P ≤ vpmax ∧ r.D ≤ vdmax) →
        ∫⁻ ω, ((hitTime F (run P π x (fun m => a m ω) (fun i => v i ω)) : ℕ∞) : ℝ≥0∞) ∂μ
          < ⊤ := by
  intro K π hπ hWC _
  set T := P.t P.bmax with hTdef
  have hT : 1 ≤ T := hP.2.2.2
  -- the drift condition in `ℝ≥0∞`
  have hvp_meas : Measurable (fun ω => ((v 0 ω).1 : ℝ)) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (measurable_fst.comp (hA.meas_v 0))
  have hvd_meas : Measurable (fun ω => ((v 0 ω).2 : ℝ)) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (measurable_snd.comp (hA.meas_v 0))
  have hint_p : Integrable (fun ω => ((v 0 ω).1 : ℝ)) μ := by
    refine Integrable.of_bound (C := (vpmax : ℝ)) hvp_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have := (hA.size_bounds 0 ω).2.1
    simp only [Real.norm_natCast]; exact_mod_cast this
  have hint_d : Integrable (fun ω => ((v 0 ω).2 : ℝ)) μ := by
    refine Integrable.of_bound (C := (vdmax : ℝ)) hvd_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have := (hA.size_bounds 0 ω).2.2.2
    simp only [Real.norm_natCast]; exact_mod_cast this
  have hla : ∫⁻ ω, (a 0 ω : ℝ≥0∞) ∂μ = ENNReal.ofReal (arrivalRate μ a) := by
    rw [arrivalRate, ofReal_integral_eq_lintegral_ofReal hA.integrable_a
      (Filter.Eventually.of_forall fun ω => by positivity)]
    simp
  have hlw : ∫⁻ ω, (((v 0 ω).1 + (v 0 ω).2 : ℕ) : ℝ≥0∞) ∂μ =
      ENNReal.ofReal (meanPrefill μ v + meanDecode μ v) := by
    rw [meanPrefill, meanDecode, ← integral_add hint_p hint_d,
      ofReal_integral_eq_lintegral_ofReal (f := fun ω => ((v 0 ω).1 : ℝ) + ((v 0 ω).2 : ℝ))
      (hint_p.add hint_d)
      (Filter.Eventually.of_forall fun ω => by simp only [Pi.add_apply, Pi.zero_apply]; positivity)]
    congr 1; funext ω
    rw [← Nat.cast_add, ENNReal.ofReal_natCast]
  have hlam0 : 0 ≤ arrivalRate μ a := integral_nonneg fun ω => by positivity
  have hm0 : 0 ≤ meanPrefill μ v + meanDecode μ v :=
    add_nonneg (integral_nonneg fun ω => by positivity) (integral_nonneg fun ω => by positivity)
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hB : (T : ℝ≥0∞) * (∫⁻ ω, (a 0 ω : ℝ≥0∞) ∂μ) *
      (∫⁻ ω, (((v 0 ω).1 + (v 0 ω).2 : ℕ) : ℝ≥0∞) ∂μ) < P.bmax := by
    rw [hla, hlw, ← ENNReal.ofReal_natCast T, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast P.bmax,
      ENNReal.ofReal_lt_ofReal_iff (by have := hP.2.2.1; exact_mod_cast (by omega : 0 < P.bmax))]
    rw [lt_div_iff₀ hTr] at hload
    linarith
  refine ⟨(Core.FS_finite T P.bmax vpmax vdmax).toFinset, ?_⟩
  intro x hx hsz
  set W0 := totalTokens x
  set D := x.R + T
  -- pathwise bound on the hitting time
  have hpath : ∀ ω, ((hitTime (Core.FS_finite T P.bmax vpmax vdmax).toFinset
      (run P π x (fun m => a m ω) (fun i => v i ω)) : ℕ∞) : ℝ≥0∞) ≤
      (D : ℝ≥0∞) + (T : ℝ≥0∞) * ((Core.kappa a v D T P.bmax W0 ω : ℕ∞) : ℝ≥0∞) := by
    intro ω
    have hv : ∀ i, 1 ≤ (v i ω).2 ∧ (v i ω).1 ≤ vpmax ∧ (v i ω).2 ≤ vdmax := fun i =>
      ⟨(hA.size_bounds i ω).2.2.1, (hA.size_bounds i ω).2.1, (hA.size_bounds i ω).2.2.2⟩
    classical
    by_cases hex : ∃ k, W0 + Core.Acc a v ω (D + k * T) ≤ k * P.bmax
    · obtain ⟨k0, hk0s, hk0m⟩ : ∃ k0, W0 + Core.Acc a v ω (D + k0 * T) ≤ k0 * P.bmax ∧
          ∀ k, W0 + Core.Acc a v ω (D + k * T) ≤ k * P.bmax → k0 ≤ k :=
        ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min' hex hk⟩
      have hk0 : Core.kappa a v D T P.bmax W0 ω = k0 := by
        apply le_antisymm
        · exact iInf₂_le k0 hk0s
        · exact le_iInf₂ fun k hk => Nat.cast_le.2 (hk0m k hk)
      -- some slot up to `D + k0 T` hits `F`
      have hhit : ∃ n, 1 ≤ n ∧ n ≤ D + k0 * T ∧ config (run P π x (fun m => a m ω)
          (fun i => v i ω) n) ∈ Core.FS T P.bmax vpmax vdmax := by
        by_contra hc
        push Not at hc
        have h3 : k0 * P.bmax + 1 ≤ W0 + Core.Acc a v ω (D + k0 * T) :=
          Core.no_hit_bound P hP π hπ hWC vpmax vdmax x hx hsz (fun m => a m ω)
            (fun i => v i ω) hv k0 (fun n h1 h2 => hc n h1 h2)
        omega
      obtain ⟨n, hn1, hn2, hnF⟩ := hhit
      have hle : hitTime (Core.FS_finite T P.bmax vpmax vdmax).toFinset
          (run P π x (fun m => a m ω) (fun i => v i ω)) ≤ n :=
        iInf₂_le n ⟨hn1, (Set.Finite.mem_toFinset _).2 hnF⟩
      rw [hk0]
      calc ((hitTime (Core.FS_finite T P.bmax vpmax vdmax).toFinset
            (run P π x (fun m => a m ω) (fun i => v i ω)) : ℕ∞) : ℝ≥0∞) ≤ ((n : ℕ∞) : ℝ≥0∞) :=
            ENat.toENNReal_le.2 hle
        _ = (n : ℝ≥0∞) := by simp
        _ ≤ ((D + k0 * T : ℕ) : ℝ≥0∞) := by exact_mod_cast hn2
        _ = _ := by push_cast; ring
    · push Not at hex
      have htop : Core.kappa a v D T P.bmax W0 ω = ⊤ := by
        refine iInf₂_eq_top.2 fun k hk => absurd hk (by have := hex k; omega)
      rw [htop, ENat.toENNReal_top, ENNReal.mul_top (by exact_mod_cast (by omega : T ≠ 0))]
      simp
  calc _ ≤ ∫⁻ ω, ((D : ℝ≥0∞) + (T : ℝ≥0∞) * ((Core.kappa a v D T P.bmax W0 ω : ℕ∞) : ℝ≥0∞)) ∂μ :=
        lintegral_mono hpath
    _ = (D : ℝ≥0∞) + (T : ℝ≥0∞) * ∫⁻ ω, ((Core.kappa a v D T P.bmax W0 ω : ℕ∞) : ℝ≥0∞) ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ (by simp)]
    _ < ⊤ := by
        refine ENNReal.add_lt_top.2 ⟨by simp, ENNReal.mul_lt_top (by simp) ?_⟩
        exact Core.kappa_lintegral_lt_top hA D T P.bmax W0 hB
