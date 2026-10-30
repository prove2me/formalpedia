-- Prove2me | solution 1 for LLMThroughput.TokenBudget.theorem_2_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T13:43:57.363223+00:00
-- url     : https://prove2.me/submissions/e4e510d7-5f74-4403-bc9d-7a2378b67681

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Model
import Theorems.Thm_LLMThroughput_TokenBudget_eq_56

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
open Filter Topology

theorem path_diverge (P : Params) (hP : P.Valid) (π : Policy) (hπ : IsScheduler P π)
    (x : State) (hx : Admissible P.bmax x) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ) (hv : ∀ i, 1 ≤ (v i).2)
    (lam m1 m2 : ℝ)
    (hE : Tendsto (fun n : ℕ => (arrivalsBefore a n : ℝ) / n) atTop (𝓝 lam))
    (hS1 : Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, ((v i).1 : ℝ)) / N) atTop (𝓝 m1))
    (hS2 : Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, ((v i).2 : ℝ)) / N) atTop (𝓝 m2))
    (hload : (P.bmax : ℝ) / (P.t P.bmax : ℝ) < lam * (m1 + m2)) :
    Tendsto (fun n => totalTokens (run P π x a v n)) atTop atTop := by
  set T : ℕ := P.t P.bmax with hTdef
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hP.2.2.2
  set κ : ℝ := (P.bmax : ℝ) / T with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set m := m1 + m2 with hm
  set E := arrivalsBefore a with hEdef
  -- combined size average
  have hS : Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, (((v i).1 + (v i).2 : ℕ) : ℝ)) / N)
      atTop (𝓝 m) := by
    have := hS1.add hS2
    refine this.congr (fun N => ?_)
    rw [← add_div, ← Finset.sum_add_distrib]; push_cast; rfl
  have hm0 : 0 ≤ m := by
    refine ge_of_tendsto hS (Eventually.of_forall fun N => ?_)
    positivity
  have hlam0 : 0 ≤ lam := by
    refine ge_of_tendsto hE (Eventually.of_forall fun N => ?_)
    positivity
  have hlam : 0 < lam := by
    rcases hlam0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hload; simp at hload; linarith
  -- E n → ∞
  have hEr : Tendsto (fun n : ℕ => (E n : ℝ)) atTop atTop := by
    have h2 := hE.pos_mul_atTop hlam tendsto_natCast_atTop_atTop
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hEn : Tendsto E atTop atTop := tendsto_natCast_atTop_iff.1 hEr
  -- A n / n → m lam
  set A : ℕ → ℕ := fun n => ∑ i ∈ Finset.range (E n), ((v i).1 + (v i).2) with hA
  have hAn : Tendsto (fun n : ℕ => (A n : ℝ) / n) atTop (𝓝 (m * lam)) := by
    have h1 := (hS.comp hEn).mul hE
    refine h1.congr' ?_
    filter_upwards [hEn.eventually_ge_atTop 1, eventually_ge_atTop 1] with n hn hn'
    have : (E n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Function.comp, hA]
    push_cast
    field_simp
  -- deterministic lower bound
  have hlow : ∀ n : ℕ, (A n : ℝ) - κ * (n + T) ≤ totalTokens (run P π x a v n) := by
    intro n
    have h1 := run_tokens P hP π hπ x hx a v hv n
    rw [← hEdef] at h1
    have h2 := processed_bound P hP π hπ x hx a v hv n
    set Pr := ∑ m ∈ Finset.range n,
        (if (run P π x a v m).R = 0 then load (π (run P π x a v m)) else 0)
    have h1' : (A n : ℝ) ≤ totalTokens (run P π x a v n) + Pr := by
      have : A n ≤ totalTokens (run P π x a v n) + Pr := by simp only [hA]; omega
      exact_mod_cast this
    have h2' : (Pr : ℝ) * T ≤ P.bmax * (n + T) := by exact_mod_cast h2
    have h3 : (Pr : ℝ) ≤ κ * (n + T) := by
      rw [hκ, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      linarith
    linarith
  -- lower bound grows linearly
  have hg : Tendsto (fun n : ℕ => (A n : ℝ) / n - κ - κ * T * (n : ℝ)⁻¹) atTop
      (𝓝 (m * lam - κ - κ * T * 0)) :=
    ((hAn.sub tendsto_const_nhds).sub (tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat))
  simp only [mul_zero, sub_zero] at hg
  have hpos : 0 < m * lam - κ := by rw [mul_comm]; linarith
  set c := (m * lam - κ) / 2 with hc
  have hev : ∀ᶠ n : ℕ in atTop, c < (A n : ℝ) / n - κ - κ * T * (n : ℝ)⁻¹ :=
    hg.eventually (lt_mem_nhds (by rw [hc]; linarith))
  apply (tendsto_natCast_atTop_iff (R := ℝ)).1
  refine tendsto_atTop_mono' atTop ?_
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (show 0 < c by rw [hc]; linarith))
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have := hlow n
  have e : (A n : ℝ) / n - κ - κ * T * (n : ℝ)⁻¹ = ((A n : ℝ) - κ * (n + T)) / n := by
    field_simp; ring
  rw [e, lt_div_iff₀ hn0] at hn
  linarith

end LLMThroughput.TokenBudget.Core


open MeasureTheory ProbabilityTheory Filter Topology
open LLMThroughput.TokenBudget

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Params) (hP : P.Valid) (vpmax vdmax : ℕ) (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ)
    (hA : IIDArrivals μ a v vpmax vdmax)
    (hload : (P.bmax : ℝ) / (P.t P.bmax : ℝ) < arrivalRate μ a * (meanPrefill μ v + meanDecode μ v)) :
    ∀ π : Policy, IsScheduler P π → ∀ x : State, Admissible P.bmax x →
      ∀ᵐ ω ∂μ, Tendsto
        (fun n => totalTokens (run P π x (fun m => a m ω) (fun i => v i ω) n)) atTop atTop := by
  intro π hπ x hx
  filter_upwards [eq_56 μ vpmax vdmax a v hA] with ω ⟨h1, h2, h3⟩
  exact Core.path_diverge P hP π hπ x hx (fun m => a m ω) (fun i => v i ω)
    (fun i => (hA.size_bounds i ω).2.2.1) _ _ _ h1 h2 h3 hload
