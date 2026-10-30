-- Prove2me | solution 1 for LLMThroughput.TokenBudget.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T14:17:10.971774+00:00
-- url     : https://prove2.me/submissions/b12af172-f369-477a-b0eb-6ba07e2ea6c5

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

/-! ### Per-label bookkeeping -/

/-- Tokens left of the request labelled `ℓ` in a request list (0 if absent). -/
def tkL (L : List Req) (ℓ : ℕ) : ℕ := ((L.filter fun r => r.label = ℓ).map fun r => r.P + r.D).sum

/-- Decode tokens left of the request labelled `ℓ`. -/
def dkL (L : List Req) (ℓ : ℕ) : ℕ := ((L.filter fun r => r.label = ℓ).map fun r => r.D).sum

/-- Tokens allocated to label `ℓ` by `δ`. -/
def gaL (L : List Req) (δ : Alloc) (ℓ : ℕ) : ℕ :=
  (((L.zip δ).filter fun p => p.1.label = ℓ).map fun p => p.2.1 + p.2.2).sum

/-- Decode tokens allocated to label `ℓ` by `δ`. -/
def gdL (L : List Req) (δ : Alloc) (ℓ : ℕ) : ℕ :=
  (((L.zip δ).filter fun p => p.1.label = ℓ).map fun p => p.2.2).sum

theorem applyAlloc_tkL {L : List Req} {δ : Alloc}
    (h : List.Forall₂ (fun r d => d.1 ≤ r.P ∧ d.2 ≤ r.D) L δ) (ℓ : ℕ) :
    tkL (applyAlloc L δ) ℓ + gaL L δ ℓ = tkL L ℓ := by
  induction h with
  | nil => simp [tkL, gaL, applyAlloc]
  | @cons r d rs ds hrd _ ih =>
    rw [applyAlloc_cons]
    simp only [tkL, gaL, List.zip_cons_cons, List.filter_cons] at ih ⊢
    by_cases hl : r.label = ℓ
    · simp only [hl, decide_true, if_true, List.map_cons, List.sum_cons]
      omega
    · simp only [hl, decide_false, Bool.false_eq_true, if_false]
      exact ih

theorem applyAlloc_dkL {L : List Req} {δ : Alloc}
    (h : List.Forall₂ (fun r d => d.1 ≤ r.P ∧ d.2 ≤ r.D) L δ) (ℓ : ℕ) :
    dkL (applyAlloc L δ) ℓ + gdL L δ ℓ = dkL L ℓ := by
  induction h with
  | nil => simp [dkL, gdL, applyAlloc]
  | @cons r d rs ds hrd _ ih =>
    rw [applyAlloc_cons]
    simp only [dkL, gdL, List.zip_cons_cons, List.filter_cons] at ih ⊢
    by_cases hl : r.label = ℓ
    · simp only [hl, decide_true, if_true, List.map_cons, List.sum_cons]
      omega
    · simp only [hl, decide_false, Bool.false_eq_true, if_false]
      exact ih

theorem filter_tkL (L : List Req) (h : ∀ r ∈ L, 0 < r.P → 1 ≤ r.D) (ℓ : ℕ) :
    tkL (L.filter fun r => decide (r.D ≠ 0)) ℓ = tkL L ℓ := by
  unfold tkL
  rw [List.filter_filter]
  have : (fun r : Req => decide (r.label = ℓ) && decide (r.D ≠ 0)) =
      (fun r => decide (r.D ≠ 0) && decide (r.label = ℓ)) := by funext r; exact Bool.and_comm _ _
  rw [this, ← List.filter_filter]
  exact tokens_filter _ (fun r hr => h r (List.mem_filter.1 hr).1)

theorem filter_dkL (L : List Req) (ℓ : ℕ) :
    dkL (L.filter fun r => decide (r.D ≠ 0)) ℓ = dkL L ℓ := by
  induction L with
  | nil => simp [dkL]
  | cons r rs ih =>
    simp only [dkL] at ih ⊢
    by_cases hD : r.D = 0
    · rw [List.filter_cons, if_neg (by simp [hD]), ih, List.filter_cons]
      by_cases hl : r.label = ℓ
      · rw [if_pos (by simp [hl]), List.map_cons, List.sum_cons, hD, Nat.zero_add]
      · rw [if_neg (by simp [hl])]
    · rw [List.filter_cons, if_pos (by simp [hD]), List.filter_cons, List.filter_cons]
      by_cases hl : r.label = ℓ
      · rw [if_pos (by simp [hl]), if_pos (by simp [hl]), List.map_cons, List.sum_cons,
          List.map_cons, List.sum_cons, ih]
      · rw [if_neg (by simp [hl]), if_neg (by simp [hl]), ih]

theorem tkL_append (L1 L2 : List Req) (ℓ : ℕ) : tkL (L1 ++ L2) ℓ = tkL L1 ℓ + tkL L2 ℓ := by
  simp [tkL, List.filter_append]

theorem dkL_append (L1 L2 : List Req) (ℓ : ℕ) : dkL (L1 ++ L2) ℓ = dkL L1 ℓ + dkL L2 ℓ := by
  simp [dkL, List.filter_append]

theorem tkL_absent {L : List Req} {ℓ : ℕ} (h : ∀ r ∈ L, r.label ≠ ℓ) : tkL L ℓ = 0 := by
  unfold tkL
  rw [List.filter_eq_nil_iff.2 (fun r hr => by simpa using h r hr)]; rfl

theorem dkL_absent {L : List Req} {ℓ : ℕ} (h : ∀ r ∈ L, r.label ≠ ℓ) : dkL L ℓ = 0 := by
  unfold dkL
  rw [List.filter_eq_nil_iff.2 (fun r hr => by simpa using h r hr)]; rfl

theorem gaL_absent {L : List Req} {δ : Alloc} {ℓ : ℕ} (h : ∀ r ∈ L, r.label ≠ ℓ) :
    gaL L δ ℓ = 0 := by
  unfold gaL
  rw [List.filter_eq_nil_iff.2 (fun p hp => by simpa using h p.1 (List.of_mem_zip hp).1)]; rfl

theorem gdL_absent {L : List Req} {δ : Alloc} {ℓ : ℕ} (h : ∀ r ∈ L, r.label ≠ ℓ) :
    gdL L δ ℓ = 0 := by
  unfold gdL
  rw [List.filter_eq_nil_iff.2 (fun p hp => by simpa using h p.1 (List.of_mem_zip hp).1)]; rfl

theorem freshList_tkL (n : ℕ) (arr : List (ℕ × ℕ)) :
    ∀ k (hk : k < arr.length), tkL (freshList n arr) (n + k) = arr[k].1 + arr[k].2 ∧
      dkL (freshList n arr) (n + k) = arr[k].2 := by
  induction arr generalizing n with
  | nil => intro k hk; simp at hk
  | cons s l ih =>
    intro k hk
    have htail : ∀ r ∈ freshList (n + 1) l, r.label ≠ n := fun r hr => by
      have := (freshList_mem (n + 1) l r hr).1; omega
    rcases k with _ | k
    · simp only [freshList, tkL, dkL, List.filter_cons, Nat.add_zero, decide_true, if_true,
        List.map_cons, List.sum_cons, List.getElem_cons_zero]
      have h1 := tkL_absent htail
      have h2 := dkL_absent htail
      simp only [tkL, dkL] at h1 h2
      rw [h1, h2]; simp
    · have := ih (n + 1) k (by simpa using hk)
      rw [show n + 1 + k = n + (k + 1) by omega] at this
      simp only [freshList, tkL, dkL, List.filter_cons,
        show ¬ (n = n + (k + 1)) by omega, decide_false, Bool.false_eq_true, if_false,
        List.getElem_cons_succ]
      exact this

/-- The kept requests of a step are good for the old `next`. -/
theorem step_L_good (P : Params) (π : Policy) (hπ : IsScheduler P π) (x : State)
    (hx : Admissible P.bmax x) (arr : List (ℕ × ℕ)) :
    ∃ L : List Req, (step P π x arr).reqs = L ++ freshList x.next arr ∧ GoodL P.bmax x.next L ∧
      (∀ ℓ, ℓ < x.next → tkL L ℓ + (if x.R = 0 then gaL x.reqs (π x) ℓ else 0) = tkL x.reqs ℓ ∧
        dkL L ℓ + (if x.R = 0 then gdL x.reqs (π x) ℓ else 0) = dkL x.reqs ℓ) ∧
      (∀ r ∈ L, ∃ r' ∈ x.reqs, r'.label = r.label) := by
  obtain ⟨L, hreq, ⟨hL0, hL1⟩, -⟩ := step_reqs P π x arr
  refine ⟨L, hreq, ?_, ?_, ?_⟩
  · by_cases hR : x.R = 0
    · rcases hL0 hR with rfl | rfl
      · exact GoodL_applyAlloc P π hπ x hx hR
      · exact GoodL_filter (GoodL_applyAlloc P π hπ x hx hR)
    · rcases hL1 (Nat.pos_of_ne_zero hR) with rfl | rfl
      · exact GoodL_of_adm hx
      · exact GoodL_filter (GoodL_of_adm hx)
  · intro ℓ _
    by_cases hR : x.R = 0
    · have hF := (hπ x hx hR).1
      have hF' : List.Forall₂ (fun r d => d.1 ≤ r.P ∧ d.2 ≤ r.D) x.reqs (π x) :=
        hF.imp (fun r d h => ⟨h.2.1, h.2.2.2⟩)
      rw [if_pos hR, if_pos hR]
      rcases hL0 hR with rfl | rfl
      · exact ⟨applyAlloc_tkL hF' ℓ, applyAlloc_dkL hF' ℓ⟩
      · rw [filter_tkL _ (GoodL_applyAlloc P π hπ x hx hR).2.2.1, filter_dkL]
        exact ⟨applyAlloc_tkL hF' ℓ, applyAlloc_dkL hF' ℓ⟩
    · rw [if_neg hR, if_neg hR]
      rcases hL1 (Nat.pos_of_ne_zero hR) with rfl | rfl
      · simp
      · rw [filter_tkL _ hx.2.2.1, filter_dkL]; simp
  · intro r hr
    by_cases hR : x.R = 0
    · have hmem := applyAlloc_mem (hπ x hx hR).1
      rcases hL0 hR with rfl | rfl
      · obtain ⟨r0, hr0, d, _, rfl⟩ := hmem r hr
        exact ⟨r0, hr0, rfl⟩
      · obtain ⟨r0, hr0, d, _, rfl⟩ := hmem r (List.mem_filter.1 hr).1
        exact ⟨r0, hr0, rfl⟩
    · rcases hL1 (Nat.pos_of_ne_zero hR) with rfl | rfl
      · exact ⟨r, hr, rfl⟩
      · exact ⟨r, (List.mem_filter.1 hr).1, rfl⟩

/-! ### Allocation sums -/

theorem gaL_cons (r : Req) (rs : List Req) (d : ℕ × ℕ) (ds : Alloc) (ℓ : ℕ) :
    gaL (r :: rs) (d :: ds) ℓ = (if r.label = ℓ then d.1 + d.2 else 0) + gaL rs ds ℓ := by
  simp only [gaL, List.zip_cons_cons, List.filter_cons]
  split_ifs with h <;> simp_all

theorem gdL_cons (r : Req) (rs : List Req) (d : ℕ × ℕ) (ds : Alloc) (ℓ : ℕ) :
    gdL (r :: rs) (d :: ds) ℓ = (if r.label = ℓ then d.2 else 0) + gdL rs ds ℓ := by
  simp only [gdL, List.zip_cons_cons, List.filter_cons]
  split_ifs with h <;> simp_all

theorem sum_gaL_le (T : Finset ℕ) : ∀ (L : List Req) (δ : Alloc),
    ∑ ℓ ∈ T, gaL L δ ℓ ≤ load δ := by
  intro L
  induction L with
  | nil => intro δ; simp [gaL]
  | cons r rs ih =>
    intro δ
    cases δ with
    | nil => simp [gaL]
    | cons d ds =>
      simp_rw [gaL_cons]
      rw [Finset.sum_add_distrib]
      have h1 : ∑ ℓ ∈ T, (if r.label = ℓ then d.1 + d.2 else 0) ≤ d.1 + d.2 := by
        rw [Finset.sum_ite_eq]; split_ifs <;> omega
      have h2 := ih ds
      simp only [load, List.map_cons, List.sum_cons] at h2 ⊢
      omega

theorem sum_gdL_le (T : Finset ℕ) : ∀ (L : List Req) (δ : Alloc),
    ∑ ℓ ∈ T, gdL L δ ℓ ≤ load δ := by
  intro L
  induction L with
  | nil => intro δ; simp [gdL]
  | cons r rs ih =>
    intro δ
    cases δ with
    | nil => simp [gdL]
    | cons d ds =>
      simp_rw [gdL_cons]
      rw [Finset.sum_add_distrib]
      have h1 : ∑ ℓ ∈ T, (if r.label = ℓ then d.2 else 0) ≤ d.1 + d.2 := by
        rw [Finset.sum_ite_eq]; split_ifs <;> omega
      have h2 := ih ds
      simp only [load, List.map_cons, List.sum_cons] at h2 ⊢
      omega

theorem exists_zip_entry : ∀ (L : List Req) (δ : Alloc), L.length = δ.length →
    ∀ r ∈ L, ∃ d, (r, d) ∈ L.zip δ := by
  intro L
  induction L with
  | nil => intro δ _ r hr; simp at hr
  | cons r0 rs ih =>
    intro δ hlen r hr
    cases δ with
    | nil => simp at hlen
    | cons d ds =>
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨d, by simp⟩
      · obtain ⟨d', hd'⟩ := ih ds (by simpa using hlen) r hr
        exact ⟨d', by simp [hd']⟩

theorem gdL_pos {L : List Req} {δ : Alloc} {ℓ : ℕ} (h : 1 ≤ gdL L δ ℓ) :
    ∃ q ∈ L.zip δ, q.1.label = ℓ ∧ 0 < q.2.2 := by
  unfold gdL at h
  by_contra hc
  push Not at hc
  have : ((L.zip δ).filter fun p => p.1.label = ℓ).map (fun p => p.2.2) =
      ((L.zip δ).filter fun p => p.1.label = ℓ).map (fun _ => 0) := by
    apply List.map_congr_left
    intro p hp
    have := (List.mem_filter.1 hp)
    have h2 := hc p this.1 (by simpa using this.2)
    omega
  rw [this] at h
  simp at h

theorem gaL_ge_entry {L : List Req} {δ : Alloc} {p : Req × (ℕ × ℕ)} (hp : p ∈ L.zip δ) :
    p.2.1 + p.2.2 ≤ gaL L δ p.1.label := by
  unfold gaL
  exact List.le_sum_of_mem (List.mem_map_of_mem (f := fun p : Req × (ℕ × ℕ) => p.2.1 + p.2.2)
    (List.mem_filter.2 ⟨hp, by simp⟩))

/-- K-FCFS: if `q` decodes, every present request at least `K` labels older gets a token. -/
theorem kfcfs_ga (P : Params) (K : ℕ) (π : Policy) (hπ : IsScheduler P π) (hK : IsKFCFS P K π)
    (x : State) (hx : Admissible P.bmax x) (hR : x.R = 0) {q ℓ : ℕ}
    (hq : 1 ≤ gdL x.reqs (π x) q) (hℓ : ∃ r ∈ x.reqs, r.label = ℓ) (hlq : ℓ + K ≤ q) :
    1 ≤ gaL x.reqs (π x) ℓ := by
  obtain ⟨qe, hqe, hql, hqd⟩ := gdL_pos hq
  obtain ⟨r, hr, rfl⟩ := hℓ
  obtain ⟨d, hd⟩ := exists_zip_entry x.reqs (π x) (hπ x hx hR).1.length_eq r hr
  have := hK x hx hR (r, d) hd qe hqe hqd (by simp only; omega)
  have h2 := gaL_ge_entry hd
  simp only at this h2
  omega

theorem card_le_of_sum {T : Finset ℕ} {f : ℕ → ℕ} {B : ℕ} (h1 : ∀ ℓ ∈ T, 1 ≤ f ℓ)
    (h2 : ∑ ℓ ∈ T, f ℓ ≤ B) : T.card ≤ B := by
  have : T.card = ∑ ℓ ∈ T, 1 := by simp
  rw [this]
  exact le_trans (Finset.sum_le_sum h1) h2

theorem arrivalsBefore_mono' (a : ℕ → ℕ) {n n' : ℕ} (h : n ≤ n') :
    arrivalsBefore a n ≤ arrivalsBefore a n' :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem dkL_ge {L : List Req} {r : Req} (hr : r ∈ L) : r.D ≤ dkL L r.label :=
  List.le_sum_of_mem (List.mem_map_of_mem (f := fun r : Req => r.D) (List.mem_filter.2 ⟨hr, by simp⟩))

theorem tkL_ge {L : List Req} {r : Req} (hr : r ∈ L) : r.P + r.D ≤ tkL L r.label :=
  List.le_sum_of_mem (List.mem_map_of_mem (f := fun r : Req => r.P + r.D)
    (List.mem_filter.2 ⟨hr, by simp⟩))

/-! ### Runs from the empty state -/

section RunEmpty

variable (P : Params) (π : Policy) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ)

theorem empty_adm (bmax : ℕ) : Admissible bmax State.empty := by
  simp [Admissible, State.empty]

theorem run_next_empty : ∀ m, (run P π State.empty a v m).next = arrivalsBefore a m := by
  intro m
  induction m with
  | zero => simp [run, State.empty, arrivalsBefore]
  | succ m ih =>
    show (step P π (run P π State.empty a v m) (slotArrivals a v m)).next = _
    rw [step_next, ih]
    simp [slotArrivals, arrivalsBefore, Finset.sum_range_succ]

variable {P π a v}

theorem run_inv (hP : P.Valid) (hπ : IsScheduler P π) (hv : ∀ i, 1 ≤ (v i).2) :
    ∀ m ℓ, ℓ < arrivalsBefore a m →
      tkL (run P π State.empty a v m).reqs ℓ + ∑ m' ∈ Finset.range m,
        (if (run P π State.empty a v m').R = 0 then
          gaL (run P π State.empty a v m').reqs (π (run P π State.empty a v m')) ℓ else 0) =
        (v ℓ).1 + (v ℓ).2 ∧
      dkL (run P π State.empty a v m).reqs ℓ + ∑ m' ∈ Finset.range m,
        (if (run P π State.empty a v m').R = 0 then
          gdL (run P π State.empty a v m').reqs (π (run P π State.empty a v m')) ℓ else 0) =
        (v ℓ).2 := by
  have hadm := run_adm P hP π hπ State.empty (empty_adm P.bmax) a v hv
  intro m
  induction m with
  | zero => intro ℓ h; simp [arrivalsBefore] at h
  | succ m ih =>
    intro ℓ hℓ
    obtain ⟨L, hreq, hG, htk, -⟩ := step_L_good P π hπ (run P π State.empty a v m) (hadm m)
      (slotArrivals a v m)
    have e : run P π State.empty a v (m + 1) =
        step P π (run P π State.empty a v m) (slotArrivals a v m) := rfl
    have hnext := run_next_empty P π a v m
    have hE : arrivalsBefore a (m + 1) = arrivalsBefore a m + a m := by
      simp [arrivalsBefore, Finset.sum_range_succ]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, e, hreq, tkL_append, dkL_append]
    by_cases hlt : ℓ < arrivalsBefore a m
    · have hfr : ∀ r ∈ freshList (run P π State.empty a v m).next (slotArrivals a v m),
          r.label ≠ ℓ := fun r hr => by
        have := (freshList_mem _ _ r hr).1; omega
      rw [tkL_absent hfr, dkL_absent hfr]
      obtain ⟨h1, h2⟩ := htk ℓ (by omega)
      obtain ⟨i1, i2⟩ := ih ℓ hlt
      constructor <;> omega
    · push Not at hlt
      have hL : ∀ r ∈ L, r.label ≠ ℓ := fun r hr => by have := hG.2.1 r hr; omega
      rw [tkL_absent hL, dkL_absent hL]
      have hzero : ∀ m' ∈ Finset.range (m + 1),
          (run P π State.empty a v m').reqs.all (fun r => decide (r.label ≠ ℓ)) := by
        intro m' hm'
        rw [List.all_eq_true]
        intro r hr
        have h1 := (hadm m').2.1 r hr
        rw [run_next_empty] at h1
        have h2 := arrivalsBefore_mono' a (show m' ≤ m by simp at hm'; omega)
        simp only [ne_eq, decide_eq_true_eq]
        omega
      have hga : ∀ m' ∈ Finset.range (m + 1), (if (run P π State.empty a v m').R = 0 then
          gaL (run P π State.empty a v m').reqs (π (run P π State.empty a v m')) ℓ else 0) = 0 := by
        intro m' hm'
        have := hzero m' hm'
        rw [List.all_eq_true] at this
        rw [gaL_absent (fun r hr => by simpa using this r hr)]; simp
      have hgd : ∀ m' ∈ Finset.range (m + 1), (if (run P π State.empty a v m').R = 0 then
          gdL (run P π State.empty a v m').reqs (π (run P π State.empty a v m')) ℓ else 0) = 0 := by
        intro m' hm'
        have := hzero m' hm'
        rw [List.all_eq_true] at this
        rw [gdL_absent (fun r hr => by simpa using this r hr)]; simp
      rw [← Finset.sum_range_succ, ← Finset.sum_range_succ, Finset.sum_eq_zero hga,
        Finset.sum_eq_zero hgd]
      set k := ℓ - arrivalsBefore a m
      have hk : k < (slotArrivals a v m).length := by simp [slotArrivals]; omega
      have hf := freshList_tkL (run P π State.empty a v m).next (slotArrivals a v m) k hk
      rw [hnext, show arrivalsBefore a m + k = ℓ by omega] at hf
      rw [hnext, hf.1, hf.2]
      simp only [slotArrivals, List.getElem_map, List.getElem_range]
      rw [show arrivalsBefore a m + k = ℓ by omega]
      simp

theorem present_back (hP : P.Valid) (hπ : IsScheduler P π) (hv : ∀ i, 1 ≤ (v i).2) (m ℓ : ℕ)
    (h : Present (run P π State.empty a v (m + 1)) ℓ)
    (hℓ : ℓ < (run P π State.empty a v m).next) : Present (run P π State.empty a v m) ℓ := by
  have hadm := run_adm P hP π hπ State.empty (empty_adm P.bmax) a v hv
  obtain ⟨L, hreq, -, -, hlab⟩ := step_L_good P π hπ (run P π State.empty a v m) (hadm m)
    (slotArrivals a v m)
  obtain ⟨r, hr, hrl⟩ := h
  have e : run P π State.empty a v (m + 1) =
      step P π (run P π State.empty a v m) (slotArrivals a v m) := rfl
  rw [e, hreq] at hr
  rcases List.mem_append.1 hr with hr | hr
  · obtain ⟨r', hr', hl⟩ := hlab r hr
    exact ⟨r', hr', hl.trans hrl⟩
  · have := (freshList_mem _ _ r hr).1; omega

theorem present_back' (hP : P.Valid) (hπ : IsScheduler P π) (hv : ∀ i, 1 ≤ (v i).2) (m ℓ : ℕ)
    (hℓ : ℓ < (run P π State.empty a v m).next) :
    ∀ d, Present (run P π State.empty a v (m + d)) ℓ → Present (run P π State.empty a v m) ℓ := by
  intro d
  induction d with
  | zero => intro h; simpa using h
  | succ d ih =>
    intro h
    apply ih
    refine present_back hP hπ hv (m + d) ℓ h ?_
    rw [run_next_empty] at hℓ ⊢
    exact lt_of_lt_of_le hℓ (arrivalsBefore_mono' a (by omega))

end RunEmpty

end LLMThroughput.TokenBudget.Core


open LLMThroughput.TokenBudget

theorem solution (K vpmax vdmax bmax : ℕ) :
    ∃ K' : ℕ, ∀ (P : Params), P.bmax = bmax → P.Valid →
      ∀ π : Policy, IsScheduler P π → IsWorkConserving P π → IsKFCFS P K π →
      ∀ (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ),
        (∀ i, 1 ≤ (v i).1 ∧ (v i).1 ≤ vpmax ∧ 1 ≤ (v i).2 ∧ (v i).2 ≤ vdmax) →
      ∀ (n i j : ℕ), i + K' ≤ j →
        Present (run P π State.empty a v n) j →
        Departed (run P π State.empty a v (n + 1)) j →
        Departed (run P π State.empty a v n) i := by
  classical
  refine ⟨2 * K + bmax * (vpmax + vdmax) + 1, ?_⟩
  intro P hbm hP π hπ _ hK a v hv n i j hij hjn hjd
  have hv2 : ∀ i, 1 ≤ (v i).2 := fun i => (hv i).2.2.1
  have hadm := Core.run_adm P hP π hπ State.empty (Core.empty_adm P.bmax) a v hv2
  have hjlt : j < (run P π State.empty a v n).next := by
    obtain ⟨r, hr, rfl⟩ := hjn; exact (hadm n).2.1 r hr
  refine ⟨by omega, ?_⟩
  intro r hr hri
  have hip : Present (run P π State.empty a v n) i := ⟨r, hr, hri⟩
  -- Step A: `j` decodes at some scheduling instant `m ≤ n`
  obtain ⟨m, hmn, hmR, hmj⟩ : ∃ m, m ≤ n ∧ (run P π State.empty a v m).R = 0 ∧
      1 ≤ Core.gdL (run P π State.empty a v m).reqs (π (run P π State.empty a v m)) j := by
    obtain ⟨L, hreq, -, htk, -⟩ := Core.step_L_good P π hπ (run P π State.empty a v n) (hadm n)
      (slotArrivals a v n)
    have hjL : ∀ r ∈ L, r.label ≠ j := by
      intro r hr hrl
      apply hjd.2 r _ hrl
      show r ∈ (step P π (run P π State.empty a v n) (slotArrivals a v n)).reqs
      rw [hreq]; exact List.mem_append_left _ hr
    have hdk := (htk j hjlt).2
    rw [Core.dkL_absent hjL, Nat.zero_add] at hdk
    by_cases hR : (run P π State.empty a v n).R = 0
    · refine ⟨n, le_rfl, hR, ?_⟩
      rw [if_pos hR] at hdk
      obtain ⟨rj, hrj, hrjl⟩ := hjn
      have h1 := (hadm n).2.2.2.1 hR rj hrj
      have h2 := Core.dkL_ge hrj
      rw [hrjl] at h2
      omega
    · rw [if_neg hR] at hdk
      have hinv := (Core.run_inv hP hπ hv2 n j (by rwa [Core.run_next_empty] at hjlt)).2
      rw [← hdk, Nat.zero_add] at hinv
      have hne : ∑ m' ∈ Finset.range n, (if (run P π State.empty a v m').R = 0 then
          Core.gdL (run P π State.empty a v m').reqs (π (run P π State.empty a v m')) j else 0)
            ≠ 0 := by rw [hinv]; have := hv2 j; omega
      obtain ⟨m', hm', hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      refine ⟨m', by simp at hm'; omega, ?_, ?_⟩
      · by_contra hc; rw [if_neg hc] at hne'; exact hne' rfl
      · by_cases hc : (run P π State.empty a v m').R = 0
        · rw [if_pos hc] at hne'; omega
        · rw [if_neg hc] at hne'; exact absurd rfl hne'
  -- `j` and hence `i` are present at `m`
  have hjm : Present (run P π State.empty a v m) j := by
    obtain ⟨q, hq, hql, -⟩ := Core.gdL_pos hmj
    exact ⟨q.1, (List.of_mem_zip hq).1, hql⟩
  have hjmlt : j < (run P π State.empty a v m).next := by
    obtain ⟨r, hr, rfl⟩ := hjm; exact (hadm m).2.1 r hr
  -- presence of `i` at earlier times
  have hiback : ∀ m', m' ≤ n → i < (run P π State.empty a v m').next →
      Present (run P π State.empty a v m') i := by
    intro m' hm' hlt
    have := Core.present_back' hP hπ hv2 m' i hlt (n - m')
    rw [show m' + (n - m') = n by omega] at this
    exact this hip
  have him : Present (run P π State.empty a v m) i := hiback m hmn (by omega)
  -- the window of labels
  set S := Finset.Icc (i + K) (j - K)
  set Pres := S.filter (fun ℓ => Present (run P π State.empty a v m) ℓ)
  set Dep := S.filter (fun ℓ => ¬ Present (run P π State.empty a v m) ℓ)
  have hcard : Pres.card + Dep.card = S.card := Finset.card_filter_add_card_filter_not _
  have hS : S.card = j - K + 1 - (i + K) := Nat.card_Icc _ _
  -- (1) present requests in the window each get a token at `m`
  have hPres : Pres.card ≤ bmax := by
    refine Core.card_le_of_sum (f := fun ℓ => Core.gaL (run P π State.empty a v m).reqs
      (π (run P π State.empty a v m)) ℓ) ?_ ?_
    · intro ℓ hℓ
      obtain ⟨hℓS, hℓp⟩ := Finset.mem_filter.1 hℓ
      have := Finset.mem_Icc.1 hℓS
      exact Core.kfcfs_ga P K π hπ hK _ (hadm m) hmR hmj hℓp (by omega)
    · exact le_trans (Core.sum_gaL_le _ _ _) (hbm ▸ (hπ _ (hadm m) hmR).2)
  -- (2) departed requests in the window each decoded while `i` was present
  have hinvi := (Core.run_inv hP hπ hv2 m i (by rw [← Core.run_next_empty P π a v m]; omega)).1
  set G := ∑ m' ∈ Finset.range m, (if (run P π State.empty a v m').R = 0 then
    Core.gaL (run P π State.empty a v m').reqs (π (run P π State.empty a v m')) i else 0)
  have hDep : Dep.card ≤ bmax * G := by
    have h1 : ∀ ℓ ∈ Dep, 1 ≤ ∑ m' ∈ Finset.range m, (if (run P π State.empty a v m').R = 0 then
        Core.gdL (run P π State.empty a v m').reqs (π (run P π State.empty a v m')) ℓ else 0) := by
      intro ℓ hℓ
      obtain ⟨hℓS, hℓp⟩ := Finset.mem_filter.1 hℓ
      have := Finset.mem_Icc.1 hℓS
      have hinv := (Core.run_inv hP hπ hv2 m ℓ (by rw [← Core.run_next_empty P π a v m]; omega)).2
      have habs : ∀ r ∈ (run P π State.empty a v m).reqs, r.label ≠ ℓ :=
        fun r hr hrl => hℓp ⟨r, hr, hrl⟩
      rw [Core.dkL_absent habs, Nat.zero_add] at hinv
      rw [hinv]; exact hv2 ℓ
    have h2 : Dep.card ≤ ∑ ℓ ∈ Dep, ∑ m' ∈ Finset.range m,
        (if (run P π State.empty a v m').R = 0 then
          Core.gdL (run P π State.empty a v m').reqs (π (run P π State.empty a v m')) ℓ else 0) :=
      Core.card_le_of_sum h1 le_rfl
    rw [Finset.sum_comm] at h2
    refine le_trans h2 ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m' hm' => ?_
    rw [Finset.mem_range] at hm'
    by_cases hR : (run P π State.empty a v m').R = 0
    · simp only [if_pos hR]
      by_cases hall : ∀ ℓ ∈ Dep, Core.gdL (run P π State.empty a v m').reqs
          (π (run P π State.empty a v m')) ℓ = 0
      · rw [Finset.sum_eq_zero hall]; exact Nat.zero_le _
      · push Not at hall
        obtain ⟨ℓ, hℓ, hℓne⟩ := hall
        have hℓS := Finset.mem_Icc.1 (Finset.mem_filter.1 hℓ).1
        have hℓdec : 1 ≤ Core.gdL (run P π State.empty a v m').reqs
            (π (run P π State.empty a v m')) ℓ := Nat.pos_of_ne_zero hℓne
        have hℓpres : Present (run P π State.empty a v m') ℓ := by
          obtain ⟨q, hq, hql, -⟩ := Core.gdL_pos hℓdec
          exact ⟨q.1, (List.of_mem_zip hq).1, hql⟩
        have hℓlt : ℓ < (run P π State.empty a v m').next := by
          obtain ⟨r, hr, rfl⟩ := hℓpres; exact (hadm m').2.1 r hr
        have hi' := hiback m' (by omega) (by omega)
        have hga := Core.kfcfs_ga P K π hπ hK _ (hadm m') hR hℓdec hi' (by omega)
        have hsum := le_trans (Core.sum_gdL_le Dep (run P π State.empty a v m').reqs
          (π (run P π State.empty a v m'))) (hbm ▸ (hπ _ (hadm m') hR).2)
        calc _ ≤ bmax := hsum
          _ = bmax * 1 := (mul_one _).symm
          _ ≤ _ := Nat.mul_le_mul_left _ hga
    · simp [if_neg hR]
  -- (3) `i` still has tokens at `m`
  have htki : 1 ≤ Core.tkL (run P π State.empty a v m).reqs i := by
    obtain ⟨ri, hri2, hril⟩ := him
    have h1 := (hadm m).2.2.2.1 hmR ri hri2
    have h2 := Core.tkL_ge hri2
    rw [hril] at h2
    omega
  have hvi := hv i
  have hG1 : G + 1 ≤ vpmax + vdmax := by omega
  have hmul : bmax * G + bmax ≤ bmax * (vpmax + vdmax) := by
    have := Nat.mul_le_mul_left bmax hG1
    rw [Nat.mul_add, mul_one] at this; exact this
  omega
