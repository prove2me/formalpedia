-- Prove2me | solution 1 for HararySachs.Hyper.numTours_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T04:06:49.926937+00:00
-- url     : https://prove2.me/submissions/7872cfa5-96a5-4df6-b7f6-226867228d96

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators

open HararySachs.Hyper
open Classical

set_option linter.unusedSectionVars false

namespace EulerAux

/-! ## Part A: trails in an abstract finite multidigraph

Arcs form a finite type `A`; each arc has a tail `tl a` and a head `hd a` in `V`.
A *trail* is a duplicate-free list of arcs in which the head of each arc is the
tail of the next one; it is *closed* if moreover the head of the last arc is the
tail of the first one. -/

section Generic

variable {A V : Type*} [Fintype A] [DecidableEq A] [DecidableEq V] (tl hd : A → V)

/-- consecutive arcs `a, b` of a trail: the head of `a` is the tail of `b` -/
def Link (a b : A) : Prop := hd a = tl b

/-- a closed chain of arcs -/
def Closed (l : List A) : Prop :=
  l.IsChain (Link tl hd) ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, Link tl hd x y

/-- in-arcs minus out-arcs along a chain: only the endpoints contribute -/
lemma count_chain (l : List A) (hl : l.IsChain (Link tl hd)) (x : V) :
    l.countP (fun a => hd a = x) + (if l.head?.map tl = some x then 1 else 0) =
      l.countP (fun a => tl a = x) + (if l.getLast?.map hd = some x then 1 else 0) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.isChain_cons] at hl
    cases l with
    | nil =>
      simp only [List.countP_cons, List.countP_nil, List.head?_cons, Option.map_some,
        List.getLast?_singleton, Option.some.injEq]
      split_ifs <;> simp_all
    | cons b l =>
      have hab : hd a = tl b := hl.1 b (by simp)
      have ih' := ih hl.2
      simp only [List.countP_cons, List.head?_cons, Option.map_some, Option.some.injEq,
        List.getLast?_cons_cons] at ih' ⊢
      rw [hab] at ⊢
      split_ifs at ih' ⊢ <;> simp_all

/-- a closed chain enters and leaves every vertex equally often -/
lemma closed_balanced {l : List A} (hl : Closed tl hd l) (x : V) :
    l.countP (fun a => hd a = x) = l.countP (fun a => tl a = x) := by
  have h := count_chain tl hd l hl.1 x
  cases hh : l.head? with
  | none =>
    rw [List.head?_eq_none_iff] at hh
    subst hh
    simp
  | some y =>
    cases hlst : l.getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff] at hlst
      subst hlst
      simp
    | some z =>
      have hzy : hd z = tl y := hl.2 z hlst y hh
      rw [hh, hlst] at h
      simp only [Option.map_some, Option.some.injEq, hzy] at h
      omega

/-- number of arcs of a duplicate-free list satisfying `p`, as a `Finset` count -/
lemma countP_eq_card {l : List A} (hnd : l.Nodup) (p : A → Prop) [DecidablePred p] :
    l.countP (fun a => p a) = (l.toFinset.filter p).card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _)]
  congr 1
  ext a
  simp

/-- a trail inside a balanced arc set that cannot be extended is closed -/
lemma stuck_closed (U : Finset A)
    (hU : ∀ x, (U.filter (fun a => tl a = x)).card = (U.filter (fun a => hd a = x)).card)
    (l : List A) (hl : l.IsChain (Link tl hd)) (hnd : l.Nodup) (hsub : ∀ a ∈ l, a ∈ U)
    (hstuck : ∀ a ∈ U, a ∉ l → ∀ z ∈ l.getLast?, tl a ≠ hd z) : Closed tl hd l := by
  refine ⟨hl, ?_⟩
  intro z hz y hy
  by_contra hne
  have hne' : tl y ≠ hd z := fun h => hne h.symm
  have h := count_chain tl hd l hl (hd z)
  rw [hz, hy] at h
  simp only [Option.map_some, Option.some.injEq, hne', if_false, if_true, add_zero] at h
  -- more arcs of `l` end at `hd z` than start there
  rw [countP_eq_card hnd (fun a => hd a = hd z), countP_eq_card hnd (fun a => tl a = hd z)] at h
  have hle : (l.toFinset.filter (fun a => hd a = hd z)).card ≤
      (U.filter (fun a => hd a = hd z)).card := by
    apply Finset.card_le_card
    intro a ha
    simp only [Finset.mem_filter, List.mem_toFinset] at ha ⊢
    exact ⟨hsub a ha.1, ha.2⟩
  have hlt : (l.toFinset.filter (fun a => tl a = hd z)).card <
      (U.filter (fun a => tl a = hd z)).card := by
    rw [hU]
    omega
  have hsubset : U.filter (fun a => tl a = hd z) ⊆ l.toFinset.filter (fun a => tl a = hd z) := by
    intro a ha
    simp only [Finset.mem_filter, List.mem_toFinset] at ha ⊢
    by_contra hal
    exact hstuck a ha.1 (fun h => hal ⟨h, ha.2⟩) z hz ha.2
  have := Finset.card_le_card hsubset
  omega

/-- every trail inside `U` extends to a trail inside `U` that cannot be extended further -/
lemma extend (U : Finset A) : ∀ (k : ℕ) (l : List A), U.card - l.length = k →
    l.IsChain (Link tl hd) → l.Nodup → (∀ a ∈ l, a ∈ U) → l ≠ [] →
    ∃ l' : List A, l'.IsChain (Link tl hd) ∧ l'.Nodup ∧ (∀ a ∈ l', a ∈ U) ∧
      l'.head? = l.head? ∧ l' ≠ [] ∧ (∀ a ∈ U, a ∉ l' → ∀ z ∈ l'.getLast?, tl a ≠ hd z) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro l hk hl hnd hsub hne
    by_cases hst : ∀ a ∈ U, a ∉ l → ∀ z ∈ l.getLast?, tl a ≠ hd z
    · exact ⟨l, hl, hnd, hsub, rfl, hne, hst⟩
    · push Not at hst
      obtain ⟨a, haU, hal, z, hz, hza⟩ := hst
      have hnd' : (l ++ [a]).Nodup := by
        rw [List.nodup_append]
        exact ⟨hnd, List.nodup_singleton a, fun x hx y hy => by
          simp only [List.mem_singleton] at hy
          rintro rfl
          exact hal (hy ▸ hx)⟩
      have hsub' : ∀ b ∈ l ++ [a], b ∈ U := by
        intro b hb
        rw [List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact hsub b hb
        · exact haU
      have hlen : (l ++ [a]).length ≤ U.card := by
        rw [← List.toFinset_card_of_nodup hnd']
        exact Finset.card_le_card (fun b hb => hsub' b (List.mem_toFinset.mp hb))
      have hl' : (l ++ [a]).IsChain (Link tl hd) := by
        rw [List.isChain_append]
        refine ⟨hl, List.isChain_singleton a, ?_⟩
        intro x hx y hy
        rw [hz, Option.mem_def, Option.some.injEq] at hx
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hx hy
        exact hza.symm
      simp only [List.length_append, List.length_singleton] at hlen
      obtain ⟨l', h1, h2, h3, h4, h5, h6⟩ :=
        ih (U.card - (l ++ [a]).length) (by simp; omega) (l ++ [a]) rfl hl' hnd' hsub'
          (by simp)
      refine ⟨l', h1, h2, h3, ?_, h5, h6⟩
      rw [h4, List.head?_append_of_ne_nil _ hne]

/-- rotating a closed chain so that it starts with a chosen arc -/
lemma rotate_closed {C : List A} (hC : Closed tl hd C) {c : A} (hc : c ∈ C) :
    ∃ C' : List A, Closed tl hd C' ∧ C'.Perm C ∧ C'.head? = some c := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hc
  refine ⟨(c :: t) ++ s, ⟨?_, ?_⟩, List.perm_append_comm, by simp⟩
  · have hch := hC.1
    rw [List.isChain_append] at hch ⊢
    refine ⟨hch.2.1, hch.1, ?_⟩
    intro x hx y hy
    apply hC.2 x _ y _
    · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil c t)]
      exact hx
    · rw [List.head?_append_of_ne_nil _ (List.ne_nil_of_mem (List.mem_of_mem_head? hy))]
      exact hy
  · intro x hx y hy
    simp only [List.head?_append, List.head?_cons, Option.some_or, Option.mem_def,
      Option.some.injEq] at hy
    subst hy
    by_cases hs : s = []
    · subst hs
      simp only [List.append_nil] at hx
      apply hC.2 x (by simpa using hx) c (by simp)
    · rw [List.getLast?_append_of_ne_nil _ hs] at hx
      exact (List.isChain_append.mp hC.1).2.2 x hx c (by simp)

/-- splicing a closed chain through `w` with another closed chain through `w` -/
lemma splice {C D : List A} (hC : Closed tl hd C) (hD : Closed tl hd D) (w : V)
    (hCne : C ≠ []) (hCw : ∀ y ∈ C.head?, tl y = w) (hDw : ∀ y ∈ D.head?, tl y = w) :
    Closed tl hd (C ++ D) := by
  obtain ⟨y0, hy0⟩ := Option.ne_none_iff_exists'.mp (fun h => hCne (List.head?_eq_none_iff.mp h))
  refine ⟨?_, ?_⟩
  · rw [List.isChain_append]
    refine ⟨hC.1, hD.1, ?_⟩
    intro x hx y hy
    have h1 : hd x = tl y0 := hC.2 x hx y0 hy0
    unfold Link
    rw [h1, hCw y0 hy0, hDw y hy]
  · intro x hx y hy
    rw [List.head?_append_of_ne_nil _ hCne] at hy
    by_cases hDn : D = []
    · subst hDn
      simp only [List.append_nil] at hx
      exact hC.2 x hx y hy
    · rw [List.getLast?_append_of_ne_nil _ hDn] at hx
      obtain ⟨z0, hz0⟩ :=
        Option.ne_none_iff_exists'.mp (fun h => hDn (List.head?_eq_none_iff.mp h))
      have h1 : hd x = tl z0 := hD.2 x hx z0 hz0
      unfold Link
      rw [h1, hDw z0 hz0, hCw y hy]

/-- the head of every arc of a closed chain is the tail of some arc of the chain -/
lemma hd_mem_tails {C : List A} (hC : Closed tl hd C) {c : A} (hc : c ∈ C) :
    ∃ c' ∈ C, tl c' = hd c := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hc
  cases t with
  | cons b t =>
    have := (List.isChain_append.mp hC.1).2.1
    rw [List.isChain_cons_cons] at this
    exact ⟨b, by simp, this.1.symm⟩
  | nil =>
    obtain ⟨y0, hy0⟩ := Option.ne_none_iff_exists'.mp
      (fun h => (List.append_ne_nil_of_right_ne_nil s (List.cons_ne_nil c []))
        (List.head?_eq_none_iff.mp h))
    exact ⟨y0, List.mem_of_mem_head? hy0, (hC.2 c (by simp) y0 hy0).symm⟩

/-! ## Part B: Euler's theorem by the maximal closed trail argument -/

/-- two vertices joined by an arc, in either direction -/
def Adj (u v : V) : Prop := ∃ c : A, (tl c = u ∧ hd c = v) ∨ (tl c = v ∧ hd c = u)

lemma crossing {α : Type*} {r : α → α → Prop} {P : α → Prop} {x y : α}
    (h : Relation.ReflTransGen r x y) (hx : P x) (hy : ¬ P y) :
    ∃ z z', r z z' ∧ P z ∧ ¬ P z' := by
  induction h with
  | refl => exact absurd hx hy
  | tail _ hbc ih =>
    rename_i b c _
    by_cases hb : P b
    · exact ⟨b, c, hbc, hb, hy⟩
    · exact ih hb

/-- the arcs outside a closed trail are again balanced -/
lemma rest_balanced
    (hbal : ∀ x, (Finset.univ.filter (fun a => tl a = x)).card =
      (Finset.univ.filter (fun a => hd a = x)).card)
    {C : List A} (hC : Closed tl hd C) (hnd : C.Nodup) (x : V) :
    ((Finset.univ.filter (fun a => a ∉ C)).filter (fun a => tl a = x)).card =
      ((Finset.univ.filter (fun a => a ∉ C)).filter (fun a => hd a = x)).card := by
  have key : ∀ (p : A → Prop) [DecidablePred p],
      ((Finset.univ.filter (fun a => a ∉ C)).filter p).card + (C.toFinset.filter p).card =
        (Finset.univ.filter p).card := by
    intro p _
    rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter p)
      (fun a => a ∉ C)]
    congr 1
    · congr 1
      ext a
      simp [and_comm]
    · congr 1
      ext a
      simp [and_comm]
  have h1 := key (fun a => tl a = x)
  have h2 := key (fun a => hd a = x)
  have hb := closed_balanced tl hd hC x
  rw [countP_eq_card hnd (fun a => hd a = x), countP_eq_card hnd (fun a => tl a = x)] at hb
  have := hbal x
  omega

/-- a closed trail missing some arc can be strictly lengthened -/
lemma grow
    (hbal : ∀ x, (Finset.univ.filter (fun a => tl a = x)).card =
      (Finset.univ.filter (fun a => hd a = x)).card)
    (hconn : ∀ a b : A, Relation.ReflTransGen (Adj tl hd) (tl a) (tl b))
    {C : List A} (hC : Closed tl hd C) (hnd : C.Nodup) (hne : C ≠ []) {b : A} (hb : b ∉ C) :
    ∃ C' : List A, Closed tl hd C' ∧ C'.Nodup ∧ C' ≠ [] ∧ C.length < C'.length := by
  set U := Finset.univ.filter (fun a => a ∉ C) with hUdef
  have hU := rest_balanced tl hd hbal hC hnd
  obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil C hne
  -- an unused arc touching a vertex of `C`
  have htouch : ∃ a, a ∉ C ∧ ((∃ c ∈ C, tl c = tl a) ∨ (∃ c ∈ C, tl c = hd a)) := by
    by_cases hPb : ∃ c ∈ C, tl c = tl b
    · exact ⟨b, hb, Or.inl hPb⟩
    · obtain ⟨z, z', ⟨a, ha⟩, hz, hz'⟩ :=
        crossing (P := fun z => ∃ c ∈ C, tl c = z) (hconn c0 b) ⟨c0, hc0, rfl⟩ hPb
      have haC : a ∉ C := by
        intro haC
        rcases ha with ⟨_, h2⟩ | ⟨h1, _⟩
        · obtain ⟨c', hc', hc'a⟩ := hd_mem_tails tl hd hC haC
          exact hz' ⟨c', hc', hc'a.trans h2⟩
        · exact hz' ⟨a, haC, h1⟩
      rcases ha with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact ⟨a, haC, Or.inl (h1 ▸ hz)⟩
      · exact ⟨a, haC, Or.inr (h2 ▸ hz)⟩
  -- an unused arc leaving a vertex of `C`
  obtain ⟨a0, ha0C, c, hcC, hcw⟩ : ∃ a0, a0 ∉ C ∧ ∃ c ∈ C, tl c = tl a0 := by
    obtain ⟨a, haC, hP | hP⟩ := htouch
    · exact ⟨a, haC, hP⟩
    · obtain ⟨c, hcC, hca⟩ := hP
      have hpos : 0 < (U.filter (fun x => tl x = hd a)).card := by
        rw [hU]
        exact Finset.card_pos.mpr ⟨a, by simp [haC]⟩
      obtain ⟨a0, ha0⟩ := Finset.card_pos.mp hpos
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at ha0
      exact ⟨a0, ha0.1, c, hcC, hca.trans ha0.2.symm⟩
  -- a closed trail of unused arcs starting with `a0`
  obtain ⟨D, hD1, hD2, hD3, hD4, hD5, hD6⟩ :=
    extend tl hd U _ [a0] rfl (List.isChain_singleton a0) (List.nodup_singleton a0)
      (by simp [U, ha0C]) (by simp)
  have hDc : Closed tl hd D := stuck_closed tl hd U hU D hD1 hD2 hD3 hD6
  -- rotate `C` to start at `c`, then splice in `D`
  obtain ⟨C', hC'c, hperm, hhead⟩ := rotate_closed tl hd hC hcC
  have hC'ne : C' ≠ [] := by
    intro h
    rw [h] at hhead
    simp at hhead
  refine ⟨C' ++ D, splice tl hd hC'c hDc (tl a0) hC'ne ?_ ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [hhead, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact hcw
  · intro y hy
    rw [hD4] at hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    rw [hy]
  · rw [List.nodup_append]
    refine ⟨hperm.nodup_iff.mpr hnd, hD2, ?_⟩
    intro x hx y hy hxy
    subst hxy
    have := hD3 x hy
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this (hperm.mem_iff.mp hx)
  · simp [hC'ne]
  · rw [List.length_append, hperm.length_eq]
    have : D.length ≠ 0 := by simpa using hD5
    omega

/-- **Euler's theorem**: a balanced, connected arc set has a closed trail through every arc -/
lemma exists_full
    (hbal : ∀ x, (Finset.univ.filter (fun a => tl a = x)).card =
      (Finset.univ.filter (fun a => hd a = x)).card)
    (hconn : ∀ a b : A, Relation.ReflTransGen (Adj tl hd) (tl a) (tl b)) (a0 : A) :
    ∃ C : List A, Closed tl hd C ∧ C.Nodup ∧ ∀ a, a ∈ C := by
  obtain ⟨D, hD1, hD2, hD3, -, hD5, hD6⟩ :=
    extend tl hd Finset.univ _ [a0] rfl (List.isChain_singleton a0) (List.nodup_singleton a0)
      (by simp) (by simp)
  have hD : Closed tl hd D := stuck_closed tl hd Finset.univ hbal D hD1 hD2 hD3 hD6
  suffices h : ∀ k, ∀ C : List A, Fintype.card A - C.length = k → Closed tl hd C → C.Nodup →
      C ≠ [] → ∃ C' : List A, Closed tl hd C' ∧ C'.Nodup ∧ ∀ a, a ∈ C' from
    h _ D rfl hD hD2 hD5
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hk hC hnd hne
    by_cases hall : ∀ a, a ∈ C
    · exact ⟨C, hC, hnd, hall⟩
    · push Not at hall
      obtain ⟨b, hb⟩ := hall
      obtain ⟨C', h1, h2, h3, h4⟩ := grow tl hd hbal hconn hC hnd hne hb
      have := h2.length_le_card
      exact ih _ (by omega) C' rfl h1 h2 h3

/-- the closing condition in index form -/
lemma closed_getElem {C : List A} (hC : Closed tl hd C) (i : ℕ) (hi : i < C.length) :
    hd C[i] = tl (C[(i + 1) % C.length]'(Nat.mod_lt _ (by omega))) := by
  by_cases h : i + 1 < C.length
  · have := (List.isChain_iff_getElem.mp hC.1) i h
    have he : C[(i + 1) % C.length]'(Nat.mod_lt _ (by omega)) = C[i + 1] := by
      congr 1
      exact Nat.mod_eq_of_lt h
    rw [he]
    exact this
  · have hi' : i + 1 = C.length := by omega
    have he : C[(i + 1) % C.length]'(Nat.mod_lt _ (by omega)) = C[0] := by
      congr 1
      rw [hi', Nat.mod_self]
    rw [he]
    apply hC.2
    · rw [List.getLast?_eq_getElem?]
      simp [show C.length - 1 = i by omega]
    · rw [List.head?_eq_getElem?]
      simp

end Generic

/-! ## Part C: the mission's arc multiplicities -/

variable {n : ℕ}

lemma card_tl (m : ArcMult n) (x : Fin n) :
    (Finset.univ.filter (fun a : Arcs m => a.1 = x)).card = outDeg m x := by
  rw [Finset.card_filter, Fintype.sum_sigma, Finset.sum_eq_single x]
  · simp [outDeg, Fintype.card_sigma]
  · intro u _ hu
    simp [hu]
  · simp

lemma card_hd (m : ArcMult n) (x : Fin n) :
    (Finset.univ.filter (fun a : Arcs m => a.2.1 = x)).card = inDeg m x := by
  rw [Finset.card_filter, Fintype.sum_sigma]
  unfold inDeg
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Fintype.sum_sigma, Finset.sum_eq_single x]
  · simp
  · intro v _ hv
    simp [hv]
  · simp

lemma card_arcs (m : ArcMult n) :
    Fintype.card (Arcs m) = ∑ u : Fin n, ∑ v : Fin n, m u v := by
  simp [Arcs, Fintype.card_sigma]

lemma tail_active (m : ArcMult n) (c : Arcs m) : c.1 ∈ active m := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  have : 0 < outDeg m c.1 := by
    rw [← card_tl]
    exact Finset.card_pos.mpr ⟨c, by simp⟩
  omega

lemma mod_succ {a L : ℕ} (ha : a < L) : (a + 1) % L = if a + 1 < L then a + 1 else 0 := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [show a + 1 = L by omega, Nat.mod_self]

/-- a tour forces the Eulerian conditions -/
lemma eulerian_of_tour {L : ℕ} (hL : 0 < L) (m : ArcMult n) (σ : Fin L ≃ Arcs m)
    (hσ : IsTour m hL σ) : IsEulerian m := by
  let nx : Fin L → Fin L := fun t => ⟨(t.val + 1) % L, Nat.mod_lt _ hL⟩
  have hnx : Function.Bijective nx := by
    apply Finite.injective_iff_bijective.mp
    intro a b hab
    simp only [nx, Fin.mk.injEq, mod_succ a.isLt, mod_succ b.isLt] at hab
    apply Fin.ext
    split_ifs at hab <;> omega
  have hbal : ∀ x, outDeg m x = inDeg m x := by
    intro x
    rw [← card_tl, ← card_hd, Finset.card_filter, Finset.card_filter, ← σ.sum_comp,
      ← σ.sum_comp, ← hnx.sum_comp (fun t => if (σ t).1 = x then 1 else 0)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hσ t]
  have hreach : ∀ k (hk : k < L), Relation.ReflTransGen (WeakAdjacent m)
      (σ ⟨0, hL⟩).1 (σ ⟨k, hk⟩).1 := by
    intro k
    induction k with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro hk
      refine Relation.ReflTransGen.tail (ih (by omega)) ?_
      have hstep := hσ ⟨k, by omega⟩
      have hidx : (⟨(k + 1) % L, Nat.mod_lt _ hL⟩ : Fin L) = ⟨k + 1, hk⟩ := by
        apply Fin.ext
        simp [Nat.mod_eq_of_lt hk]
      simp only [hidx] at hstep
      rw [← hstep]
      left
      exact (σ ⟨k, by omega⟩).2.2.pos
  have hsym : ∀ {a b : Fin n}, WeakAdjacent m a b → WeakAdjacent m b a := fun h => h.symm
  have htail : ∀ u ∈ active m, ∃ t, (σ t).1 = u := by
    intro u hu
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have : 0 < outDeg m u := by rw [hbal u] at hu ⊢; omega
    rw [← card_tl] at this
    obtain ⟨a, ha⟩ := Finset.card_pos.mp this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact ⟨σ.symm a, by simp [ha]⟩
  refine ⟨⟨_, tail_active m (σ ⟨0, hL⟩)⟩, hbal, ?_⟩
  intro u hu v hv
  obtain ⟨t, rfl⟩ := htail u hu
  obtain ⟨s, rfl⟩ := htail v hv
  have hswap : ∀ {a b : Fin n}, Relation.ReflTransGen (WeakAdjacent m) a b →
      Relation.ReflTransGen (WeakAdjacent m) b a := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hsym hbc) ih
  exact (hswap (hreach t.val t.isLt)).trans (hreach s.val s.isLt)

/-- an Eulerian digraph has a tour (Euler's theorem) -/
lemma tour_of_eulerian {L : ℕ} (hL : 0 < L) (m : ArcMult n)
    (hm : (∑ u : Fin n, ∑ v : Fin n, m u v) = L) (hE : IsEulerian m) :
    0 < numTours m hL := by
  have hcard : Fintype.card (Arcs m) = L := by rw [card_arcs, hm]
  have hbal : ∀ x, (Finset.univ.filter (fun a : Arcs m => a.1 = x)).card =
      (Finset.univ.filter (fun a : Arcs m => a.2.1 = x)).card := by
    intro x
    rw [card_tl, card_hd]
    exact hE.2.1 x
  have hconn : ∀ a b : Arcs m, Relation.ReflTransGen
      (Adj (fun a : Arcs m => a.1) (fun a : Arcs m => a.2.1)) a.1 b.1 := by
    intro a b
    refine Relation.ReflTransGen.mono ?_ _ _
      (hE.2.2 _ (tail_active m a) _ (tail_active m b))
    intro u v huv
    rcases huv with h | h
    · exact ⟨⟨u, v, ⟨0, h⟩⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨⟨v, u, ⟨0, h⟩⟩, Or.inr ⟨rfl, rfl⟩⟩
  obtain ⟨a0⟩ : Nonempty (Arcs m) := Fintype.card_pos_iff.mp (hcard ▸ hL)
  obtain ⟨C, hC, hnd, hall⟩ := exists_full (fun a : Arcs m => a.1) (fun a => a.2.1) hbal hconn a0
  have hlen : C.length = L := by
    rw [← hcard]
    refine le_antisymm hnd.length_le_card ?_
    rw [← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card (fun a _ => List.mem_toFinset.mpr (hall a))
  subst hlen
  unfold numTours
  apply Finset.card_pos.mpr
  refine ⟨hnd.getEquivOfForallMemList C hall, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro t
  simpa [List.Nodup.getEquivOfForallMemList] using
    closed_getElem (fun a : Arcs m => a.1) (fun a => a.2.1) hC t.val t.isLt

end EulerAux

open EulerAux in
theorem solution {n L : ℕ} (hL : 0 < L) (m : ArcMult n)
    (hm : (∑ u : Fin n, ∑ v : Fin n, m u v) = L) :
    0 < numTours m hL ↔ IsEulerian m := by
  constructor
  · intro h
    unfold numTours at h
    obtain ⟨σ, hσ⟩ := Finset.card_pos.mp h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact eulerian_of_tour hL m σ hσ
  · exact tour_of_eulerian hL m hm
