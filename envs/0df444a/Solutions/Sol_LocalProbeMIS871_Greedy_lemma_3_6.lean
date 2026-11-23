-- Prove2me | solution 1 for LocalProbeMIS871.Greedy.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:37:13.690008+00:00
-- url     : https://prove2.me/submissions/c5785537-9a92-47dd-a0c1-f89992e629dd

import Definitions.Def_LocalProbeMIS871_Greedy_Elimination
import Mathlib

-- ===== Solutions.LPM.Run =====

set_option autoImplicit false

namespace LPM
open RGMISFast

section generic
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
  {α : Type*} [LinearOrder α]

/-- `w` scans (calls) `u`: a lower neighbour all of whose lower-ranked fellow neighbours are
rejected. -/
def callRel (r : V → α) (w u : V) : Prop :=
  G.Adj w u ∧ r u < r w ∧ ∀ z, G.Adj w z → r z < r u → inMIS G r z = false

theorem scanOrder_sorted (r : V → α) (hr : Function.Injective r) (s : Finset V) :
    (scanOrder r s).Pairwise (fun a b => r a < r b) := by
  classical
  rcases s with ⟨m, hm⟩
  induction m using Quot.ind with
  | mk l =>
    change (((l.map (fun a => toLex (r a, a))).insertionSort (· ≤ ·)).map
      (fun p => (ofLex p).2)).Pairwise _
    rw [List.pairwise_map]
    have hnd : (l.map (fun a => toLex (r a, a))).Nodup := by
      refine (List.nodup_map_iff_inj_on (by simpa using hm)).2 ?_
      intro a _ b _ h
      have := congrArg (fun p => (ofLex p).2) h
      simpa using this
    have hnd' := (List.perm_insertionSort (fun a b : α ×ₗ V => a ≤ b) _).nodup_iff.2 hnd
    have hp := (List.pairwise_insertionSort (fun a b : α ×ₗ V => a ≤ b) (l.map (fun a => toLex (r a, a))))
    have hp2 := hp.and hnd'
    apply hp2.imp_of_mem
    intro a b ha hb ⟨hab, hne⟩
    have ha' : (ofLex a).1 = r (ofLex a).2 := by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ((List.mem_insertionSort _).mp ha)
      rfl
    have hb' : (ofLex b).1 = r (ofLex b).2 := by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ((List.mem_insertionSort _).mp hb)
      rfl
    have hlt : a < b := lt_of_le_of_ne hab hne
    rcases Prod.Lex.lt_iff.1 hlt with h | ⟨h1, h2⟩
    · simpa only [ha', hb'] using h
    · exfalso
      rw [ha', hb'] at h1
      have := hr h1
      rw [this] at h2
      exact lt_irrefl _ h2

/-- Fresh callees recorded in a state. -/
def Fresh (st : RunState V) : List V := (st.trace.filter (fun e => e.fresh)).map (fun e => e.callee)

/-- Invariant of states. -/
def Inv (r : V → α) (st : RunState V) : Prop :=
  (∀ x b, st.memo x = some b → b = inMIS G r x) ∧
  (∀ x, (st.memo x).isSome → ∀ y, callRel G r x y → (st.memo y).isSome) ∧
  (∀ x, (st.memo x).isSome → x ∈ Fresh st)

theorem call_spec (r : V → α) (hr : Function.Injective r) (n : ℕ) :
    ∀ caller v (hn : rk r v < n) (st : RunState V), Inv G r st →
      Inv G r (callF G r n caller v hn st).2 ∧
      (callF G r n caller v hn st).1 = inMIS G r v ∧
      (∀ x, (st.memo x).isSome → ((callF G r n caller v hn st).2.memo x).isSome) ∧
      ((callF G r n caller v hn st).2.memo v).isSome ∧
      (∃ xs, (callF G r n caller v hn st).2.trace = st.trace ++ xs ∧
        ∀ e ∈ xs, Relation.ReflTransGen (callRel G r) v e.callee) := by
  classical
  induction n with
  | zero => intro caller v hn; omega
  | succ n ih =>
    intro caller v hn st hI
    simp only [callF]
    split
    next b hb =>
      refine ⟨?_, hI.1 v b hb, fun x hx => hx, by simp [hb], ⟨[⟨caller, v, false⟩], rfl, ?_⟩⟩
      · refine ⟨hI.1, hI.2.1, ?_⟩
        intro x hx
        have := hI.2.2 x hx
        simpa [Fresh, List.filter_append] using this
      · intro e he
        simp only [List.mem_singleton] at he
        subst he
        exact Relation.ReflTransGen.refl
    next hb =>
      set s1 : RunState V :=
        { st with count := st.count + 1, trace := st.trace ++ [⟨caller, v, true⟩] } with hs1
      set l := lowerNbrs G r v with hl
      have hsort : l.Pairwise (fun a b => r a < r b) := scanOrder_sorted r hr _
      -- fold invariant, over a split l = p ++ rest
      let φ := fun (acc : Bool × RunState V) (w : {w // w ∈ l}) =>
        if acc.1 then acc else callF G r n (some v) w.1
          (by have := rk_lt r ((mem_lowerNbrs G r).1 w.2).2; omega) acc.2
      let Q := fun (p : List V) (acc : Bool × RunState V) =>
        Inv G r acc.2 ∧ (∀ x, (s1.memo x).isSome → (acc.2.memo x).isSome) ∧
        (∃ xs, acc.2.trace = s1.trace ++ xs ∧
          ∀ e ∈ xs, Relation.ReflTransGen (callRel G r) v e.callee) ∧
        (acc.1 = true ↔ ∃ z ∈ p, inMIS G r z = true) ∧
        (∀ z ∈ p, (∀ y ∈ p, r y < r z → inMIS G r y = false) → (acc.2.memo z).isSome)
      have key : ∀ (rest : List {w // w ∈ l}) (p : List V) (acc : Bool × RunState V),
          p ++ rest.map Subtype.val = l → Q p acc →
          Q l (rest.foldl φ acc) := by
        intro rest
        induction rest with
        | nil => intro p acc hp hQ; simpa using (hp ▸ (by simpa using hQ) : Q l acc)
        | cons w rest ihr =>
          intro p acc hp hQ
          simp only [List.foldl_cons]
          apply ihr (p ++ [w.1]) (φ acc w) (by simpa using hp)
          obtain ⟨hIa, hmono, ⟨xs, hxs, hxsR⟩, hb1, hmem⟩ := hQ
          -- position facts
          have hp' : p ++ (w.1 :: rest.map Subtype.val) = l := by simpa using hp
          have hsort' : (p ++ (w.1 :: rest.map Subtype.val)).Pairwise (fun a b => r a < r b) := by
            rw [hp']; exact hsort
          have hw_after : ∀ y ∈ p, r y < r w.1 := by
            intro y hy
            have := hsort'
            rw [List.pairwise_append] at this
            exact this.2.2 y hy w.1 (by simp)
          by_cases hacc : acc.1 = true
          · have hφ : φ acc w = acc := by simp [φ, hacc]
            rw [hφ]
            refine ⟨hIa, hmono, ⟨xs, hxs, hxsR⟩, ?_, ?_⟩
            · rw [hb1] at hacc
              constructor
              · intro _; obtain ⟨z, hz, hz'⟩ := hacc; exact ⟨z, by simp [hz], hz'⟩
              · intro _; exact hb1.2 hacc
            · intro z hz hlow
              obtain ⟨y, hy, hy'⟩ := hb1.1 hacc
              rcases List.mem_append.1 hz with hz | hz
              · exact hmem z hz (fun y' hy' h => hlow y' (by simp [hy']) h)
              · simp only [List.mem_singleton] at hz
                subst hz
                have := hlow y (by simp [hy]) (hw_after y hy)
                rw [this] at hy'
                exact absurd hy' (by simp)
          · have hacc' : acc.1 = false := by simpa using hacc
            have hφ : φ acc w = callF G r n (some v) w.1
                (by have := rk_lt r ((mem_lowerNbrs G r).1 w.2).2; omega) acc.2 := by
              simp [φ, hacc']
            rw [hφ]
            have hnone : ∀ z ∈ p, inMIS G r z = false := by
              intro z hz
              by_contra hc
              have : acc.1 = true := hb1.2 ⟨z, hz, by simpa using hc⟩
              rw [hacc'] at this; exact absurd this (by simp)
            obtain ⟨hI', hres, hmono', hwm, ⟨ys, hys, hysR⟩⟩ :=
              ih (some v) w.1 (by have := rk_lt r ((mem_lowerNbrs G r).1 w.2).2; omega)
                acc.2 hIa
            have hcall : callRel G r v w.1 := by
              obtain ⟨hadj, hlt⟩ := (mem_lowerNbrs G r).1 w.2
              refine ⟨hadj, hlt, ?_⟩
              intro z hz hzw
              have hzl : z ∈ l := (mem_lowerNbrs G r).2 ⟨hz, hzw.trans hlt⟩
              rw [← hp'] at hzl
              rcases List.mem_append.1 hzl with hzp | hzr
              · exact hnone z hzp
              · exfalso
                rcases List.mem_cons.1 (by simpa using hzr : z ∈ w.1 :: rest.map Subtype.val)
                  with h | h
                · subst h; exact lt_irrefl _ hzw
                · have : (w.1 :: rest.map Subtype.val).Pairwise (fun a b => r a < r b) :=
                    (List.pairwise_append.1 hsort').2.1
                  exact lt_asymm hzw ((List.pairwise_cons.1 this).1 z h)
            refine ⟨hI', fun x hx => hmono' x (hmono x hx), ⟨xs ++ ys, ?_, ?_⟩, ?_, ?_⟩
            · rw [hys, hxs, List.append_assoc]
            · intro e he
              rcases List.mem_append.1 he with he | he
              · exact hxsR e he
              · exact Relation.ReflTransGen.head hcall (hysR e he)
            · rw [hres]
              constructor
              · intro h; exact ⟨w.1, by simp, h⟩
              · rintro ⟨z, hz, hz'⟩
                rcases List.mem_append.1 hz with hz | hz
                · rw [hnone z hz] at hz'; exact absurd hz' (by simp)
                · simp only [List.mem_singleton] at hz; subst hz; exact hz'
            · intro z hz _
              rcases List.mem_append.1 hz with hz | hz
              · exact hmono' z (hmem z hz (fun y hy _ => hnone y hy))
              · simp only [List.mem_singleton] at hz; subst hz; exact hwm
      have hQ0 : Q [] (false, s1) := by
        refine ⟨⟨hI.1, hI.2.1, ?_⟩, fun x hx => hx, ⟨[], by simp, by simp⟩, by simp, by simp⟩
        intro x hx
        have := hI.2.2 x hx
        simp only [Fresh, hs1, List.filter_append, List.map_append]
        exact List.mem_append_left _ this
      have hfin := key l.attach [] (false, s1) (by simp) hQ0
      obtain ⟨hIf, hmonof, ⟨xs, hxs, hxsR⟩, hbf, hmemf⟩ := hfin
      set res := l.attach.foldl φ (false, s1) with hres
      have hval : (!res.1) = inMIS G r v := by
        rw [inMIS_eq]
        cases h : res.1
        · simp only [Bool.not_false]
          symm
          rw [List.all_eq_true]
          intro w _
          have : ¬ ∃ z ∈ l, inMIS G r z = true := by
            intro hz; have := hbf.2 hz; rw [h] at this; exact absurd this (by simp)
          push Not at this
          simpa using this w.1 w.2
        · simp only [Bool.not_true]
          symm
          rw [List.all_eq_false]
          obtain ⟨z, hz, hz'⟩ := hbf.1 h
          exact ⟨⟨z, hz⟩, List.mem_attach _ _, by simp [hz']⟩
      have hchild : ∀ y, callRel G r v y → (res.2.memo y).isSome := by
        intro y hy
        obtain ⟨hadj, hlt, hlow⟩ := hy
        have hyl : y ∈ l := (mem_lowerNbrs G r).2 ⟨hadj, hlt⟩
        refine hmemf y hyl ?_
        intro z hz hzy
        exact hlow z ((mem_lowerNbrs G r).1 hz).1 hzy
      have hvF : v ∈ Fresh res.2 := by
        simp only [Fresh, hxs, hs1, List.filter_append, List.map_append]
        simp
      refine ⟨⟨?_, ?_, ?_⟩, hval, ?_, by simp, ⟨⟨caller, v, true⟩ :: xs, ?_, ?_⟩⟩
      · intro x b hx
        by_cases hxv : x = v
        · subst hxv
          simp only [Function.update_self, Option.some.injEq] at hx
          rw [← hx, hval]
        · simp [Function.update_of_ne hxv] at hx
          exact hIf.1 x b hx
      · intro x hx y hy
        by_cases hyv : y = v
        · simp [hyv]
        · simp only [Function.update_of_ne hyv]
          by_cases hxv : x = v
          · subst hxv; exact hchild y hy
          · simp only [Function.update_of_ne hxv] at hx
            exact hIf.2.1 x hx y hy
      · intro x hx
        by_cases hxv : x = v
        · subst hxv; simpa [Fresh] using hvF
        · simp only [Function.update_of_ne hxv] at hx
          simpa [Fresh] using hIf.2.2 x hx
      · intro x hx
        by_cases hxv : x = v
        · simp [hxv]
        · simp only [Function.update_of_ne hxv]
          exact hmonof x hx
      · simp [hxs, hs1]
      · intro e he
        rcases List.mem_cons.1 he with he | he
        · subst he; exact Relation.ReflTransGen.refl
        · exact hxsR e he

theorem run_fresh_iff (r : V → α) (hr : Function.Injective r) (v u : V) :
    u ∈ Fresh (run G r v).2 ↔ Relation.ReflTransGen (callRel G r) v u := by
  classical
  have hI0 : Inv G r (initState : RunState V) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro x <;> simp [initState]
  obtain ⟨hI, _, _, hvm, ⟨xs, hxs, hxsR⟩⟩ :=
    call_spec G r hr (rk r v + 1) none v (Nat.lt_succ_self _) initState hI0
  change Inv G r (run G r v).2 at hI
  change ((run G r v).2.memo v).isSome at hvm
  change (run G r v).2.trace = initState.trace ++ xs at hxs
  simp only [initState, List.nil_append] at hxs
  constructor
  · intro hu
    simp only [Fresh, List.mem_map, List.mem_filter] at hu
    obtain ⟨e, ⟨he, _⟩, rfl⟩ := hu
    rw [hxs] at he
    exact hxsR e he
  · intro hu
    apply hI.2.2
    induction hu with
    | refl => exact hvm
    | tail _ hbc ih => exact hI.2.1 _ ih _ hbc

theorem run_result (r : V → α) (hr : Function.Injective r) (v : V) :
    (run G r v).1 = inMIS G r v := by
  classical
  have hI0 : Inv G r (initState : RunState V) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro x <;> simp [initState]
  exact (call_spec G r hr (rk r v + 1) none v (Nat.lt_succ_self _) initState hI0).2.1

end generic

end LPM


-- ===== Solutions.LPM.Basic =====

set_option autoImplicit false

namespace LPM
open RGMISFast

section generic2
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
  {α : Type*} [LinearOrder α]

theorem inMIS_iff (r : V → α) (u : V) :
    inMIS G r u = true ↔ ∀ w, G.Adj u w → r w < r u → inMIS G r w = false := by
  rw [inMIS_eq, List.all_eq_true]
  constructor
  · intro h w hw hlt
    have := h ⟨w, (mem_lowerNbrs G r).2 ⟨hw, hlt⟩⟩ (List.mem_attach _ _)
    simpa using this
  · intro h w _
    have := h w.1 ((mem_lowerNbrs G r).1 w.2).1 ((mem_lowerNbrs G r).1 w.2).2
    simp [this]

/-- inMIS depends only on the order. -/
theorem inMIS_congr {β : Type*} [LinearOrder β] (r : V → α) (r' : V → β)
    (h : ∀ a b, r a < r b ↔ r' a < r' b) : inMIS G r = inMIS G r' := by
  funext u
  induction hk : rk r u using Nat.strong_induction_on generalizing u with
  | _ k ih =>
    apply Bool.eq_iff_iff.2
    rw [inMIS_iff, inMIS_iff]
    constructor
    · intro H w hw hlt
      rw [← ih (rk r w) (hk ▸ rk_lt r ((h w u).2 hlt)) w rfl]
      exact H w hw ((h w u).2 hlt)
    · intro H w hw hlt
      rw [ih (rk r w) (hk ▸ rk_lt r hlt) w rfl]
      exact H w hw ((h w u).1 hlt)

theorem callRel_congr {β : Type*} [LinearOrder β] (r : V → α) (r' : V → β)
    (h : ∀ a b, r a < r b ↔ r' a < r' b) : callRel G r = callRel G r' := by
  funext w u
  apply propext
  unfold callRel
  rw [inMIS_congr G r r' h]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, (h _ _).1 h2, fun z hz hzu => h3 z hz ((h _ _).2 hzu)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, (h _ _).2 h2, fun z hz hzu => h3 z hz ((h _ _).1 hzu)⟩

/-- The set whose minimum defines tau. -/
def tauSet (r : V → α) (u : V) : Finset V :=
  (insert u (G.neighborFinset u)).filter (fun x => inMIS G r x = true)

theorem tau_mem (r : V → α) (u : V) : ∃ z ∈ tauSet G r u, RGMISFast.tau G r u = r z := by
  have := Finset.min'_mem _ ((tauSet_nonempty G r u).image r)
  obtain ⟨z, hz, he⟩ := Finset.mem_image.1 this
  exact ⟨z, hz, he.symm⟩

theorem tau_le (r : V → α) (u z : V) (hz : z ∈ tauSet G r u) : RGMISFast.tau G r u ≤ r z :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem r hz)

theorem tau_le_self (r : V → α) (u : V) : RGMISFast.tau G r u ≤ r u := by
  obtain ⟨z, hz, he⟩ := tau_mem G r u
  by_cases hu : inMIS G r u = true
  · exact tau_le G r u u (by simp [tauSet, hu])
  · rw [he]
    simp only [tauSet, Finset.mem_filter, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hz
    rcases hz with ⟨rfl | hadj, hzm⟩
    · exact absurd hzm hu
    · rcases lt_or_ge (r z) (r u) with h | h
      · exact h.le
      · exfalso
        apply hu
        rw [inMIS_iff]
        intro w hw hlt
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        -- w is a lower accepted neighbour; then tau ≤ r w < r u ≤ r z, contradicting minimality? no:
        -- use: if u not in MIS there must be lower accepted neighbour; contradiction comes otherwise
        have hzw : RGMISFast.tau G r u ≤ r w :=
          tau_le G r u w (by
            simp only [tauSet, Finset.mem_filter, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
            exact ⟨Or.inr hw, hc⟩)
        rw [he] at hzw
        exact absurd (lt_of_le_of_lt hzw hlt) (not_lt.2 h)

theorem tau_eq_self (r : V → α) (u : V) (hu : inMIS G r u = true) :
    RGMISFast.tau G r u = r u := by
  apply le_antisymm (tau_le_self G r u)
  obtain ⟨z, hz, he⟩ := tau_mem G r u
  rw [he]
  simp only [tauSet, Finset.mem_filter, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hz
  rcases hz with ⟨rfl | hadj, hzm⟩
  · exact le_rfl
  · by_contra hlt
    push Not at hlt
    have := (inMIS_iff G r u).1 hu z hadj hlt
    rw [this] at hzm; exact absurd hzm (by simp)

theorem tau_lt_self (r : V → α) (u : V) (hu : inMIS G r u = false) :
    RGMISFast.tau G r u < r u := by
  obtain ⟨z, hz, he⟩ := tau_mem G r u
  rw [he]
  simp only [tauSet, Finset.mem_filter, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hz
  rcases hz with ⟨rfl | hadj, hzm⟩
  · rw [hu] at hzm; exact absurd hzm (by simp)
  · rcases lt_or_ge (r z) (r u) with h | h
    · exact h
    · exfalso
      have hu' : inMIS G r u = true := by
        rw [inMIS_iff]
        intro w hw hlt
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        have hzw : RGMISFast.tau G r u ≤ r w :=
          tau_le G r u w (by simp [tauSet, hc, hw])
        rw [he] at hzw
        exact absurd (lt_of_le_of_lt hzw hlt) (not_lt.2 h)
      rw [hu] at hu'; exact absurd hu' (by simp)

/-- Call relation in tau form, for injective ranks. -/
theorem callRel_iff_tau (r : V → α) (w u : V) :
    callRel G r w u ↔ G.Adj w u ∧ r u < r w ∧ r u ≤ RGMISFast.tau G r w := by
  constructor
  · rintro ⟨hadj, hlt, hlow⟩
    refine ⟨hadj, hlt, ?_⟩
    cases hw : inMIS G r w
    · obtain ⟨z, hz, he⟩ := tau_mem G r w
      rw [he]
      simp only [tauSet, Finset.mem_filter, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hz
      rcases hz with ⟨rfl | hadj', hzm⟩
      · rw [hw] at hzm; exact absurd hzm (by simp)
      · by_contra hc
        push Not at hc
        have := hlow z hadj' hc
        rw [this] at hzm; exact absurd hzm (by simp)
    · rw [tau_eq_self G r w hw]; exact hlt.le
  · rintro ⟨hadj, hlt, hle⟩
    refine ⟨hadj, hlt, ?_⟩
    intro z hz hzu
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    have : RGMISFast.tau G r w ≤ r z := tau_le G r w z (by simp [tauSet, hc, hz])
    exact absurd (lt_of_le_of_lt (hle.trans this) hzu) (lt_irrefl _)

end generic2

/-! ## Specialisation to the mission model -/

open LocalProbeMIS871.Greedy
open scoped Classical

variable {n : ℕ}

theorem key_injective (r : Fin n → ℝ) : Function.Injective (key r) := by
  intro a b h
  have := congrArg (fun p => (ofLex p).2) h
  simpa [key] using this

theorem key_lt_iff (r : Fin n → ℝ) (a b : Fin n) :
    key r a < key r b ↔ r a < r b ∨ (r a = r b ∧ a < b) := by
  simp [key, Prod.Lex.toLex_lt_toLex]

theorem key_le_fst {r : Fin n → ℝ} {a b : Fin n} (h : key r a ≤ key r b) : r a ≤ r b := by
  rw [key, key, Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

theorem key_lt_of_lt {r : Fin n → ℝ} {a b : Fin n} (h : r a < r b) : key r a < key r b :=
  (key_lt_iff r a b).2 (Or.inl h)

theorem fst_lt_of_key_lt {r : Fin n → ℝ} (hr : Function.Injective r) {a b : Fin n}
    (h : key r a < key r b) : r a < r b := by
  rcases (key_lt_iff r a b).1 h with h | ⟨h1, h2⟩
  · exact h
  · rw [hr h1] at h2; exact absurd h2 (lt_irrefl _)

theorem key_lt_iff_of_inj {r : Fin n → ℝ} (hr : Function.Injective r) (a b : Fin n) :
    key r a < key r b ↔ r a < r b := ⟨fst_lt_of_key_lt hr, key_lt_of_lt⟩

/-- The callRel of the mission (on keys). -/
abbrev Call (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) : Fin n → Fin n → Prop :=
  callRel G (key r)

theorem mem_R_iff (G : SimpleGraph (Fin n)) (v : Fin n) (r : Fin n → ℝ) (u : Fin n) :
    u ∈ R G v r ↔ Relation.ReflTransGen (Call G r) v u := by
  classical
  rw [← run_fresh_iff G (key r) (key_injective r) v u]
  simp only [R, execution, Fresh, List.mem_toFinset]

theorem mem_I_iff (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) (u : Fin n) :
    u ∈ I G r ↔ inMIS G (key r) u = true := by
  simp [I]

theorem execution_correct (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) (v : Fin n) :
    (execution G r v).1 = decide (v ∈ I G r) := by
  classical
  rw [execution, run_result G (key r) (key_injective r) v]
  by_cases h : inMIS G (key r) v = true
  · simp [I, h]
  · simp [I, h]

theorem I_indep (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) :
    ∀ u ∈ I G r, ∀ z ∈ I G r, ¬ G.Adj u z := by
  classical
  intro u hu z hz hadj
  rw [mem_I_iff] at hu hz
  rcases lt_trichotomy (key r u) (key r z) with h | h | h
  · have := (inMIS_iff G (key r) z).1 hz u hadj.symm h
    rw [hu] at this; exact absurd this (by simp)
  · rw [key_injective r h] at hadj; exact G.irrefl hadj
  · have := (inMIS_iff G (key r) u).1 hu z hadj h
    rw [hz] at this; exact absurd this (by simp)

theorem I_maximal (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) :
    ∀ u, u ∉ I G r → ∃ z ∈ I G r, G.Adj u z := by
  classical
  intro u hu
  rw [mem_I_iff] at hu
  obtain ⟨z, hz, _⟩ := tau_mem G (key r) u
  simp only [tauSet, Finset.mem_filter, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hz
  rcases hz with ⟨rfl | hadj, hzm⟩
  · exact absurd hzm hu
  · exact ⟨z, (mem_I_iff G r z).2 hzm, hadj⟩

end LPM


-- ===== Solutions.LPM.Meas =====

set_option autoImplicit false

namespace LPM
open LocalProbeMIS871.Greedy MeasureTheory
open scoped Classical

variable {n : ℕ}

noncomputable def patB (r : Fin n → ℝ) : Fin n → Fin n → Bool := fun a b => decide (r a < r b)

theorem measurable_patB : Measurable (patB (n := n)) := by
  apply measurable_pi_lambda
  intro a
  apply measurable_pi_lambda
  intro b
  apply measurable_to_countable'
  intro x
  have hs : MeasurableSet {c : Fin n → ℝ | c a < c b} :=
    measurableSet_lt (measurable_pi_apply a) (measurable_pi_apply b)
  cases x
  · convert hs.compl using 1
    ext c; simp [patB]
  · convert hs using 1
    ext c; simp [patB]

def PatInv {β : Type*} (f : (Fin n → ℝ) → β) : Prop :=
  ∀ r r', patB r = patB r' → f r = f r'

theorem measurable_of_patInv {β : Type*} [MeasurableSpace β] (f : (Fin n → ℝ) → β)
    (hf : PatInv f) : Measurable f := by
  let g : (Fin n → Fin n → Bool) → β := fun σ =>
    if h : ∃ r, patB r = σ then f h.choose else f 0
  have : f = g ∘ patB := by
    funext r
    simp only [Function.comp, g]
    have h : ∃ r', patB r' = patB r := ⟨r, rfl⟩
    rw [dif_pos h]
    exact (hf _ _ h.choose_spec).symm
  rw [this]
  exact Measurable.of_discrete.comp measurable_patB

theorem pat_key {r r' : Fin n → ℝ} (h : patB r = patB r') (a b : Fin n) :
    key r a < key r b ↔ key r' a < key r' b := by
  have h1 : ∀ x y, r x < r y ↔ r' x < r' y := by
    intro x y
    have := congrFun (congrFun h x) y
    simpa [patB] using this
  rw [key_lt_iff, key_lt_iff]
  have h2 : ∀ x y, r x = r y ↔ r' x = r' y := by
    intro x y
    constructor
    · intro e
      rcases lt_trichotomy (r' x) (r' y) with c | c | c
      · exact absurd ((h1 x y).2 c) (by rw [e]; exact lt_irrefl _)
      · exact c
      · exact absurd ((h1 y x).2 c) (by rw [e]; exact lt_irrefl _)
    · intro e
      rcases lt_trichotomy (r x) (r y) with c | c | c
      · exact absurd ((h1 x y).1 c) (by rw [e]; exact lt_irrefl _)
      · exact c
      · exact absurd ((h1 y x).1 c) (by rw [e]; exact lt_irrefl _)
  rw [h1, h2]

theorem inMIS_pat (G : SimpleGraph (Fin n)) {r r' : Fin n → ℝ} (h : patB r = patB r') :
    RGMISFast.inMIS G (key r) = RGMISFast.inMIS G (key r') :=
  inMIS_congr G _ _ (pat_key h)

theorem Call_pat (G : SimpleGraph (Fin n)) {r r' : Fin n → ℝ} (h : patB r = patB r') :
    Call G r = Call G r' :=
  callRel_congr G _ _ (pat_key h)

theorem R_pat (G : SimpleGraph (Fin n)) (v : Fin n) : PatInv (R G v) := by
  intro r r' h
  ext u
  rw [mem_R_iff, mem_R_iff, Call_pat G h]

theorem I_pat (G : SimpleGraph (Fin n)) : PatInv (I G) := by
  intro r r' h
  ext u
  rw [mem_I_iff, mem_I_iff, inMIS_pat G h]

/-- The vertex realising the elimination time. -/
noncomputable def tauV (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) (u : Fin n) : Fin n :=
  (ofLex (RGMISFast.tau G (key r) u)).2

theorem tauKey_eq (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) (u : Fin n) :
    RGMISFast.tau G (key r) u = key r (tauV G r u) := by
  obtain ⟨z, _, he⟩ := tau_mem G (key r) u
  simp [tauV, he, key]

theorem tauV_mem (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) (u : Fin n) :
    tauV G r u ∈ tauSet G (key r) u := by
  obtain ⟨z, hz, he⟩ := tau_mem G (key r) u
  have : tauV G r u = z := by simp [tauV, he, key]
  rw [this]; exact hz

theorem tau_eq (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) (u : Fin n) :
    tau G r u = r (tauV G r u) := by
  simp [tau, tauKey_eq, key]

theorem tauV_pat (G : SimpleGraph (Fin n)) (u : Fin n) : PatInv (fun r => tauV G r u) := by
  intro r r' h
  simp only
  have hS : tauSet G (key r) u = tauSet G (key r') u := by
    simp [tauSet, inMIS_pat G h]
  have m1 := tauV_mem G r u
  have m2 := tauV_mem G r' u
  rw [hS] at m1
  rw [← hS] at m2
  have l1 : key r (tauV G r u) ≤ key r (tauV G r' u) := by
    rw [← tauKey_eq]; exact tau_le G _ u _ m2
  have l2 : key r' (tauV G r' u) ≤ key r' (tauV G r u) := by
    rw [← tauKey_eq]; exact tau_le G _ u _ m1
  by_contra hne
  rcases lt_or_eq_of_le l1 with c | c
  · have := (pat_key h _ _).1 c
    exact absurd l2 (not_le.2 this)
  · exact hne (key_injective r c)

theorem measurable_tau (G : SimpleGraph (Fin n)) (u : Fin n) :
    Measurable (fun r : Fin n → ℝ => tau G r u) := by
  have hv := measurable_of_patInv _ (tauV_pat G u)
  have : (fun r : Fin n → ℝ => tau G r u) =
      fun r => ∑ z : Fin n, if tauV G r u = z then r z else 0 := by
    funext r
    rw [tau_eq, Finset.sum_ite_eq]
    simp
  rw [this]
  apply Finset.measurable_sum
  intro z _
  apply Measurable.ite _ (measurable_pi_apply z) measurable_const
  exact hv (measurableSet_singleton z)

theorem measurableSet_mem_R (G : SimpleGraph (Fin n)) (v u : Fin n) :
    MeasurableSet {r : Fin n → ℝ | u ∈ R G v r} := by
  have : Measurable (fun r : Fin n → ℝ => decide (u ∈ R G v r)) := by
    apply measurable_of_patInv
    intro r r' h
    simp [R_pat G v r r' h]
  convert this (measurableSet_singleton true) using 1
  ext r; simp

theorem measurableSet_mem_I (G : SimpleGraph (Fin n)) (u : Fin n) :
    MeasurableSet {r : Fin n → ℝ | u ∈ I G r} := by
  have : Measurable (fun r : Fin n → ℝ => decide (u ∈ I G r)) := by
    apply measurable_of_patInv
    intro r r' h
    simp [I_pat G r r' h]
  convert this (measurableSet_singleton true) using 1
  ext r; simp

/-- Sums over the evaluated set of measurable per-vertex quantities are measurable. -/
theorem measurable_sum_R (G : SimpleGraph (Fin n)) (v : Fin n) (f : Fin n → (Fin n → ℝ) → ℝ)
    (hf : ∀ u, Measurable (f u)) :
    Measurable (fun r => ∑ u ∈ R G v r, f u r) := by
  have : (fun r => ∑ u ∈ R G v r, f u r) =
      fun r => ∑ u : Fin n, if u ∈ R G v r then f u r else 0 := by
    funext r; rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [this]
  apply Finset.measurable_sum
  intro u _
  exact Measurable.ite (measurableSet_mem_R G v u) (hf u) measurable_const

theorem measurable_sum_R_erase (G : SimpleGraph (Fin n)) (v : Fin n)
    (f : Fin n → (Fin n → ℝ) → ℝ) (hf : ∀ u, Measurable (f u)) :
    Measurable (fun r => ∑ u ∈ (R G v r).erase v, f u r) := by
  have : (fun r => ∑ u ∈ (R G v r).erase v, f u r) =
      fun r => ∑ u ∈ R G v r, (if u = v then 0 else f u r) := by
    funext r
    rw [← Finset.filter_ne', Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : u = v <;> simp [h]
  rw [this]
  exact measurable_sum_R G v _ (fun u => by
    by_cases h : u = v
    · simp only [h, if_true]; exact measurable_const
    · simp only [h, if_false]; exact hf u)

theorem measurable_U (G : SimpleGraph (Fin n)) (v : Fin n) :
    Measurable (fun r => (U G v r : ℝ)) := by
  have : (fun r => (U G v r : ℝ)) = fun r => ∑ u ∈ R G v r, (fun _ _ => (1 : ℝ)) u r := by
    funext r; simp [U]
  rw [this]; exact measurable_sum_R G v _ (fun _ => measurable_const)

theorem measurable_M (G : SimpleGraph (Fin n)) (v : Fin n) (s : ℝ) :
    Measurable (M G v s) := by
  have : M G v s = fun r => ∑ u ∈ R G v r, (fun u r => tau G r u ^ s) u r := by
    funext r; simp [M]
  rw [this]
  exact measurable_sum_R G v _ (fun u => (measurable_tau G u).pow_const s)

theorem measurable_Q (G : SimpleGraph (Fin n)) (lists : AdjacencyLists G) (v : Fin n) :
    Measurable (fun r => (Q G lists v r : ℝ)) := by
  have : (fun r => (Q G lists v r : ℝ)) =
      fun r => ∑ u ∈ R G v r, (fun u (_ : Fin n → ℝ) => (1 + (G.degree u : ℝ))) u r := by
    funext r; simp [Q]
  rw [this]; exact measurable_sum_R G v _ (fun _ => measurable_const)

theorem measurable_forceRoot (v : Fin n) : Measurable (forceRoot v) := by
  unfold forceRoot
  exact measurable_update_left

end LPM


-- ===== Solutions.LPM.Prob =====

set_option autoImplicit false

namespace LPM
open LocalProbeMIS871.Greedy MeasureTheory ProbabilityTheory
open scoped Classical

instance unif_isProb : IsProbabilityMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
  ⟨by simp [Real.volume_Ioo]⟩

instance rankLaw_isProb (n : ℕ) : IsProbabilityMeasure (rankLaw n) := by
  unfold rankLaw; infer_instance

variable {n : ℕ}

theorem ae_rank_mem : ∀ᵐ r ∂rankLaw n, ∀ u, r u ∈ Set.Ioo (0 : ℝ) 1 := by
  apply Filter.eventually_all.mpr
  intro u
  rw [ae_iff]
  have : {a : Fin n → ℝ | ¬ a u ∈ Set.Ioo 0 1} = Function.eval u ⁻¹' (Set.Ioo 0 1)ᶜ := rfl
  rw [this, rankLaw]
  apply Measure.pi_eval_preimage_null
  rw [Measure.restrict_apply measurableSet_Ioo.compl]
  simp

theorem ae_rank_inj : ∀ᵐ r ∂rankLaw n, Function.Injective r := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  have hmap (v : Fin n) : (rankLaw n).map (fun r => r v) = μ :=
    (measurePreserving_eval (fun _ : Fin n => μ) v).map_eq
  have hpair (v w : Fin n) (hvw : v ≠ w) : ∀ᵐ r ∂rankLaw n, r v ≠ r w := by
    have hind := (iIndepFun_pi (μ := fun _ : Fin n => μ)
      (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hvw
    have hm := hind.map_prod_eq_prod_map_map
      (measurable_pi_apply v).aemeasurable (measurable_pi_apply w).aemeasurable
    change (rankLaw n).map (fun r => (r v, r w)) =
      ((rankLaw n).map (fun r => r v)).prod ((rankLaw n).map (fun r => r w)) at hm
    rw [hmap, hmap] at hm
    have hp : ∀ᵐ z ∂μ.prod μ, z.1 ≠ z.2 := by
      rw [ae_iff]
      simp only [not_not]
      apply Measure.measure_prod_null_of_ae_null
      · exact measurableSet_eq_fun measurable_fst measurable_snd
      · filter_upwards [] with x
        change μ {y : ℝ | x = y} = 0
        have : {y : ℝ | x = y} = {x} := by ext y; simp [eq_comm]
        rw [this]
        simp only [μ, Measure.restrict_apply (measurableSet_singleton x)]
        exact measure_mono_null Set.inter_subset_left Real.volume_singleton
    apply ae_of_ae_map (μ := rankLaw n) (p := fun z : ℝ × ℝ => z.1 ≠ z.2)
      ((measurable_pi_apply v).prodMk (measurable_pi_apply w)).aemeasurable
    rw [hm]
    exact hp
  apply Filter.eventually_all.mpr
  intro v
  apply Filter.eventually_all.mpr
  intro w
  by_cases he : v = w
  · exact Filter.Eventually.of_forall (fun _ _ => he)
  · filter_upwards [hpair v w he] with r hr heq
    exact (hr heq).elim

theorem measurableSet_goodRanks (v : Fin n) : MeasurableSet {r : Fin n → ℝ | GoodRanks v r} := by
  have h1 : MeasurableSet {r : Fin n → ℝ | r v = 1} :=
    measurableSet_eq_fun (measurable_pi_apply v) measurable_const
  have h2 : MeasurableSet {r : Fin n → ℝ | ∀ u, u ≠ v → 0 < r u ∧ r u < 1} := by
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun u => MeasurableSet.iInter (fun _ => ?_))
    exact (measurableSet_lt measurable_const (measurable_pi_apply u)).inter
      (measurableSet_lt (measurable_pi_apply u) measurable_const)
  have h3 : MeasurableSet {r : Fin n → ℝ | Function.Injective r} := by
    unfold Function.Injective
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun b => ?_))
    by_cases hab : a = b
    · simp [hab]
    · have : {r : Fin n → ℝ | r a = r b → a = b} = {r | r a = r b}ᶜ := by
        ext r; simp [hab]
      rw [this]
      exact (measurableSet_eq_fun (measurable_pi_apply a) (measurable_pi_apply b)).compl
  exact h1.inter (h2.inter h3)

theorem ae_goodRanks_pre (v : Fin n) : ∀ᵐ r ∂rankLaw n, GoodRanks v (forceRoot v r) := by
  filter_upwards [ae_rank_mem, ae_rank_inj] with r hm hi
  refine ⟨by simp [forceRoot], ?_, ?_⟩
  · intro u hu
    simpa [forceRoot, Function.update_of_ne hu] using hm u
  · intro a b hab
    by_cases ha : a = v <;> by_cases hb : b = v
    · rw [ha, hb]
    · exfalso
      rw [ha] at hab
      simp only [forceRoot, Function.update_self, Function.update_of_ne hb] at hab
      have := (hm b).2; linarith
    · exfalso
      rw [hb] at hab
      simp only [forceRoot, Function.update_self, Function.update_of_ne ha] at hab
      have := (hm a).2; linarith
    · simp only [forceRoot, Function.update_of_ne ha, Function.update_of_ne hb] at hab
      exact hi hab

theorem ae_goodRanks (v : Fin n) : ∀ᵐ r ∂forcedLaw v, GoodRanks v r := by
  rw [forcedLaw, ae_map_iff (measurable_forceRoot v).aemeasurable (measurableSet_goodRanks v)]
  exact ae_goodRanks_pre v

theorem forcedLaw_isProb (v : Fin n) : IsProbabilityMeasure (forcedLaw v) := by
  unfold forcedLaw
  exact Measure.isProbabilityMeasure_map (measurable_forceRoot v).aemeasurable

end LPM


-- ===== Solutions.LPM.Tri =====

set_option autoImplicit false

namespace LPM
open MeasureTheory
open scoped ENNReal

variable {n : ℕ}

/-- Triangular dependency structure along a list (head = integrated first). -/
def Tri (k ℓ : Fin n → (Fin n → ℝ) → ℝ≥0∞) (μ : Measure ℝ) : List (Fin n) → Prop
  | [] => True
  | x :: L =>
    (∀ y ∈ L, ∀ r t, k y (Function.update r x t) = k y r ∧ ℓ y (Function.update r x t) = ℓ y r) ∧
    (∀ r r', (∀ j, (j ∉ x :: L ∨ j = x) → r j = r' j) → ℓ x r = ℓ x r') ∧
    (∀ r, ∫⁻ t, k x (Function.update r x t) ∂μ ≤ ∫⁻ t, ℓ x (Function.update r x t) ∂μ) ∧
    Tri k ℓ μ L

theorem tri_lemma (μ : Measure ℝ) [SigmaFinite μ] (k ℓ : Fin n → (Fin n → ℝ) → ℝ≥0∞)
    (hk : ∀ y, Measurable (k y)) (hl : ∀ y, Measurable (ℓ y)) :
    ∀ (L : List (Fin n)), L.Nodup → Tri k ℓ μ L → ∀ (φ : (Fin n → ℝ) → ℝ≥0∞), Measurable φ →
      (∀ i ∈ L, ∀ r t, φ (Function.update r i t) = φ r) →
      ∀ r, lmarginal (fun _ => μ) L.toFinset (fun r => φ r * ∏ y ∈ L.toFinset, k y r) r ≤
        lmarginal (fun _ => μ) L.toFinset (fun r => φ r * ∏ y ∈ L.toFinset, ℓ y r) r := by
  intro L
  induction L with
  | nil => intro _ _ φ _ _ r; simp
  | cons x L ih =>
    intro hnd hT φ hφ hφi r
    obtain ⟨hxL, hndL⟩ := List.nodup_cons.1 hnd
    obtain ⟨hdep, hlx, hint, hTL⟩ := hT
    have hxL' : x ∉ L.toFinset := by simpa using hxL
    rw [List.toFinset_cons]
    have mk : Measurable (fun r => φ r * ∏ y ∈ insert x L.toFinset, k y r) :=
      hφ.mul (Finset.measurable_prod _ (fun y _ => hk y))
    have ml : Measurable (fun r => φ r * ∏ y ∈ insert x L.toFinset, ℓ y r) :=
      hφ.mul (Finset.measurable_prod _ (fun y _ => hl y))
    rw [lmarginal_insert' _ mk hxL', lmarginal_insert' _ ml hxL']
    -- rewrite the inner integrals
    set c : (Fin n → ℝ) → ℝ≥0∞ := fun r => ∫⁻ t, ℓ x (Function.update r x t) ∂μ with hc
    have eqk : (fun r => ∫⁻ t, (fun r => φ r * ∏ y ∈ insert x L.toFinset, k y r)
        (Function.update r x t) ∂μ) =
        fun r => φ r * (∏ y ∈ L.toFinset, k y r) * ∫⁻ t, k x (Function.update r x t) ∂μ := by
      funext r
      simp only
      have hm : Measurable (fun t => k x (Function.update r x t)) :=
        (hk x).comp (measurable_update r)
      rw [← lintegral_const_mul _ hm]
      congr 1; funext t
      rw [Finset.prod_insert hxL', hφi x (by simp) r t]
      rw [Finset.prod_congr rfl (fun y hy => (hdep y (by simpa using hy) r t).1)]
      ring
    have eql : (fun r => ∫⁻ t, (fun r => φ r * ∏ y ∈ insert x L.toFinset, ℓ y r)
        (Function.update r x t) ∂μ) =
        fun r => φ r * (∏ y ∈ L.toFinset, ℓ y r) * c r := by
      funext r
      simp only [hc]
      have hm : Measurable (fun t => ℓ x (Function.update r x t)) :=
        (hl x).comp (measurable_update r)
      rw [← lintegral_const_mul _ hm]
      congr 1; funext t
      rw [Finset.prod_insert hxL', hφi x (by simp) r t]
      rw [Finset.prod_congr rfl (fun y hy => (hdep y (by simpa using hy) r t).2)]
      ring
    rw [eqk, eql]
    have hcm : Measurable c := by
      have : Measurable (fun p : (Fin n → ℝ) × ℝ => ℓ x (Function.update p.1 x p.2)) :=
        (hl x).comp measurable_update'
      exact this.lintegral_prod_right'
    have hci : ∀ i ∈ L, ∀ r t, c (Function.update r i t) = c r := by
      intro i hi r t
      simp only [hc]
      congr 1; funext t'
      apply hlx
      intro j hj
      have hix : i ≠ x := by rintro rfl; exact hxL hi
      by_cases hji : j = i
      · subst hji
        rcases hj with hj | hj
        · exact absurd (List.mem_cons_of_mem _ hi) hj
        · exact absurd hj hix
      · by_cases hjx : j = x
        · subst hjx; simp
        · simp [Function.update_of_ne hji, Function.update_of_ne hjx]
    calc lmarginal (fun _ => μ) L.toFinset
          (fun r => φ r * (∏ y ∈ L.toFinset, k y r) * ∫⁻ t, k x (Function.update r x t) ∂μ) r
        ≤ lmarginal (fun _ => μ) L.toFinset (fun r => (φ r * c r) * ∏ y ∈ L.toFinset, k y r) r := by
          apply lmarginal_mono
          intro r'
          simp only
          rw [mul_right_comm]
          gcongr
          exact hint r'
      _ ≤ lmarginal (fun _ => μ) L.toFinset (fun r => (φ r * c r) * ∏ y ∈ L.toFinset, ℓ y r) r := by
          apply ih hndL hTL (fun r => φ r * c r) (hφ.mul hcm)
          intro i hi r' t
          rw [hφi i (List.mem_cons_of_mem _ hi) r' t, hci i hi r' t]
      _ = lmarginal (fun _ => μ) L.toFinset (fun r => φ r * (∏ y ∈ L.toFinset, ℓ y r) * c r) r := by
          congr 1; funext r'; ring

end LPM


-- ===== Solutions.LPM.L36a =====

set_option autoImplicit false

namespace LPM
namespace L36
open LocalProbeMIS871.Greedy MeasureTheory
open scoped Classical

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)

/-- keys of the forced-root rank vector -/
noncomputable def κ (r : Fin n → ℝ) : Fin n → ℝ ×ₗ Fin n := key (forceRoot v r)

noncomputable def NJ (J : Finset (Fin n)) (u : Fin n) : Finset (Fin n) :=
  (insert u (G.neighborFinset u)).filter (· ∈ J)

/-- realising vertex of the J-elimination time -/
noncomputable def Tv (J : Finset (Fin n)) (r : Fin n → ℝ) (u : Fin n) : Fin n :=
  if h : (NJ G J u).Nonempty then (ofLex (((NJ G J u).image (κ v r)).min' (h.image _))).2 else v

noncomputable def T (J : Finset (Fin n)) (r : Fin n → ℝ) (u : Fin n) : ℝ ×ₗ Fin n :=
  κ v r (Tv G v J r u)

def E (J : Finset (Fin n)) (r : Fin n → ℝ) (θ : ℝ ×ₗ Fin n) (w u : Fin n) : Prop :=
  θ < T G v J r w ∧ θ < T G v J r u ∧ G.Adj w u ∧ κ v r u < κ v r w ∧ κ v r u ≤ T G v J r w

def InP (J : Finset (Fin n)) (r : Fin n → ℝ) (θ : ℝ ×ₗ Fin n) (u : Fin n) : Prop :=
  θ < T G v J r v ∧ Relation.ReflTransGen (E G v J r θ) v u

noncomputable def S (J : Finset (Fin n)) (r : Fin n → ℝ) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => InP G v J r (T G v J r x) u ∧ G.Adj u x)

def InR (J : Finset (Fin n)) (r : Fin n → ℝ) (x : Fin n) : Prop :=
  ∃ u ∈ S G v J r x, κ v r x ≤ T G v J r u

/-- real time of a key -/
def tm (p : ℝ ×ₗ Fin n) : ℝ := (ofLex p).1

noncomputable def piX (J : Finset (Fin n)) (r : Fin n → ℝ) (x : Fin n) : ℝ :=
  (∑ u ∈ S G v J r x, max (tm (T G v J r u) - tm (T G v J r x)) 0) / (1 - tm (T G v J r x))

def B (J : Finset (Fin n)) : Finset (Fin n) := Finset.univ \ insert v J

def Static (J : Finset (Fin n)) (r : Fin n → ℝ) : Prop :=
  (∀ u ∈ J, ∀ z ∈ J, ¬ G.Adj u z) ∧
  (v ∉ J → ∃ z ∈ J, G.Adj v z ∧ κ v r z < κ v r v) ∧
  (∀ x ∈ B v J, (NJ G J x).Nonempty) ∧
  (∀ z ∈ J, z ≠ v → r z ∈ Set.Ioo (0 : ℝ) 1)

/-! ### basic facts about keys -/

theorem κ_eq_ne (r : Fin n → ℝ) (u : Fin n) (h : u ≠ v) : κ v r u = toLex (r u, u) := by
  simp [κ, key, forceRoot, Function.update_of_ne h]

theorem κ_v (r : Fin n → ℝ) : κ v r v = toLex ((1 : ℝ), v) := by
  simp [κ, key, forceRoot]

theorem κ_snd (r : Fin n → ℝ) (u : Fin n) : (ofLex (κ v r u)).2 = u := by
  simp [κ, key]

theorem κ_inj (r : Fin n → ℝ) : Function.Injective (κ v r) := key_injective _

theorem tm_κ (r : Fin n → ℝ) (u : Fin n) : tm (κ v r u) = forceRoot v r u := by
  simp [tm, κ, key]

theorem T_min (J : Finset (Fin n)) (r : Fin n → ℝ) (u : Fin n) (h : (NJ G J u).Nonempty) :
    T G v J r u = ((NJ G J u).image (κ v r)).min' (h.image _) := by
  unfold T Tv
  rw [dif_pos h]
  obtain ⟨z, _, hz⟩ := Finset.mem_image.1 (Finset.min'_mem _ (h.image (κ v r)))
  rw [← hz, κ_snd]

theorem Tv_mem (J : Finset (Fin n)) (r : Fin n → ℝ) (u : Fin n) (h : (NJ G J u).Nonempty) :
    Tv G v J r u ∈ NJ G J u := by
  have := Finset.min'_mem _ (h.image (κ v r))
  obtain ⟨z, hz, hz'⟩ := Finset.mem_image.1 this
  unfold Tv; rw [dif_pos h, ← hz', κ_snd]; exact hz

theorem T_le (J : Finset (Fin n)) (r : Fin n → ℝ) (u z : Fin n) (hz : z ∈ NJ G J u) :
    T G v J r u ≤ κ v r z := by
  rw [T_min G v J r u ⟨z, hz⟩]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hz)

/-! ### pattern invariance and measurability -/

theorem κ_pat {r r' : Fin n → ℝ} (h : patB (forceRoot v r) = patB (forceRoot v r'))
    (a b : Fin n) : κ v r a < κ v r b ↔ κ v r' a < κ v r' b := pat_key h a b

theorem κ_pat_le {r r' : Fin n → ℝ} (h : patB (forceRoot v r) = patB (forceRoot v r'))
    (a b : Fin n) : κ v r a ≤ κ v r b ↔ κ v r' a ≤ κ v r' b := by
  rw [← not_lt, ← not_lt, κ_pat v h]

theorem Tv_pat (J : Finset (Fin n)) {r r' : Fin n → ℝ}
    (h : patB (forceRoot v r) = patB (forceRoot v r')) (u : Fin n) :
    Tv G v J r u = Tv G v J r' u := by
  by_cases hne : (NJ G J u).Nonempty
  · have m1 := Tv_mem G v J r u hne
    have m2 := Tv_mem G v J r' u hne
    have l1 : κ v r (Tv G v J r u) ≤ κ v r (Tv G v J r' u) := by
      have := T_le G v J r u _ m2; rwa [T] at this
    have l2 : κ v r' (Tv G v J r' u) ≤ κ v r' (Tv G v J r u) := by
      have := T_le G v J r' u _ m1; rwa [T] at this
    rw [← κ_pat_le v h] at l2
    exact κ_inj v r (le_antisymm l1 l2)
  · simp [Tv, hne]

theorem T_pat_lt (J : Finset (Fin n)) {r r' : Fin n → ℝ}
    (h : patB (forceRoot v r) = patB (forceRoot v r')) (a b : Fin n) :
    T G v J r a < T G v J r b ↔ T G v J r' a < T G v J r' b := by
  simp only [T, Tv_pat G v J h]; exact κ_pat v h _ _

theorem T_pat_le (J : Finset (Fin n)) {r r' : Fin n → ℝ}
    (h : patB (forceRoot v r) = patB (forceRoot v r')) (a b : Fin n) :
    T G v J r a ≤ T G v J r b ↔ T G v J r' a ≤ T G v J r' b := by
  simp only [T, Tv_pat G v J h]; exact κ_pat_le v h _ _

theorem κT_pat_le (J : Finset (Fin n)) {r r' : Fin n → ℝ}
    (h : patB (forceRoot v r) = patB (forceRoot v r')) (a b : Fin n) :
    κ v r a ≤ T G v J r b ↔ κ v r' a ≤ T G v J r' b := by
  simp only [T, Tv_pat G v J h]; exact κ_pat_le v h _ _

theorem κT_pat_lt (J : Finset (Fin n)) {r r' : Fin n → ℝ}
    (h : patB (forceRoot v r) = patB (forceRoot v r')) (a b : Fin n) :
    T G v J r b < κ v r a ↔ T G v J r' b < κ v r' a := by
  simp only [T, Tv_pat G v J h]; exact κ_pat v h _ _

theorem E_pat (J : Finset (Fin n)) {r r' : Fin n → ℝ}
    (h : patB (forceRoot v r) = patB (forceRoot v r')) (x : Fin n) :
    E G v J r (T G v J r x) = E G v J r' (T G v J r' x) := by
  funext w u
  simp only [E, T_pat_lt G v J h, κ_pat v h, κT_pat_le G v J h]

theorem InP_pat (J : Finset (Fin n)) {r r' : Fin n → ℝ}
    (h : patB (forceRoot v r) = patB (forceRoot v r')) (x u : Fin n) :
    InP G v J r (T G v J r x) u ↔ InP G v J r' (T G v J r' x) u := by
  simp only [InP, E_pat G v J h, T_pat_lt G v J h]

theorem S_pat (J : Finset (Fin n)) {r r' : Fin n → ℝ}
    (h : patB (forceRoot v r) = patB (forceRoot v r')) (x : Fin n) :
    S G v J r x = S G v J r' x := by
  ext u; simp [S, InP_pat G v J h]

theorem InR_pat (J : Finset (Fin n)) {r r' : Fin n → ℝ}
    (h : patB (forceRoot v r) = patB (forceRoot v r')) (x : Fin n) :
    InR G v J r x ↔ InR G v J r' x := by
  simp only [InR, S_pat G v J h, κT_pat_le G v J h]

/-- measurability of a pattern-invariant function of the forced vector -/
theorem measurable_of_fpat {β : Type*} [MeasurableSpace β] (f : (Fin n → ℝ) → β)
    (hf : ∀ r r', patB (forceRoot v r) = patB (forceRoot v r') → f r = f r') : Measurable f := by
  let g : (Fin n → Fin n → Bool) → β := fun σ =>
    if h : ∃ r, patB (forceRoot v r) = σ then f h.choose else f 0
  have : f = g ∘ patB ∘ forceRoot v := by
    funext r
    simp only [Function.comp, g]
    have h : ∃ r', patB (forceRoot v r') = patB (forceRoot v r) := ⟨r, rfl⟩
    rw [dif_pos h]
    exact (hf _ _ h.choose_spec).symm
  rw [this]
  exact ((Measurable.of_discrete (f := g)).comp measurable_patB).comp (measurable_forceRoot v)

theorem measurableSet_of_fpat (p : (Fin n → ℝ) → Prop)
    (hp : ∀ r r', patB (forceRoot v r) = patB (forceRoot v r') → (p r ↔ p r')) :
    MeasurableSet {r | p r} := by
  have : Measurable (fun r => decide (p r)) := by
    apply measurable_of_fpat (β := Bool) v
    intro r r' h; simp [hp r r' h]
  convert this (measurableSet_singleton true) using 1
  ext r; simp

theorem measurable_tmT (J : Finset (Fin n)) (u : Fin n) :
    Measurable (fun r => tm (T G v J r u)) := by
  have hv : Measurable (fun r => Tv G v J r u) :=
    measurable_of_fpat (β := Fin n) v _ (fun r r' h => Tv_pat G v J h u)
  have : (fun r => tm (T G v J r u)) =
      fun r => ∑ z : Fin n, if Tv G v J r u = z then forceRoot v r z else 0 := by
    funext r
    rw [Finset.sum_ite_eq]
    simp [T, tm_κ]
  rw [this]
  apply Finset.measurable_sum
  intro z _
  exact Measurable.ite (hv (measurableSet_singleton z))
    ((measurable_pi_apply z).comp (measurable_forceRoot v)) measurable_const

theorem measurable_piX (J : Finset (Fin n)) (x : Fin n) :
    Measurable (fun r => piX G v J r x) := by
  unfold piX
  apply Measurable.div _ (measurable_const.sub (measurable_tmT G v J x))
  have : (fun r => ∑ u ∈ S G v J r x, max (tm (T G v J r u) - tm (T G v J r x)) 0) =
      fun r => ∑ u : Fin n, if u ∈ S G v J r x then
        max (tm (T G v J r u) - tm (T G v J r x)) 0 else 0 := by
    funext r; rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [this]
  apply Finset.measurable_sum
  intro u _
  apply Measurable.ite _ (((measurable_tmT G v J u).sub (measurable_tmT G v J x)).max
    measurable_const) measurable_const
  exact measurableSet_of_fpat v (fun r => u ∈ S G v J r x)
    (fun r r' h => by rw [S_pat G v J h])

end L36
end LPM


-- ===== Solutions.LPM.L36b =====

set_option autoImplicit false

namespace LPM
namespace L36
open LocalProbeMIS871.Greedy MeasureTheory
open scoped Classical

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)

theorem inMIS_iff_J (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J)
    (x : Fin n) : RGMISFast.inMIS G (κ v r) x = true ↔ x ∈ J := by
  rw [← hJ, mem_I_iff]; rfl

theorem tauSet_eq (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J)
    (u : Fin n) : tauSet G (κ v r) u = NJ G J u := by
  ext x; simp [tauSet, NJ, inMIS_iff_J G v J r hJ]

theorem T_eq_tau (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J)
    (u : Fin n) : T G v J r u = RGMISFast.tau G (κ v r) u := by
  have hne : (NJ G J u).Nonempty := by
    rw [← tauSet_eq G v J r hJ]; exact RGMISFast.tauSet_nonempty G _ u
  rw [T_min G v J r u hne]
  unfold RGMISFast.tau
  congr 1
  · rw [← tauSet_eq G v J r hJ]; rfl

theorem T_le_κ (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J) (u : Fin n) :
    T G v J r u ≤ κ v r u := by
  rw [T_eq_tau G v J r hJ]; exact tau_le_self G _ u

theorem Call_iff (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J)
    (w u : Fin n) :
    Call G (forceRoot v r) w u ↔ G.Adj w u ∧ κ v r u < κ v r w ∧ κ v r u ≤ T G v J r w := by
  rw [T_eq_tau G v J r hJ]
  exact callRel_iff_tau G (key (forceRoot v r)) w u

theorem reach_InP (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J)
    (θ : ℝ ×ₗ Fin n) (u : Fin n) (hu : Relation.ReflTransGen (Call G (forceRoot v r)) v u)
    (hθ : θ < T G v J r u) : InP G v J r θ u := by
  induction hu with
  | refl => exact ⟨hθ, Relation.ReflTransGen.refl⟩
  | @tail w u' _ hwu ih =>
    obtain ⟨hadj, hlt, hle⟩ := (Call_iff G v J r hJ w u').1 hwu
    have hw : θ < T G v J r w := lt_of_lt_of_le (lt_of_lt_of_le hθ (T_le_κ G v J r hJ u')) hle
    obtain ⟨h1, h2⟩ := ih hw
    exact ⟨h1, h2.tail ⟨hw, hθ, hadj, hlt, hle⟩⟩

theorem InP_reach (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J)
    (θ : ℝ ×ₗ Fin n) (u : Fin n) (hu : InP G v J r θ u) :
    Relation.ReflTransGen (Call G (forceRoot v r)) v u ∧ θ < T G v J r u := by
  obtain ⟨h0, hp⟩ := hu
  induction hp with
  | refl => exact ⟨Relation.ReflTransGen.refl, h0⟩
  | @tail w u' _ hwu ih =>
    obtain ⟨_, h2, hadj, hlt, hle⟩ := hwu
    exact ⟨ih.1.tail ((Call_iff G v J r hJ w u').2 ⟨hadj, hlt, hle⟩), h2⟩

theorem mem_B (J : Finset (Fin n)) (x : Fin n) : x ∈ B v J ↔ x ≠ v ∧ x ∉ J := by
  simp [B, not_or]

theorem T_lt_κ_of_B (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J)
    (x : Fin n) (hx : x ∈ B v J) : T G v J r x < κ v r x := by
  rw [T_eq_tau G v J r hJ]
  apply tau_lt_self
  have : x ∉ J := ((mem_B v J x).1 hx).2
  rw [← inMIS_iff_J G v J r hJ] at this
  simpa using this

theorem mem_R_iff_InR (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J)
    (x : Fin n) (hx : x ∈ B v J) : x ∈ R G v (forceRoot v r) ↔ InR G v J r x := by
  rw [mem_R_iff]
  have hxv : x ≠ v := ((mem_B v J x).1 hx).1
  constructor
  · intro h
    obtain ⟨u, hu, hux⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h |>.resolve_left
      (fun e => hxv e)
    obtain ⟨hadj, hlt, hle⟩ := (Call_iff G v J r hJ u x).1 hux
    have hθ : T G v J r x < T G v J r u := lt_of_lt_of_le (T_lt_κ_of_B G v J r hJ x hx) hle
    refine ⟨u, ?_, hle⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨reach_InP G v J r hJ _ u hu hθ, hadj⟩
  · rintro ⟨u, hu, hle⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨hP, hadj⟩ := hu
    obtain ⟨hreach, hθ⟩ := InP_reach G v J r hJ _ u hP
    apply hreach.tail
    rw [Call_iff G v J r hJ]
    refine ⟨hadj, ?_, hle⟩
    have hxu : x ≠ u := by rintro rfl; exact lt_irrefl _ hθ
    exact lt_of_le_of_ne (hle.trans (T_le_κ G v J r hJ u)) (fun e => hxu (κ_inj v r e))

/-- the static conditions hold on the event, for good ranks -/
theorem static_of_eq (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J)
    (hg : GoodRanks v (forceRoot v r)) : Static G v J r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hJ]; exact I_indep G _
  · intro hv
    rw [← hJ] at hv
    obtain ⟨z, hz, hadj⟩ := I_maximal G _ v hv
    refine ⟨z, hJ ▸ hz, hadj, ?_⟩
    rw [mem_I_iff] at hz hv
    simp only [Bool.not_eq_true] at hv
    -- an accepted neighbour of a rejected vertex... use the min
    rcases lt_or_gt_of_ne (fun e => (G.ne_of_adj hadj) (κ_inj v r e).symm) with h | h
    · exact h
    · exfalso
      have := (inMIS_iff G _ z).1 hz v hadj.symm h
      -- v rejected; but z accepted and lower than ... contradiction derived differently
      have hzv : z ≠ v := (G.ne_of_adj hadj).symm
      have hr := hg.2.1 z hzv
      rw [κ_v, κ_eq_ne v r z hzv] at h
      rw [Prod.Lex.toLex_lt_toLex] at h
      simp only [forceRoot, Function.update_of_ne hzv] at hr
      rcases h with h | ⟨h, _⟩ <;> linarith [hr.2]
  · intro x hx
    rw [← tauSet_eq G v J r hJ]; exact RGMISFast.tauSet_nonempty G _ x
  · intro z _ hzv
    have := hg.2.1 z hzv
    simpa [forceRoot, Function.update_of_ne hzv] using this

/-- converse characterisation of the accepted set -/
theorem eq_of_static (J : Finset (Fin n)) (r : Fin n → ℝ) (hs : Static G v J r)
    (hB : ∀ x ∈ B v J, T G v J r x < κ v r x) : I G (forceRoot v r) = J := by
  obtain ⟨hind, hvJ, hne, _⟩ := hs
  -- every non-member has a lower-key neighbour in J
  have hlow : ∀ x, x ∉ J → ∃ z ∈ J, G.Adj x z ∧ κ v r z < κ v r x := by
    intro x hx
    by_cases hxv : x = v
    · subst hxv; exact hvJ hx
    · have hxB : x ∈ B v J := (mem_B v J x).2 ⟨hxv, hx⟩
      have hm := Tv_mem G v J r x (hne x hxB)
      simp only [NJ, Finset.mem_filter, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hm
      obtain ⟨h1, h2⟩ := hm
      rcases h1 with h1 | h1
      · rw [h1] at h2; exact absurd h2 hx
      · exact ⟨_, h2, h1, hB x hxB⟩
  have key : ∀ x, RGMISFast.inMIS G (κ v r) x = true ↔ x ∈ J := by
    intro x
    induction hk : RGMISFast.rk (κ v r) x using Nat.strong_induction_on generalizing x with
    | _ k ih =>
      rw [inMIS_iff]
      constructor
      · intro H
        by_contra hx
        obtain ⟨z, hz, hadj, hlt⟩ := hlow x hx
        have h1 := H z hadj hlt
        have h2 := (ih _ (hk ▸ RGMISFast.rk_lt _ hlt) z rfl).2 hz
        rw [h1] at h2; exact absurd h2 (by simp)
      · intro hx w hw hlt
        have : w ∉ J := fun hwJ => hind x hx w hwJ hw
        rw [← ih _ (hk ▸ RGMISFast.rk_lt _ hlt) w rfl] at this
        simpa using this
  ext x
  rw [mem_I_iff]
  exact key x

end L36
end LPM


-- ===== Solutions.LPM.L36c =====

set_option autoImplicit false

namespace LPM
namespace L36
open LocalProbeMIS871.Greedy MeasureTheory
open scoped Classical

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)

theorem tau_pos_good (r : Fin n → ℝ) (hr : GoodRanks v r) (u : Fin n) : 0 < tau G r u := by
  rw [tau_eq]
  by_cases h : tauV G r u = v
  · rw [h, hr.1]; norm_num
  · exact (hr.2.1 _ h).1

theorem tau_le_one_good (r : Fin n → ℝ) (hr : GoodRanks v r) (u : Fin n) : tau G r u ≤ 1 := by
  rw [tau_eq]
  by_cases h : tauV G r u = v
  · rw [h, hr.1]
  · exact (hr.2.1 _ h).2.le

theorem tm_mono {p q : ℝ ×ₗ Fin n} (h : p ≤ q) : tm p ≤ tm q := by
  unfold tm
  rcases (Prod.Lex.le_iff).1 h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

theorem tau_eq_tm (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J)
    (u : Fin n) : tau G (forceRoot v r) u = tm (T G v J r u) := by
  rw [T_eq_tau G v J r hJ]; rfl

theorem card_bound (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J) :
    (U G v (forceRoot v r) : ℝ) ≤ 2 + 2 * ((B v J).filter (fun x => InR G v J r x)).card := by
  set Rr := R G v (forceRoot v r) with hRr
  set RB := Rr.filter (· ∈ B v J) with hRB
  set RJ := Rr.filter (fun a => a ∈ J ∧ a ≠ v) with hRJ
  have hcardB : RB.card = ((B v J).filter (fun x => InR G v J r x)).card := by
    congr 1
    ext x
    simp only [hRB, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, (mem_R_iff_InR G v J r hJ x h2).1 h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨(mem_R_iff_InR G v J r hJ x h1).2 h2, h1⟩
  have hsub : Rr ⊆ insert v (RB ∪ RJ) := by
    intro x hx
    by_cases hxv : x = v
    · simp [hxv]
    · apply Finset.mem_insert_of_mem
      by_cases hxJ : x ∈ J
      · exact Finset.mem_union_right _ (by simp [hRJ, hx, hxJ, hxv])
      · exact Finset.mem_union_left _ (by simp [hRB, hx, (mem_B v J x).2 ⟨hxv, hxJ⟩])
  -- injection from RJ into insert v RB
  have hcall : ∀ a ∈ RJ, ∃ c, Relation.ReflTransGen (Call G (forceRoot v r)) v c ∧
      Call G (forceRoot v r) c a := by
    intro a ha
    simp only [hRJ, Finset.mem_filter] at ha
    have := (mem_R_iff G v _ a).1 ha.1
    exact ((Relation.ReflTransGen.cases_tail_iff _ _ _).1 this).resolve_left
      (fun e => ha.2.2 e)
  choose! c hc1 hc2 using hcall
  have hJ' : ∀ a, a ∈ J ↔ a ∈ I G (forceRoot v r) := by intro a; rw [hJ]
  have hmaps : ∀ a ∈ RJ, c a ∈ insert v RB := by
    intro a ha
    have h1 := hc1 a ha
    have h2 := hc2 a ha
    simp only [hRJ, Finset.mem_filter] at ha
    by_cases hcv : c a = v
    · simp [hcv]
    · apply Finset.mem_insert_of_mem
      simp only [hRB, Finset.mem_filter, hRr, mem_R_iff]
      refine ⟨h1, (mem_B v J _).2 ⟨hcv, ?_⟩⟩
      intro hcJ
      have := I_indep G (forceRoot v r) (c a) ((hJ' _).1 hcJ) a ((hJ' _).1 ha.2.1) h2.1
      exact this
  have hinj : Set.InjOn c RJ := by
    intro a ha a' ha' he
    have h2 := hc2 a ha
    have h2' := hc2 a' ha'
    simp only [hRJ, Finset.coe_filter, Set.mem_ofPred_eq] at ha ha'
    have ma : RGMISFast.inMIS G (key (forceRoot v r)) a = true := (mem_I_iff G _ a).1 ((hJ' _).1 ha.2.1)
    have ma' : RGMISFast.inMIS G (key (forceRoot v r)) a' = true :=
      (mem_I_iff G _ a').1 ((hJ' _).1 ha'.2.1)
    rw [he] at h2
    by_contra hne
    rcases lt_or_gt_of_ne (fun e => hne (key_injective _ e)) with h | h
    · have := h2'.2.2 a h2.1 h
      rw [ma] at this; exact absurd this (by simp)
    · have := h2.2.2 a' h2'.1 h
      rw [ma'] at this; exact absurd this (by simp)
  have hRJcard : RJ.card ≤ RB.card + 1 := by
    calc RJ.card ≤ (insert v RB).card := Finset.card_le_card_of_injOn c hmaps hinj
      _ ≤ RB.card + 1 := Finset.card_insert_le _ _
  have : Rr.card ≤ RB.card + RJ.card + 1 := by
    calc Rr.card ≤ (insert v (RB ∪ RJ)).card := Finset.card_le_card hsub
      _ ≤ (RB ∪ RJ).card + 1 := Finset.card_insert_le _ _
      _ ≤ RB.card + RJ.card + 1 := by gcongr; exact Finset.card_union_le _ _
  have hU : U G v (forceRoot v r) = Rr.card := rfl
  rw [hU, ← hcardB]
  have : (Rr.card : ℝ) ≤ RB.card + RJ.card + 1 := by exact_mod_cast this
  have : (RJ.card : ℝ) ≤ RB.card + 1 := by exact_mod_cast hRJcard
  linarith

theorem piX_nonneg (J : Finset (Fin n)) (r : Fin n → ℝ) (x : Fin n)
    (h1 : tm (T G v J r x) ≤ 1) : 0 ≤ piX G v J r x := by
  unfold piX
  apply div_nonneg (Finset.sum_nonneg (fun _ _ => le_max_right _ _)) (by linarith)

theorem piX_le (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J)
    (hg : GoodRanks v (forceRoot v r)) (x : Fin n) (hx : x ∈ B v J) :
    piX G v J r x ≤ ∑ u ∈ (R G v (forceRoot v r)).filter (fun u => G.Adj u x),
      tau G (forceRoot v r) u := by
  have hτx0 : 0 < tm (T G v J r x) := by
    rw [← tau_eq_tm G v J r hJ]; exact tau_pos_good G v _ hg x
  have hτx1 : tm (T G v J r x) < 1 := by
    have h := T_lt_κ_of_B G v J r hJ x hx
    have hxv : x ≠ v := ((mem_B v J x).1 hx).1
    have : tm (T G v J r x) ≤ tm (κ v r x) := tm_mono h.le
    rw [tm_κ] at this
    have := (hg.2.1 x hxv).2
    linarith
  unfold piX
  rw [Finset.sum_div]
  calc ∑ u ∈ S G v J r x, max (tm (T G v J r u) - tm (T G v J r x)) 0 / (1 - tm (T G v J r x))
      ≤ ∑ u ∈ S G v J r x, tau G (forceRoot v r) u := by
        apply Finset.sum_le_sum
        intro u _
        rw [tau_eq_tm G v J r hJ]
        have ha0 : 0 < tm (T G v J r u) := by
          rw [← tau_eq_tm G v J r hJ]; exact tau_pos_good G v _ hg u
        have ha1 : tm (T G v J r u) ≤ 1 := by
          rw [← tau_eq_tm G v J r hJ]; exact tau_le_one_good G v _ hg u
        rw [div_le_iff₀ (by linarith)]
        rcases le_total (tm (T G v J r u) - tm (T G v J r x)) 0 with h | h
        · rw [max_eq_right h]; nlinarith
        · rw [max_eq_left h]; nlinarith
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro u hu
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          simp only [Finset.mem_filter, mem_R_iff]
          exact ⟨(InP_reach G v J r hJ _ u hu.1).1, hu.2⟩
        · intro u _ _; exact (tau_pos_good G v _ hg u).le

theorem sum_piX_le (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J)
    (hg : GoodRanks v (forceRoot v r)) (Δ : ℕ) (hdeg : ∀ u, G.degree u ≤ Δ) :
    ∑ x ∈ B v J, piX G v J r x ≤ Δ * M G v 1 (forceRoot v r) := by
  set Rr := R G v (forceRoot v r)
  set τ := fun u => tau G (forceRoot v r) u
  calc ∑ x ∈ B v J, piX G v J r x
      ≤ ∑ x ∈ B v J, ∑ u ∈ Rr.filter (fun u => G.Adj u x), τ u :=
        Finset.sum_le_sum (fun x hx => piX_le G v J r hJ hg x hx)
    _ = ∑ x ∈ B v J, ∑ u ∈ Rr, (if G.Adj u x then τ u else 0) := by
        apply Finset.sum_congr rfl; intro x _; rw [Finset.sum_filter]
    _ ≤ ∑ x : Fin n, ∑ u ∈ Rr, (if G.Adj u x then τ u else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro x _ _
        exact Finset.sum_nonneg (fun u _ => by
          split_ifs
          · exact (tau_pos_good G v _ hg u).le
          · exact le_rfl)
    _ = ∑ u ∈ Rr, τ u * (G.degree u : ℝ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro u _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
        congr 2
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        congr 1; ext x; simp
    _ ≤ ∑ u ∈ Rr, τ u * Δ := by
        apply Finset.sum_le_sum; intro u _
        apply mul_le_mul_of_nonneg_left (by exact_mod_cast hdeg u) (tau_pos_good G v _ hg u).le
    _ = Δ * M G v 1 (forceRoot v r) := by
        rw [M, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro u _
        rw [Real.rpow_one]; ring

theorem pointwise (J : Finset (Fin n)) (r : Fin n → ℝ) (hJ : I G (forceRoot v r) = J)
    (hg : GoodRanks v (forceRoot v r)) (Δ : ℕ) (hdeg : ∀ u, G.degree u ≤ Δ) :
    ((U G v (forceRoot v r) : ℝ) - 2) / 2 - 2 * Δ * M G v 1 (forceRoot v r) ≤
      ∑ x ∈ B v J, ((if InR G v J r x then (1 : ℝ) else 0) - (Real.exp 1 - 1) * piX G v J r x) := by
  have h1 := card_bound G v J r hJ
  have h2 := sum_piX_le G v J r hJ hg Δ hdeg
  have hpos : 0 ≤ ∑ x ∈ B v J, piX G v J r x := by
    apply Finset.sum_nonneg; intro x hx
    apply piX_nonneg
    rw [← tau_eq_tm G v J r hJ]; exact tau_le_one_good G v _ hg x
  have he : Real.exp 1 - 1 ≤ 2 := by have := Real.exp_one_lt_d9; linarith
  have he0 : 0 ≤ Real.exp 1 - 1 := by have := Real.add_one_le_exp 1; linarith
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  have : (Real.exp 1 - 1) * ∑ x ∈ B v J, piX G v J r x ≤ 2 * ∑ x ∈ B v J, piX G v J r x :=
    mul_le_mul_of_nonneg_right he hpos
  have hcard : (((B v J).filter (fun x => InR G v J r x)).card : ℝ) =
      (((B v J).filter (fun x => InR G v J r x)).card : ℝ) := rfl
  linarith

end L36
end LPM


-- ===== Solutions.LPM.L36d =====

set_option autoImplicit false

namespace LPM
namespace L36
open LocalProbeMIS871.Greedy MeasureTheory
open scoped Classical ENNReal

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)

theorem κ_update_ne (r : Fin n → ℝ) (x : Fin n) (t : ℝ) (u : Fin n) (h : u ≠ x) :
    κ v (Function.update r x t) u = κ v r u := by
  by_cases hu : u = v
  · subst hu; rw [κ_v, κ_v]
  · rw [κ_eq_ne v _ u hu, κ_eq_ne v _ u hu, Function.update_of_ne h]

theorem κ_update_self (r : Fin n → ℝ) (x : Fin n) (t : ℝ) (hx : x ≠ v) :
    κ v (Function.update r x t) x = toLex (t, x) := by
  rw [κ_eq_ne v _ x hx, Function.update_self]

theorem NJ_sub (J : Finset (Fin n)) (u z : Fin n) (hz : z ∈ NJ G J u) : z ∈ J := by
  simp only [NJ, Finset.mem_filter] at hz; exact hz.2

theorem Tv_mem_or (J : Finset (Fin n)) (r : Fin n → ℝ) (u : Fin n) :
    Tv G v J r u ∈ J ∨ Tv G v J r u = v := by
  by_cases h : (NJ G J u).Nonempty
  · exact Or.inl (NJ_sub G J u _ (Tv_mem G v J r u h))
  · right; simp [Tv, h]

/-- `Tv` only depends on the coordinates in `J`. -/
theorem Tv_congr (J : Finset (Fin n)) (r r' : Fin n → ℝ)
    (hκ : ∀ z ∈ J, κ v r z = κ v r' z) (u : Fin n) : Tv G v J r u = Tv G v J r' u := by
  by_cases hne : (NJ G J u).Nonempty
  · have m1 := Tv_mem G v J r u hne
    have m2 := Tv_mem G v J r' u hne
    have l1 : κ v r (Tv G v J r u) ≤ κ v r (Tv G v J r' u) := by
      have := T_le G v J r u _ m2; rwa [T] at this
    have l2 : κ v r' (Tv G v J r' u) ≤ κ v r' (Tv G v J r u) := by
      have := T_le G v J r' u _ m1; rwa [T] at this
    rw [← hκ _ (NJ_sub G J u _ m1), ← hκ _ (NJ_sub G J u _ m2)] at l2
    exact κ_inj v r (le_antisymm l1 l2)
  · simp [Tv, hne]

theorem T_congr (J : Finset (Fin n)) (r r' : Fin n → ℝ)
    (hκ : ∀ z ∈ J, κ v r z = κ v r' z) (u : Fin n) : T G v J r u = T G v J r' u := by
  unfold T
  rw [Tv_congr G v J r r' hκ u]
  rcases Tv_mem_or G v J r' u with h | h
  · exact hκ _ h
  · rw [h, κ_v, κ_v]

theorem T_update (J : Finset (Fin n)) (r : Fin n → ℝ) (x : Fin n) (t : ℝ) (hx : x ∉ J)
    (u : Fin n) : T G v J (Function.update r x t) u = T G v J r u :=
  T_congr G v J _ _ (fun z hz => κ_update_ne v r x t z (fun e => hx (e ▸ hz))) u

theorem E_update (J : Finset (Fin n)) (r : Fin n → ℝ) (x : Fin n) (t : ℝ) (hx : x ∉ J)
    (θ : ℝ ×ₗ Fin n) (hθ : ¬ θ < T G v J r x) :
    E G v J (Function.update r x t) θ = E G v J r θ := by
  funext w u
  apply propext
  simp only [E, T_update G v J r x t hx]
  by_cases hw : w = x
  · subst hw; simp [hθ]
  · by_cases hu : u = x
    · subst hu; simp [hθ]
    · rw [κ_update_ne v r x t u hu, κ_update_ne v r x t w hw]

theorem S_update (J : Finset (Fin n)) (r : Fin n → ℝ) (x : Fin n) (t : ℝ) (hx : x ∉ J)
    (y : Fin n) (hy : T G v J r x ≤ T G v J r y) :
    S G v J (Function.update r x t) y = S G v J r y := by
  have hP : ∀ u, InP G v J (Function.update r x t) (T G v J (Function.update r x t) y) u ↔
      InP G v J r (T G v J r y) u := by
    intro u
    unfold InP
    rw [T_update G v J r x t hx y, T_update G v J r x t hx v,
      E_update G v J r x t hx _ (not_lt.2 hy)]
  ext u
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hP]

theorem piX_update (J : Finset (Fin n)) (r : Fin n → ℝ) (x : Fin n) (t : ℝ) (hx : x ∉ J)
    (y : Fin n) (hy : T G v J r x ≤ T G v J r y) :
    piX G v J (Function.update r x t) y = piX G v J r y := by
  simp only [piX, S_update G v J r x t hx y hy, T_update G v J r x t hx]

theorem InR_update (J : Finset (Fin n)) (r : Fin n → ℝ) (x : Fin n) (t : ℝ) (hx : x ∉ J)
    (y : Fin n) (hy : T G v J r x ≤ T G v J r y) :
    InR G v J (Function.update r x t) y ↔ ∃ u ∈ S G v J r y,
      κ v (Function.update r x t) y ≤ T G v J r u := by
  simp only [InR, S_update G v J r x t hx y hy, T_update G v J r x t hx]

theorem Static_update (J : Finset (Fin n)) (r : Fin n → ℝ) (x : Fin n) (t : ℝ)
    (hx : x ∈ B v J) : Static G v J (Function.update r x t) ↔ Static G v J r := by
  obtain ⟨hxv, hxJ⟩ := (mem_B v J x).1 hx
  have hz : ∀ z ∈ J, z ≠ x := fun z hz e => hxJ (e ▸ hz)
  unfold Static
  simp only [κ_update_ne v r x t v (Ne.symm hxv)]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, h3, ?_⟩
    · intro hv; obtain ⟨z, hzJ, ha, hl⟩ := h2 hv
      exact ⟨z, hzJ, ha, by rwa [κ_update_ne v r x t z (hz z hzJ)] at hl⟩
    · intro z hzJ hzv
      have := h4 z hzJ hzv; rwa [Function.update_of_ne (hz z hzJ)] at this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, h3, ?_⟩
    · intro hv; obtain ⟨z, hzJ, ha, hl⟩ := h2 hv
      exact ⟨z, hzJ, ha, by rwa [κ_update_ne v r x t z (hz z hzJ)]⟩
    · intro z hzJ hzv
      rw [Function.update_of_ne (hz z hzJ)]; exact h4 z hzJ hzv

/-! ### the elimination order -/

noncomputable def ok (J : Finset (Fin n)) (r : Fin n → ℝ) (a : Fin n) :
    (ℝ ×ₗ Fin n)ᵒᵈ ×ₗ Fin n := toLex (OrderDual.toDual (T G v J r a), a)

noncomputable def ordL (J : Finset (Fin n)) (r : Fin n → ℝ) : List (Fin n) :=
  (B v J).toList.insertionSort (fun a b => ok G v J r a ≤ ok G v J r b)

theorem ordL_perm (J : Finset (Fin n)) (r : Fin n → ℝ) : (ordL G v J r).Perm (B v J).toList :=
  List.perm_insertionSort _ _

theorem ordL_sorted (J : Finset (Fin n)) (r : Fin n → ℝ) :
    (ordL G v J r).Pairwise (fun a b => ok G v J r a ≤ ok G v J r b) := by
  have : Std.Total (fun a b => ok G v J r a ≤ ok G v J r b) := ⟨fun a b => le_total _ _⟩
  have : IsTrans (Fin n) (fun a b => ok G v J r a ≤ ok G v J r b) := ⟨fun a b c => le_trans⟩
  exact List.pairwise_insertionSort _ _

theorem T_le_of_ok (J : Finset (Fin n)) (r : Fin n → ℝ) (a b : Fin n)
    (h : ok G v J r a ≤ ok G v J r b) : T G v J r b ≤ T G v J r a := by
  unfold ok at h
  rcases (Prod.Lex.le_iff).1 h with h | ⟨h, _⟩
  · exact le_of_lt (by simpa using h)
  · exact le_of_eq (by simpa using h.symm)

theorem ordL_update (J : Finset (Fin n)) (r : Fin n → ℝ) (x : Fin n) (t : ℝ) (hx : x ∉ J) :
    ordL G v J (Function.update r x t) = ordL G v J r := by
  have : ok G v J (Function.update r x t) = ok G v J r := by
    funext a; simp [ok, T_update G v J r x t hx]
  unfold ordL; rw [this]

theorem ordL_pat (J : Finset (Fin n)) {r r' : Fin n → ℝ}
    (h : patB (forceRoot v r) = patB (forceRoot v r')) : ordL G v J r = ordL G v J r' := by
  have hrel : (fun a b => ok G v J r a ≤ ok G v J r b) =
      (fun a b => ok G v J r' a ≤ ok G v J r' b) := by
    funext a b
    apply propext
    have heq : ∀ a b, T G v J r a = T G v J r b ↔ T G v J r' a = T G v J r' b := by
      intro a b
      simp only [T, Tv_pat G v J h]
      constructor
      · intro e; rw [κ_inj v r e]
      · intro e; rw [κ_inj v r' e]
    simp only [ok, Prod.Lex.toLex_le_toLex, OrderDual.toDual_lt_toDual, EmbeddingLike.apply_eq_iff_eq]
    rw [T_pat_lt G v J h, heq]
  unfold ordL
  congr 1

/-! ### the integrands -/

noncomputable def cJ (J : Finset (Fin n)) (σ : List (Fin n)) (r : Fin n → ℝ) : ℝ≥0∞ :=
  if Static G v J r ∧ ordL G v J r = σ then 1 else 0

noncomputable def kJ (J : Finset (Fin n)) (σ : List (Fin n)) (x : Fin n) (r : Fin n → ℝ) : ℝ≥0∞ :=
  if Static G v J r ∧ ordL G v J r = σ ∧ T G v J r x < κ v r x then
    ENNReal.ofReal (Real.exp ((if InR G v J r x then (1 : ℝ) else 0) -
      (Real.exp 1 - 1) * piX G v J r x))
  else 0

noncomputable def lJ (J : Finset (Fin n)) (x : Fin n) (r : Fin n → ℝ) : ℝ≥0∞ :=
  if T G v J r x < κ v r x then 1 else 0

theorem measurableSet_Static (J : Finset (Fin n)) : MeasurableSet {r | Static G v J r} := by
  have e : {r | Static G v J r} =
      {r | (∀ u ∈ J, ∀ z ∈ J, ¬ G.Adj u z) ∧ (∀ x ∈ B v J, (NJ G J x).Nonempty)} ∩
      ({r | v ∉ J → ∃ z ∈ J, G.Adj v z ∧ κ v r z < κ v r v} ∩
       ⋂ z ∈ J, {r : Fin n → ℝ | z ≠ v → r z ∈ Set.Ioo (0 : ℝ) 1}) := by
    ext r; simp only [Static, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]; tauto
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.const _) (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_of_fpat v _ (fun r r' h => by simp only [κ_pat v h])
  · refine MeasurableSet.biInter (Set.to_countable _) (fun z _ => ?_)
    by_cases hz : z = v
    · simp [hz]
    · simp only [hz, ne_eq, not_false_eq_true, forall_const]
      exact (measurable_pi_apply z) measurableSet_Ioo

theorem measurableSet_ord (J : Finset (Fin n)) (σ : List (Fin n)) :
    MeasurableSet {r | ordL G v J r = σ} :=
  measurableSet_of_fpat v _ (fun r r' h => by rw [ordL_pat G v J h])

theorem measurable_cJ (J : Finset (Fin n)) (σ : List (Fin n)) : Measurable (cJ G v J σ) :=
  Measurable.ite ((measurableSet_Static G v J).inter (measurableSet_ord G v J σ))
    measurable_const measurable_const

theorem measurable_kJ (J : Finset (Fin n)) (σ : List (Fin n)) (x : Fin n) :
    Measurable (kJ G v J σ x) := by
  apply Measurable.ite
  · refine (measurableSet_Static G v J).inter ((measurableSet_ord G v J σ).inter ?_)
    exact measurableSet_of_fpat v _ (fun r r' h => κT_pat_lt G v J h x x)
  · apply ENNReal.measurable_ofReal.comp
    apply Real.measurable_exp.comp
    apply Measurable.sub
    · apply Measurable.ite _ measurable_const measurable_const
      exact measurableSet_of_fpat v _ (fun r r' h => InR_pat G v J h x)
    · exact (measurable_piX G v J x).const_mul _
  · exact measurable_const

theorem measurable_lJ (J : Finset (Fin n)) (x : Fin n) : Measurable (lJ G v J x) :=
  Measurable.ite (measurableSet_of_fpat v _ (fun r r' h => κT_pat_lt G v J h x x))
    measurable_const measurable_const

end L36
end LPM


-- ===== Solutions.LPM.L36e =====

set_option autoImplicit false

namespace LPM
namespace L36
open LocalProbeMIS871.Greedy MeasureTheory
open scoped Classical ENNReal

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)

theorem lex_lt_iff' (a b : ℝ) (z x : Fin n) :
    toLex (a, z) < toLex (b, x) ↔ a < b ∨ (a = b ∧ z < x) := Prod.Lex.toLex_lt_toLex

theorem measurableSet_lexgt (p : ℝ ×ₗ Fin n) (x : Fin n) :
    MeasurableSet {t : ℝ | p < toLex (t, x)} := by
  obtain ⟨⟨a, z⟩, rfl⟩ : ∃ q : ℝ × Fin n, toLex q = p := ⟨ofLex p, rfl⟩
  by_cases hzx : z < x
  · have : {t : ℝ | toLex (a, z) < toLex (t, x)} = Set.Ici a := by
      ext t; simp only [Set.mem_ofPred_eq, Set.mem_Ici, lex_lt_iff']
      constructor
      · rintro (h | ⟨h, _⟩) <;> linarith
      · intro h; rcases lt_or_eq_of_le h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, hzx⟩
    rw [this]; exact measurableSet_Ici
  · have : {t : ℝ | toLex (a, z) < toLex (t, x)} = Set.Ioi a := by
      ext t; simp only [Set.mem_ofPred_eq, Set.mem_Ioi, lex_lt_iff']
      constructor
      · rintro (h | ⟨_, h⟩)
        · exact h
        · exact absurd h hzx
      · intro h; exact Or.inl h
    rw [this]; exact measurableSet_Ioi

theorem tm_T_le_one (J : Finset (Fin n)) (r : Fin n → ℝ) (hs : Static G v J r) (x : Fin n) :
    tm (T G v J r x) ≤ 1 := by
  unfold T
  rw [tm_κ]
  rcases Tv_mem_or G v J r x with h | h
  · by_cases hzv : Tv G v J r x = v
    · rw [hzv]; simp [forceRoot]
    · rw [forceRoot, Function.update_of_ne hzv]; exact (hs.2.2.2 _ h hzv).2.le
  · rw [h]; simp [forceRoot]

theorem tm_T_pos (J : Finset (Fin n)) (r : Fin n → ℝ) (hs : Static G v J r) (x : Fin n) :
    0 < tm (T G v J r x) := by
  unfold T
  rw [tm_κ]
  rcases Tv_mem_or G v J r x with h | h
  · by_cases hzv : Tv G v J r x = v
    · rw [hzv]; simp [forceRoot]
    · rw [forceRoot, Function.update_of_ne hzv]; exact (hs.2.2.2 _ h hzv).1
  · rw [h]; simp [forceRoot]

theorem coord_bound (J : Finset (Fin n)) (σ : List (Fin n)) (x : Fin n) (hx : x ∈ B v J)
    (r : Fin n → ℝ) :
    ∫⁻ t, kJ G v J σ x (Function.update r x t) ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) ≤
      ∫⁻ t, lJ G v J x (Function.update r x t) ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  obtain ⟨hxv, hxJ⟩ := (mem_B v J x).1 hx
  set μ := volume.restrict (Set.Ioo (0 : ℝ) 1) with hμ
  set Tx := T G v J r x with hTx
  set τ := tm Tx with hτ
  set A : Set ℝ := {t : ℝ | Tx < toLex (t, x)} with hA
  have hAm : MeasurableSet A := measurableSet_lexgt Tx x
  have hl : ∀ t, lJ G v J x (Function.update r x t) = A.indicator 1 t := by
    intro t
    simp only [lJ, T_update G v J r x t hxJ, κ_update_self v r x t hxv, Set.indicator, hA,
      Set.mem_ofPred_eq, Pi.one_apply, ← hTx]
  rw [lintegral_congr (fun t => hl t), lintegral_indicator_one hAm]
  by_cases hC : Static G v J r ∧ ordL G v J r = σ
  swap
  · have : ∀ t, kJ G v J σ x (Function.update r x t) = 0 := by
      intro t
      simp only [kJ, Static_update G v J r x t hx, ordL_update G v J r x t hxJ]
      rw [if_neg]; tauto
    simp [this]
  obtain ⟨hs, hord⟩ := hC
  set π := piX G v J r x with hπ
  set c := Real.exp 1 - 1 with hc
  have hc0 : 0 ≤ c := by have := Real.add_one_le_exp 1; linarith
  have hτ1 : τ ≤ 1 := tm_T_le_one G v J r hs x
  have hτ0 : 0 < τ := tm_T_pos G v J r hs x
  have hπ0 : 0 ≤ π := piX_nonneg G v J r x hτ1
  set K : Set ℝ := ⋃ u ∈ S G v J r x, Set.Icc τ (tm (T G v J r u)) with hK
  have hKm : MeasurableSet K := Finset.measurableSet_biUnion _ (fun _ _ => measurableSet_Icc)
  have hpt : ∀ t, kJ G v J σ x (Function.update r x t) ≤
      ENNReal.ofReal (Real.exp (-(c * π))) *
        (A.indicator 1 t + ENNReal.ofReal c * (A ∩ K).indicator 1 t) := by
    intro t
    simp only [kJ, Static_update G v J r x t hx, ordL_update G v J r x t hxJ,
      T_update G v J r x t hxJ, κ_update_self v r x t hxv, piX_update G v J r x t hxJ x le_rfl]
    rw [InR_update G v J r x t hxJ x le_rfl, κ_update_self v r x t hxv]
    simp only [hs, hord, true_and, ← hTx, ← hπ, ← hc]
    by_cases htA : Tx < toLex (t, x)
    · have htA' : t ∈ A := htA
      rw [if_pos htA, Set.indicator_of_mem htA']
      by_cases hB : ∃ u ∈ S G v J r x, toLex (t, x) ≤ T G v J r u
      · rw [if_pos hB]
        have htK : t ∈ A ∩ K := by
          refine ⟨htA', ?_⟩
          obtain ⟨u, hu, htu⟩ := hB
          simp only [hK, Set.mem_iUnion, Set.mem_Icc]
          refine ⟨u, hu, ?_, ?_⟩
          · have := tm_mono htA.le; rw [hτ]; simpa [tm] using this
          · have := tm_mono htu; simpa [tm] using this
        rw [Set.indicator_of_mem htK]
        simp only [Pi.one_apply, mul_one]
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) hc0,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        apply ENNReal.ofReal_le_ofReal
        rw [show (1 : ℝ) - c * π = 1 + -(c * π) by ring, Real.exp_add]
        simp only [hc]; nlinarith [Real.exp_pos (-((Real.exp 1 - 1) * π))]
      · rw [if_neg hB]
        simp only [Pi.one_apply, zero_sub]
        calc ENNReal.ofReal (Real.exp (-(c * π))) = ENNReal.ofReal (Real.exp (-(c * π))) * 1 := by
              rw [mul_one]
          _ ≤ _ := by gcongr; exact le_add_right le_rfl
    · rw [if_neg htA]; exact zero_le
  have hA_K : μ (A ∩ K) ≤ ENNReal.ofReal π * μ A := by
    rcases lt_or_eq_of_le hτ1 with hlt | heq
    · have hμA : ENNReal.ofReal (1 - τ) ≤ μ A := by
        rw [hμ, Measure.restrict_apply hAm]
        rw [← Real.volume_Ioo]
        apply measure_mono
        intro t ht
        refine ⟨?_, ⟨by linarith [ht.1], ht.2⟩⟩
        show Tx < toLex (t, x)
        obtain ⟨⟨a, z⟩, ha⟩ : ∃ q : ℝ × Fin n, toLex q = Tx := ⟨ofLex Tx, rfl⟩
        rw [← ha, lex_lt_iff']
        left
        have : τ = a := by rw [hτ, ← ha]; rfl
        rw [← this]; exact ht.1
      calc μ (A ∩ K) ≤ volume K := by
            rw [hμ, Measure.restrict_apply (hAm.inter hKm)]
            exact measure_mono (fun t ht => ht.1.2)
        _ ≤ ∑ u ∈ S G v J r x, volume (Set.Icc τ (tm (T G v J r u))) :=
            measure_biUnion_finset_le _ _
        _ = ∑ u ∈ S G v J r x, ENNReal.ofReal (max (tm (T G v J r u) - τ) 0) := by
            apply Finset.sum_congr rfl; intro u _
            rw [Real.volume_Icc]
            rcases le_total (tm (T G v J r u) - τ) 0 with h | h
            · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
            · rw [max_eq_left h]
        _ = ENNReal.ofReal (∑ u ∈ S G v J r x, max (tm (T G v J r u) - τ) 0) := by
            rw [ENNReal.ofReal_sum_of_nonneg]; intro u _; exact le_max_right _ _
        _ = ENNReal.ofReal π * ENNReal.ofReal (1 - τ) := by
            rw [← ENNReal.ofReal_mul hπ0]
            congr 1
            rw [hπ, piX, ← hTx, ← hτ]
            field_simp [show (1 - τ) ≠ 0 by linarith]
        _ ≤ ENNReal.ofReal π * μ A := by gcongr
    · have : μ A = 0 := by
        rw [hμ, Measure.restrict_apply hAm]
        apply measure_mono_null _ measure_empty
        intro t ⟨htA, ht⟩
        exfalso
        obtain ⟨⟨a, z⟩, ha⟩ : ∃ q : ℝ × Fin n, toLex q = Tx := ⟨ofLex Tx, rfl⟩
        have hta : Tx < toLex (t, x) := htA
        rw [← ha, lex_lt_iff'] at hta
        have : τ = a := by rw [hτ, ← ha]; rfl
        rw [heq] at this
        rcases hta with h | ⟨h, _⟩ <;> linarith [ht.2]
      have h0 : μ (A ∩ K) = 0 := measure_mono_null Set.inter_subset_left this
      rw [h0]; exact zero_le
  calc ∫⁻ t, kJ G v J σ x (Function.update r x t) ∂μ
      ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (-(c * π))) *
          (A.indicator 1 t + ENNReal.ofReal c * (A ∩ K).indicator 1 t) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (-(c * π))) * (μ A + ENNReal.ofReal c * μ (A ∩ K)) := by
        have hm1 : Measurable (A.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hAm
        have hm2 : Measurable ((A ∩ K).indicator (1 : ℝ → ℝ≥0∞)) :=
          measurable_one.indicator (hAm.inter hKm)
        have hm : Measurable (fun t => A.indicator (1 : ℝ → ℝ≥0∞) t +
            ENNReal.ofReal c * (A ∩ K).indicator 1 t) := hm1.add (hm2.const_mul _)
        rw [lintegral_const_mul _ hm]
        rw [lintegral_add_left hm1,
          lintegral_const_mul _ (measurable_one.indicator (hAm.inter hKm)),
          lintegral_indicator_one hAm, lintegral_indicator_one (hAm.inter hKm)]
    _ ≤ ENNReal.ofReal (Real.exp (-(c * π))) * (μ A + ENNReal.ofReal c * (ENNReal.ofReal π * μ A)) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (-(c * π)) * (1 + c * π)) * μ A := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_add (by norm_num)
          (mul_nonneg hc0 hπ0), ENNReal.ofReal_mul hc0, ENNReal.ofReal_one]
        ring
    _ ≤ 1 * μ A := by
        gcongr
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have := Real.add_one_le_exp (c * π)
        have h2 : Real.exp (-(c * π)) * Real.exp (c * π) = 1 := by
          rw [← Real.exp_add]; simp
        nlinarith [Real.exp_pos (-(c * π))]
    _ = μ A := one_mul _

end L36
end LPM


-- ===== Solutions.LPM.L36f =====

set_option autoImplicit false

namespace LPM
namespace L36
open LocalProbeMIS871.Greedy MeasureTheory
open scoped Classical ENNReal

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)

noncomputable def perms (J : Finset (Fin n)) : Finset (List (Fin n)) :=
  (B v J).toList.permutations.toFinset

theorem κ_congr (r r' : Fin n → ℝ) (u : Fin n) (h : u ≠ v → r u = r' u) :
    κ v r u = κ v r' u := by
  by_cases hu : u = v
  · subst hu; rw [κ_v, κ_v]
  · rw [κ_eq_ne v r u hu, κ_eq_ne v r' u hu, h hu]

theorem mem_perms {J : Finset (Fin n)} {σ : List (Fin n)} (hσ : σ ∈ perms v J) :
    σ.Perm (B v J).toList := by
  simpa [perms, List.mem_permutations] using hσ

theorem tri_sub (J : Finset (Fin n)) (σ : List (Fin n)) (hσ : σ ∈ perms v J) :
    ∀ L : List (Fin n), L.Sublist σ.reverse →
      Tri (kJ G v J σ) (lJ G v J) (volume.restrict (Set.Ioo (0 : ℝ) 1)) L := by
  have hσB : ∀ y ∈ σ, y ∈ B v J := by
    intro y hy; have := (mem_perms v hσ).subset hy; simpa using this
  have hnd : σ.reverse.Nodup := by
    rw [List.nodup_reverse]; exact (mem_perms v hσ).nodup_iff.2 (Finset.nodup_toList _)
  intro L
  induction L with
  | nil => intro _; trivial
  | cons x L' ih =>
    intro hsub
    have hxσ : x ∈ σ := by
      have := hsub.subset (List.mem_cons_self); simpa using this
    have hxB := hσB x hxσ
    obtain ⟨hxv, hxJ⟩ := (mem_B v J x).1 hxB
    have hndL := hnd.sublist hsub
    have hxL' : x ∉ L' := (List.nodup_cons.1 hndL).1
    refine ⟨?_, ?_, ?_, ih (List.sublist_of_cons_sublist hsub)⟩
    · intro y hy r t
      have hyx : y ≠ x := fun e => hxL' (e ▸ hy)
      have hyB : y ∈ B v J := hσB y (by
        have := (List.sublist_of_cons_sublist hsub).subset hy; simpa using this)
      constructor
      · unfold kJ
        rw [Static_update G v J r x t hxB, ordL_update G v J r x t hxJ,
          T_update G v J r x t hxJ, κ_update_ne v r x t y hyx]
        by_cases hc : Static G v J r ∧ ordL G v J r = σ ∧ T G v J r y < κ v r y
        · rw [if_pos hc, if_pos hc]
          -- order: x is after y in σ
          have hpair : [y, x].Sublist σ := by
            have h1 : [x, y].Sublist σ.reverse :=
              (List.cons_sublist_cons.2 (List.singleton_sublist.2 hy)).trans hsub
            have := List.reverse_sublist.2 h1
            simpa using this
          have hsorted := ordL_sorted G v J r
          rw [hc.2.1] at hsorted
          have hok : ok G v J r y ≤ ok G v J r x := by
            have := hsorted.sublist hpair
            simpa using this
          have hT := T_le_of_ok G v J r y x hok
          rw [piX_update G v J r x t hxJ y hT]
          have hiff : InR G v J (Function.update r x t) y ↔ InR G v J r y := by
            rw [InR_update G v J r x t hxJ y hT, κ_update_ne v r x t y hyx]; rfl
          simp only [hiff]
        · rw [if_neg hc, if_neg hc]
      · unfold lJ
        rw [T_update G v J r x t hxJ, κ_update_ne v r x t y hyx]
    · intro r r' h
      unfold lJ
      have hT : T G v J r x = T G v J r' x := by
        apply T_congr
        intro z hz
        apply κ_congr
        intro _
        apply h
        left
        intro hzL
        have : z ∈ B v J := by
          rcases List.mem_cons.1 hzL with e | e
          · rw [e]; exact hxB
          · exact hσB z (by
              have := (List.sublist_of_cons_sublist hsub).subset e; simpa using this)
        exact ((mem_B v J z).1 this).2 hz
      rw [hT, κ_congr v r r' x (fun _ => h x (Or.inr rfl))]
    · intro r; exact coord_bound G v J σ x hxB r

theorem prod_ofReal_exp (s : Finset (Fin n)) (a : Fin n → ℝ) :
    ∏ x ∈ s, ENNReal.ofReal (Real.exp (a x)) = ENNReal.ofReal (Real.exp (∑ x ∈ s, a x)) := by
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun x _ => (Real.exp_pos _).le)]

theorem lemma_3_6_proof (Δ : ℕ) (hdeg : ∀ u, G.degree u ≤ Δ) :
    ExpBound (forcedLaw v) (fun r => ((U G v r : ℝ) - 2) / 2 - 2 * Δ * M G v 1 r) 1 := by
  set f : (Fin n → ℝ) → ℝ := fun r => ((U G v r : ℝ) - 2) / 2 - 2 * Δ * M G v 1 r with hf
  have hfm : Measurable f :=
    (((measurable_U G v).sub measurable_const).div_const 2).sub
      ((measurable_M G v 1).const_mul _)
  refine ⟨hfm.aemeasurable, ?_⟩
  set μ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  have hF : Measurable (fun r => ENNReal.ofReal (Real.exp (f r))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hfm)
  rw [forcedLaw, lintegral_map hF (measurable_forceRoot v)]
  -- the decomposition
  set D : (Fin n → ℝ) → ℝ≥0∞ := fun r => ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset,
    ∑ σ ∈ perms v J, cJ G v J σ r * ∏ x ∈ B v J, kJ G v J σ x r with hD
  have hdec : ∀ᵐ r ∂rankLaw n, ENNReal.ofReal (Real.exp (f (forceRoot v r))) ≤ D r := by
    filter_upwards [ae_goodRanks_pre v] with r hg
    set J := I G (forceRoot v r)
    set σ := ordL G v J r
    have hJ : I G (forceRoot v r) = J := rfl
    have hσ : σ ∈ perms v J := by
      simp only [perms, List.mem_toFinset, List.mem_permutations]; exact ordL_perm G v J r
    have hs := static_of_eq G v J r hJ hg
    have hc : cJ G v J σ r = 1 := by simp [cJ, hs, σ]
    have hk : ∀ x ∈ B v J, kJ G v J σ x r = ENNReal.ofReal (Real.exp
        ((if InR G v J r x then (1 : ℝ) else 0) - (Real.exp 1 - 1) * piX G v J r x)) := by
      intro x hx
      simp [kJ, hs, σ, T_lt_κ_of_B G v J r hJ x hx]
    calc ENNReal.ofReal (Real.exp (f (forceRoot v r)))
        ≤ cJ G v J σ r * ∏ x ∈ B v J, kJ G v J σ x r := by
          rw [hc, one_mul, Finset.prod_congr rfl hk, prod_ofReal_exp]
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.2
          exact pointwise G v J r hJ hg Δ hdeg
      _ ≤ ∑ σ' ∈ perms v J, cJ G v J σ' r * ∏ x ∈ B v J, kJ G v J σ' x r :=
          Finset.single_le_sum (f := fun σ' => cJ G v J σ' r * ∏ x ∈ B v J, kJ G v J σ' x r)
            (fun _ _ => zero_le) hσ
      _ ≤ D r := Finset.single_le_sum
            (f := fun J => ∑ σ' ∈ perms v J, cJ G v J σ' r * ∏ x ∈ B v J, kJ G v J σ' x r)
            (fun _ _ => zero_le) (Finset.mem_powerset.2 (Finset.subset_univ _))
  have hmk : ∀ J σ, Measurable (fun r => cJ G v J σ r * ∏ x ∈ B v J, kJ G v J σ x r) :=
    fun J σ => (measurable_cJ G v J σ).mul
      (Finset.measurable_prod _ (fun x _ => measurable_kJ G v J σ x))
  have hml : ∀ J σ, Measurable (fun r => cJ G v J σ r * ∏ x ∈ B v J, lJ G v J x r) :=
    fun J σ => (measurable_cJ G v J σ).mul
      (Finset.measurable_prod _ (fun x _ => measurable_lJ G v J x))
  -- triangular comparison for each term
  have hterm : ∀ J, ∀ σ ∈ perms v J,
      ∫⁻ r, cJ G v J σ r * ∏ x ∈ B v J, kJ G v J σ x r ∂rankLaw n ≤
        ∫⁻ r, cJ G v J σ r * ∏ x ∈ B v J, lJ G v J x r ∂rankLaw n := by
    intro J σ hσ
    have hBσ : σ.reverse.toFinset = B v J := by
      ext y; simp only [List.mem_toFinset, List.mem_reverse]
      rw [(mem_perms v hσ).mem_iff]; simp
    rw [rankLaw]
    apply lintegral_le_of_lmarginal_le σ.reverse.toFinset (hmk J σ) (hml J σ)
    intro r
    have hnd : σ.reverse.Nodup := by
      rw [List.nodup_reverse]; exact (mem_perms v hσ).nodup_iff.2 (Finset.nodup_toList _)
    have := tri_lemma μ (kJ G v J σ) (lJ G v J) (measurable_kJ G v J σ) (measurable_lJ G v J)
      σ.reverse hnd (tri_sub G v J σ hσ σ.reverse (List.Sublist.refl _)) (cJ G v J σ)
      (measurable_cJ G v J σ) ?_ r
    · rw [hBσ] at this ⊢; exact this
    · intro i hi r' t
      have hiB : i ∈ B v J := by rw [← hBσ]; simpa using hi
      simp only [cJ, Static_update G v J r' i t hiB,
        ordL_update G v J r' i t ((mem_B v J i).1 hiB).2]
  -- the final pointwise sum is at most one
  have hone : ∀ r, ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset,
      ∑ σ ∈ perms v J, cJ G v J σ r * ∏ x ∈ B v J, lJ G v J x r ≤ 1 := by
    intro r
    have h1 : ∀ J, ∑ σ ∈ perms v J, cJ G v J σ r * ∏ x ∈ B v J, lJ G v J x r ≤
        if I G (forceRoot v r) = J then 1 else 0 := by
      intro J
      have hmem : ordL G v J r ∈ perms v J := by
        simp only [perms, List.mem_toFinset, List.mem_permutations]; exact ordL_perm G v J r
      have : ∑ σ ∈ perms v J, cJ G v J σ r * ∏ x ∈ B v J, lJ G v J x r =
          if Static G v J r then ∏ x ∈ B v J, lJ G v J x r else 0 := by
        simp only [cJ]
        by_cases hs : Static G v J r
        · simp only [hs, true_and, if_true]
          rw [Finset.sum_eq_single (ordL G v J r)]
          · simp
          · intro b _ hb; rw [if_neg (Ne.symm hb)]; simp
          · intro h; exact absurd hmem h
        · simp [hs]
      rw [this]
      by_cases hs : Static G v J r
      · rw [if_pos hs]
        by_cases hall : ∀ x ∈ B v J, T G v J r x < κ v r x
        · rw [if_pos (eq_of_static G v J r hs hall)]
          apply Finset.prod_le_one (fun _ _ => zero_le)
          intro x _; simp only [lJ]; split_ifs <;> simp
        · push Not at hall
          obtain ⟨x, hx, hxn⟩ := hall
          rw [Finset.prod_eq_zero hx (by simp [lJ, not_lt.2 hxn])]
          exact zero_le
      · rw [if_neg hs]; exact zero_le
    calc _ ≤ ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset,
          (if I G (forceRoot v r) = J then (1 : ℝ≥0∞) else 0) := Finset.sum_le_sum (fun J _ => h1 J)
      _ = 1 := by
          rw [Finset.sum_ite_eq]
          simp
  calc ∫⁻ r, ENNReal.ofReal (Real.exp (f (forceRoot v r))) ∂rankLaw n
      ≤ ∫⁻ r, D r ∂rankLaw n := lintegral_mono_ae hdec
    _ = ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset, ∑ σ ∈ perms v J,
          ∫⁻ r, cJ G v J σ r * ∏ x ∈ B v J, kJ G v J σ x r ∂rankLaw n := by
        rw [hD, lintegral_finsetSum]
        · apply Finset.sum_congr rfl; intro J _
          rw [lintegral_finsetSum]
          intro σ _; exact hmk J σ
        · intro J _; exact Finset.measurable_sum _ (fun σ _ => hmk J σ)
    _ ≤ ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset, ∑ σ ∈ perms v J,
          ∫⁻ r, cJ G v J σ r * ∏ x ∈ B v J, lJ G v J x r ∂rankLaw n := by
        exact Finset.sum_le_sum (fun J _ => Finset.sum_le_sum (fun σ hσ => hterm J σ hσ))
    _ = ∫⁻ r, ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset, ∑ σ ∈ perms v J,
          cJ G v J σ r * ∏ x ∈ B v J, lJ G v J x r ∂rankLaw n := by
        rw [lintegral_finsetSum]
        · apply Finset.sum_congr rfl; intro J _
          rw [lintegral_finsetSum]
          intro σ _; exact hml J σ
        · intro J _; exact Finset.measurable_sum _ (fun σ _ => hml J σ)
    _ ≤ ∫⁻ _, 1 ∂rankLaw n := lintegral_mono hone
    _ = ENNReal.ofReal 1 := by simp

end L36
end LPM


open MeasureTheory
open scoped BigOperators Classical
noncomputable section
open LocalProbeMIS871.Greedy

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (hdeg : ∀ u, G.degree u ≤ Δ) (v : Fin n) :
    ExpBound (forcedLaw v) (fun r => ((U G v r : ℝ) - 2) / 2 - 2 * Δ * M G v 1 r) 1 :=
  LPM.L36.lemma_3_6_proof G v Δ hdeg

