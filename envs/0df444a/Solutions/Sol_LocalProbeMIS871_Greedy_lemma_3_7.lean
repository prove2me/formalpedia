-- Prove2me | solution 1 for LocalProbeMIS871.Greedy.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T01:00:02.044516+00:00
-- url     : https://prove2.me/submissions/3ca0c27d-779a-4893-8b95-f7bdeabc5c37

import Definitions.Def_LocalProbeMIS871_Greedy_Elimination
import Definitions.Def_LocalProbeMIS871_Greedy_Weighted

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


-- ===== Solutions.LPM.L37a =====

set_option autoImplicit false

namespace LPM
open MeasureTheory ProbabilityTheory
open scoped ENNReal

section local_
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
  {α : Type*} [LinearOrder α]

/-- Greedy membership only depends on the ranks at or below the vertex. -/
theorem inMIS_local (r r' : V → α) :
    ∀ z, (∀ y, (r y ≤ r z ∨ r' y ≤ r' z) → r y = r' y) →
      RGMISFast.inMIS G r z = RGMISFast.inMIS G r' z := by
  intro z
  induction hk : RGMISFast.rk r z using Nat.strong_induction_on generalizing z with
  | _ k ih =>
    intro h
    have hz : r z = r' z := h z (Or.inl le_rfl)
    apply Bool.eq_iff_iff.2
    rw [inMIS_iff, inMIS_iff]
    have hlow : ∀ w, r w < r z → (∀ y, (r y ≤ r w ∨ r' y ≤ r' w) → r y = r' y) := by
      intro w hw y hy
      have hw' : r w = r' w := h w (Or.inl hw.le)
      apply h
      rcases hy with hy | hy
      · exact Or.inl (hy.trans hw.le)
      · right; rw [← hz]; rw [← hw'] at hy; exact hy.trans hw.le
    have hiff : ∀ w, r w < r z ↔ r' w < r' z := by
      intro w
      constructor
      · intro hw; rw [← h w (Or.inl hw.le), ← hz]; exact hw
      · intro hw
        have : r w = r' w := h w (Or.inr hw.le)
        rw [this, hz]; exact hw
    constructor
    · intro H w hw hlt
      have hlt' := (hiff w).2 hlt
      rw [← ih _ (hk ▸ RGMISFast.rk_lt r hlt') w rfl (hlow w hlt')]
      exact H w hw hlt'
    · intro H w hw hlt
      rw [ih _ (hk ▸ RGMISFast.rk_lt r hlt) w rfl (hlow w hlt)]
      exact H w hw ((hiff w).1 hlt)

end local_

variable {n : ℕ}

/-- product measure with a product density -/
theorem pi_withDensity (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (hfin : ∀ i, ∫⁻ x, f i x ∂μ i ≠ ⊤) :
    (Measure.pi μ).withDensity (fun r => ∏ i, f i (r i)) =
      Measure.pi (fun i => (μ i).withDensity (f i)) := by
  have : ∀ i, IsFiniteMeasure ((μ i).withDensity (f i)) := fun i =>
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact (hfin i).lt_top⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have : (Set.univ.pi s).indicator (fun r : Fin n → ℝ => ∏ i, f i (r i)) =
      fun r => ∏ i, (s i).indicator (f i) (r i) := by
    funext r
    by_cases hr : r ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hr]
      apply Finset.prod_congr rfl; intro i _
      rw [Set.indicator_of_mem (hr i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hr]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hr
      obtain ⟨i, hi⟩ := hr
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
  rw [this]
  have hind := iIndepFun_pi (μ := μ) (X := fun i => (s i).indicator (f i))
    (fun i => ((hf i).indicator (hs i)).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => ((hf i).indicator (hs i)).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl; intro i _
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
  exact (measurePreserving_eval μ i).lintegral_comp ((hf i).indicator (hs i))

/-- integrals factor over functions of disjoint coordinate blocks -/
theorem lintegral_mul_blocks (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Finset (Fin n)) (g h : (Fin n → ℝ) → ℝ≥0∞) (hg : Measurable g) (hh : Measurable h)
    (hgS : ∀ r r', (∀ i ∈ S, r i = r' i) → g r = g r')
    (hhS : ∀ r r', (∀ i ∉ S, r i = r' i) → h r = h r') :
    ∫⁻ r, g r * h r ∂Measure.pi μ = (∫⁻ r, g r ∂Measure.pi μ) * ∫⁻ r, h r ∂Measure.pi μ := by
  have hind := iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => aemeasurable_id)
  have hI := hind.indepFun_finset S Sᶜ disjoint_compl_right (fun i => measurable_pi_apply i)
  let ext : (Fin n → ℝ) → (Fin n → ℝ) := id
  let eS : ((i : S) → ℝ) → (Fin n → ℝ) := fun y i => if hi : i ∈ S then y ⟨i, hi⟩ else 0
  let eT : ((i : (Sᶜ : Finset (Fin n))) → ℝ) → (Fin n → ℝ) :=
    fun y i => if hi : i ∈ Sᶜ then y ⟨i, hi⟩ else 0
  have meS : Measurable eS := by
    apply measurable_pi_lambda; intro i
    by_cases hi : i ∈ S
    · simp only [eS, hi, dif_pos]; exact measurable_pi_apply _
    · simp only [eS, hi, dif_neg, not_false_eq_true]; exact measurable_const
  have meT : Measurable eT := by
    apply measurable_pi_lambda; intro i
    by_cases hi : i ∈ Sᶜ
    · simp only [eT, hi, dif_pos]; exact measurable_pi_apply _
    · simp only [eT, hi, dif_neg, not_false_eq_true]; exact measurable_const
  have hgeq : g = (g ∘ eS) ∘ (fun (a : Fin n → ℝ) (i : S) => id (a i)) := by
    funext r; apply hgS; intro i hi; simp [eS, hi]
  have hheq : h = (h ∘ eT) ∘ (fun (a : Fin n → ℝ) (i : (Sᶜ : Finset (Fin n))) => id (a i)) := by
    funext r; apply hhS; intro i hi
    have : i ∈ Sᶜ := Finset.mem_compl.2 hi
    simp only [Function.comp, eT, this, dif_pos, id]
  have hI2 := hI.comp (hg.comp meS) (hh.comp meT)
  rw [← hgeq, ← hheq] at hI2
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hg hh hI2

end LPM


-- ===== Solutions.LPM.L37b =====

set_option autoImplicit false

namespace LPM
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

section cdf
variable (ψ : ℝ → ℝ) (a : ℝ)

/-- tail integral -/
noncomputable def Ftail (z : ℝ) : ℝ := ∫ y in z..2, ψ y

variable {ψ a}
variable (hψm : Measurable ψ) (hψ0 : ∀ z, 0 ≤ ψ z) (hψs : ∀ z, z ∉ Ioo a 1 → ψ z = 0)
  (hint : Integrable ψ) (ha : 0 < a) (ha1 : a < 1)
include hψm hψ0 hψs hint ha ha1 ha1

theorem Ftail_eq_Ioi (z : ℝ) (hz : z ≤ 2) : Ftail ψ z = ∫ y in Ioi z, ψ y := by
  unfold Ftail
  rw [intervalIntegral.integral_of_le hz]
  rw [← Ioc_union_Ioi_eq_Ioi hz, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    hint.integrableOn hint.integrableOn]
  have : ∫ y in Ioi (2 : ℝ), ψ y = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy; apply hψs; intro h; simp at hy h; linarith [h.2]
  rw [this, add_zero]

theorem Ftail_cont : Continuous (Ftail ψ) := by
  have : Ftail ψ = fun z => -∫ y in (2 : ℝ)..z, ψ y := by
    funext z; unfold Ftail; rw [intervalIntegral.integral_symm]
  rw [this]
  exact (hint.continuous_primitive 2).neg

theorem Ftail_anti : Antitone (Ftail ψ) := by
  intro z z' hzz'
  have h := intervalIntegral.integral_add_adjacent_intervals (a := z) (b := z') (c := 2)
    hint.intervalIntegrable hint.intervalIntegrable
  unfold Ftail
  have : 0 ≤ ∫ y in z..z', ψ y := intervalIntegral.integral_nonneg hzz' (fun y _ => hψ0 y)
  linarith

theorem Ftail_nonneg (z : ℝ) : 0 ≤ Ftail ψ z := by
  by_cases hz : z ≤ 2
  · rw [Ftail_eq_Ioi hψm hψ0 hψs hint ha ha1 z hz]; exact setIntegral_nonneg measurableSet_Ioi
      (fun y _ => hψ0 y)
  · unfold Ftail
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le (by linarith)]
    have : ∫ y in Ioc 2 z, ψ y = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro y hy; apply hψs; intro h; simp at hy h; linarith [h.2, hy.1]
    rw [this, neg_zero]

theorem Ftail_low (z : ℝ) (hz : z ≤ a) : Ftail ψ z = ∫ y, ψ y := by
  rw [Ftail_eq_Ioi hψm hψ0 hψs hint ha ha1 z (by linarith)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy; apply hψs; intro h; simp at hy; linarith [h.1]

theorem Ftail_high (z : ℝ) (hz : 1 ≤ z) : Ftail ψ z = 0 := by
  apply le_antisymm _ (Ftail_nonneg hψm hψ0 hψs hint ha ha1 z)
  by_cases hz2 : z ≤ 2
  · rw [Ftail_eq_Ioi hψm hψ0 hψs hint ha ha1 z hz2]
    apply le_of_eq
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy; apply hψs; intro h; simp at hy; linarith [h.2]
  · unfold Ftail
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le (by linarith)]
    have : ∫ y in Ioc 2 z, ψ y = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro y hy; apply hψs; intro h; simp at hy h; linarith [h.2, hy.1]
    rw [this, neg_zero]

theorem cdf_push :
    Measure.map (Ftail ψ) (volume.withDensity (fun z => ENNReal.ofReal (ψ z))) =
      volume.restrict (Ioo 0 (∫ y, ψ y)) := by
  set b := ∫ y, ψ y with hb
  set ν := volume.withDensity (fun z => ENNReal.ofReal (ψ z)) with hν
  have hb0 : 0 ≤ b := integral_nonneg hψ0
  have hFm : Measurable (Ftail ψ) := (Ftail_cont hψm hψ0 hψs hint ha ha1).measurable
  have hνfin : ν univ = ENNReal.ofReal b := by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hψ0)]
  have : IsFiniteMeasure ν := ⟨by rw [hνfin]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure (Measure.map (Ftail ψ) ν) := Measure.isFiniteMeasure_map _ _
  apply Measure.ext_of_Iic
  intro y
  rw [Measure.map_apply hFm measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge y 0 with hy | hy
  · have h1 : Ftail ψ ⁻¹' Iic y = ∅ := by
      ext z; simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hy (Ftail_nonneg hψm hψ0 hψs hint ha ha1 z)
    have h2 : Iic y ∩ Ioo 0 b = ∅ := by
      ext z; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2; linarith
    rw [h1, h2]; simp
  rcases le_or_gt b y with hby | hby
  · have h1 : Ftail ψ ⁻¹' Iic y = univ := by
      ext z; simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      calc Ftail ψ z ≤ Ftail ψ (min z a) := Ftail_anti hψm hψ0 hψs hint ha ha1 (min_le_left _ _)
        _ = b := Ftail_low hψm hψ0 hψs hint ha ha1 _ (min_le_right _ _)
        _ ≤ y := hby
    have h2 : Iic y ∩ Ioo 0 b = Ioo 0 b := by
      ext z; simp only [mem_inter_iff, mem_Iic, mem_Ioo, and_iff_right_iff_imp]
      intro h; linarith [h.2]
    rw [h1, h2, hνfin, Real.volume_Ioo, sub_zero]
  -- the main case 0 ≤ y < b
  set A := {z : ℝ | Ftail ψ z ≤ y} with hA
  have hAc : IsClosed A := isClosed_le (Ftail_cont hψm hψ0 hψs hint ha ha1) continuous_const
  have hAne : A.Nonempty := ⟨1, by simp [hA, Ftail_high hψm hψ0 hψs hint ha ha1 1 le_rfl, hy]⟩
  have hAbdd : BddBelow A := ⟨a, fun z hz => by
    by_contra h
    push Not at h
    have := Ftail_low hψm hψ0 hψs hint ha ha1 z h.le
    simp only [hA, mem_ofPred_eq] at hz
    linarith⟩
  set c := sInf A with hc
  have hcA : c ∈ A := hAc.csInf_mem hAne hAbdd
  have hAeq : A = Ici c := by
    ext z; constructor
    · intro hz; exact csInf_le hAbdd hz
    · intro hz
      simp only [hA, mem_ofPred_eq]
      exact (Ftail_anti hψm hψ0 hψs hint ha ha1 hz).trans hcA
  have hac : a ≤ c := by
    by_contra h; push Not at h
    have := Ftail_low hψm hψ0 hψs hint ha ha1 c h.le
    simp only [hA, mem_ofPred_eq] at hcA; linarith
  have hFc : Ftail ψ c = y := by
    apply le_antisymm hcA
    obtain ⟨d, hd, hdy⟩ := intermediate_value_Icc' hac
      (Ftail_cont hψm hψ0 hψs hint ha ha1).continuousOn
      ⟨hcA, by rw [Ftail_low hψm hψ0 hψs hint ha ha1 a le_rfl]; exact hby.le⟩
    have hdA : d ∈ A := by simp [hA, hdy]
    have : c ≤ d := csInf_le hAbdd hdA
    have hdc : d = c := le_antisymm hd.2 this
    rw [← hdc, hdy]
  have hc2 : c ≤ 2 := by
    have : (1 : ℝ) ∈ A := by simp [hA, Ftail_high hψm hψ0 hψs hint ha ha1 1 le_rfl, hy]
    have := csInf_le hAbdd this; linarith
  have h1 : Ftail ψ ⁻¹' Iic y = Ici c := hAeq
  have h2 : Iic y ∩ Ioo 0 b = Ioc 0 y := by
    ext z; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, lt_of_le_of_lt h2 hby⟩
  rw [h1, h2, Real.volume_Ioc, sub_zero, hν, withDensity_apply _ measurableSet_Ici]
  rw [← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
    (Filter.Eventually.of_forall hψ0)]
  rw [integral_Ici_eq_integral_Ioi, ← Ftail_eq_Ioi hψm hψ0 hψs hint ha ha1 c hc2, hFc]

end cdf

end LPM


-- ===== Solutions.LPM.L37c =====

set_option autoImplicit false

namespace LPM
open MeasureTheory ProbabilityTheory Set LocalProbeMIS871.Greedy
open scoped ENNReal

variable {n : ℕ}

noncomputable abbrev μU : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

theorem prod_ite_univ (X : Finset (Fin n)) (h : ℝ → ℝ≥0∞) (r : Fin n → ℝ) :
    ∏ x ∈ X, h (r x) = ∏ i, (if i ∈ X then h else fun _ => (1 : ℝ≥0∞)) (r i) := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ X)]
  rw [Finset.prod_eq_one (s := Finset.univ.filter (fun i => i ∉ X)) (fun i hi => by
    simp only [Finset.mem_filter] at hi; simp [hi.2]), mul_one]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  apply Finset.prod_congr rfl; intro i hi; simp [hi]

/-- Transport comparison. -/
theorem transport_le (ψ : ℝ → ℝ) (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hψm : Measurable ψ) (hψ0 : ∀ z, 0 ≤ ψ z) (hψs : ∀ z, z ∉ Ioo a 1 → ψ z = 0)
    (hint : Integrable ψ) (hb : ∫ y, ψ y ≤ a)
    (X : Finset (Fin n)) (P Q : Set (Fin n → ℝ)) (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (hPQ : ∀ r s, (∀ u ∈ X, ∀ z ∈ X, r u < r z ↔ s z < s u) → (r ∈ P ↔ s ∈ Q)) :
    ∫⁻ r, P.indicator 1 r * ∏ x ∈ X, ENNReal.ofReal (ψ (r x)) ∂rankLaw n ≤
      rankLaw n ({r | ∀ x ∈ X, r x ≤ a} ∩ Q) := by
  set b := ∫ y, ψ y with hbdef
  have hb0 : 0 ≤ b := integral_nonneg hψ0
  set f : Fin n → ℝ → ℝ≥0∞ := fun i => if i ∈ X then (fun z => ENNReal.ofReal (ψ z))
    else fun _ => 1 with hf
  have hfm : ∀ i, Measurable (f i) := by
    intro i; by_cases hi : i ∈ X
    · simp only [hf, hi, if_true]; exact ENNReal.measurable_ofReal.comp hψm
    · simp only [hf, hi, if_false]; exact measurable_const
  have hlψ : ∫⁻ z, ENNReal.ofReal (ψ z) ∂μU ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := ∫⁻ z, ENNReal.ofReal (ψ z))
    · rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hψ0)]
      exact ENNReal.ofReal_ne_top
    · exact setLIntegral_le_lintegral _ _
  have hffin : ∀ i, ∫⁻ z, f i z ∂μU ≠ ⊤ := by
    intro i; by_cases hi : i ∈ X
    · simp only [hf, hi, if_true]; exact hlψ
    · simp [hf, hi]
  -- step 1: LHS as a product measure with densities
  set ρ : Fin n → Measure ℝ := fun i => μU.withDensity (f i) with hρ
  have hpiρ : (Measure.pi (fun _ : Fin n => μU)).withDensity (fun r => ∏ i, f i (r i)) =
      Measure.pi ρ := pi_withDensity (fun _ => μU) f hfm hffin
  have hLHS : ∫⁻ r, P.indicator 1 r * ∏ x ∈ X, ENNReal.ofReal (ψ (r x)) ∂rankLaw n =
      Measure.pi ρ P := by
    rw [← hpiρ, withDensity_apply _ hP, ← lintegral_indicator hP, rankLaw]
    apply lintegral_congr; intro r
    rw [prod_ite_univ X (fun z => ENNReal.ofReal (ψ z)) r]
    by_cases hr : r ∈ P
    · simp [Set.indicator_of_mem hr, hf]
    · simp [Set.indicator_of_notMem hr]
  rw [hLHS]
  -- step 2: push forward
  set φ : Fin n → ℝ → ℝ := fun i => if i ∈ X then Ftail ψ else id with hφ
  have hFc := Ftail_cont hψm hψ0 hψs hint ha ha1
  have hφm : ∀ i, Measurable (φ i) := by
    intro i; by_cases hi : i ∈ X
    · simp only [hφ, hi, if_true]; exact hFc.measurable
    · simp only [hφ, hi, if_false]; exact measurable_id
  set g : Fin n → ℝ → ℝ≥0∞ := fun i => if i ∈ X then (Ioo 0 b).indicator 1 else fun _ => 1 with hg
  have hgm : ∀ i, Measurable (g i) := by
    intro i; by_cases hi : i ∈ X
    · simp only [hg, hi, if_true]; exact measurable_one.indicator measurableSet_Ioo
    · simp only [hg, hi, if_false]; exact measurable_const
  have hgfin : ∀ i, ∫⁻ z, g i z ∂μU ≠ ⊤ := by
    intro i
    apply ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ℝ≥0∞) ∂μU) (by simp)
    apply lintegral_mono; intro z
    by_cases hi : i ∈ X
    · simp only [hg, hi, if_true]; exact Set.indicator_le_self' (fun _ _ => zero_le) z
    · simp [hg, hi]
  have hmapi : ∀ i, (ρ i).map (φ i) = μU.withDensity (g i) := by
    intro i
    by_cases hi : i ∈ X
    · simp only [hρ, hφ, hg, hf, hi, if_true]
      have e1 : μU.withDensity (fun z => ENNReal.ofReal (ψ z)) =
          volume.withDensity (fun z => ENNReal.ofReal (ψ z)) := by
        change (volume.restrict (Ioo (0:ℝ) 1)).withDensity _ = _
        rw [← restrict_withDensity measurableSet_Ioo]
        apply Measure.restrict_eq_self_of_ae_mem
        rw [ae_withDensity_iff (f := fun z => ENNReal.ofReal (ψ z))
          (ENNReal.measurable_ofReal.comp hψm)]
        filter_upwards with z hz
        by_contra hzc
        apply hz
        have : z ∉ Ioo a 1 := fun h => hzc ⟨by linarith [h.1], h.2⟩
        simp [hψs z this]
      rw [e1, cdf_push hψm hψ0 hψs hint ha ha1, withDensity_indicator measurableSet_Ioo,
        withDensity_one]
      change _ = (volume.restrict (Ioo (0:ℝ) 1)).restrict _
      rw [Measure.restrict_restrict measurableSet_Ioo]
      congr 1
      ext z; simp only [mem_inter_iff, mem_Ioo]
      constructor
      · intro h; exact ⟨h, h.1, by linarith [h.2]⟩
      · intro h; exact h.1
    · simp only [hρ, hφ, hg, hf, hi, if_false]
      rw [Measure.map_id]
  have hfinρ : ∀ i, IsFiniteMeasure (ρ i) := fun i =>
    ⟨by rw [hρ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact (hffin i).lt_top⟩
  have hfinm : ∀ i, SigmaFinite ((ρ i).map (φ i)) := by
    intro i
    have := hfinρ i
    infer_instance
  have hpimap : (Measure.pi ρ).map (fun r i => φ i (r i)) = Measure.pi (fun i => μU.withDensity (g i)) := by
    rw [Measure.pi_map_pi (fun i => (hφm i).aemeasurable)]
    congr 1; funext i; exact hmapi i
  have hpig : (Measure.pi (fun _ : Fin n => μU)).withDensity (fun r => ∏ i, g i (r i)) =
      Measure.pi (fun i => μU.withDensity (g i)) := pi_withDensity (fun _ => μU) g hgm hgfin
  set Φ : (Fin n → ℝ) → (Fin n → ℝ) := fun r i => φ i (r i) with hΦ
  have hΦm : Measurable Φ := measurable_pi_lambda _ (fun i => (hφm i).comp (measurable_pi_apply i))
  -- ties
  set Tt : Set (Fin n → ℝ) := {s | ∃ u ∈ X, ∃ z ∈ X, u ≠ z ∧ s u = s z} with hTt
  have hTm : MeasurableSet Tt := by
    have : Tt = ⋃ u ∈ X, ⋃ z ∈ X, {s : Fin n → ℝ | u ≠ z ∧ s u = s z} := by
      ext s; simp only [hTt, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    rw [this]
    refine Finset.measurableSet_biUnion _ (fun u _ => Finset.measurableSet_biUnion _ (fun z _ => ?_))
    by_cases huz : u = z
    · simp [huz]
    · simp only [huz, ne_eq, not_false_eq_true, true_and]
      exact measurableSet_eq_fun (measurable_pi_apply u) (measurable_pi_apply z)
  have hT0 : Measure.pi (fun i => μU.withDensity (g i)) Tt = 0 := by
    rw [← hpig]
    apply withDensity_absolutelyContinuous
    have := (ae_rank_inj (n := n))
    rw [rankLaw] at this
    rw [ae_iff] at this
    apply measure_mono_null _ this
    intro s hs
    obtain ⟨u, _, z, _, huz, he⟩ := hs
    intro hinj; exact huz (hinj he)
  -- the inclusion
  have hsub : P ⊆ Φ ⁻¹' Q ∪ Φ ⁻¹' Tt := by
    intro r hr
    by_cases hT : Φ r ∈ Tt
    · exact Or.inr hT
    · left
      simp only [mem_preimage]
      refine (hPQ r (Φ r) ?_).1 hr
      intro u hu z hz
      have hFa := Ftail_anti hψm hψ0 hψs hint ha ha1
      simp only [hΦ, hφ, hu, hz, if_true]
      constructor
      · intro h
        rcases lt_or_eq_of_le (hFa h.le) with h' | h'
        · exact h'
        · exfalso; apply hT
          refine ⟨z, hz, u, hu, ?_, ?_⟩
          · rintro rfl; exact lt_irrefl _ h
          · simp only [hΦ, hφ, hu, hz, if_true]; exact h'
      · intro h
        by_contra hc; push Not at hc
        exact absurd (hFa hc) (not_le.2 h)
  calc Measure.pi ρ P ≤ Measure.pi ρ (Φ ⁻¹' Q) + Measure.pi ρ (Φ ⁻¹' Tt) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = Measure.pi (fun i => μU.withDensity (g i)) Q +
          Measure.pi (fun i => μU.withDensity (g i)) Tt := by
        rw [← Measure.map_apply hΦm hQ, ← Measure.map_apply hΦm hTm, hpimap]
    _ = Measure.pi (fun i => μU.withDensity (g i)) Q := by rw [hT0, add_zero]
    _ ≤ rankLaw n ({r | ∀ x ∈ X, r x ≤ a} ∩ Q) := by
        rw [← hpig, withDensity_apply _ hQ, rankLaw]
        calc ∫⁻ r in Q, ∏ i, g i (r i) ∂Measure.pi (fun _ => μU)
            ≤ ∫⁻ r in Q, ({r : Fin n → ℝ | ∀ x ∈ X, r x ≤ a}).indicator 1 r
                ∂Measure.pi (fun _ => μU) := by
              apply lintegral_mono; intro r
              by_cases hr : ∀ x ∈ X, r x ≤ a
              · rw [Set.indicator_of_mem (show r ∈ {r : Fin n → ℝ | ∀ x ∈ X, r x ≤ a} from hr)]
                apply Finset.prod_le_one (fun _ _ => zero_le)
                intro i _
                by_cases hi : i ∈ X
                · simp only [hg, hi, if_true]
                  exact Set.indicator_le_self' (fun _ _ => zero_le) _ |>.trans (by simp)
                · simp [hg, hi]
              · push Not at hr
                obtain ⟨x, hx, hxa⟩ := hr
                show ∏ i, g i (r i) ≤ _
                rw [Finset.prod_eq_zero (Finset.mem_univ x)]
                · exact zero_le
                · simp only [hg, hx, if_true]
                  apply Set.indicator_of_notMem
                  simp only [mem_Ioo, not_and, not_lt]; intro _; linarith
          _ = Measure.pi (fun _ => μU) (Q ∩ {r : Fin n → ℝ | ∀ x ∈ X, r x ≤ a}) := by
              rw [lintegral_indicator_one₀]
              · rw [Measure.restrict_apply' hQ, Set.inter_comm]
              · have : {r : Fin n → ℝ | ∀ x ∈ X, r x ≤ a} = ⋂ x ∈ X, {r : Fin n → ℝ | r x ≤ a} := by
                  ext r; simp
                rw [this]
                exact (MeasurableSet.biInter (Finset.countable_toSet X) (fun x _ =>
                  measurableSet_le (measurable_pi_apply x) measurable_const)).nullMeasurableSet
          _ = _ := by rw [Set.inter_comm]

end LPM


-- ===== Solutions.LPM.L37d =====

set_option autoImplicit false

namespace LPM
namespace L37
open MeasureTheory ProbabilityTheory Set LocalProbeMIS871.Greedy
open scoped ENNReal Classical

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (a : ℝ)

def AdmX (X : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {r | ∀ u ∈ X, ∃ z ∈ insert v X, G.Adj u z ∧ (z = v ∨ r u < r z)}

def ValidX (X : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {r | ∀ u ∈ X, ∃ z ∈ insert v X, G.Adj u z ∧ (z = v ∨ r z < r u)}

noncomputable def rt (X : Finset (Fin n)) (r : Fin n → ℝ) : Fin n → ℝ :=
  fun u => if u ∈ insert v X then 2 else r u

def Block (X : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {r | ∀ z, z ∉ insert v X → (∃ y ∈ insert v X, G.Adj z y) → r z ≤ a →
    RGMISFast.inMIS G (key (rt v X r)) z = false}

def EX (X : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {r | ∀ x ∈ X, r x ≤ a} ∩ ValidX G v X ∩ Block G v a X

/-! ### measurability -/

theorem measurableSet_AdmX (X : Finset (Fin n)) : MeasurableSet (AdmX G v X) := by
  have : AdmX G v X = ⋂ u ∈ X, ⋃ z ∈ insert v X,
      {r : Fin n → ℝ | G.Adj u z ∧ (z = v ∨ r u < r z)} := by
    ext r; simp only [AdmX, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
  rw [this]
  refine Finset.measurableSet_biInter _ (fun u _ => Finset.measurableSet_biUnion _ (fun z _ => ?_))
  by_cases h : G.Adj u z
  · by_cases hz : z = v
    · simp [h, hz]
    · simp only [h, hz, true_and, false_or]
      exact measurableSet_lt (measurable_pi_apply u) (measurable_pi_apply z)
  · simp [h]

theorem measurableSet_ValidX (X : Finset (Fin n)) : MeasurableSet (ValidX G v X) := by
  have : ValidX G v X = ⋂ u ∈ X, ⋃ z ∈ insert v X,
      {r : Fin n → ℝ | G.Adj u z ∧ (z = v ∨ r z < r u)} := by
    ext r; simp only [ValidX, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
  rw [this]
  refine Finset.measurableSet_biInter _ (fun u _ => Finset.measurableSet_biUnion _ (fun z _ => ?_))
  by_cases h : G.Adj u z
  · by_cases hz : z = v
    · simp [h, hz]
    · simp only [h, hz, true_and, false_or]
      exact measurableSet_lt (measurable_pi_apply z) (measurable_pi_apply u)
  · simp [h]

theorem measurable_rt (X : Finset (Fin n)) : Measurable (rt v X) := by
  apply measurable_pi_lambda; intro u
  by_cases h : u ∈ insert v X
  · simp only [rt, h, if_true]; exact measurable_const
  · simp only [rt, h, if_false]; exact measurable_pi_apply u

theorem measurableSet_inMIS (z : Fin n) :
    MeasurableSet {r : Fin n → ℝ | RGMISFast.inMIS G (key r) z = false} := by
  have : Measurable (fun r : Fin n → ℝ => RGMISFast.inMIS G (key r) z) := by
    apply measurable_of_patInv (β := Bool)
    intro r r' h; simp only [inMIS_pat G h]
  exact this (measurableSet_singleton false)

theorem measurableSet_Block (X : Finset (Fin n)) : MeasurableSet (Block G v a X) := by
  have : Block G v a X = ⋂ z ∈ (Finset.univ.filter (fun z => z ∉ insert v X ∧
      ∃ y ∈ insert v X, G.Adj z y)),
      ({r : Fin n → ℝ | r z ≤ a}ᶜ ∪ (rt v X) ⁻¹' {r | RGMISFast.inMIS G (key r) z = false}) := by
    ext r
    simp only [Block, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_filter, Finset.mem_univ,
      true_and, Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, not_le]
    constructor
    · intro h z ⟨hz1, hz2⟩
      by_cases hza : r z ≤ a
      · exact Or.inr (h z hz1 hz2 hza)
      · exact Or.inl (lt_of_not_ge hza)
    · intro h z hz1 hz2 hza
      rcases h z ⟨hz1, hz2⟩ with h' | h'
      · exact absurd hza (not_le.2 h')
      · exact h'
  rw [this]
  refine Finset.measurableSet_biInter _ (fun z _ => ?_)
  exact (measurableSet_le (measurable_pi_apply z) measurable_const).compl.union
    (measurable_rt v X (measurableSet_inMIS G z))

theorem measurableSet_le_a (X : Finset (Fin n)) :
    MeasurableSet {r : Fin n → ℝ | ∀ x ∈ X, r x ≤ a} := by
  have : {r : Fin n → ℝ | ∀ x ∈ X, r x ≤ a} = ⋂ x ∈ X, {r : Fin n → ℝ | r x ≤ a} := by
    ext r; simp
  rw [this]
  exact Finset.measurableSet_biInter _ (fun x _ =>
    measurableSet_le (measurable_pi_apply x) measurable_const)

theorem measurableSet_EX (X : Finset (Fin n)) : MeasurableSet (EX G v a X) :=
  ((measurableSet_le_a a X).inter (measurableSet_ValidX G v X)).inter (measurableSet_Block G v a X)

/-! ### combinatorial lemmas -/

theorem tau_gt_iff (r : Fin n → ℝ) (u : Fin n) :
    a < tau G r u ↔ ∀ z ∈ tauSet G (key r) u, a < r z := by
  constructor
  · intro h z hz
    have h1 := tau_le G (key r) u z hz
    have h2 : key r (tauV G r u) ≤ key r z := by rw [← tauKey_eq]; exact h1
    have h3 := key_le_fst h2
    rw [tau_eq] at h
    linarith
  · intro h
    rw [tau_eq]
    exact h _ (tauV_mem G r u)

theorem inMIS_rt (X : Finset (Fin n)) (r : Fin n → ℝ) (hv : v ∉ X)
    (hX : ∀ x ∈ X, a < r x) (ha1 : a < 1) (z : Fin n) (hz : z ∉ insert v X) (hza : r z ≤ a) :
    RGMISFast.inMIS G (key (forceRoot v r)) z = RGMISFast.inMIS G (key (rt v X r)) z := by
  have hzv : z ≠ v := fun e => hz (by simp [e])
  have hzX : z ∉ X := fun e => hz (by simp [e])
  have hfz : forceRoot v r z = r z := by simp [forceRoot, Function.update_of_ne hzv]
  have hrz : rt v X r z = r z := by simp [rt, hz]
  apply inMIS_local
  intro y hy
  have hyout : y ∉ insert v X := by
    intro hy'
    rcases hy with hy | hy
    · have := key_le_fst hy
      rw [hfz] at this
      rcases Finset.mem_insert.1 hy' with e | e
      · rw [e] at this; simp [forceRoot] at this; linarith
      · have hyv : y ≠ v := fun e' => hv (e' ▸ e)
        simp only [forceRoot, Function.update_of_ne hyv] at this
        linarith [hX y e]
    · have := key_le_fst hy
      rw [hrz] at this
      simp only [rt, hy', if_true] at this
      linarith
  have hyv : y ≠ v := fun e => hyout (by simp [e])
  simp only [key, forceRoot, rt, Function.update_of_ne hyv, hyout, if_false]

theorem H_iff_Block (X : Finset (Fin n)) (hv : v ∉ X) (r : Fin n → ℝ) (ha1 : a < 1)
    (hX : ∀ x ∈ X, r x ∈ Ioo a 1) :
    insert v X ⊆ H G (forceRoot v r) a ↔ r ∈ Block G v a X := by
  have hX' : ∀ x ∈ X, a < r x := fun x hx => (hX x hx).1
  constructor
  · intro hsub z hz ⟨y, hy, hzy⟩ hza
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    rw [← inMIS_rt G v a X r hv hX' ha1 z hz hza] at hc
    have hyH := hsub hy
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and] at hyH
    rw [tau_gt_iff] at hyH
    have hzv : z ≠ v := fun e => hz (by simp [e])
    have := hyH z (by
      simp only [tauSet, Finset.mem_filter, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      exact ⟨Or.inr hzy.symm, hc⟩)
    simp only [forceRoot, Function.update_of_ne hzv] at this
    linarith
  · intro hB u hu
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [tau_gt_iff]
    intro z hz
    simp only [tauSet, Finset.mem_filter, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hz
    obtain ⟨hzN, hzm⟩ := hz
    by_cases hzin : z ∈ insert v X
    · rcases Finset.mem_insert.1 hzin with e | e
      · rw [e]; simp [forceRoot]; exact ha1
      · have hzv : z ≠ v := fun e' => hv (e' ▸ e)
        simp only [forceRoot, Function.update_of_ne hzv]; exact hX' z e
    · have hzv : z ≠ v := fun e => hzin (by simp [e])
      simp only [forceRoot, Function.update_of_ne hzv]
      by_contra hza
      push Not at hza
      have hadj : ∃ y ∈ insert v X, G.Adj z y := by
        rcases hzN with e | e
        · exact absurd (e ▸ hu) hzin
        · exact ⟨u, hu, e.symm⟩
      have := hB z hzin hadj hza
      rw [← inMIS_rt G v a X r hv hX' ha1 z hzin hza] at this
      rw [this] at hzm; exact absurd hzm (by simp)

theorem Adm_iff (X : Finset (Fin n)) (hv : v ∉ X) (r : Fin n → ℝ) (hX : ∀ x ∈ X, r x < 1) :
    Adm G v (forceRoot v r) (insert v X) ↔ r ∈ AdmX G v X := by
  have he : (insert v X).erase v = X := Finset.erase_insert hv
  unfold Adm AdmX
  rw [he]
  simp only [Set.mem_ofPred_eq]
  apply forall₂_congr
  intro u hu
  have huv : u ≠ v := fun e => hv (e ▸ hu)
  apply exists_congr; intro z
  apply and_congr_right; intro hz
  apply and_congr_right; intro _
  simp only [forceRoot, Function.update_of_ne huv]
  by_cases hzv : z = v
  · simp [hzv, hX u hu]
  · simp [hzv, Function.update_of_ne hzv]

theorem EX_disjoint (ha1 : a < 1) (X Y : Finset (Fin n)) (hvX : v ∉ X) (hvY : v ∉ Y) (hXY : X ≠ Y)
    (r : Fin n → ℝ) (hr : Function.Injective r) (h1 : r ∈ EX G v a X) (h2 : r ∈ EX G v a Y) :
    False := by
  -- generic one-sided argument
  have key : ∀ (X Y : Finset (Fin n)), v ∉ X → v ∉ Y → r ∈ EX G v a X → r ∈ EX G v a Y →
      ∀ w ∈ X, w ∉ Y → (∀ y ∈ symmDiff X Y, r w ≤ r y) → False := by
    intro X Y hvX hvY hX hY w hwX hwY hmin
    obtain ⟨⟨hXa, hXv⟩, hXb⟩ := hX
    obtain ⟨⟨hYa, hYv⟩, hYb⟩ := hY
    have hwv : w ≠ v := fun e => hvX (e ▸ hwX)
    have hwa : r w ≤ a := hXa w hwX
    obtain ⟨z, hz, hwz, hzc⟩ := hXv w hwX
    have hzY : z ∈ insert v Y := by
      by_cases hzv : z = v
      · rw [hzv]; exact Finset.mem_insert_self _ _
      · have hzX : z ∈ X := by
          rcases Finset.mem_insert.1 hz with e | e
          · exact absurd e hzv
          · exact e
        have hlt : r z < r w := by
          rcases hzc with e | e
          · exact absurd e hzv
          · exact e
        by_contra hzY'
        have hzY : z ∉ Y := fun e => hzY' (Finset.mem_insert_of_mem e)
        have := hmin z (by simp [symmDiff, hzX, hzY])
        linarith
    have hwout : w ∉ insert v Y := by simp [hwv, hwY]
    have hB := hYb w hwout ⟨z, hzY, hwz⟩ hwa
    -- w is rejected in rt Y, so it has a lower accepted neighbour z'
    have : ¬ (∀ z', G.Adj w z' → key (rt v Y r) z' < key (rt v Y r) w →
        RGMISFast.inMIS G (key (rt v Y r)) z' = false) := by
      rw [← inMIS_iff]; rw [hB]; simp
    push Not at this
    obtain ⟨z', hwz', hlt, hz'm⟩ := this
    have hrtw : rt v Y r w = r w := by simp [rt, hwout]
    have hz'out : z' ∉ insert v Y := by
      intro h
      have := key_le_fst hlt.le
      rw [hrtw] at this
      simp only [rt, h, if_true] at this
      linarith
    have hrtz' : rt v Y r z' = r z' := by simp [rt, hz'out]
    have hz'lt : r z' < r w := by
      have := key_le_fst hlt.le
      rw [hrtz', hrtw] at this
      rcases lt_or_eq_of_le this with h | h
      · exact h
      · exfalso; have := hr h; rw [this] at hlt; exact lt_irrefl _ hlt
    have hz'X : z' ∉ X := by
      intro h
      have hz'Y : z' ∉ Y := fun e => hz'out (Finset.mem_insert_of_mem e)
      have := hmin z' (by simp [symmDiff, h, hz'Y])
      linarith
    have hz'v : z' ≠ v := fun e => hz'out (by simp [e])
    have hz'outX : z' ∉ insert v X := by simp [hz'v, hz'X]
    have hBX := hXb z' hz'outX ⟨w, Finset.mem_insert_of_mem hwX, hwz'.symm⟩ (by linarith)
    -- compare the two greedy runs below z'
    have hloc : RGMISFast.inMIS G (key (rt v X r)) z' = RGMISFast.inMIS G (key (rt v Y r)) z' := by
      apply inMIS_local
      intro y hy
      have hyX : y ∉ insert v X ∧ y ∉ insert v Y := by
        have hrtz'X : rt v X r z' = r z' := by simp [rt, hz'outX]
        have hb : r y ≤ r z' ∧ y ∉ insert v X ∨ r y ≤ r z' ∧ y ∉ insert v Y := by
          rcases hy with hy | hy
          · have := key_le_fst hy
            rw [hrtz'X] at this
            by_cases hyX : y ∈ insert v X
            · simp only [rt, hyX, if_true] at this; exfalso; linarith
            · simp only [rt, hyX, if_false] at this; exact Or.inl ⟨this, hyX⟩
          · have := key_le_fst hy
            rw [hrtz'] at this
            by_cases hyY : y ∈ insert v Y
            · simp only [rt, hyY, if_true] at this; exfalso; linarith
            · simp only [rt, hyY, if_false] at this; exact Or.inr ⟨this, hyY⟩
        have hyw : r y < r w := by rcases hb with h | h <;> linarith [h.1]
        have hyv : y ≠ v := by
          rcases hb with h | h <;> exact fun e => h.2 (by simp [e])
        have hsd : y ∉ symmDiff X Y := fun h => by have := hmin y h; linarith
        rcases hb with ⟨_, h⟩ | ⟨_, h⟩
        · refine ⟨h, ?_⟩
          intro hyY
          have hyY' : y ∈ Y := by simpa [hyv] using hyY
          have hyX' : y ∉ X := fun e => h (Finset.mem_insert_of_mem e)
          exact hsd (by simp [symmDiff, hyY', hyX'])
        · refine ⟨?_, h⟩
          intro hyX
          have hyX' : y ∈ X := by simpa [hyv] using hyX
          have hyY' : y ∉ Y := fun e => h (Finset.mem_insert_of_mem e)
          exact hsd (by simp [symmDiff, hyY', hyX'])
      simp [key, rt, hyX.1, hyX.2]
    rw [hloc] at hBX
    exact hz'm hBX
  -- pick the minimal element of the symmetric difference
  have hne : (symmDiff X Y).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    exact hXY (by simpa [symmDiff_eq_bot] using h)
  obtain ⟨w, hw, hwmin⟩ := (symmDiff X Y).exists_min_image r hne
  rcases Finset.mem_symmDiff.1 hw with ⟨hwX, hwY⟩ | ⟨hwY, hwX⟩
  · exact key X Y hvX hvY h1 h2 w hwX hwY hwmin
  · exact key Y X hvY hvX h2 h1 w hwY hwX (by rw [symmDiff_comm]; exact hwmin)

end L37
end LPM


-- ===== Solutions.LPM.L37e =====

set_option autoImplicit false

namespace LPM
namespace L37
open MeasureTheory ProbabilityTheory Set LocalProbeMIS871.Greedy
open scoped ENNReal Classical

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (a : ℝ)

/-- summand indexed by the non-root part -/
noncomputable def TX (ψ : ℝ → ℝ) (X : Finset (Fin n)) (r : Fin n → ℝ) : ℝ :=
  if insert v X ⊆ H G (forceRoot v r) a ∧ Adm G v (forceRoot v r) (insert v X) then
    ∏ x ∈ X, ψ (r x) else 0

theorem weightValue_eq (ψ : ℝ → ℝ) (hs : ∀ z, z ∉ Ioo a 1 → ψ z = 0) (z : ℝ) :
    weightValue a ψ z = ψ z := by
  unfold weightValue; split_ifs with h
  · rfl
  · rw [hs z h]

theorem Z_reindex (ψ : ℝ → ℝ) (hs : ∀ z, z ∉ Ioo a 1 → ψ z = 0) (r : Fin n → ℝ) :
    Z G v a ψ (forceRoot v r) =
      ∑ X ∈ (Finset.univ.erase v).powerset, TX G v a ψ X r := by
  unfold Z TX
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun S => S.erase v) (fun X => insert v X)
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    obtain ⟨hSH, hvS, hadm⟩ := hS
    refine ⟨Finset.erase_subset_erase _ (Finset.subset_univ _), ?_, ?_⟩
    · rw [Finset.insert_erase hvS]; exact hSH
    · rw [Finset.insert_erase hvS]; exact hadm
  · intro X hX
    simp only [Finset.mem_filter, Finset.mem_powerset] at hX ⊢
    obtain ⟨hXv, hXH, hadm⟩ := hX
    exact ⟨hXH, Finset.mem_insert_self _ _, hadm⟩
  · intro S hS
    simp only [Finset.mem_filter] at hS
    exact Finset.insert_erase hS.2.1
  · intro X hX
    simp only [Finset.mem_filter, Finset.mem_powerset] at hX
    have hv : v ∉ X := fun h => by simpa using hX.1 h
    exact Finset.erase_insert hv
  · intro S hS
    simp only [Finset.mem_filter] at hS
    unfold omega
    apply Finset.prod_congr rfl
    intro u hu
    have huv : u ≠ v := Finset.ne_of_mem_erase hu
    rw [weightValue_eq a ψ hs]
    simp [forceRoot, Function.update_of_ne huv]

theorem measurableSet_cond (X : Finset (Fin n)) :
    MeasurableSet {r : Fin n → ℝ |
      insert v X ⊆ H G (forceRoot v r) a ∧ Adm G v (forceRoot v r) (insert v X)} := by
  have h1 : MeasurableSet {r : Fin n → ℝ | insert v X ⊆ H G (forceRoot v r) a} := by
    have : {r : Fin n → ℝ | insert v X ⊆ H G (forceRoot v r) a} =
        ⋂ u ∈ insert v X, {r | a < tau G (forceRoot v r) u} := by
      ext r; simp [Finset.subset_iff, H]
    rw [this]
    exact Finset.measurableSet_biInter _ (fun u _ =>
      measurableSet_lt measurable_const ((measurable_tau G u).comp (measurable_forceRoot v)))
  have h2 : MeasurableSet {r : Fin n → ℝ | Adm G v (forceRoot v r) (insert v X)} := by
    have : {r : Fin n → ℝ | Adm G v (forceRoot v r) (insert v X)} =
        ⋂ u ∈ (insert v X).erase v, ⋃ z ∈ insert v X,
          {r : Fin n → ℝ | G.Adj u z ∧ forceRoot v r u < forceRoot v r z} := by
      ext r; simp only [Adm, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
    rw [this]
    refine Finset.measurableSet_biInter _ (fun u _ => Finset.measurableSet_biUnion _ (fun z _ => ?_))
    by_cases h : G.Adj u z
    · simp only [h, true_and]
      exact measurableSet_lt ((measurable_pi_apply u).comp (measurable_forceRoot v))
        ((measurable_pi_apply z).comp (measurable_forceRoot v))
    · simp [h]
  exact h1.inter h2

theorem measurable_TX (ψ : ℝ → ℝ) (hm : Measurable ψ) (X : Finset (Fin n)) :
    Measurable (TX G v a ψ X) := by
  unfold TX
  exact Measurable.ite (measurableSet_cond G v a X)
    (Finset.measurable_prod _ (fun x _ => hm.comp (measurable_pi_apply x))) measurable_const

theorem measurableSet_inj : MeasurableSet {r : Fin n → ℝ | Function.Injective r} := by
  unfold Function.Injective
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter (fun a => MeasurableSet.iInter (fun b => ?_))
  by_cases hab : a = b
  · simp [hab]
  · have : {r : Fin n → ℝ | r a = r b → a = b} = {r | r a = r b}ᶜ := by
      ext r; simp [hab]
    rw [this]
    exact (measurableSet_eq_fun (measurable_pi_apply a) (measurable_pi_apply b)).compl

theorem core (ψ : ℝ → ℝ) (hm : Measurable ψ) (h0 : ∀ z, 0 ≤ ψ z)
    (hs : ∀ z, z ∉ Ioo a 1 → ψ z = 0) (hint : Integrable ψ) (hb : ∫ y, ψ y ≤ a)
    (ha : 0 < a) (ha1 : a < 1) :
    ∫⁻ r, ENNReal.ofReal (Z G v a ψ (forceRoot v r)) ∂rankLaw n ≤ 1 := by
  have hT0 : ∀ X r, 0 ≤ TX G v a ψ X r := by
    intro X r; unfold TX; split_ifs
    · exact Finset.prod_nonneg (fun x _ => h0 _)
    · exact le_rfl
  simp_rw [Z_reindex G v a ψ hs]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun X _ => hT0 X _)]
  rw [lintegral_finsetSum _ (f := fun X r => ENNReal.ofReal (TX G v a ψ X r))
    (fun X _ => ENNReal.measurable_ofReal.comp (measurable_TX G v a ψ hm X))]
  -- each term is bounded by the measure of E_X
  have hterm : ∀ X ∈ (Finset.univ.erase v).powerset,
      ∫⁻ r, ENNReal.ofReal (TX G v a ψ X r) ∂rankLaw n ≤ rankLaw n (EX G v a X) := by
    intro X hX
    have hvX : v ∉ X := fun h => by simpa using Finset.mem_powerset.1 hX h
    set g : (Fin n → ℝ) → ℝ≥0∞ := fun r =>
      (AdmX G v X).indicator 1 r * ∏ x ∈ X, ENNReal.ofReal (ψ (r x)) with hg
    set h : (Fin n → ℝ) → ℝ≥0∞ := fun r => (Block G v a X).indicator 1 r with hh
    set g' : (Fin n → ℝ) → ℝ≥0∞ := fun r =>
      ({r : Fin n → ℝ | ∀ x ∈ X, r x ≤ a} ∩ ValidX G v X).indicator 1 r with hg'
    have hgm : Measurable g := ((measurable_one).indicator (measurableSet_AdmX G v X)).mul
      (Finset.measurable_prod _ (fun x _ => ENNReal.measurable_ofReal.comp
        (hm.comp (measurable_pi_apply x))))
    have hhm : Measurable h := (measurable_one).indicator (measurableSet_Block G v a X)
    have hg'm : Measurable g' := (measurable_one).indicator
      ((measurableSet_le_a a X).inter (measurableSet_ValidX G v X))
    have hgS : ∀ r r', (∀ i ∈ X, r i = r' i) → g r = g r' := by
      intro r r' hrr
      simp only [hg]
      congr 1
      · have : r ∈ AdmX G v X ↔ r' ∈ AdmX G v X := by
          simp only [AdmX, Set.mem_ofPred_eq]
          apply forall₂_congr; intro u hu
          apply exists_congr; intro z
          apply and_congr_right; intro hz
          apply and_congr_right; intro _
          rcases Finset.mem_insert.1 hz with e | e
          · simp [e]
          · rw [hrr u hu, hrr z e]
        by_cases hr : r ∈ AdmX G v X
        · rw [Set.indicator_of_mem hr, Set.indicator_of_mem (this.1 hr)]; rfl
        · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem (fun h => hr (this.2 h))]
      · apply Finset.prod_congr rfl; intro x hx; rw [hrr x hx]
    have hg'S : ∀ r r', (∀ i ∈ X, r i = r' i) → g' r = g' r' := by
      intro r r' hrr
      have : r ∈ {r : Fin n → ℝ | ∀ x ∈ X, r x ≤ a} ∩ ValidX G v X ↔
          r' ∈ {r : Fin n → ℝ | ∀ x ∈ X, r x ≤ a} ∩ ValidX G v X := by
        simp only [ValidX, Set.mem_inter_iff, Set.mem_ofPred_eq]
        apply and_congr
        · apply forall₂_congr; intro x hx; rw [hrr x hx]
        · apply forall₂_congr; intro u hu
          apply exists_congr; intro z
          apply and_congr_right; intro hz
          apply and_congr_right; intro _
          rcases Finset.mem_insert.1 hz with e | e
          · simp [e]
          · rw [hrr u hu, hrr z e]
      simp only [hg']
      by_cases hr : r ∈ {r : Fin n → ℝ | ∀ x ∈ X, r x ≤ a} ∩ ValidX G v X
      · rw [Set.indicator_of_mem hr, Set.indicator_of_mem (this.1 hr)]; rfl
      · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem (fun h => hr (this.2 h))]
    have hhS : ∀ r r', (∀ i ∉ X, r i = r' i) → h r = h r' := by
      intro r r' hrr
      have hrt : rt v X r = rt v X r' := by
        funext u; simp only [rt]
        split_ifs with hu
        · rfl
        · exact hrr u (fun e => hu (Finset.mem_insert_of_mem e))
      have : r ∈ Block G v a X ↔ r' ∈ Block G v a X := by
        simp only [Block, Set.mem_ofPred_eq, hrt]
        apply forall_congr'; intro z
        apply imp_congr_right; intro hz
        have : r z = r' z := hrr z (fun e => hz (Finset.mem_insert_of_mem e))
        rw [this]
      simp only [hh]
      by_cases hr : r ∈ Block G v a X
      · rw [Set.indicator_of_mem hr, Set.indicator_of_mem (this.1 hr)]; rfl
      · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem (fun h => hr (this.2 h))]
    have hpt : ∀ r, ENNReal.ofReal (TX G v a ψ X r) = g r * h r := by
      intro r
      simp only [hg, hh, TX]
      by_cases hX' : ∀ x ∈ X, r x ∈ Ioo a 1
      · have e1 := H_iff_Block G v a X hvX r ha1 hX'
        have e2 := Adm_iff G v X hvX r (fun x hx => (hX' x hx).2)
        by_cases hB : r ∈ Block G v a X
        · by_cases hA : r ∈ AdmX G v X
          · rw [if_pos ⟨e1.2 hB, e2.2 hA⟩, Set.indicator_of_mem hA, Set.indicator_of_mem hB,
              ENNReal.ofReal_prod_of_nonneg (fun x _ => h0 _)]
            simp
          · rw [if_neg (fun h => hA (e2.1 h.2)), Set.indicator_of_notMem hA]; simp
        · rw [if_neg (fun h => hB (e1.1 h.1)), Set.indicator_of_notMem hB]; simp
      · push Not at hX'
        obtain ⟨x, hx, hxn⟩ := hX'
        have hz : ∏ x ∈ X, ψ (r x) = 0 := Finset.prod_eq_zero hx (hs _ hxn)
        have hz' : ∏ x ∈ X, ENNReal.ofReal (ψ (r x)) = 0 :=
          Finset.prod_eq_zero hx (by rw [hs _ hxn]; simp)
        split_ifs <;> simp [hz, hz']
    have hfac := lintegral_mul_blocks (fun _ => volume.restrict (Ioo (0 : ℝ) 1)) X g h hgm hhm hgS hhS
    have hfac' := lintegral_mul_blocks (fun _ => volume.restrict (Ioo (0 : ℝ) 1)) X g' h hg'm hhm
      hg'S hhS
    have htr := transport_le ψ a ha ha1 hm h0 hs hint hb X (AdmX G v X) (ValidX G v X)
      (measurableSet_AdmX G v X) (measurableSet_ValidX G v X) (by
        intro r s hrs
        simp only [AdmX, ValidX, Set.mem_ofPred_eq]
        apply forall₂_congr; intro u hu
        apply exists_congr; intro z
        apply and_congr_right; intro hz
        apply and_congr_right; intro _
        rcases Finset.mem_insert.1 hz with e | e
        · simp [e]
        · rw [hrs u hu z e])
    have hEX : rankLaw n (EX G v a X) = ∫⁻ r, g' r * h r ∂rankLaw n := by
      rw [← lintegral_indicator_one (measurableSet_EX G v a X)]
      apply lintegral_congr; intro r
      simp only [hg', hh, EX]
      by_cases h1 : r ∈ {r : Fin n → ℝ | ∀ x ∈ X, r x ≤ a} ∩ ValidX G v X
      · by_cases h2 : r ∈ Block G v a X
        · rw [Set.indicator_of_mem (Set.mem_inter h1 h2), Set.indicator_of_mem h1,
            Set.indicator_of_mem h2]; simp
        · rw [Set.indicator_of_notMem (fun h => h2 h.2), Set.indicator_of_notMem h2]; simp
      · rw [Set.indicator_of_notMem (fun h => h1 h.1), Set.indicator_of_notMem h1]; simp
    calc ∫⁻ r, ENNReal.ofReal (TX G v a ψ X r) ∂rankLaw n = ∫⁻ r, g r * h r ∂rankLaw n :=
          lintegral_congr hpt
      _ = (∫⁻ r, g r ∂rankLaw n) * ∫⁻ r, h r ∂rankLaw n := hfac
      _ ≤ (∫⁻ r, g' r ∂rankLaw n) * ∫⁻ r, h r ∂rankLaw n := by
          have : ∫⁻ r, g r ∂rankLaw n ≤ ∫⁻ r, g' r ∂rankLaw n := by
            simp only [hg']
            rw [lintegral_indicator_one ((measurableSet_le_a a X).inter (measurableSet_ValidX G v X))]
            exact htr
          exact mul_le_mul_of_nonneg_right this (zero_le)
      _ = rankLaw n (EX G v a X) := by rw [hEX]; exact hfac'.symm
  calc ∑ X ∈ (Finset.univ.erase v).powerset, ∫⁻ r, ENNReal.ofReal (TX G v a ψ X r) ∂rankLaw n
      ≤ ∑ X ∈ (Finset.univ.erase v).powerset, rankLaw n (EX G v a X) := Finset.sum_le_sum hterm
    _ = ∑ X ∈ (Finset.univ.erase v).powerset,
          rankLaw n (EX G v a X ∩ {r | Function.Injective r}) := by
        apply Finset.sum_congr rfl; intro X _
        symm
        apply measure_inter_conull
        have := ae_rank_inj (n := n)
        rw [ae_iff] at this
        exact this
    _ = rankLaw n (⋃ X ∈ (Finset.univ.erase v).powerset,
          EX G v a X ∩ {r | Function.Injective r}) := by
        rw [measure_biUnion_finset]
        · intro X hX Y hY hXY
          simp only [Function.onFun]
          rw [Set.disjoint_left]
          intro r h1 h2
          have hvX : v ∉ X := fun h => by simpa using Finset.mem_powerset.1 hX h
          have hvY : v ∉ Y := fun h => by simpa using Finset.mem_powerset.1 hY h
          exact EX_disjoint G v a ha1 X Y hvX hvY hXY r h1.2 h1.1 h2.1
        · intro X _; exact (measurableSet_EX G v a X).inter measurableSet_inj
    _ ≤ 1 := prob_le_one

end L37
end LPM


-- ===== Solutions.LPM.L37f =====

set_option autoImplicit false

namespace LPM
namespace L37
open MeasureTheory ProbabilityTheory Set LocalProbeMIS871.Greedy
open scoped ENNReal Classical

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (a : ℝ)

theorem weightValue_eq_indicator (ψ : ℝ → ℝ) : weightValue a ψ = (Ioo a 1).indicator ψ := by
  funext z; unfold weightValue; simp [Set.indicator_apply]

theorem Z_eq_sum (ψ : ℝ → ℝ) (r : Fin n → ℝ) :
    Z G v a ψ r = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      if S ⊆ H G r a ∧ v ∈ S ∧ Adm G v r S then omega v r a ψ S else 0 := by
  unfold Z
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    exact ⟨Finset.subset_univ _, hS.1, hS.2⟩
  · intro S hS2 hS1
    exfalso; apply hS1
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS2 ⊢
    exact ⟨hS2.2.1, hS2.2.2.1, hS2.2.2.2⟩

theorem measurable_Z (ψ : ℝ → ℝ) (hm : Measurable ψ) : Measurable (Z G v a ψ) := by
  have : Z G v a ψ = fun r => ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      if S ⊆ H G r a ∧ v ∈ S ∧ Adm G v r S then omega v r a ψ S else 0 := by
    funext r; exact Z_eq_sum G v a ψ r
  rw [this]
  apply Finset.measurable_sum; intro S _
  have h1 : MeasurableSet {r : Fin n → ℝ | S ⊆ H G r a} := by
    have : {r : Fin n → ℝ | S ⊆ H G r a} = ⋂ u ∈ S, {r | a < tau G r u} := by
      ext r; simp [Finset.subset_iff, H]
    rw [this]
    exact Finset.measurableSet_biInter _ (fun u _ =>
      measurableSet_lt measurable_const (measurable_tau G u))
  have h3 : MeasurableSet {r : Fin n → ℝ | Adm G v r S} := by
    have : {r : Fin n → ℝ | Adm G v r S} = ⋂ u ∈ S.erase v, ⋃ z ∈ S,
        {r : Fin n → ℝ | G.Adj u z ∧ r u < r z} := by
      ext r; simp only [Adm, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
    rw [this]
    refine Finset.measurableSet_biInter _ (fun u _ => Finset.measurableSet_biUnion _ (fun z _ => ?_))
    by_cases h : G.Adj u z
    · simp only [h, true_and]
      exact measurableSet_lt (measurable_pi_apply u) (measurable_pi_apply z)
    · simp [h]
  have h2 : MeasurableSet {r : Fin n → ℝ | v ∈ S} := MeasurableSet.const _
  apply Measurable.ite (h1.inter (h2.inter h3))
  · unfold omega
    apply Finset.measurable_prod; intro u _
    rw [weightValue_eq_indicator]
    exact (hm.indicator measurableSet_Ioo).comp (measurable_pi_apply u)
  · exact measurable_const

theorem Z_congr (ψ ψ' : ℝ → ℝ) (r : Fin n → ℝ)
    (h : ∀ u, u ≠ v → weightValue a ψ (r u) = weightValue a ψ' (r u)) :
    Z G v a ψ r = Z G v a ψ' r := by
  unfold Z omega
  apply Finset.sum_congr rfl; intro S _
  apply Finset.prod_congr rfl; intro u hu
  exact h u (Finset.ne_of_mem_erase hu)

theorem part13 (ha : 0 < a ∧ a < 1) (ψ : ℝ → ℝ) (hψ : Weight a ψ)
    (hb : (∫ z in Set.Ioo a 1, ψ z) ≤ a) :
    AEMeasurable (Z G v a ψ) (forcedLaw v) ∧
      (∫⁻ r, ENNReal.ofReal (Z G v a ψ r) ∂forcedLaw v) ≤ 1 := by
  obtain ⟨hψ0, hψi⟩ := hψ
  set ψ1 := weightValue a ψ with hψ1
  have hψ1e : ψ1 = (Ioo a 1).indicator ψ := weightValue_eq_indicator a ψ
  have hint1 : Integrable ψ1 := by rw [hψ1e]; exact hψi.integrable_indicator measurableSet_Ioo
  set ψm := hint1.aestronglyMeasurable.mk ψ1 with hψm
  have hψmm : Measurable ψm := hint1.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hψme : ψm =ᵐ[volume] ψ1 := hint1.aestronglyMeasurable.ae_eq_mk.symm
  set ψc : ℝ → ℝ := (Ioo a 1).indicator (fun z => max (ψm z) 0) with hψc
  have hψcm : Measurable ψc := (hψmm.max measurable_const).indicator measurableSet_Ioo
  have hψc0 : ∀ z, 0 ≤ ψc z := by
    intro z; simp only [hψc, Set.indicator_apply]; split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  have hψcs : ∀ z, z ∉ Ioo a 1 → ψc z = 0 := by
    intro z hz; simp [hψc, Set.indicator_of_notMem hz]
  have hψce : ψc =ᵐ[volume] ψ1 := by
    filter_upwards [hψme] with z hz
    simp only [hψc, Set.indicator_apply]
    split_ifs with h
    · rw [hz, hψ1e, Set.indicator_of_mem h]; exact max_eq_left (hψ0 z h)
    · rw [hψ1e, Set.indicator_of_notMem h]
  have hintc : Integrable ψc := hint1.congr hψce.symm
  have hbc : ∫ y, ψc y ≤ a := by
    rw [integral_congr_ae hψce, hψ1e, integral_indicator measurableSet_Ioo]; exact hb
  -- null set
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (μ := volume)
    (s := {z | ψ1 z ≠ ψc z}) (by
      have := hψce
      rw [Filter.EventuallyEq, ae_iff] at this
      simpa [eq_comm] using this)
  have hgood : ∀ᵐ r ∂forcedLaw v, ∀ u, u ≠ v → r u ∉ N := by
    have hm : MeasurableSet {r : Fin n → ℝ | ∀ u, u ≠ v → r u ∉ N} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun u => MeasurableSet.iInter (fun _ =>
        (measurable_pi_apply u hNm).compl))
    rw [forcedLaw, ae_map_iff (measurable_forceRoot v).aemeasurable hm]
    have : ∀ᵐ r ∂rankLaw n, ∀ u, r u ∉ N := by
      apply Filter.eventually_all.mpr; intro u
      rw [ae_iff]
      simp only [not_not]
      have : {a : Fin n → ℝ | a u ∈ N} = Function.eval u ⁻¹' N := rfl
      rw [this, rankLaw]
      apply Measure.pi_eval_preimage_null
      rw [Measure.restrict_apply hNm]; exact measure_mono_null Set.inter_subset_left hN0
    filter_upwards [this] with r hr u hu
    simpa [forceRoot, Function.update_of_ne hu] using hr u
  have hZe : Z G v a ψ =ᵐ[forcedLaw v] Z G v a ψc := by
    filter_upwards [hgood] with r hr
    apply Z_congr
    intro u hu
    rw [weightValue_eq a ψc hψcs]
    have : r u ∉ {z | ψ1 z ≠ ψc z} := fun h => hr u hu (hNsub h)
    simp only [Set.mem_ofPred_eq, not_not] at this
    exact this
  have hZcm := measurable_Z G v a ψc hψcm
  refine ⟨hZcm.aemeasurable.congr hZe.symm, ?_⟩
  have hcongr : (fun r => ENNReal.ofReal (Z G v a ψ r)) =ᵐ[forcedLaw v]
      (fun r => ENNReal.ofReal (Z G v a ψc r)) := hZe.mono (fun r hr => by simp only [hr])
  rw [lintegral_congr_ae hcongr]
  rw [forcedLaw, lintegral_map (f := fun r => ENNReal.ofReal (Z G v a ψc r))
    (ENNReal.measurable_ofReal.comp hZcm) (measurable_forceRoot v)]
  exact core G v a ψc hψcm hψc0 hψcs hintc hbc ha.1 ha.2

theorem part14 (ψ : ℝ → ℝ) (hψ : Weight a ψ) (r : Fin n → ℝ) (S B : Finset (Fin n))
    (hSH : S ⊆ H G r a) (hvS : v ∈ S) (hadm : Adm G v r S) (hBH : B ⊆ H G r a \ S)
    (hB : ∀ u ∈ B, ∃ z ∈ S, G.Adj u z ∧ r u < r z) :
    omega v r a ψ S * (∏ u ∈ B, (1 + weightValue a ψ (r u))) ≤ Z G v a ψ r := by
  have hw0 : ∀ z, 0 ≤ weightValue a ψ z := by
    intro z; unfold weightValue; split_ifs with h
    · exact hψ.1 z h
    · exact le_rfl
  have hdisj : Disjoint S B := by
    rw [Finset.disjoint_right]; intro u hu huS
    have := hBH hu; simp at this; exact this.2 huS
  have hvB : v ∉ B := fun h => Finset.disjoint_left.1 hdisj hvS h
  have hω : ∀ B' ⊆ B, omega v r a ψ (S ∪ B') = omega v r a ψ S * ∏ u ∈ B', weightValue a ψ (r u) := by
    intro B' hB'
    unfold omega
    have : (S ∪ B').erase v = S.erase v ∪ B' := by
      rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem (fun h => hvB (hB' h))]
    rw [this, Finset.prod_union]
    rw [Finset.disjoint_left]; intro u hu hu'
    exact Finset.disjoint_left.1 hdisj (Finset.mem_of_mem_erase hu) (hB' hu')
  calc omega v r a ψ S * (∏ u ∈ B, (1 + weightValue a ψ (r u)))
      = ∑ B' ∈ B.powerset, omega v r a ψ (S ∪ B') := by
        rw [Finset.prod_one_add, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro B' hB'
        rw [hω B' (Finset.mem_powerset.1 hB')]
    _ = ∑ S' ∈ B.powerset.image (fun B' => S ∪ B'), omega v r a ψ S' := by
        rw [Finset.sum_image]
        intro B1 h1 B2 h2 he
        have h1' := Finset.mem_powerset.1 h1
        have h2' := Finset.mem_powerset.1 h2
        ext u
        constructor
        · intro hu
          have : u ∈ S ∪ B2 := by
            have h' : u ∈ S ∪ B1 := Finset.mem_union_right S hu
            simp only at he; rw [he] at h'; exact h'
          rcases Finset.mem_union.1 this with h | h
          · exact absurd h (Finset.disjoint_right.1 hdisj (h1' hu))
          · exact h
        · intro hu
          have : u ∈ S ∪ B1 := by
            have h' : u ∈ S ∪ B2 := Finset.mem_union_right S hu
            simp only at he; rw [← he] at h'; exact h'
          rcases Finset.mem_union.1 this with h | h
          · exact absurd h (Finset.disjoint_right.1 hdisj (h2' hu))
          · exact h
    _ ≤ Z G v a ψ r := by
        unfold Z
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro S' hS'
          obtain ⟨B', hB', rfl⟩ := Finset.mem_image.1 hS'
          have hB'' := Finset.mem_powerset.1 hB'
          simp only [Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.union_subset hSH (fun u hu => (Finset.mem_sdiff.1 (hBH (hB'' hu))).1),
            Finset.mem_union_left _ hvS, ?_⟩
          intro u hu
          have hu' := Finset.mem_of_mem_erase hu
          rcases Finset.mem_union.1 hu' with h | h
          · obtain ⟨z, hz, h1, h2⟩ := hadm u (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hu, h⟩)
            exact ⟨z, Finset.mem_union_left _ hz, h1, h2⟩
          · obtain ⟨z, hz, h1, h2⟩ := hB u (hB'' h)
            exact ⟨z, Finset.mem_union_left _ hz, h1, h2⟩
        · intro S' _ _
          unfold omega
          exact Finset.prod_nonneg (fun u _ => hw0 _)

theorem lemma_3_7_proof (a : ℝ) (ha : 0 < a ∧ a < 1) (ψ : ℝ → ℝ) (hψ : Weight a ψ) :
    ((∫ z in Set.Ioo a 1, ψ z) ≤ a →
      AEMeasurable (Z G v a ψ) (forcedLaw v) ∧
      (∫⁻ r, ENNReal.ofReal (Z G v a ψ r) ∂forcedLaw v) ≤ 1) ∧
    (∀ r, GoodRanks v r → ∀ S B : Finset (Fin n),
      S ⊆ H G r a → v ∈ S → Adm G v r S →
      B ⊆ H G r a \ S →
      (∀ u ∈ B, ∃ z ∈ S, G.Adj u z ∧ r u < r z) →
      omega v r a ψ S * (∏ u ∈ B, (1 + weightValue a ψ (r u))) ≤ Z G v a ψ r) :=
  ⟨fun hb => part13 G v a ha ψ hψ hb,
   fun r _ S B h1 h2 h3 h4 h5 => part14 G v a ψ hψ r S B h1 h2 h3 h4 h5⟩

end L37
end LPM


open MeasureTheory
open scoped BigOperators Classical
noncomputable section
open LocalProbeMIS871.Greedy

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (a : ℝ) (ha : 0 < a ∧ a < 1) (ψ : ℝ → ℝ) (hψ : Weight a ψ) :
    ((∫ z in Set.Ioo a 1, ψ z) ≤ a →
      AEMeasurable (Z G v a ψ) (forcedLaw v) ∧
      (∫⁻ r, ENNReal.ofReal (Z G v a ψ r) ∂forcedLaw v) ≤ 1) ∧
    (∀ r, GoodRanks v r → ∀ S B : Finset (Fin n),
      S ⊆ H G r a → v ∈ S → Adm G v r S →
      B ⊆ H G r a \ S →
      (∀ u ∈ B, ∃ z ∈ S, G.Adj u z ∧ r u < r z) →
      omega v r a ψ S * (∏ u ∈ B, (1 + weightValue a ψ (r u))) ≤ Z G v a ψ r) :=
  LPM.L37.lemma_3_7_proof G v a ha ψ hψ

