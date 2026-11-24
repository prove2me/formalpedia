-- Prove2me | solution 1 for LocalProbeMIS871.Greedy.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:18:26.067674+00:00
-- url     : https://prove2.me/submissions/39923246-3bb4-4fbe-b2ed-27c97e3cb86c

import Definitions.Def_LocalProbeMIS871_Greedy_Elimination
import Theorems.Thm_LocalProbeMIS871_Greedy_theorem_3_1

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


-- ===== Solutions.LPM.T11 =====

set_option autoImplicit false

namespace LPM
open LocalProbeMIS871.Greedy MeasureTheory
open scoped Classical

instance rankLaw_isProb (n : ℕ) : IsProbabilityMeasure (rankLaw n) := by
  have : ∀ _ : Fin n, IsProbabilityMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    fun _ => ⟨by simp [Real.volume_Ioo]⟩
  unfold rankLaw
  infer_instance

theorem theorem_1_1_proof : ∃ C : ℝ, 0 < C ∧
    ∀ (n Δ : ℕ), 2 ≤ Δ → ∀ G : SimpleGraph (Fin n), (∀ u, G.degree u ≤ Δ) →
    ∀ lists : AdjacencyLists G, ∀ δ : ℝ, 0 < δ → δ < 1 →
      ENNReal.ofReal (1 - δ) ≤ rankLaw n {r |
        (∀ v, (execution G r v).1 = decide (v ∈ I G r)) ∧
        (∀ u ∈ I G r, ∀ z ∈ I G r, ¬ G.Adj u z) ∧
        (∀ u, u ∉ I G r → ∃ z ∈ I G r, G.Adj u z) ∧
        (if n = 0 then True else ∀ v,
          (Q G lists v r : ℝ) ≤ C * (Δ : ℝ) ^ (6 : ℕ) * (1 + Real.log ((n : ℝ) / δ)))} := by
  obtain ⟨C, hC, h31⟩ := theorem_3_1
  refine ⟨C, hC, ?_⟩
  intro n Δ hΔ G hdeg lists δ hδ0 hδ1
  by_cases hn : n = 0
  · have : {r : Fin n → ℝ |
        (∀ v, (execution G r v).1 = decide (v ∈ I G r)) ∧
        (∀ u ∈ I G r, ∀ z ∈ I G r, ¬ G.Adj u z) ∧
        (∀ u, u ∉ I G r → ∃ z ∈ I G r, G.Adj u z) ∧
        (if n = 0 then True else ∀ v,
          (Q G lists v r : ℝ) ≤ C * (Δ : ℝ) ^ (6 : ℕ) * (1 + Real.log ((n : ℝ) / δ)))} =
        Set.univ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨fun v => execution_correct G r v, I_indep G r, I_maximal G r, by simp [hn]⟩
    rw [this, measure_univ]
    exact ENNReal.ofReal_le_one.2 (by linarith)
  · set ell := Real.log ((n : ℝ) / δ) with hell
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    have hell0 : 0 ≤ ell := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hδ0]; linarith
    set B : Set (Fin n → ℝ) :=
      ⋃ v : Fin n, {r | C * (Δ : ℝ) ^ (6 : ℕ) * (1 + ell) < (Q G lists v r : ℝ)} with hB
    have hBle : rankLaw n B ≤ ENNReal.ofReal δ := by
      calc rankLaw n B ≤ ∑ v : Fin n,
            rankLaw n {r | C * (Δ : ℝ) ^ (6 : ℕ) * (1 + ell) < (Q G lists v r : ℝ)} :=
            measure_iUnion_fintype_le _ _
        _ ≤ ∑ _v : Fin n, ENNReal.ofReal (Real.exp (-ell)) := by
            apply Finset.sum_le_sum; intro v _
            exact h31 n Δ hΔ G hdeg lists v ell hell0
        _ = ENNReal.ofReal δ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            have : Real.exp (-ell) = δ / n := by
              rw [hell, Real.exp_neg, Real.exp_log (by positivity)]
              field_simp
            rw [this, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            field_simp
    have hsub : Bᶜ ⊆ {r : Fin n → ℝ |
        (∀ v, (execution G r v).1 = decide (v ∈ I G r)) ∧
        (∀ u ∈ I G r, ∀ z ∈ I G r, ¬ G.Adj u z) ∧
        (∀ u, u ∉ I G r → ∃ z ∈ I G r, G.Adj u z) ∧
        (if n = 0 then True else ∀ v,
          (Q G lists v r : ℝ) ≤ C * (Δ : ℝ) ^ (6 : ℕ) * (1 + Real.log ((n : ℝ) / δ)))} := by
      intro r hr
      simp only [hB, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists,
        not_lt] at hr
      simp only [Set.mem_ofPred_eq]
      refine ⟨fun v => execution_correct G r v, I_indep G r, I_maximal G r, ?_⟩
      simp only [hn, if_false]
      exact hr
    calc ENNReal.ofReal (1 - δ) = 1 - ENNReal.ofReal δ := by
          rw [ENNReal.ofReal_sub _ hδ0.le, ENNReal.ofReal_one]
      _ ≤ 1 - rankLaw n B := tsub_le_tsub_left hBle _
      _ ≤ rankLaw n Bᶜ := by
          rw [tsub_le_iff_right]
          calc (1 : ENNReal) = rankLaw n Set.univ := measure_univ.symm
            _ = rankLaw n (Bᶜ ∪ B) := by rw [Set.compl_union_self]
            _ ≤ rankLaw n Bᶜ + rankLaw n B := measure_union_le _ _
      _ ≤ _ := measure_mono hsub

end LPM



open MeasureTheory
open scoped BigOperators Classical
noncomputable section
open LocalProbeMIS871.Greedy

theorem solution : ∃ C : ℝ, 0 < C ∧
    ∀ (n Δ : ℕ), 2 ≤ Δ → ∀ G : SimpleGraph (Fin n), (∀ u, G.degree u ≤ Δ) →
    ∀ lists : AdjacencyLists G, ∀ δ : ℝ, 0 < δ → δ < 1 →
      ENNReal.ofReal (1 - δ) ≤ rankLaw n {r |
        (∀ v, (execution G r v).1 = decide (v ∈ I G r)) ∧
        (∀ u ∈ I G r, ∀ z ∈ I G r, ¬ G.Adj u z) ∧
        (∀ u, u ∉ I G r → ∃ z ∈ I G r, G.Adj u z) ∧
        (if n = 0 then True else ∀ v,
          (Q G lists v r : ℝ) ≤ C * (Δ : ℝ) ^ (6 : ℕ) * (1 + Real.log ((n : ℝ) / δ)))} :=
  LPM.theorem_1_1_proof

