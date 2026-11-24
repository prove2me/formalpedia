-- Prove2me | solution 1 for LocalProbeMIS871.Greedy.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T02:52:39.093963+00:00
-- url     : https://prove2.me/submissions/69e1f2be-86e3-4338-a9c7-6e07a7440052

import Definitions.Def_LocalProbeMIS871_Greedy_Elimination
import Mathlib
import Theorems.Thm_LocalProbeMIS871_Greedy_lemma_3_7
import Theorems.Thm_LocalProbeMIS871_Greedy_lemma_A_1

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


-- ===== Solutions.LPM.Calc =====

set_option autoImplicit false

namespace LPM
open MeasureTheory Set intervalIntegral Real

theorem cont_pow_mul_log (k : ℕ) : Continuous (fun x : ℝ => x ^ (k + 1) * Real.log x) := by
  have : (fun x : ℝ => x ^ (k + 1) * Real.log x) = fun x => x ^ k * (x * Real.log x) := by
    funext x; ring
  rw [this]
  exact (continuous_pow k).mul continuous_mul_log

/-- ∫₀ᶜ λ⁴ log(1/λ) dλ -/
theorem integral_pow4_log_inv (c : ℝ) (hc : 0 < c) :
    ∫ x in (0 : ℝ)..c, x ^ 4 * (-Real.log x) = c ^ 5 * (-Real.log c) / 5 + c ^ 5 / 25 := by
  have hF : ∀ x ∈ Ioo (0 : ℝ) c, HasDerivAt (fun x : ℝ => x ^ 5 * (-Real.log x) / 5 + x ^ 5 / 25)
      (x ^ 4 * (-Real.log x)) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have h1 := ((hasDerivAt_pow 5 x).mul (Real.hasDerivAt_log hx0).neg).div_const 5
    have h2 := (hasDerivAt_pow 5 x).div_const 25
    refine (h1.add h2).congr_deriv ?_
    simp only [Pi.neg_apply]
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => x ^ 5 * (-Real.log x) / 5 + x ^ 5 / 25) (Icc 0 c) := by
    have : (fun x : ℝ => x ^ 5 * (-Real.log x) / 5 + x ^ 5 / 25) =
        fun x => -(x ^ (4 + 1) * Real.log x) / 5 + x ^ 5 / 25 := by funext x; ring
    rw [this]
    exact (((cont_pow_mul_log 4).neg.div_const 5).add ((continuous_pow 5).div_const 25)).continuousOn
  have hint : IntervalIntegrable (fun x : ℝ => x ^ 4 * (-Real.log x)) volume 0 c := by
    have : (fun x : ℝ => x ^ 4 * (-Real.log x)) = fun x => -(x ^ (3 + 1) * Real.log x) := by
      funext x; ring
    rw [this]
    exact ((cont_pow_mul_log 3).neg).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt_of_le hc.le hcont hF hint]
  simp

/-- ∫_τ^ρ t⁴ (5 log(t/τ) + 1) dt = ρ⁵ log(ρ/τ) -/
theorem integral_pow4_log_ratio (τ ρ : ℝ) (hτ : 0 < τ) (hτρ : τ ≤ ρ) :
    ∫ t in τ..ρ, t ^ 4 * (5 * (Real.log t - Real.log τ) + 1) =
      ρ ^ 5 * (Real.log ρ - Real.log τ) := by
  have hF : ∀ x ∈ Ioo τ ρ, HasDerivAt (fun t : ℝ => t ^ 5 * (Real.log t - Real.log τ))
      (x ^ 4 * (5 * (Real.log x - Real.log τ) + 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans hτ hx.1)
    have h1 := (hasDerivAt_pow 5 x).mul ((Real.hasDerivAt_log hx0).sub_const (Real.log τ))
    refine h1.congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn (fun t : ℝ => t ^ 5 * (Real.log t - Real.log τ)) (Icc τ ρ) := by
    apply ContinuousOn.mul (continuous_pow 5).continuousOn
    apply ContinuousOn.sub _ continuousOn_const
    exact Real.continuousOn_log.mono (fun x hx => ne_of_gt (lt_of_lt_of_le hτ hx.1))
  have hint : IntervalIntegrable (fun t : ℝ => t ^ 4 * (5 * (Real.log t - Real.log τ) + 1))
      volume τ ρ := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul (continuous_pow 4).continuousOn
    apply ContinuousOn.add _ continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.sub _ continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    rw [uIcc_of_le hτρ] at hx
    exact ne_of_gt (lt_of_lt_of_le hτ hx.1)
  rw [integral_eq_sub_of_hasDerivAt_of_le hτρ hcont hF hint]
  simp

/-- ∫₀^τ 25 t⁴ log(ρ/t) dt = 5τ⁵ log(ρ/τ) + τ⁵ -/
theorem integral_pow4_log_rho (τ ρ : ℝ) (hτ : 0 < τ) :
    ∫ t in (0 : ℝ)..τ, 25 * t ^ 4 * (Real.log ρ - Real.log t) =
      5 * τ ^ 5 * (Real.log ρ - Real.log τ) + τ ^ 5 := by
  have hF : ∀ x ∈ Ioo (0 : ℝ) τ, HasDerivAt
      (fun t : ℝ => 5 * t ^ 5 * (Real.log ρ - Real.log t) + t ^ 5)
      (25 * x ^ 4 * (Real.log ρ - Real.log x)) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have h1 := (((hasDerivAt_pow 5 x).const_mul 5).mul
      ((Real.hasDerivAt_log hx0).const_sub (Real.log ρ))).add (hasDerivAt_pow 5 x)
    refine h1.congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn (fun t : ℝ => 5 * t ^ 5 * (Real.log ρ - Real.log t) + t ^ 5)
      (Icc 0 τ) := by
    have : (fun t : ℝ => 5 * t ^ 5 * (Real.log ρ - Real.log t) + t ^ 5) =
        fun t => 5 * Real.log ρ * t ^ 5 - 5 * (t ^ (4 + 1) * Real.log t) + t ^ 5 := by
      funext t; ring
    rw [this]
    exact ((((continuous_pow 5).const_mul _).sub ((cont_pow_mul_log 4).const_mul 5)).add
      (continuous_pow 5)).continuousOn
  have hint : IntervalIntegrable (fun t : ℝ => 25 * t ^ 4 * (Real.log ρ - Real.log t))
      volume 0 τ := by
    have : (fun t : ℝ => 25 * t ^ 4 * (Real.log ρ - Real.log t)) =
        fun t => 25 * Real.log ρ * t ^ 4 - 25 * (t ^ (3 + 1) * Real.log t) := by
      funext t; ring
    rw [this]
    exact (((continuous_pow 4).const_mul _).sub ((cont_pow_mul_log 3).const_mul 25)).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt_of_le hτ.le hcont hF hint]
  simp

theorem integral_5pow4 (τ : ℝ) : ∫ t in (0 : ℝ)..τ, 5 * t ^ 4 = τ ^ 5 := by
  rw [intervalIntegral.integral_const_mul, integral_pow]
  ring

end LPM


-- ===== Solutions.LPM.Jensen =====

set_option autoImplicit false

namespace LPM
open MeasureTheory Function
open scoped ENNReal NNReal

theorem jensen_lint {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω] (μ : Measure Θ)
    [SFinite μ] (P : Measure Ω) [SFinite P]
    (φ : Θ → ℝ≥0) (hφ : Measurable φ) (hφ1 : ∫⁻ θ, (φ θ : ℝ≥0∞) ∂μ = 1)
    (Λ : Θ → Ω → ℝ) (hΛ : Measurable (uncurry Λ)) (K : ℝ)
    (hΛK : ∀ᵐ θ ∂μ, ∀ ω, 0 ≤ Λ θ ω ∧ Λ θ ω ≤ K)
    (hb : ∀ᵐ θ ∂μ, ∫⁻ ω, ENNReal.ofReal (Real.exp (Λ θ ω)) ∂P ≤ 2) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (∫ θ, (φ θ : ℝ) * Λ θ ω ∂μ)) ∂P ≤ 2 := by
  set ν := μ.withDensity (fun θ => (φ θ : ℝ≥0∞)) with hν
  have hνprob : IsProbabilityMeasure ν := ⟨by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hφ1]⟩
  have hmθ : ∀ ω, Measurable (fun θ => Λ θ ω) := fun ω => hΛ.comp (measurable_prodMk_right)
  have hmω : ∀ θ, Measurable (fun ω => Λ θ ω) := fun θ => hΛ.comp (measurable_prodMk_left)
  have hint : ∀ ω, Integrable (fun θ => Λ θ ω) ν := by
    intro ω
    refine Integrable.mono' (integrable_const K) (hmθ ω).aestronglyMeasurable ?_
    refine (withDensity_absolutelyContinuous μ _).ae_le ?_
    filter_upwards [hΛK] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (hθ ω).1]; exact (hθ ω).2
  have hinte : ∀ ω, Integrable (fun θ => Real.exp (Λ θ ω)) ν := by
    intro ω
    refine Integrable.mono' (integrable_const (Real.exp K))
      (Real.measurable_exp.comp (hmθ ω)).aestronglyMeasurable ?_
    refine (withDensity_absolutelyContinuous μ _).ae_le ?_
    filter_upwards [hΛK] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (hθ ω).2
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (∫ θ, (φ θ : ℝ) * Λ θ ω ∂μ)) ≤
      ∫⁻ θ, (φ θ : ℝ≥0∞) * ENNReal.ofReal (Real.exp (Λ θ ω)) ∂μ := by
    intro ω
    have e1 : ∫ θ, (φ θ : ℝ) * Λ θ ω ∂μ = ∫ θ, Λ θ ω ∂ν := by
      rw [hν, integral_withDensity_eq_integral_smul hφ]
      rfl
    rw [e1]
    have hj := ConvexOn.map_integral_le (μ := ν) (s := Set.univ) (g := Real.exp)
      (f := fun θ => Λ θ ω) convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) (hint ω) (hinte ω)
    calc ENNReal.ofReal (Real.exp (∫ θ, Λ θ ω ∂ν))
        ≤ ENNReal.ofReal (∫ θ, Real.exp (Λ θ ω) ∂ν) := ENNReal.ofReal_le_ofReal hj
      _ = ∫⁻ θ, ENNReal.ofReal (Real.exp (Λ θ ω)) ∂ν :=
          ofReal_integral_eq_lintegral_ofReal (hinte ω)
            (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
      _ = ∫⁻ θ, (φ θ : ℝ≥0∞) * ENNReal.ofReal (Real.exp (Λ θ ω)) ∂μ := by
          rw [hν, lintegral_withDensity_eq_lintegral_mul μ (f := fun θ => (φ θ : ℝ≥0∞))
            (measurable_coe_nnreal_ennreal.comp hφ)
            (g := fun θ => ENNReal.ofReal (Real.exp (Λ θ ω)))
            (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hmθ ω)))]
          rfl
  have hjoint : Measurable (uncurry fun ω θ => (φ θ : ℝ≥0∞) * ENNReal.ofReal (Real.exp (Λ θ ω))) := by
    have h1 : Measurable (fun p : Ω × Θ => (φ p.2 : ℝ≥0∞)) :=
      measurable_coe_nnreal_ennreal.comp (hφ.comp measurable_snd)
    have h2 : Measurable (fun p : Ω × Θ => Λ p.2 p.1) := hΛ.comp measurable_swap
    exact h1.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp h2))
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (∫ θ, (φ θ : ℝ) * Λ θ ω ∂μ)) ∂P
      ≤ ∫⁻ ω, ∫⁻ θ, (φ θ : ℝ≥0∞) * ENNReal.ofReal (Real.exp (Λ θ ω)) ∂μ ∂P := lintegral_mono hpt
    _ = ∫⁻ θ, ∫⁻ ω, (φ θ : ℝ≥0∞) * ENNReal.ofReal (Real.exp (Λ θ ω)) ∂P ∂μ :=
        lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ θ, (φ θ : ℝ≥0∞) * ∫⁻ ω, ENNReal.ofReal (Real.exp (Λ θ ω)) ∂P ∂μ := by
        apply lintegral_congr; intro θ
        exact lintegral_const_mul _ (f := fun ω => ENNReal.ofReal (Real.exp (Λ θ ω)))
          (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hmω θ)))
    _ ≤ ∫⁻ θ, (φ θ : ℝ≥0∞) * 2 ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hb] with θ hθ
        exact mul_le_mul_of_nonneg_left hθ zero_le
    _ = 2 := by
        rw [lintegral_mul_const (f := fun θ => (φ θ : ℝ≥0∞)) _
          (measurable_coe_nnreal_ennreal.comp hφ), hφ1, one_mul]

end LPM


-- ===== Solutions.LPM.L32b =====

set_option autoImplicit false

namespace LPM
namespace L32
open MeasureTheory Set LocalProbeMIS871.Greedy
open scoped Classical

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)

noncomputable def w1 (t : ℝ) : ℝ → ℝ := fun z => 4 * (t / z) ^ 5
noncomputable def w2 (lam t : ℝ) : ℝ → ℝ := fun z => if t < z then 4 * lam * (t / z) ^ 5 else 0

noncomputable def Rv (r : Fin n → ℝ) : Finset (Fin n) := (R G v r).erase v

noncomputable def Pv (t : ℝ) (r : Fin n → ℝ) : Finset (Fin n) :=
  (Rv G v r).filter (fun u => t < tau G r u)

noncomputable def Nc (t : ℝ) (r : Fin n → ℝ) : ℝ := ((Pv G v t r).card : ℝ)

noncomputable def Ep (t : ℝ) (r : Fin n → ℝ) : ℝ :=
  ∑ u ∈ Pv G v t r, 5 * (Real.log (r u) - Real.log t)

noncomputable def Bs (lam t : ℝ) (r : Fin n → ℝ) : Finset (Fin n) :=
  (Rv G v r).filter (fun x => lam * t < tau G r x ∧ tau G r x ≤ t ∧ t < r x)

noncomputable def SB (lam t : ℝ) (r : Fin n → ℝ) : ℝ := ∑ x ∈ Bs G v lam t r, (t / r x) ^ 5

noncomputable def Λ1 (t : ℝ) (r : Fin n → ℝ) : ℝ := Real.log (1 + Z G v t (w1 t) r)

noncomputable def Λ2 (lam t : ℝ) (r : Fin n → ℝ) : ℝ :=
  Real.log (1 + Z G v (lam * t) (w2 lam t) r)

/-! ### structure of the evaluated set -/

theorem caller_exists (r : Fin n → ℝ) (hr : GoodRanks v r) (u : Fin n) (hu : u ∈ R G v r)
    (huv : u ≠ v) : ∃ c ∈ R G v r, G.Adj u c ∧ r u < r c ∧ r u ≤ tau G r c := by
  rw [mem_R_iff] at hu
  obtain ⟨c, hc, hcu⟩ := ((Relation.ReflTransGen.cases_tail_iff _ _ _).1 hu).resolve_left
    (fun e => huv e)
  rw [Call, callRel_iff_tau] at hcu
  obtain ⟨hadj, hlt, hle⟩ := hcu
  refine ⟨c, (mem_R_iff G v r c).2 hc, hadj.symm, fst_lt_of_key_lt hr.2.2 hlt, ?_⟩
  have := key_le_fst (r := r) (a := u) (b := tauV G r c) (by rw [← tauKey_eq]; exact hle)
  rw [tau_eq]; exact this

theorem tau_le_r (r : Fin n → ℝ) (u : Fin n) : tau G r u ≤ r u := by
  have h := tau_le_self G (key r) u
  have h2 : key r (tauV G r u) ≤ key r u := by rw [← tauKey_eq]; exact h
  rw [tau_eq]; exact key_le_fst h2

theorem tau_le_root (r : Fin n → ℝ) (hr : GoodRanks v r) (u : Fin n) (hu : u ∈ R G v r) :
    tau G r u ≤ tau G r v := by
  rw [mem_R_iff] at hu
  induction hu with
  | refl => exact le_rfl
  | @tail w u' _ hwu ih =>
    rw [Call, callRel_iff_tau] at hwu
    obtain ⟨_, _, hle⟩ := hwu
    have h1 : r u' ≤ tau G r w := by
      have := key_le_fst (r := r) (a := u') (b := tauV G r w) (by rw [← tauKey_eq]; exact hle)
      rw [tau_eq]; exact this
    linarith [tau_le_r G r u']

theorem r_lt_one (r : Fin n → ℝ) (hr : GoodRanks v r) (u : Fin n) (hu : u ≠ v) : r u < 1 :=
  (hr.2.1 u hu).2

theorem Z_nonneg (a : ℝ) (ψ : ℝ → ℝ) (hψ : ∀ z, 0 ≤ weightValue a ψ z) (r : Fin n → ℝ) :
    0 ≤ Z G v a ψ r := by
  unfold Z omega
  exact Finset.sum_nonneg (fun S _ => Finset.prod_nonneg (fun u _ => hψ _))

theorem wv_w1_nonneg (t : ℝ) (ht : 0 < t) (z : ℝ) : 0 ≤ weightValue t (w1 t) z := by
  unfold weightValue w1; split_ifs with h
  · have : 0 < z := lt_trans ht h.1
    positivity
  · exact le_rfl

theorem wv_w2_nonneg (lam t : ℝ) (hl : 0 < lam) (ht : 0 < t) (z : ℝ) :
    0 ≤ weightValue (lam * t) (w2 lam t) z := by
  unfold weightValue w2; split_ifs with h h'
  · have : 0 < z := lt_trans ht h'
    positivity
  · exact le_rfl
  · exact le_rfl

theorem weight_w1 (t : ℝ) (ht : 0 < t) (ht1 : t < 1) : Weight t (w1 t) := by
  refine ⟨fun z hz => ?_, ?_⟩
  · have : 0 < z := lt_trans ht hz.1
    unfold w1; positivity
  · apply IntegrableOn.mono_set (t := Icc t 1) _ Ioo_subset_Icc_self
    apply ContinuousOn.integrableOn_Icc
    unfold w1
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.pow
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro z hz; exact ne_of_gt (lt_of_lt_of_le ht hz.1)

theorem weight_w2 (lam t : ℝ) (hl : 0 < lam) (hl1 : lam < 1) (ht : 0 < t) (ht1 : t < 1) :
    Weight (lam * t) (w2 lam t) := by
  have hlt : lam * t < t := by nlinarith
  refine ⟨fun z hz => ?_, ?_⟩
  · unfold w2; split_ifs with h
    · have : 0 < z := lt_trans ht h
      positivity
    · exact le_rfl
  · have hb : ∀ z ∈ Ioo (lam * t) 1, |w2 lam t z| ≤ 4 := by
      intro z hz
      unfold w2; split_ifs with h
      · have hz0 : 0 < z := lt_trans ht h
        have h1 : t / z ≤ 1 := (div_le_one hz0).2 h.le
        have h2 : 0 ≤ t / z := by positivity
        have h3 : (t / z) ^ 5 ≤ 1 := pow_le_one₀ h2 h1
        rw [abs_of_nonneg (by positivity)]
        nlinarith
      · simp
    have hmeas : AEStronglyMeasurable (w2 lam t) volume := by
      apply Measurable.aestronglyMeasurable
      unfold w2
      exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
        (measurable_const.mul ((measurable_const.div measurable_id).pow_const 5)) measurable_const
    refine Measure.integrableOn_of_bounded (M := 4) ?_ hmeas ?_
    · simp [Real.volume_Ioo]
    · rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall (fun z hz => by rw [Real.norm_eq_abs]; exact hb z hz)

theorem concave_log (z b : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hb : 0 ≤ b) :
    z * Real.log (1 + b) ≤ Real.log (1 + b * z) := by
  have hc := strictConcaveOn_log_Ioi.concaveOn
  have h1b : (1 + b) ∈ Ioi (0:ℝ) := by simp only [mem_Ioi]; linarith
  have := hc.2 (by norm_num : (1:ℝ) ∈ Ioi 0) h1b (by linarith : (0:ℝ) ≤ 1 - z) hz0 (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at this
  have e : (1 - z) * 1 + z * (1 + b) = 1 + b * z := by ring
  rw [e] at this
  linarith

end L32
end LPM

namespace LPM
namespace L32
open MeasureTheory Set LocalProbeMIS871.Greedy
open scoped Classical

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)

theorem Pv_erase (t : ℝ) (r : Fin n → ℝ) :
    ((R G v r).filter (fun u => t < tau G r u)).erase v = Pv G v t r := by
  ext u; simp only [Pv, Rv, Finset.mem_erase, Finset.mem_filter]; tauto

theorem Pv_sub_H (t : ℝ) (r : Fin n → ℝ) :
    (R G v r).filter (fun u => t < tau G r u) ⊆ H G r t := by
  intro u hu; simp only [Finset.mem_filter] at hu; simp [H, hu.2]

theorem adm_P (t : ℝ) (r : Fin n → ℝ) (hr : GoodRanks v r) :
    Adm G v r ((R G v r).filter (fun u => t < tau G r u)) := by
  intro u hu
  have hu' := Finset.mem_of_mem_erase hu
  have huv := Finset.ne_of_mem_erase hu
  simp only [Finset.mem_filter] at hu'
  obtain ⟨c, hc, hadj, hlt, hle⟩ := caller_exists G v r hr u hu'.1 huv
  refine ⟨c, ?_, hadj, hlt⟩
  simp only [Finset.mem_filter]
  exact ⟨hc, by linarith [tau_le_r G r u, hu'.2]⟩

theorem Pv_empty (t : ℝ) (r : Fin n → ℝ) (hr : GoodRanks v r) (h : ¬ t < tau G r v) :
    Pv G v t r = ∅ := by
  ext u
  simp only [Pv, Rv, Finset.mem_filter, Finset.mem_erase, Finset.notMem_empty, iff_false, not_and]
  rintro ⟨_, hu⟩ ht
  exact h (lt_of_lt_of_le ht (tau_le_root G v r hr u hu))

theorem I1 (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (r : Fin n → ℝ) (hr : GoodRanks v r) :
    Real.log 4 * Nc G v t r ≤ Λ1 G v t r + Ep G v t r := by
  have hZ0 := Z_nonneg G v t (w1 t) (wv_w1_nonneg t ht) r
  have hΛ0 : 0 ≤ Λ1 G v t r := Real.log_nonneg (by linarith)
  by_cases hv : t < tau G r v
  · have hvS : v ∈ (R G v r).filter (fun u => t < tau G r u) := by
      simp only [Finset.mem_filter]; exact ⟨(mem_R_iff G v r v).2 Relation.ReflTransGen.refl, hv⟩
    have h14 := ((lemma_3_7 G v t ⟨ht, ht1⟩ (w1 t) (weight_w1 t ht ht1)).2 r hr
      _ ∅ (Pv_sub_H G v t r) hvS (adm_P G v t r hr) (by simp) (by simp))
    simp only [Finset.prod_empty, mul_one] at h14
    unfold omega at h14
    rw [Pv_erase] at h14
    have hval : ∀ u ∈ Pv G v t r, weightValue t (w1 t) (r u) = 4 * (t / r u) ^ 5 := by
      intro u hu
      simp only [Pv, Rv, Finset.mem_filter, Finset.mem_erase] at hu
      have h1 : t < r u := lt_of_lt_of_le hu.2 (tau_le_r G r u)
      have h2 : r u < 1 := r_lt_one v r hr u hu.1.1
      simp [weightValue, w1, h1, h2]
    rw [Finset.prod_congr rfl hval] at h14
    have hpos : ∀ u ∈ Pv G v t r, 0 < 4 * (t / r u) ^ 5 := by
      intro u hu
      simp only [Pv, Rv, Finset.mem_filter, Finset.mem_erase] at hu
      have : 0 < r u := lt_trans ht (lt_of_lt_of_le hu.2 (tau_le_r G r u))
      positivity
    have hprod_pos : 0 < ∏ u ∈ Pv G v t r, 4 * (t / r u) ^ 5 := Finset.prod_pos hpos
    have hlog := Real.log_le_log hprod_pos (show _ ≤ 1 + Z G v t (w1 t) r by linarith)
    rw [Real.log_prod (fun u hu => ne_of_gt (hpos u hu))] at hlog
    have hterm : ∀ u ∈ Pv G v t r, Real.log (4 * (t / r u) ^ 5) =
        Real.log 4 - 5 * (Real.log (r u) - Real.log t) := by
      intro u hu
      simp only [Pv, Rv, Finset.mem_filter, Finset.mem_erase] at hu
      have : 0 < r u := lt_trans ht (lt_of_lt_of_le hu.2 (tau_le_r G r u))
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_div (ne_of_gt ht)
        (ne_of_gt this)]
      push_cast; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const] at hlog
    simp only [nsmul_eq_mul] at hlog
    unfold Nc Ep Λ1
    linarith
  · rw [Nc, Ep, Pv_empty G v t r hr hv]
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero, Finset.sum_empty, add_zero]
    exact hΛ0

theorem Bs_empty (lam t : ℝ) (r : Fin n → ℝ) (hr : GoodRanks v r) (h : ¬ t < tau G r v) :
    Bs G v lam t r = ∅ := by
  ext x
  simp only [Bs, Rv, Finset.mem_filter, Finset.mem_erase, Finset.notMem_empty, iff_false, not_and]
  rintro ⟨hxv, hx⟩ _ _ htx
  obtain ⟨c, hc, _, _, hle⟩ := caller_exists G v r hr x hx hxv
  exact h (lt_of_lt_of_le (lt_of_lt_of_le htx hle) (tau_le_root G v r hr c hc))

set_option maxHeartbeats 1000000 in
theorem I2 (lam t : ℝ) (hl : 0 < lam) (hl1 : lam < 1) (ht : 0 < t) (ht1 : t < 1)
    (r : Fin n → ℝ) (hr : GoodRanks v r) :
    Real.log (1 + 4 * lam) * SB G v lam t r + Real.log 4 * Nc G v t r ≤
      Λ2 G v lam t r + Ep G v t r + Real.log (1 / lam) * Nc G v t r := by
  have ha : 0 < lam * t := by positivity
  have hat : lam * t < t := by nlinarith
  have ha1 : lam * t < 1 := by linarith
  have hZ0 := Z_nonneg G v (lam * t) (w2 lam t) (wv_w2_nonneg lam t hl ht) r
  have hΛ0 : 0 ≤ Λ2 G v lam t r := Real.log_nonneg (by linarith)
  by_cases hv : t < tau G r v
  · have hvS : v ∈ (R G v r).filter (fun u => t < tau G r u) := by
      simp only [Finset.mem_filter]; exact ⟨(mem_R_iff G v r v).2 Relation.ReflTransGen.refl, hv⟩
    have hSH : (R G v r).filter (fun u => t < tau G r u) ⊆ H G r (lam * t) := by
      intro u hu; simp only [Finset.mem_filter] at hu; simp only [H, Finset.mem_filter,
        Finset.mem_univ, true_and]; linarith [hu.2]
    have hBH : Bs G v lam t r ⊆ H G r (lam * t) \ (R G v r).filter (fun u => t < tau G r u) := by
      intro x hx
      simp only [Bs, Rv, Finset.mem_filter, Finset.mem_erase] at hx
      simp only [Finset.mem_sdiff, H, Finset.mem_filter, Finset.mem_univ, true_and, not_and,
        not_lt]
      exact ⟨hx.2.1, fun _ => hx.2.2.1⟩
    have hBp : ∀ x ∈ Bs G v lam t r, ∃ z ∈ (R G v r).filter (fun u => t < tau G r u),
        G.Adj x z ∧ r x < r z := by
      intro x hx
      simp only [Bs, Rv, Finset.mem_filter, Finset.mem_erase] at hx
      obtain ⟨c, hc, hadj, hlt, hle⟩ := caller_exists G v r hr x hx.1.2 hx.1.1
      refine ⟨c, ?_, hadj, hlt⟩
      simp only [Finset.mem_filter]
      exact ⟨hc, lt_of_lt_of_le hx.2.2.2 hle⟩
    have h14 := ((lemma_3_7 G v (lam * t) ⟨ha, ha1⟩ (w2 lam t)
      (weight_w2 lam t hl hl1 ht ht1)).2 r hr _ _ hSH hvS (adm_P G v t r hr) hBH hBp)
    unfold omega at h14
    rw [Pv_erase] at h14
    have hvalP : ∀ u ∈ Pv G v t r, weightValue (lam * t) (w2 lam t) (r u) =
        4 * lam * (t / r u) ^ 5 := by
      intro u hu
      simp only [Pv, Rv, Finset.mem_filter, Finset.mem_erase] at hu
      have h1 : t < r u := lt_of_lt_of_le hu.2 (tau_le_r G r u)
      have h2 : r u < 1 := r_lt_one v r hr u hu.1.1
      have h3 : lam * t < r u := by linarith
      simp [weightValue, w2, h1, h2, h3]
    have hvalB : ∀ x ∈ Bs G v lam t r, weightValue (lam * t) (w2 lam t) (r x) =
        4 * lam * (t / r x) ^ 5 := by
      intro x hx
      simp only [Bs, Rv, Finset.mem_filter, Finset.mem_erase] at hx
      have h1 : t < r x := hx.2.2.2
      have h2 : r x < 1 := r_lt_one v r hr x hx.1.1
      have h3 : lam * t < r x := by linarith
      simp [weightValue, w2, h1, h2, h3]
    rw [Finset.prod_congr rfl hvalP, Finset.prod_congr (s₁ := Bs G v lam t r) rfl
      (fun x hx => by rw [hvalB x hx])] at h14
    have hposP : ∀ u ∈ Pv G v t r, 0 < 4 * lam * (t / r u) ^ 5 := by
      intro u hu
      simp only [Pv, Rv, Finset.mem_filter, Finset.mem_erase] at hu
      have : 0 < r u := lt_trans ht (lt_of_lt_of_le hu.2 (tau_le_r G r u))
      positivity
    have hposB : ∀ x ∈ Bs G v lam t r, 0 < 1 + 4 * lam * (t / r x) ^ 5 := by
      intro x hx
      simp only [Bs, Rv, Finset.mem_filter, Finset.mem_erase] at hx
      have : 0 < r x := lt_trans ht hx.2.2.2
      positivity
    have hp1 := Finset.prod_pos hposP
    have hp2 := Finset.prod_pos hposB
    have hlog := Real.log_le_log (mul_pos hp1 hp2)
      (show _ ≤ 1 + Z G v (lam * t) (w2 lam t) r by linarith)
    rw [Real.log_mul (ne_of_gt hp1) (ne_of_gt hp2), Real.log_prod (fun u hu => ne_of_gt (hposP u hu)),
      Real.log_prod (fun x hx => ne_of_gt (hposB x hx))] at hlog
    have htermP : ∀ u ∈ Pv G v t r, Real.log (4 * lam * (t / r u) ^ 5) =
        Real.log 4 + Real.log lam - 5 * (Real.log (r u) - Real.log t) := by
      intro u hu
      simp only [Pv, Rv, Finset.mem_filter, Finset.mem_erase] at hu
      have : 0 < r u := lt_trans ht (lt_of_lt_of_le hu.2 (tau_le_r G r u))
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow, Real.log_div (ne_of_gt ht) (ne_of_gt this)]
      push_cast; ring
    rw [Finset.sum_congr rfl htermP, Finset.sum_sub_distrib, Finset.sum_const] at hlog
    simp only [nsmul_eq_mul] at hlog
    have hconc : Real.log (1 + 4 * lam) * SB G v lam t r ≤
        ∑ x ∈ Bs G v lam t r, Real.log (1 + 4 * lam * (t / r x) ^ 5) := by
      unfold SB
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x hx
      simp only [Bs, Rv, Finset.mem_filter, Finset.mem_erase] at hx
      have hx0 : 0 < r x := lt_trans ht hx.2.2.2
      have hz0 : 0 ≤ (t / r x) ^ 5 := by positivity
      have hz1 : (t / r x) ^ 5 ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hx0).2 hx.2.2.2.le)
      have := concave_log ((t / r x) ^ 5) (4 * lam) hz0 hz1 (by positivity)
      linarith
    have hlogl : Real.log (1 / lam) = - Real.log lam := by rw [one_div, Real.log_inv]
    unfold Nc Ep Λ2
    rw [hlogl]
    linarith
  · rw [SB, Nc, Ep, Pv_empty G v t r hr hv, Bs_empty G v lam t r hr hv]
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero, Finset.sum_empty, add_zero]
    exact hΛ0

end L32
end LPM


-- ===== Solutions.LPM.L32c =====

set_option autoImplicit false

namespace LPM
namespace L32
open MeasureTheory Set LocalProbeMIS871.Greedy Function
open scoped Classical ENNReal NNReal

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)

theorem Z_eq_sum' (a : ℝ) (ψ : ℝ → ℝ) (r : Fin n → ℝ) :
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

theorem measurableSet_Adm (S : Finset (Fin n)) : MeasurableSet {r : Fin n → ℝ | Adm G v r S} := by
  have : {r : Fin n → ℝ | Adm G v r S} = ⋂ u ∈ S.erase v, ⋃ z ∈ S,
      {r : Fin n → ℝ | G.Adj u z ∧ r u < r z} := by
    ext r; simp only [Adm, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
  rw [this]
  refine Finset.measurableSet_biInter _ (fun u _ => Finset.measurableSet_biUnion _ (fun z _ => ?_))
  by_cases h : G.Adj u z
  · simp only [h, true_and]
    exact measurableSet_lt (measurable_pi_apply u) (measurable_pi_apply z)
  · simp [h]

/-- joint measurability of `Z` in the time parameter and the ranks -/
theorem measurable_Z_gen {Y : Type*} [MeasurableSpace Y] (A : Y → ℝ) (hA : Measurable A)
    (Ψ : Y → ℝ → ℝ) (hΨ : Measurable (fun p : Y × ℝ => Ψ p.1 p.2))
    (Rr : Y → (Fin n → ℝ)) (hR : Measurable Rr) :
    Measurable (fun y => Z G v (A y) (Ψ y) (Rr y)) := by
  simp_rw [Z_eq_sum']
  apply Finset.measurable_sum; intro S _
  apply Measurable.ite
  · have h1 : MeasurableSet {y : Y | S ⊆ H G (Rr y) (A y)} := by
      have : {y : Y | S ⊆ H G (Rr y) (A y)} = ⋂ u ∈ S, {y | A y < tau G (Rr y) u} := by
        ext p; simp [Finset.subset_iff, H]
      rw [this]
      exact Finset.measurableSet_biInter _ (fun u _ =>
        measurableSet_lt hA ((measurable_tau G u).comp hR))
    have h3 : MeasurableSet {y : Y | Adm G v (Rr y) S} := hR (measurableSet_Adm G v S)
    have h2 : MeasurableSet {y : Y | v ∈ S} := MeasurableSet.const _
    exact h1.inter (h2.inter h3)
  · unfold omega
    apply Finset.measurable_prod; intro u _
    unfold weightValue
    apply Measurable.ite
    · exact (measurableSet_lt hA ((measurable_pi_apply u).comp hR)).inter
        (measurableSet_lt ((measurable_pi_apply u).comp hR) measurable_const)
    · exact hΨ.comp (measurable_id.prodMk ((measurable_pi_apply u).comp hR))
    · exact measurable_const
  · exact measurable_const

theorem Z_le (a : ℝ) (ψ : ℝ → ℝ) (h : ∀ z, 0 ≤ weightValue a ψ z ∧ weightValue a ψ z ≤ 4)
    (r : Fin n → ℝ) : Z G v a ψ r ≤ 8 ^ n := by
  rw [Z_eq_sum']
  calc ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (if S ⊆ H G r a ∧ v ∈ S ∧ Adm G v r S then omega v r a ψ S else 0)
      ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, (4 : ℝ) ^ n := by
        apply Finset.sum_le_sum; intro S _
        split_ifs
        · unfold omega
          calc ∏ u ∈ S.erase v, weightValue a ψ (r u) ≤ ∏ _u ∈ S.erase v, (4 : ℝ) :=
                Finset.prod_le_prod (fun u _ => (h _).1) (fun u _ => (h _).2)
            _ = 4 ^ (S.erase v).card := Finset.prod_const _
            _ ≤ 4 ^ n := by
                apply pow_le_pow_right₀ (by norm_num)
                exact (Finset.card_le_univ _).trans (by simp)
        · positivity
    _ = 2 ^ n * 4 ^ n := by
        rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; push_cast; ring
    _ = 8 ^ n := by rw [← mul_pow]; norm_num

theorem wv_w1_le (t : ℝ) (ht : 0 < t) (z : ℝ) : weightValue t (w1 t) z ≤ 4 := by
  unfold weightValue w1; split_ifs with h
  · have hz : 0 < z := lt_trans ht h.1
    have h1 : t / z ≤ 1 := (div_le_one hz).2 h.1.le
    have h3 : (t / z) ^ 5 ≤ 1 := pow_le_one₀ (by positivity) h1
    linarith
  · norm_num

theorem wv_w2_le (lam t : ℝ) (hl : 0 < lam) (hl1 : lam < 1) (ht : 0 < t) (z : ℝ) :
    weightValue (lam * t) (w2 lam t) z ≤ 4 := by
  unfold weightValue w2; split_ifs with h h'
  · have hz : 0 < z := lt_trans ht h'
    have h1 : t / z ≤ 1 := (div_le_one hz).2 h'.le
    have h3 : (t / z) ^ 5 ≤ 1 := pow_le_one₀ (by positivity) h1
    have h4 : 0 ≤ (t / z) ^ 5 := by positivity
    nlinarith
  · norm_num
  · norm_num

theorem integral_w1 (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    ∫ z in Ioo t 1, w1 t z = t - t ^ 5 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht1.le]
  have hF : ∀ x ∈ Ioo t 1, HasDerivAt (fun z : ℝ => -(t ^ 5) * (z ^ 4)⁻¹) (w1 t x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans ht hx.1)
    have h := ((hasDerivAt_pow 4 x).inv (pow_ne_zero 4 hx0)).const_mul (-(t ^ 5))
    refine h.congr_deriv ?_
    unfold w1
    field_simp
    ring
  have hcont : ContinuousOn (fun z : ℝ => -(t ^ 5) * (z ^ 4)⁻¹) (Icc t 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (continuous_pow 4).continuousOn
    intro z hz; exact pow_ne_zero 4 (ne_of_gt (lt_of_lt_of_le ht hz.1))
  have hint : IntervalIntegrable (w1 t) volume t 1 := by
    apply ContinuousOn.intervalIntegrable
    unfold w1
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.pow
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro z hz; rw [uIcc_of_le ht1.le] at hz; exact ne_of_gt (lt_of_lt_of_le ht hz.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht1.le hcont hF hint]
  field_simp
  ring

theorem integral_w2 (lam t : ℝ) (hl : 0 < lam) (hl1 : lam < 1) (ht : 0 < t) (ht1 : t < 1) :
    ∫ z in Ioo (lam * t) 1, w2 lam t z = lam * (t - t ^ 5) := by
  have hlt : lam * t < t := by nlinarith
  have h1 : ∫ z in Ioo (lam * t) 1, w2 lam t z = ∫ z in Ioo t 1, w2 lam t z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
      (Ioo_subset_Ioo_left hlt.le)
    intro z hz
    simp only [mem_diff, mem_Ioo, not_and, not_lt] at hz
    unfold w2
    rw [if_neg (fun h => absurd (hz.2 h) (not_le.2 hz.1.2))]
  have h2 : ∫ z in Ioo t 1, w2 lam t z = ∫ z in Ioo t 1, lam * w1 t z := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro z hz
    simp only [w2, w1, if_pos hz.1]; ring
  rw [h1, h2, integral_const_mul, integral_w1 t ht ht1]

end L32
end LPM


-- ===== Solutions.LPM.L32d =====

set_option autoImplicit false

namespace LPM
namespace L32
open MeasureTheory Set LocalProbeMIS871.Greedy Function
open scoped Classical ENNReal NNReal

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)

noncomputable abbrev μ1 : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

noncomputable def fl (lam : ℝ) : ℝ := 5 * lam ^ 4 * (-Real.log lam) / Real.log (1 + 4 * lam)
noncomputable def φ1 (t : ℝ) : ℝ≥0 := Real.toNNReal (5 * t ^ 4)
noncomputable def φ2 (θ : ℝ × ℝ) : ℝ≥0 := Real.toNNReal (fl θ.1 * (5 * θ.2 ^ 4) / coeffU 5)

noncomputable def L1 (r : Fin n → ℝ) : ℝ := ∫ t, (φ1 t : ℝ) * Λ1 G v t r ∂μ1
noncomputable def L2 (r : Fin n → ℝ) : ℝ :=
  ∫ θ, (φ2 θ : ℝ) * Λ2 G v θ.1 θ.2 r ∂(μ1.prod μ1)

theorem fl_eq (z : ℝ) (hz : 0 < z) : fl z = 5 * uIntegrand 5 z := by
  unfold fl uIntegrand
  rw [show (5 : ℝ) - 1 = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div, Real.log_inv]
  ring

theorem integrableOn_fl : IntegrableOn fl (Ioo 0 1) := by
  have h : IntegrableOn (fun z => 5 * uIntegrand 5 z) (Ioo 0 1) := (lemma_A_1).1.const_mul 5
  exact IntegrableOn.congr_fun h (fun z hz => (fl_eq z hz.1).symm) measurableSet_Ioo

theorem integral_fl : ∫ z in Ioo (0 : ℝ) 1, fl z = coeffU 5 := by
  rw [setIntegral_congr_fun measurableSet_Ioo (fun z hz => fl_eq z hz.1), integral_const_mul]
  rfl

theorem fl_nonneg (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) : 0 ≤ fl z := by
  unfold fl
  have h1 : 0 ≤ -Real.log z := by
    have := Real.log_nonpos hz.1.le hz.2.le; linarith
  have h2 : 0 < Real.log (1 + 4 * z) := Real.log_pos (by linarith [hz.1])
  positivity

theorem integral_5t4 : ∫ t in Ioo (0 : ℝ) 1, 5 * t ^ 4 = 1 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_5pow4]; norm_num

theorem integrableOn_5t4 : IntegrableOn (fun t : ℝ => 5 * t ^ 4) (Ioo 0 1) :=
  (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self

theorem lint_φ1 : ∫⁻ t, (φ1 t : ℝ≥0∞) ∂μ1 = 1 := by
  have : (fun t => (φ1 t : ℝ≥0∞)) = fun t => ENNReal.ofReal (5 * t ^ 4) := rfl
  rw [this, ← ofReal_integral_eq_lintegral_ofReal integrableOn_5t4
    (Filter.Eventually.of_forall (fun t => by positivity)), integral_5t4, ENNReal.ofReal_one]

theorem lint_φ2 (hu : 0 < coeffU 5) : ∫⁻ θ, (φ2 θ : ℝ≥0∞) ∂(μ1.prod μ1) = 1 := by
  have : (fun θ => (φ2 θ : ℝ≥0∞)) =
      fun θ : ℝ × ℝ => ENNReal.ofReal (fl θ.1 * (5 * θ.2 ^ 4) / coeffU 5) := rfl
  have hint : Integrable (fun θ : ℝ × ℝ => fl θ.1 * (5 * θ.2 ^ 4) / coeffU 5) (μ1.prod μ1) :=
    (integrableOn_fl.mul_prod integrableOn_5t4).div_const _
  have hnn : 0 ≤ᵐ[μ1.prod μ1] fun θ : ℝ × ℝ => fl θ.1 * (5 * θ.2 ^ 4) / coeffU 5 := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with θ hθ
    have := fl_nonneg θ.1 hθ.1
    simp only [Pi.zero_apply]; positivity
  rw [this, ← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_div,
    integral_prod_mul (fun x => fl x) (fun t => 5 * t ^ 4),
    integral_fl, integral_5t4, mul_one, div_self (ne_of_gt hu), ENNReal.ofReal_one]

theorem meas_Λ1 : Measurable (uncurry (Λ1 G v)) := by
  have h := measurable_Z_gen G v (Y := ℝ × (Fin n → ℝ)) (fun p => p.1) measurable_fst
    (fun p z => w1 p.1 z) (by unfold w1; fun_prop) (fun p => p.2) measurable_snd
  unfold Λ1
  exact Real.measurable_log.comp (measurable_const.add h)

theorem meas_Λ1s : Measurable (fun p : (Fin n → ℝ) × ℝ => Λ1 G v p.2 p.1) := by
  have h := measurable_Z_gen G v (Y := (Fin n → ℝ) × ℝ) (fun p => p.2) measurable_snd
    (fun p z => w1 p.2 z) (by unfold w1; fun_prop) (fun p => p.1) measurable_fst
  unfold Λ1
  exact Real.measurable_log.comp (measurable_const.add h)

theorem meas_w2 {Y : Type*} [MeasurableSpace Y] (f g : Y → ℝ) (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun p : Y × ℝ => w2 (f p.1) (g p.1) p.2) := by
  unfold w2
  exact Measurable.ite (measurableSet_lt (hg.comp measurable_fst) measurable_snd)
    (((measurable_const.mul (hf.comp measurable_fst)).mul
      (((hg.comp measurable_fst).div measurable_snd).pow_const 5))) measurable_const

theorem meas_Λ2 : Measurable (uncurry (fun θ : ℝ × ℝ => Λ2 G v θ.1 θ.2)) := by
  have h := measurable_Z_gen G v (Y := (ℝ × ℝ) × (Fin n → ℝ)) (fun p => p.1.1 * p.1.2)
    (by fun_prop) (fun p z => w2 p.1.1 p.1.2 z)
    (meas_w2 (fun p : (ℝ × ℝ) × (Fin n → ℝ) => p.1.1) (fun p => p.1.2) (by fun_prop) (by fun_prop))
    (fun p => p.2) measurable_snd
  unfold Λ2
  exact Real.measurable_log.comp (measurable_const.add h)

theorem meas_Λ2s : Measurable (fun p : (Fin n → ℝ) × (ℝ × ℝ) => Λ2 G v p.2.1 p.2.2 p.1) := by
  have h := measurable_Z_gen G v (Y := (Fin n → ℝ) × (ℝ × ℝ)) (fun p => p.2.1 * p.2.2)
    (by fun_prop) (fun p z => w2 p.2.1 p.2.2 z)
    (meas_w2 (fun p : (Fin n → ℝ) × (ℝ × ℝ) => p.2.1) (fun p => p.2.2) (by fun_prop) (by fun_prop))
    (fun p => p.1) measurable_fst
  unfold Λ2
  exact Real.measurable_log.comp (measurable_const.add h)

theorem ae_mem1 : ∀ᵐ t ∂μ1, t ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo

theorem ae_mem2 : ∀ᵐ θ ∂(μ1.prod μ1), θ.1 ∈ Ioo (0 : ℝ) 1 ∧ θ.2 ∈ Ioo (0 : ℝ) 1 := by
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)

theorem exp_bound1 (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ r, ENNReal.ofReal (Real.exp (Λ1 G v t r)) ∂forcedLaw v ≤ 2 := by
  have hb : (∫ z in Ioo t 1, w1 t z) ≤ t := by
    rw [integral_w1 t ht.1 ht.2]; have : 0 < t ^ 5 := by have := ht.1; positivity
    linarith
  obtain ⟨hm, hle⟩ := (lemma_3_7 G v t ht (w1 t) (weight_w1 t ht.1 ht.2)).1 hb
  have hZ0 : ∀ r, 0 ≤ Z G v t (w1 t) r := Z_nonneg G v t (w1 t) (wv_w1_nonneg t ht.1)
  have e : ∀ r, ENNReal.ofReal (Real.exp (Λ1 G v t r)) = 1 + ENNReal.ofReal (Z G v t (w1 t) r) := by
    intro r
    unfold Λ1
    rw [Real.exp_log (by linarith [hZ0 r]), ENNReal.ofReal_add zero_le_one (hZ0 r),
      ENNReal.ofReal_one]
  simp_rw [e]
  have : IsProbabilityMeasure (forcedLaw v) := forcedLaw_isProb v
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul]
  calc (1 : ℝ≥0∞) + ∫⁻ r, ENNReal.ofReal (Z G v t (w1 t) r) ∂forcedLaw v ≤ 1 + 1 := by gcongr
    _ = 2 := by norm_num

theorem exp_bound2 (θ : ℝ × ℝ) (hθ : θ.1 ∈ Ioo (0 : ℝ) 1 ∧ θ.2 ∈ Ioo (0 : ℝ) 1) :
    ∫⁻ r, ENNReal.ofReal (Real.exp (Λ2 G v θ.1 θ.2 r)) ∂forcedLaw v ≤ 2 := by
  obtain ⟨⟨hl, hl1⟩, ⟨ht, ht1⟩⟩ := hθ
  have ha : 0 < θ.1 * θ.2 ∧ θ.1 * θ.2 < 1 := ⟨by positivity, by nlinarith⟩
  have hb : (∫ z in Ioo (θ.1 * θ.2) 1, w2 θ.1 θ.2 z) ≤ θ.1 * θ.2 := by
    rw [integral_w2 θ.1 θ.2 hl hl1 ht ht1]
    have : 0 < θ.2 ^ 5 := by positivity
    nlinarith
  obtain ⟨hm, hle⟩ := (lemma_3_7 G v (θ.1 * θ.2) ha (w2 θ.1 θ.2)
    (weight_w2 θ.1 θ.2 hl hl1 ht ht1)).1 hb
  have hZ0 : ∀ r, 0 ≤ Z G v (θ.1 * θ.2) (w2 θ.1 θ.2) r :=
    Z_nonneg G v _ _ (wv_w2_nonneg θ.1 θ.2 hl ht)
  have e : ∀ r, ENNReal.ofReal (Real.exp (Λ2 G v θ.1 θ.2 r)) =
      1 + ENNReal.ofReal (Z G v (θ.1 * θ.2) (w2 θ.1 θ.2) r) := by
    intro r
    unfold Λ2
    rw [Real.exp_log (by linarith [hZ0 r]), ENNReal.ofReal_add zero_le_one (hZ0 r),
      ENNReal.ofReal_one]
  simp_rw [e]
  have : IsProbabilityMeasure (forcedLaw v) := forcedLaw_isProb v
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul]
  calc (1 : ℝ≥0∞) + ∫⁻ r, ENNReal.ofReal (Z G v (θ.1 * θ.2) (w2 θ.1 θ.2) r) ∂forcedLaw v
      ≤ 1 + 1 := by gcongr
    _ = 2 := by norm_num

theorem meas_φ1 : Measurable φ1 := measurable_real_toNNReal.comp (by fun_prop)
theorem meas_φ2 : Measurable φ2 := by
  unfold φ2 fl
  exact measurable_real_toNNReal.comp (by fun_prop)

theorem expL1 : ∫⁻ r, ENNReal.ofReal (Real.exp (L1 G v r)) ∂forcedLaw v ≤ 2 := by
  have : IsProbabilityMeasure (forcedLaw v) := forcedLaw_isProb v
  unfold L1
  refine jensen_lint μ1 (forcedLaw v) φ1 meas_φ1 lint_φ1 (Λ1 G v) (meas_Λ1 G v)
    (Real.log (1 + 8 ^ n)) ?_ ?_
  · filter_upwards [ae_mem1] with t ht r
    have hZ0 := Z_nonneg G v t (w1 t) (wv_w1_nonneg t ht.1) r
    have hZ := Z_le G v t (w1 t) (fun z => ⟨wv_w1_nonneg t ht.1 z, wv_w1_le t ht.1 z⟩) r
    unfold Λ1
    exact ⟨Real.log_nonneg (by linarith), Real.log_le_log (by linarith) (by linarith)⟩
  · filter_upwards [ae_mem1] with t ht
    exact exp_bound1 G v t ht

theorem expL2 (hu : 0 < coeffU 5) :
    ∫⁻ r, ENNReal.ofReal (Real.exp (L2 G v r)) ∂forcedLaw v ≤ 2 := by
  have : IsProbabilityMeasure (forcedLaw v) := forcedLaw_isProb v
  unfold L2
  refine jensen_lint (μ1.prod μ1) (forcedLaw v) φ2 meas_φ2 (lint_φ2 hu)
    (fun θ => Λ2 G v θ.1 θ.2) (meas_Λ2 G v) (Real.log (1 + 8 ^ n)) ?_ ?_
  · filter_upwards [ae_mem2] with θ hθ r
    obtain ⟨⟨hl, hl1⟩, ⟨ht, _⟩⟩ := hθ
    have hZ0 := Z_nonneg G v _ (w2 θ.1 θ.2) (wv_w2_nonneg θ.1 θ.2 hl ht) r
    have hZ := Z_le G v _ (w2 θ.1 θ.2)
      (fun z => ⟨wv_w2_nonneg θ.1 θ.2 hl ht z, wv_w2_le θ.1 θ.2 hl hl1 ht z⟩) r
    unfold Λ2
    exact ⟨Real.log_nonneg (by linarith), Real.log_le_log (by linarith) (by linarith)⟩
  · filter_upwards [ae_mem2] with θ hθ
    exact exp_bound2 G v θ hθ

theorem meas_L1 : Measurable (L1 G v) := by
  have h1 : Measurable (fun p : (Fin n → ℝ) × ℝ => (φ1 p.2 : ℝ)) :=
    (measurable_coe_nnreal_real.comp meas_φ1).comp measurable_snd
  have h2 : Measurable (fun p : (Fin n → ℝ) × ℝ => Λ1 G v p.2 p.1) :=
    meas_Λ1s G v
  have h : StronglyMeasurable (fun p : (Fin n → ℝ) × ℝ => (φ1 p.2 : ℝ) * Λ1 G v p.2 p.1) :=
    (h1.mul h2).stronglyMeasurable
  have := h.integral_prod_right' (ν := μ1)
  exact this.measurable

theorem meas_L2 : Measurable (L2 G v) := by
  have h1 : Measurable (fun p : (Fin n → ℝ) × (ℝ × ℝ) => (φ2 p.2 : ℝ)) :=
    (measurable_coe_nnreal_real.comp meas_φ2).comp measurable_snd
  have h2 : Measurable (fun p : (Fin n → ℝ) × (ℝ × ℝ) => Λ2 G v p.2.1 p.2.2 p.1) :=
    meas_Λ2s G v
  have h : StronglyMeasurable
      (fun p : (Fin n → ℝ) × (ℝ × ℝ) => (φ2 p.2 : ℝ) * Λ2 G v p.2.1 p.2.2 p.1) :=
    (h1.mul h2).stronglyMeasurable
  have := h.integral_prod_right' (ν := μ1.prod μ1)
  exact this.measurable

end L32
end LPM


-- ===== Solutions.LPM.L32e =====

set_option autoImplicit false

namespace LPM
namespace L32
open MeasureTheory Set LocalProbeMIS871.Greedy Function
open scoped Classical ENNReal NNReal

theorem ae_ne_two (a b : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a ∧ x ≠ b := by
  have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a := by
    rw [ae_iff]; simp only [ne_eq, not_not]
    have : {x : ℝ | x = a} = {a} := by ext; simp
    rw [this]; exact Real.volume_singleton
  have h2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b := by
    rw [ae_iff]; simp only [ne_eq, not_not]
    have : {x : ℝ | x = b} = {b} := by ext; simp
    rw [this]; exact Real.volume_singleton
  filter_upwards [h1, h2] with x hx1 hx2 using ⟨hx1, hx2⟩

/-- integrating a windowed function over `(0,1)` -/
theorem setInt_window (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (p : ℝ → Prop)
    [DecidablePred p] (hp : ∀ x, x ≠ a → x ≠ b → x ∈ Ioo (0 : ℝ) 1 → (p x ↔ a < x ∧ x < b)) (g : ℝ → ℝ) :
    ∫ x in Ioo (0 : ℝ) 1, (if p x then g x else 0) = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, ← integral_indicator measurableSet_Ioo,
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_ne_two a b] with x ⟨hxa, hxb⟩
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · rw [Set.indicator_of_mem hx]
    have := hp x hxa hxb hx
    by_cases hpx : p x
    · rw [if_pos hpx, Set.indicator_of_mem]
      have := this.1 hpx; exact ⟨this.1, this.2.le⟩
    · rw [if_neg hpx, Set.indicator_of_notMem]
      intro h; exact hpx (this.2 ⟨h.1, lt_of_le_of_ne h.2 hxb⟩)
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
    intro h
    apply hx
    refine ⟨lt_of_le_of_lt ha h.1, ?_⟩
    rcases lt_or_eq_of_le (h.2.trans hb) with h' | h'
    · exact h'
    · exfalso; exact hxb (le_antisymm h.2 (hb.trans h'.symm.le))

theorem t4_log_bound (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : 0 ≤ t ^ 4 * (-Real.log t) ∧
    t ^ 4 * (-Real.log t) ≤ 1 := by
  have h1 : 0 ≤ -Real.log t := by have := Real.log_nonpos ht.1.le ht.2.le; linarith
  have h2 : -Real.log t ≤ t⁻¹ := by
    have := Real.one_sub_inv_le_log_of_pos ht.1; linarith
  refine ⟨by positivity, ?_⟩
  calc t ^ 4 * (-Real.log t) ≤ t ^ 4 * t⁻¹ := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = t ^ 3 := by field_simp
    _ ≤ 1 := pow_le_one₀ ht.1.le ht.2.le

end L32
end LPM

namespace LPM
namespace L32
open MeasureTheory Set LocalProbeMIS871.Greedy Function
open scoped Classical ENNReal NNReal

theorem K1 (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ∫ t in Ioo (0 : ℝ) 1, (if t < τ then 5 * t ^ 4 else 0) = τ ^ 5 := by
  rw [setInt_window 0 τ le_rfl hτ0.le hτ1 (fun t => t < τ)
    (fun x hx0 _ hx => ⟨fun h => ⟨hx.1, h⟩, fun h => h.2⟩), integral_5pow4]

theorem K2 (τ ρ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ∫ t in Ioo (0 : ℝ) 1, (if t < τ then 25 * t ^ 4 * (Real.log ρ - Real.log t) else 0) =
      5 * τ ^ 5 * (Real.log ρ - Real.log τ) + τ ^ 5 := by
  rw [setInt_window 0 τ le_rfl hτ0.le hτ1 (fun t => t < τ)
    (fun x hx0 _ hx => ⟨fun h => ⟨hx.1, h⟩, fun h => h.2⟩), integral_pow4_log_rho τ ρ hτ0]

noncomputable def F3 (τ ρ : ℝ) (θ : ℝ × ℝ) : ℝ :=
  25 * θ.2 ^ 4 * θ.1 ^ 4 * (-Real.log θ.1) *
    (if θ.1 * θ.2 < τ ∧ τ ≤ θ.2 ∧ θ.2 < ρ then (θ.2 / ρ) ^ 5 else 0)

theorem meas_F3 (τ ρ : ℝ) : Measurable (F3 τ ρ) := by
  unfold F3
  have h1 : Measurable (fun θ : ℝ × ℝ => 25 * θ.2 ^ 4 * θ.1 ^ 4 * (-Real.log θ.1)) :=
    ((measurable_const.mul (measurable_snd.pow_const 4)).mul (measurable_fst.pow_const 4)).mul
      (Real.measurable_log.comp measurable_fst).neg
  have h2 : Measurable (fun θ : ℝ × ℝ => (θ.2 / ρ) ^ 5) := (measurable_snd.div_const ρ).pow_const 5
  refine h1.mul (Measurable.ite ?_ h2 measurable_const)
  exact (measurableSet_lt (measurable_fst.mul measurable_snd) measurable_const).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const))

theorem F3_bound (τ ρ : ℝ) (hρ : 0 < ρ) (θ : ℝ × ℝ)
    (hθ : θ.1 ∈ Ioo (0 : ℝ) 1 ∧ θ.2 ∈ Ioo (0 : ℝ) 1) : 0 ≤ F3 τ ρ θ ∧ F3 τ ρ θ ≤ 25 := by
  obtain ⟨h1, h2⟩ := hθ
  have hl := t4_log_bound θ.1 h1
  have ht4 : θ.2 ^ 4 ≤ 1 := pow_le_one₀ h2.1.le h2.2.le
  have ht40 : 0 ≤ θ.2 ^ 4 := by positivity
  unfold F3
  split_ifs with h
  · have hq0 : 0 ≤ (θ.2 / ρ) ^ 5 := by have := h2.1; positivity
    have hq1 : (θ.2 / ρ) ^ 5 ≤ 1 := pow_le_one₀ (by have := h2.1; positivity)
      ((div_le_one hρ).2 h.2.2.le)
    have e : 25 * θ.2 ^ 4 * θ.1 ^ 4 * (-Real.log θ.1) * (θ.2 / ρ) ^ 5 =
        25 * (θ.2 ^ 4 * ((θ.1 ^ 4 * (-Real.log θ.1)) * (θ.2 / ρ) ^ 5)) := by ring
    rw [e]
    have h3 : 0 ≤ (θ.1 ^ 4 * (-Real.log θ.1)) * (θ.2 / ρ) ^ 5 := mul_nonneg hl.1 hq0
    have h4 : (θ.1 ^ 4 * (-Real.log θ.1)) * (θ.2 / ρ) ^ 5 ≤ 1 := by nlinarith [hl.2]
    constructor
    · positivity
    · nlinarith
  · simp

theorem K3 (τ ρ : ℝ) (hτ0 : 0 < τ) (hτρ : τ ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∫ θ, F3 τ ρ θ ∂(μ1.prod μ1) = τ ^ 5 * (Real.log ρ - Real.log τ) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hτ0 hτρ
  have hint : Integrable (F3 τ ρ) (μ1.prod μ1) := by
    refine Integrable.of_bound (meas_F3 τ ρ).aestronglyMeasurable 25 ?_
    filter_upwards [ae_mem2] with θ hθ
    have := F3_bound τ ρ hρ0 θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
  rw [integral_prod_symm _ hint]
  -- inner integral
  have hinner : ∀ t ∈ Ioo (0 : ℝ) 1, ∫ lam, F3 τ ρ (lam, t) ∂μ1 =
      if τ ≤ t ∧ t < ρ then (τ / ρ) ^ 5 * (t ^ 4 * (5 * (Real.log t - Real.log τ) + 1)) else 0 := by
    intro t ht
    by_cases hw : τ ≤ t ∧ t < ρ
    · rw [if_pos hw]
      have hc1 : τ / t ≤ 1 := (div_le_one ht.1).2 hw.1
      have hc0 : 0 < τ / t := by have := ht.1; positivity
      have e : ∀ lam, F3 τ ρ (lam, t) = if lam * t < τ then
          (25 * t ^ 4 * (t / ρ) ^ 5) * (lam ^ 4 * (-Real.log lam)) else 0 := by
        intro lam
        unfold F3
        simp only [hw, and_true]
        split_ifs <;> ring
      simp_rw [e]
      rw [setInt_window 0 (τ / t) le_rfl hc0.le hc1 (fun lam => lam * t < τ) (by
        intro x _ _ hx
        rw [lt_div_iff₀ ht.1]
        exact ⟨fun h => ⟨hx.1, h⟩, fun h => h.2⟩)]
      rw [intervalIntegral.integral_const_mul, integral_pow4_log_inv _ hc0]
      rw [Real.log_div (ne_of_gt hτ0) (ne_of_gt ht.1)]
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      have hr0 : ρ ≠ 0 := ne_of_gt hρ0
      field_simp
      ring
    · rw [if_neg hw]
      have : ∀ lam, F3 τ ρ (lam, t) = 0 := by
        intro lam; unfold F3
        rw [if_neg (fun h => hw ⟨h.2.1, h.2.2⟩), mul_zero]
      simp [this]
  rw [setIntegral_congr_fun measurableSet_Ioo hinner]
  rw [setInt_window τ ρ hτ0.le hτρ hρ1 (fun t => τ ≤ t ∧ t < ρ)
    (g := fun t => (τ / ρ) ^ 5 * (t ^ 4 * (5 * (Real.log t - Real.log τ) + 1))) (by
    intro x hxa _ _
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm hxa), h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.le, h2⟩)]
  rw [intervalIntegral.integral_const_mul, integral_pow4_log_ratio τ ρ hτ0 hτρ]
  field_simp

end L32
end LPM

namespace LPM
namespace L32
open MeasureTheory Set LocalProbeMIS871.Greedy Function
open scoped Classical ENNReal NNReal

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)

theorem tau_pos' (r : Fin n → ℝ) (hr : GoodRanks v r) (u : Fin n) : 0 < tau G r u := by
  rw [tau_eq]
  by_cases h : tauV G r u = v
  · rw [h, hr.1]; norm_num
  · exact (hr.2.1 _ h).1

theorem tau_le_one' (r : Fin n → ℝ) (hr : GoodRanks v r) (u : Fin n) : tau G r u ≤ 1 := by
  refine (tau_le_r G r u).trans ?_
  by_cases h : u = v
  · rw [h, hr.1]
  · exact (hr.2.1 u h).2.le

theorem rpow5 (x : ℝ) : x ^ (5 : ℝ) = x ^ 5 := by
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem integrable_K1 (τ : ℝ) :
    Integrable (fun t : ℝ => if t < τ then 5 * t ^ 4 else 0) μ1 := by
  refine Integrable.of_bound (Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (by fun_prop) measurable_const).aestronglyMeasurable 5 ?_
  filter_upwards [ae_mem1] with t ht
  split_ifs
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : t ^ 4 ≤ 1 := pow_le_one₀ ht.1.le ht.2.le
    linarith
  · simp

theorem integrable_K2 (τ ρ : ℝ) :
    Integrable (fun t : ℝ => if t < τ then 25 * t ^ 4 * (Real.log ρ - Real.log t) else 0) μ1 := by
  refine Integrable.of_bound (Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (by fun_prop) measurable_const).aestronglyMeasurable (25 * (|Real.log ρ| + 1)) ?_
  filter_upwards [ae_mem1] with t ht
  have hb := t4_log_bound t ht
  have h4 : t ^ 4 ≤ 1 := pow_le_one₀ ht.1.le ht.2.le
  have h40 : 0 ≤ t ^ 4 := by positivity
  split_ifs
  · rw [Real.norm_eq_abs]
    have e : 25 * t ^ 4 * (Real.log ρ - Real.log t) =
        25 * (t ^ 4 * Real.log ρ + t ^ 4 * (-Real.log t)) := by ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 25)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc |t ^ 4 * Real.log ρ + t ^ 4 * (-Real.log t)|
        ≤ |t ^ 4 * Real.log ρ| + |t ^ 4 * (-Real.log t)| := abs_add_le _ _
      _ ≤ |Real.log ρ| + 1 := by
          rw [abs_mul, abs_of_nonneg h40, abs_of_nonneg hb.1]
          nlinarith [abs_nonneg (Real.log ρ)]
  · simp only [norm_zero]; positivity

theorem S1 (r : Fin n → ℝ) (hr : GoodRanks v r) :
    ∫ t in Ioo (0 : ℝ) 1, 5 * t ^ 4 * Nc G v t r = X G v 5 r := by
  have e : ∀ t, 5 * t ^ 4 * Nc G v t r =
      ∑ u ∈ Rv G v r, (if t < tau G r u then 5 * t ^ 4 else 0) := by
    intro t
    unfold Nc Pv
    rw [Finset.natCast_card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u _; split_ifs <;> ring
  simp_rw [e]
  rw [integral_finset_sum _ (fun u _ => integrable_K1 _)]
  unfold X
  apply Finset.sum_congr rfl; intro u hu
  rw [rpow5, K1 _ (tau_pos' G v r hr u) (tau_le_one' G v r hr u)]

theorem S2 (r : Fin n → ℝ) (hr : GoodRanks v r) :
    ∫ t in Ioo (0 : ℝ) 1, 5 * t ^ 4 * Ep G v t r = 5 * D G v 5 r + X G v 5 r := by
  have e : ∀ t, 5 * t ^ 4 * Ep G v t r =
      ∑ u ∈ Rv G v r, (if t < tau G r u then
        25 * t ^ 4 * (Real.log (r u) - Real.log t) else 0) := by
    intro t
    unfold Ep Pv
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u _; split_ifs <;> ring
  simp_rw [e]
  rw [integral_finset_sum _ (fun u _ => integrable_K2 _ _)]
  unfold X D
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro u hu
  have hτ := tau_pos' G v r hr u
  rw [K2 _ _ hτ (tau_le_one' G v r hr u), rpow5,
    Real.log_div (ne_of_gt (lt_of_lt_of_le hτ (tau_le_r G r u))) (ne_of_gt hτ)]
  ring

theorem S3 (r : Fin n → ℝ) (hr : GoodRanks v r) :
    ∫ θ, 25 * θ.2 ^ 4 * θ.1 ^ 4 * (-Real.log θ.1) * SB G v θ.1 θ.2 r ∂(μ1.prod μ1) =
      D G v 5 r := by
  have e : ∀ θ : ℝ × ℝ, 25 * θ.2 ^ 4 * θ.1 ^ 4 * (-Real.log θ.1) * SB G v θ.1 θ.2 r =
      ∑ x ∈ Rv G v r, F3 (tau G r x) (r x) θ := by
    intro θ
    unfold SB Bs F3
    rw [Finset.sum_filter, Finset.mul_sum]
  simp_rw [e]
  have hint : ∀ x ∈ Rv G v r, Integrable (F3 (tau G r x) (r x)) (μ1.prod μ1) := by
    intro x hx
    have hρ : 0 < r x := lt_of_lt_of_le (tau_pos' G v r hr x) (tau_le_r G r x)
    refine Integrable.of_bound (meas_F3 _ _).aestronglyMeasurable 25 ?_
    filter_upwards [ae_mem2] with θ hθ
    have := F3_bound (tau G r x) (r x) hρ θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
  rw [integral_finset_sum _ hint]
  unfold D
  apply Finset.sum_congr rfl; intro x hx
  have hτ := tau_pos' G v r hr x
  have hxv : x ≠ v := Finset.ne_of_mem_erase hx
  rw [K3 _ _ hτ (tau_le_r G r x) (r_lt_one v r hr x hxv).le, rpow5,
    Real.log_div (ne_of_gt (lt_of_lt_of_le hτ (tau_le_r G r x))) (ne_of_gt hτ)]

end L32
end LPM


-- ===== Solutions.LPM.L32f =====

set_option autoImplicit false

namespace LPM
namespace L32
open MeasureTheory Set LocalProbeMIS871.Greedy Function
open scoped Classical ENNReal NNReal

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)

theorem flw_eq (z : ℝ) (hz : 0 < z) : fl z * (-Real.log z) = 5 * wIntegrand 5 z := by
  unfold fl wIntegrand
  rw [show (5 : ℝ) - 1 = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div, Real.log_inv]
  ring

theorem integrableOn_flw : IntegrableOn (fun z => fl z * (-Real.log z)) (Ioo 0 1) := by
  have h : IntegrableOn (fun z => 5 * wIntegrand 5 z) (Ioo 0 1) := (lemma_A_1).2.1.const_mul 5
  exact IntegrableOn.congr_fun h (fun z hz => (flw_eq z hz.1).symm) measurableSet_Ioo

theorem integral_flw : ∫ z in Ioo (0 : ℝ) 1, fl z * (-Real.log z) = coeffW 5 := by
  rw [setIntegral_congr_fun measurableSet_Ioo (fun z hz => flw_eq z hz.1), integral_const_mul]
  rfl

theorem meas_fl : Measurable fl := by unfold fl; fun_prop

theorem Nc_eq (r : Fin n → ℝ) (t : ℝ) : 5 * t ^ 4 * Nc G v t r =
    ∑ u ∈ Rv G v r, (if t < tau G r u then 5 * t ^ 4 else 0) := by
  unfold Nc Pv
  rw [Finset.natCast_card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro u _; split_ifs <;> ring

theorem Ep_eq (r : Fin n → ℝ) (t : ℝ) : 5 * t ^ 4 * Ep G v t r =
    ∑ u ∈ Rv G v r, (if t < tau G r u then 25 * t ^ 4 * (Real.log (r u) - Real.log t) else 0) := by
  unfold Ep Pv
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro u _; split_ifs <;> ring

theorem int_Nc (r : Fin n → ℝ) : Integrable (fun t => 5 * t ^ 4 * Nc G v t r) μ1 := by
  simp_rw [Nc_eq G v r]
  exact integrable_finset_sum _ (fun u _ => integrable_K1 _)

theorem int_Ep (r : Fin n → ℝ) : Integrable (fun t => 5 * t ^ 4 * Ep G v t r) μ1 := by
  simp_rw [Ep_eq G v r]
  exact integrable_finset_sum _ (fun u _ => integrable_K2 _ _)

theorem Λ1_bound (r : Fin n → ℝ) : ∀ᵐ t ∂μ1, ‖Λ1 G v t r‖ ≤ Real.log (1 + 8 ^ n) := by
  filter_upwards [ae_mem1] with t ht
  have hZ0 := Z_nonneg G v t (w1 t) (wv_w1_nonneg t ht.1) r
  have hZ := Z_le G v t (w1 t) (fun z => ⟨wv_w1_nonneg t ht.1 z, wv_w1_le t ht.1 z⟩) r
  unfold Λ1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith))]
  exact Real.log_le_log (by linarith) (by linarith)

theorem Λ2_bound (r : Fin n → ℝ) :
    ∀ᵐ θ ∂(μ1.prod μ1), ‖Λ2 G v θ.1 θ.2 r‖ ≤ Real.log (1 + 8 ^ n) := by
  filter_upwards [ae_mem2] with θ hθ
  obtain ⟨⟨hl, hl1⟩, ⟨ht, _⟩⟩ := hθ
  have hZ0 := Z_nonneg G v _ (w2 θ.1 θ.2) (wv_w2_nonneg θ.1 θ.2 hl ht) r
  have hZ := Z_le G v _ (w2 θ.1 θ.2)
    (fun z => ⟨wv_w2_nonneg θ.1 θ.2 hl ht z, wv_w2_le θ.1 θ.2 hl hl1 ht z⟩) r
  unfold Λ2
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith))]
  exact Real.log_le_log (by linarith) (by linarith)

theorem meas_Λ1_t (r : Fin n → ℝ) : Measurable (fun t => Λ1 G v t r) := by
  have h := measurable_Z_gen G v (Y := ℝ) id measurable_id
    (fun t z => w1 t z) (by unfold w1; fun_prop) (fun _ => r) measurable_const
  unfold Λ1
  exact Real.measurable_log.comp (measurable_const.add h)

theorem meas_Λ2_θ (r : Fin n → ℝ) : Measurable (fun θ : ℝ × ℝ => Λ2 G v θ.1 θ.2 r) := by
  have h := measurable_Z_gen G v (Y := ℝ × ℝ) (fun θ => θ.1 * θ.2) (by fun_prop)
    (fun θ z => w2 θ.1 θ.2 z)
    (meas_w2 (fun θ : ℝ × ℝ => θ.1) (fun θ => θ.2) measurable_fst measurable_snd)
    (fun _ => r) measurable_const
  unfold Λ2
  exact Real.measurable_log.comp (measurable_const.add h)

theorem T1 (r : Fin n → ℝ) (hr : GoodRanks v r) :
    Real.log 4 * X G v 5 r ≤ L1 G v r + (5 * D G v 5 r + X G v 5 r) := by
  have hm1 : Measurable (fun t => Λ1 G v t r) := meas_Λ1_t G v r
  have hi1 : Integrable (fun t => 5 * t ^ 4 * Λ1 G v t r) μ1 :=
    integrableOn_5t4.mul_bdd hm1.aestronglyMeasurable (Λ1_bound G v r)
  have hL1 : L1 G v r = ∫ t in Ioo (0 : ℝ) 1, 5 * t ^ 4 * Λ1 G v t r := by
    unfold L1
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    simp only [φ1, Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 5 * t ^ 4)]
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ (5 * t ^ 4 * Λ1 G v t r + 5 * t ^ 4 * Ep G v t r) -
      Real.log 4 * (5 * t ^ 4 * Nc G v t r) := by
    intro t ht
    have := I1 G v t ht.1 ht.2 r hr
    have h5 : 0 ≤ 5 * t ^ 4 := by positivity
    nlinarith
  have h := setIntegral_nonneg (μ := volume) measurableSet_Ioo hpt
  have hs : Integrable (fun t => 5 * t ^ 4 * Λ1 G v t r + 5 * t ^ 4 * Ep G v t r) μ1 :=
    hi1.add (int_Ep G v r)
  have hc : Integrable (fun t => Real.log 4 * (5 * t ^ 4 * Nc G v t r)) μ1 :=
    (int_Nc G v r).const_mul _
  have hE : Integrable (fun t => 5 * t ^ 4 * Ep G v t r) μ1 := int_Ep G v r
  rw [integral_sub hs hc, integral_add hi1 hE, integral_const_mul, S1 G v r hr, S2 G v r hr,
    ← hL1] at h
  linarith

set_option maxHeartbeats 1000000 in
theorem T2 (r : Fin n → ℝ) (hr : GoodRanks v r) (hu : 0 < coeffU 5) :
    D G v 5 r + Real.log 4 * (coeffU 5 * X G v 5 r) ≤
      coeffU 5 * L2 G v r + coeffU 5 * (5 * D G v 5 r + X G v 5 r) + coeffW 5 * X G v 5 r := by
  set uc := coeffU 5
  set wc := coeffW 5
  have hWint : Integrable (fun θ : ℝ × ℝ => fl θ.1 * (5 * θ.2 ^ 4)) (μ1.prod μ1) :=
    Integrable.mul_prod (f := fl) (g := fun t => 5 * t ^ 4) integrableOn_fl integrableOn_5t4
  have hm2 : Measurable (fun θ : ℝ × ℝ => Λ2 G v θ.1 θ.2 r) := meas_Λ2_θ G v r
  have hi1 : Integrable (fun θ : ℝ × ℝ => fl θ.1 * (5 * θ.2 ^ 4) * Λ2 G v θ.1 θ.2 r)
      (μ1.prod μ1) := hWint.mul_bdd hm2.aestronglyMeasurable (Λ2_bound G v r)
  have hi2 : Integrable (fun θ : ℝ × ℝ => fl θ.1 * (5 * θ.2 ^ 4 * Ep G v θ.2 r)) (μ1.prod μ1) :=
    Integrable.mul_prod (f := fl) (g := fun t => 5 * t ^ 4 * Ep G v t r) integrableOn_fl
      (int_Ep G v r)
  have hi3 : Integrable (fun θ : ℝ × ℝ => (fl θ.1 * (-Real.log θ.1)) * (5 * θ.2 ^ 4 * Nc G v θ.2 r))
      (μ1.prod μ1) := Integrable.mul_prod (f := fun z => fl z * (-Real.log z))
        (g := fun t => 5 * t ^ 4 * Nc G v t r) integrableOn_flw (int_Nc G v r)
  have hi5 : Integrable (fun θ : ℝ × ℝ => fl θ.1 * (5 * θ.2 ^ 4 * Nc G v θ.2 r)) (μ1.prod μ1) :=
    Integrable.mul_prod (f := fl) (g := fun t => 5 * t ^ 4 * Nc G v t r) integrableOn_fl
      (int_Nc G v r)
  have hi4 : Integrable (fun θ : ℝ × ℝ => 25 * θ.2 ^ 4 * θ.1 ^ 4 * (-Real.log θ.1) *
      SB G v θ.1 θ.2 r) (μ1.prod μ1) := by
    have e : (fun θ : ℝ × ℝ => 25 * θ.2 ^ 4 * θ.1 ^ 4 * (-Real.log θ.1) * SB G v θ.1 θ.2 r) =
        fun θ => ∑ x ∈ Rv G v r, F3 (tau G r x) (r x) θ := by
      funext θ; unfold SB Bs F3; rw [Finset.sum_filter, Finset.mul_sum]
    rw [e]
    apply integrable_finset_sum; intro x hx
    have hρ : 0 < r x := lt_of_lt_of_le (tau_pos' G v r hr x) (tau_le_r G r x)
    refine Integrable.of_bound (meas_F3 _ _).aestronglyMeasurable 25 ?_
    filter_upwards [ae_mem2] with θ hθ
    have := F3_bound (tau G r x) (r x) hρ θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
  have hpt : ∀ᵐ θ ∂(μ1.prod μ1), 0 ≤
      fl θ.1 * (5 * θ.2 ^ 4) * Λ2 G v θ.1 θ.2 r + fl θ.1 * (5 * θ.2 ^ 4 * Ep G v θ.2 r) +
      (fl θ.1 * (-Real.log θ.1)) * (5 * θ.2 ^ 4 * Nc G v θ.2 r) -
      25 * θ.2 ^ 4 * θ.1 ^ 4 * (-Real.log θ.1) * SB G v θ.1 θ.2 r -
      Real.log 4 * (fl θ.1 * (5 * θ.2 ^ 4 * Nc G v θ.2 r)) := by
    filter_upwards [ae_mem2] with θ hθ
    obtain ⟨⟨hl, hl1⟩, ⟨ht, ht1⟩⟩ := hθ
    have hI := I2 G v θ.1 θ.2 hl hl1 ht ht1 r hr
    rw [one_div, Real.log_inv] at hI
    have hfl0 : 0 ≤ fl θ.1 := fl_nonneg θ.1 ⟨hl, hl1⟩
    have hlog : 0 < Real.log (1 + 4 * θ.1) := Real.log_pos (by linarith)
    have hfl : fl θ.1 * Real.log (1 + 4 * θ.1) = 5 * θ.1 ^ 4 * (-Real.log θ.1) := by
      unfold fl; rw [div_mul_cancel₀ _ (ne_of_gt hlog)]
    have hW : 0 ≤ fl θ.1 * (5 * θ.2 ^ 4) := by positivity
    have key := mul_le_mul_of_nonneg_left hI hW
    have e4 : 25 * θ.2 ^ 4 * θ.1 ^ 4 * (-Real.log θ.1) * SB G v θ.1 θ.2 r =
        fl θ.1 * (5 * θ.2 ^ 4) * (Real.log (1 + 4 * θ.1) * SB G v θ.1 θ.2 r) := by
      rw [show fl θ.1 * (5 * θ.2 ^ 4) * (Real.log (1 + 4 * θ.1) * SB G v θ.1 θ.2 r) =
        (fl θ.1 * Real.log (1 + 4 * θ.1)) * (5 * θ.2 ^ 4) * SB G v θ.1 θ.2 r by ring, hfl]
      ring
    rw [e4]
    have ee : fl θ.1 * (5 * θ.2 ^ 4) * Λ2 G v θ.1 θ.2 r + fl θ.1 * (5 * θ.2 ^ 4 * Ep G v θ.2 r) +
        (fl θ.1 * (-Real.log θ.1)) * (5 * θ.2 ^ 4 * Nc G v θ.2 r) -
        fl θ.1 * (5 * θ.2 ^ 4) * (Real.log (1 + 4 * θ.1) * SB G v θ.1 θ.2 r) -
        Real.log 4 * (fl θ.1 * (5 * θ.2 ^ 4 * Nc G v θ.2 r)) =
        fl θ.1 * (5 * θ.2 ^ 4) * (Λ2 G v θ.1 θ.2 r + Ep G v θ.2 r + -Real.log θ.1 * Nc G v θ.2 r) -
        fl θ.1 * (5 * θ.2 ^ 4) * (Real.log (1 + 4 * θ.1) * SB G v θ.1 θ.2 r +
          Real.log 4 * Nc G v θ.2 r) := by ring
    rw [ee]
    linarith [key]
  have h := integral_nonneg_of_ae hpt
  have j12 : Integrable (fun θ : ℝ × ℝ => fl θ.1 * (5 * θ.2 ^ 4) * Λ2 G v θ.1 θ.2 r +
      fl θ.1 * (5 * θ.2 ^ 4 * Ep G v θ.2 r)) (μ1.prod μ1) := hi1.add hi2
  have j123 : Integrable (fun θ : ℝ × ℝ => fl θ.1 * (5 * θ.2 ^ 4) * Λ2 G v θ.1 θ.2 r +
      fl θ.1 * (5 * θ.2 ^ 4 * Ep G v θ.2 r) +
      (fl θ.1 * (-Real.log θ.1)) * (5 * θ.2 ^ 4 * Nc G v θ.2 r)) (μ1.prod μ1) := j12.add hi3
  have j1234 : Integrable (fun θ : ℝ × ℝ => fl θ.1 * (5 * θ.2 ^ 4) * Λ2 G v θ.1 θ.2 r +
      fl θ.1 * (5 * θ.2 ^ 4 * Ep G v θ.2 r) +
      (fl θ.1 * (-Real.log θ.1)) * (5 * θ.2 ^ 4 * Nc G v θ.2 r) -
      25 * θ.2 ^ 4 * θ.1 ^ 4 * (-Real.log θ.1) * SB G v θ.1 θ.2 r) (μ1.prod μ1) := j123.sub hi4
  have j5 : Integrable (fun θ : ℝ × ℝ =>
      Real.log 4 * (fl θ.1 * (5 * θ.2 ^ 4 * Nc G v θ.2 r))) (μ1.prod μ1) := hi5.const_mul _
  rw [integral_sub j1234 j5, integral_sub j123 hi4, integral_add j12 hi3,
    integral_add hi1 hi2, integral_const_mul] at h
  have e2 : ∫ θ, fl θ.1 * (5 * θ.2 ^ 4 * Ep G v θ.2 r) ∂(μ1.prod μ1) =
      uc * (5 * D G v 5 r + X G v 5 r) := by
    rw [integral_prod_mul (fun x => fl x) (fun t => 5 * t ^ 4 * Ep G v t r), integral_fl, S2 G v r hr]
  have e3 : ∫ θ, (fl θ.1 * (-Real.log θ.1)) * (5 * θ.2 ^ 4 * Nc G v θ.2 r) ∂(μ1.prod μ1) =
      wc * X G v 5 r := by
    rw [integral_prod_mul (fun x => fl x * (-Real.log x)) (fun t => 5 * t ^ 4 * Nc G v t r),
      integral_flw, S1 G v r hr]
  have e5 : ∫ θ, fl θ.1 * (5 * θ.2 ^ 4 * Nc G v θ.2 r) ∂(μ1.prod μ1) = uc * X G v 5 r := by
    rw [integral_prod_mul (fun x => fl x) (fun t => 5 * t ^ 4 * Nc G v t r), integral_fl, S1 G v r hr]
  have e1 : ∫ θ, fl θ.1 * (5 * θ.2 ^ 4) * Λ2 G v θ.1 θ.2 r ∂(μ1.prod μ1) = uc * L2 G v r := by
    unfold L2
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_mem2] with θ hθ
    have hfl0 : 0 ≤ fl θ.1 := fl_nonneg θ.1 hθ.1
    have h0 : 0 ≤ fl θ.1 * (5 * θ.2 ^ 4) / uc := by positivity
    rw [show ((φ2 θ : ℝ)) = fl θ.1 * (5 * θ.2 ^ 4) / uc from Real.coe_toNNReal _ h0]
    field_simp
  rw [e1, e2, e3, e5, S3 G v r hr] at h
  linarith

end L32
end LPM


-- ===== Solutions.LPM.L32g =====

set_option autoImplicit false

namespace LPM
namespace L32
open MeasureTheory Set LocalProbeMIS871.Greedy Function
open scoped Classical ENNReal NNReal

variable {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)

theorem M_le (r : Fin n → ℝ) (hr : GoodRanks v r) : M G v 5 r - 1 ≤ X G v 5 r := by
  have hv : v ∈ R G v r := (mem_R_iff G v r v).2 Relation.ReflTransGen.refl
  unfold M X
  rw [← Finset.add_sum_erase _ _ hv]
  have h1 := tau_le_one' G v r hr v
  have h0 := tau_pos' G v r hr v
  rw [rpow5]
  have : tau G r v ^ 5 ≤ 1 := pow_le_one₀ h0.le h1
  linarith

theorem X_nonneg (r : Fin n → ℝ) (hr : GoodRanks v r) : 0 ≤ X G v 5 r := by
  unfold X
  exact Finset.sum_nonneg (fun u _ => Real.rpow_nonneg (tau_pos' G v r hr u).le _)

theorem lemma_3_2_proof : ExpBound (forcedLaw v) (fun r => (M G v 5 r - 1) / 160) 2 := by
  obtain ⟨_, _, ⟨hu0, hu5⟩, hκ⟩ := lemma_A_1
  set uc := coeffU 5
  set wc := coeffW 5
  refine ⟨((measurable_M G v 5).sub_const 1 |>.div_const 160).aemeasurable, ?_⟩
  have hpt : ∀ᵐ r ∂forcedLaw v, ENNReal.ofReal (Real.exp ((M G v 5 r - 1) / 160)) ≤
      ENNReal.ofReal (5 * uc) * ENNReal.ofReal (Real.exp (L2 G v r)) +
        ENNReal.ofReal (1 - 5 * uc) * ENNReal.ofReal (Real.exp (L1 G v r)) := by
    filter_upwards [ae_goodRanks v] with r hr
    have t1 := T1 G v r hr
    have t2 := T2 G v r hr hu0
    have hX := X_nonneg G v r hr
    have hM := M_le G v r hr
    have hc : 0 ≤ 1 - 5 * uc := by linarith
    have t1' := mul_le_mul_of_nonneg_left t1 hc
    have key : (Real.log 4 - 1 - 5 * wc) * X G v 5 r ≤ 5 * uc * L2 G v r + (1 - 5 * uc) * L1 G v r := by
      nlinarith
    have hstep : (M G v 5 r - 1) / 160 ≤ 5 * uc * L2 G v r + (1 - 5 * uc) * L1 G v r := by
      have : X G v 5 r / 160 ≤ (Real.log 4 - 1 - 5 * wc) * X G v 5 r := by nlinarith
      linarith
    have hconv := convexOn_exp.2 (Set.mem_univ (L2 G v r)) (Set.mem_univ (L1 G v r))
      (by linarith : (0:ℝ) ≤ 5 * uc) hc (by ring)
    simp only [smul_eq_mul] at hconv
    rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hc,
      ← ENNReal.ofReal_add (by positivity) (mul_nonneg hc (Real.exp_pos _).le)]
    apply ENNReal.ofReal_le_ofReal
    exact (Real.exp_le_exp.2 hstep).trans hconv
  have hm2 : Measurable (fun r => ENNReal.ofReal (5 * uc) * ENNReal.ofReal (Real.exp (L2 G v r))) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (meas_L2 G v)))
  have hm1 : Measurable (fun r => ENNReal.ofReal (Real.exp (L1 G v r))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (meas_L1 G v))
  have hm2' : Measurable (fun r => ENNReal.ofReal (Real.exp (L2 G v r))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (meas_L2 G v))
  calc ∫⁻ r, ENNReal.ofReal (Real.exp ((M G v 5 r - 1) / 160)) ∂forcedLaw v
      ≤ ∫⁻ r, (ENNReal.ofReal (5 * uc) * ENNReal.ofReal (Real.exp (L2 G v r)) +
        ENNReal.ofReal (1 - 5 * uc) * ENNReal.ofReal (Real.exp (L1 G v r))) ∂forcedLaw v :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (5 * uc) * ∫⁻ r, ENNReal.ofReal (Real.exp (L2 G v r)) ∂forcedLaw v +
        ENNReal.ofReal (1 - 5 * uc) * ∫⁻ r, ENNReal.ofReal (Real.exp (L1 G v r)) ∂forcedLaw v := by
        rw [lintegral_add_left hm2, lintegral_const_mul _ hm2', lintegral_const_mul _ hm1]
    _ ≤ ENNReal.ofReal (5 * uc) * 2 + ENNReal.ofReal (1 - 5 * uc) * 2 := by
        gcongr
        · exact expL2 G v hu0
        · exact expL1 G v
    _ = ENNReal.ofReal 2 := by
        rw [← add_mul, ← ENNReal.ofReal_add (by linarith) (by linarith)]
        rw [show 5 * uc + (1 - 5 * uc) = 1 by ring, ENNReal.ofReal_one, one_mul]
        norm_num

end L32
end LPM


open MeasureTheory
open scoped BigOperators Classical
noncomputable section
open LocalProbeMIS871.Greedy

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    ExpBound (forcedLaw v) (fun r => (M G v 5 r - 1) / 160) 2 :=
  LPM.L32.lemma_3_2_proof G v

