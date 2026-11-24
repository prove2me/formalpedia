-- Prove2me | solution 1 for LocalProbeMIS871.Greedy.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:18:26.673977+00:00
-- url     : https://prove2.me/submissions/43511583-2b09-4c52-a1f3-286be0c402dd

import Definitions.Def_LocalProbeMIS871_Greedy_Elimination
import Theorems.Thm_LocalProbeMIS871_Greedy_lemma_3_2
import Theorems.Thm_LocalProbeMIS871_Greedy_lemma_3_3

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


-- ===== Solutions.LPM.Mono =====

set_option autoImplicit false

namespace LPM
open LocalProbeMIS871.Greedy MeasureTheory
open scoped Classical

variable {n : ℕ}

theorem key_forceRoot_ne (r : Fin n → ℝ) (v u : Fin n) (h : u ≠ v) :
    key (forceRoot v r) u = key r u := by
  simp [key, forceRoot, Function.update_of_ne h]

theorem key_le_forceRoot (r : Fin n → ℝ) (v : Fin n) (hv : r v ≤ 1) :
    key r v ≤ key (forceRoot v r) v := by
  simp only [key, forceRoot, Function.update_self]
  rw [Prod.Lex.toLex_le_toLex]
  rcases lt_or_eq_of_le hv with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, le_rfl⟩

theorem inMIS_forceRoot (G : SimpleGraph (Fin n)) (r : Fin n → ℝ) (v : Fin n) (hv : r v ≤ 1) :
    ∀ u, key r u < key r v →
      RGMISFast.inMIS G (key (forceRoot v r)) u = RGMISFast.inMIS G (key r) u := by
  intro u
  induction hk : RGMISFast.rk (key r) u using Nat.strong_induction_on generalizing u with
  | _ k ih =>
    intro hu
    have huv : u ≠ v := by rintro rfl; exact lt_irrefl _ hu
    apply Bool.eq_iff_iff.2
    rw [inMIS_iff, inMIS_iff]
    rw [key_forceRoot_ne r v u huv]
    constructor
    · intro H w hw hlt
      have hwv : w ≠ v := by rintro rfl; exact lt_asymm hlt hu
      have := H w hw (by rwa [key_forceRoot_ne r v w hwv])
      rwa [ih _ (hk ▸ RGMISFast.rk_lt _ hlt) w rfl (hlt.trans hu)] at this
    · intro H w hw hlt
      have hwv : w ≠ v := by
        intro e
        rw [e] at hlt
        exact absurd (lt_trans hlt hu) (not_lt.2 (key_le_forceRoot r v hv))
      rw [key_forceRoot_ne r v w hwv] at hlt
      rw [ih _ (hk ▸ RGMISFast.rk_lt _ hlt) w rfl (hlt.trans hu)]
      exact H w hw hlt

theorem R_subset_forceRoot (G : SimpleGraph (Fin n)) (v : Fin n) (r : Fin n → ℝ)
    (hv : r v ≤ 1) : R G v r ⊆ R G v (forceRoot v r) := by
  intro u hu
  rw [mem_R_iff] at hu ⊢
  have key1 : ∀ x, Relation.ReflTransGen (Call G r) v x →
      Relation.ReflTransGen (Call G (forceRoot v r)) v x ∧ (x = v ∨ key r x < key r v) := by
    intro x hx
    induction hx with
    | refl => exact ⟨Relation.ReflTransGen.refl, Or.inl rfl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨ih1, ih2⟩ := ih
      obtain ⟨hadj, hlt, hlow⟩ := hbc
      have hcv : key r c < key r v := by
        rcases ih2 with rfl | h
        · exact hlt
        · exact hlt.trans h
      have hcv' : c ≠ v := by rintro rfl; exact lt_irrefl _ hcv
      refine ⟨ih1.tail ⟨hadj, ?_, ?_⟩, Or.inr hcv⟩
      · rw [key_forceRoot_ne r v c hcv']
        rcases ih2 with rfl | h
        · exact lt_of_lt_of_le hlt (key_le_forceRoot r b hv)
        · rwa [key_forceRoot_ne r v b (by rintro rfl; exact lt_irrefl _ h)]
      · intro z hz hzc
        have hzv : z ≠ v := by
          rintro rfl
          rw [key_forceRoot_ne r z c hcv'] at hzc
          exact absurd (hzc.trans hcv) (not_lt.2 (key_le_forceRoot r z hv))
        rw [key_forceRoot_ne r v z hzv, key_forceRoot_ne r v c hcv'] at hzc
        rw [inMIS_forceRoot G r v hv z (hzc.trans hcv)]
        exact hlow z hz hzc
  exact (key1 u hu).1

theorem U_le_forceRoot (G : SimpleGraph (Fin n)) (v : Fin n) (r : Fin n → ℝ) (hv : r v ≤ 1) :
    U G v r ≤ U G v (forceRoot v r) :=
  Finset.card_le_card (R_subset_forceRoot G v r hv)

end LPM


-- ===== Solutions.LPM.T31 =====

set_option autoImplicit false

namespace LPM
open LocalProbeMIS871.Greedy MeasureTheory
open scoped Classical

theorem markov_exp {m : ℕ} {μ : Measure (Fin m → ℝ)} (f : (Fin m → ℝ) → ℝ) (b c : ℝ)
    (h : ExpBound μ f b) : μ {x | c < f x} ≤ ENNReal.ofReal (b / Real.exp c) := by
  obtain ⟨hm, hint⟩ := h
  have hm' : AEMeasurable (fun x => ENNReal.ofReal (Real.exp (f x))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (Real.measurable_exp.comp_aemeasurable hm)
  have hε : ENNReal.ofReal (Real.exp c) ≠ 0 := by
    simp [Real.exp_pos]
  calc μ {x | c < f x}
      ≤ μ {x | ENNReal.ofReal (Real.exp c) ≤ ENNReal.ofReal (Real.exp (f x))} := by
        apply measure_mono
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hx.le)
    _ ≤ (∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂μ) / ENNReal.ofReal (Real.exp c) :=
        meas_ge_le_lintegral_div hm' hε (by simp)
    _ ≤ ENNReal.ofReal b / ENNReal.ofReal (Real.exp c) := by gcongr
    _ = ENNReal.ofReal (b / Real.exp c) := by
        rw [ENNReal.ofReal_div_of_pos (Real.exp_pos c)]

variable {n : ℕ}

theorem Q_le (G : SimpleGraph (Fin n)) (lists : AdjacencyLists G) (Δ : ℕ)
    (hdeg : ∀ u, G.degree u ≤ Δ) (v : Fin n) (r : Fin n → ℝ) :
    (Q G lists v r : ℝ) ≤ (1 + Δ) * (U G v r : ℝ) := by
  unfold Q U
  push_cast
  calc ∑ u ∈ R G v r, ((1 : ℝ) + (G.degree u : ℝ)) ≤ ∑ u ∈ R G v r, ((1 : ℝ) + Δ) := by
        apply Finset.sum_le_sum; intro u _; gcongr; exact_mod_cast hdeg u
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem rankLaw_root_gt_one (v : Fin n) : rankLaw n {r | 1 < r v} = 0 := by
  have : {r : Fin n → ℝ | 1 < r v} = Function.eval v ⁻¹' (Set.Ioi 1) := rfl
  rw [this, rankLaw]
  apply Measure.pi_eval_preimage_null
  rw [Measure.restrict_apply measurableSet_Ioi]
  have : Set.Ioi (1 : ℝ) ∩ Set.Ioo 0 1 = ∅ := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo, Set.mem_empty_iff_false,
      iff_false, not_and]; intro h1 _ h2; linarith
  rw [this, measure_empty]

theorem theorem_3_1_proof : ∃ C : ℝ, 0 < C ∧
    ∀ (n Δ : ℕ), 2 ≤ Δ → ∀ G : SimpleGraph (Fin n), (∀ u, G.degree u ≤ Δ) →
    ∀ lists : AdjacencyLists G, ∀ v : Fin n, ∀ ell : ℝ, 0 ≤ ell →
      rankLaw n {r | C * (Δ : ℝ) ^ (6 : ℕ) * (1 + ell) < (Q G lists v r : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-ell)) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 8 ^ 5 * 400 + 8 := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; norm_num
  refine ⟨2 * K, by positivity, ?_⟩
  intro n Δ hΔ G hdeg lists v ell hell
  have hΔ1 : (1 : ℝ) ≤ Δ := by exact_mod_cast (by omega : 1 ≤ Δ)
  have hΔ5 : (1 : ℝ) ≤ (Δ : ℝ) ^ 5 := one_le_pow₀ hΔ1
  have hlog4 : Real.log 4 < 1.3863 := by
    have := Real.log_two_lt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [h4]; linarith
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  -- the two tails under the forced law
  set c1 : ℝ := 1 + ell + Real.log 2
  set c2 : ℝ := ell + Real.log 4
  have t1 := markov_exp _ _ c1 (lemma_3_3 G Δ hΔ hdeg v 5 (by norm_num))
  have t2 := markov_exp _ _ c2 (lemma_3_2 G v)
  have e1 : Real.exp 1 / Real.exp c1 = Real.exp (-ell) / 2 := by
    simp only [c1]
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2), Real.exp_neg]
    field_simp
  have e2 : 2 / Real.exp c2 = Real.exp (-ell) / 2 := by
    simp only [c2]
    rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 4), Real.exp_neg]
    field_simp; ring
  rw [e1] at t1
  rw [e2] at t2
  set S : Set (Fin n → ℝ) := {r | K * (Δ : ℝ) ^ 5 * (1 + ell) < (U G v r : ℝ)} with hS
  have hSsub : S ⊆ {r | c1 < ((U G v r : ℝ) - (8 * (Δ : ℝ)) ^ (5 : ℝ) * M G v 5 r) / 4} ∪
      {r | c2 < (M G v 5 r - 1) / 160} := by
    intro r hr
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hc
    obtain ⟨h1, h2⟩ := hc
    simp only [hS, Set.mem_ofPred_eq] at hr
    have hM : M G v 5 r ≤ 1 + 160 * c2 := by linarith
    have h8 : (8 * (Δ : ℝ)) ^ (5 : ℝ) = 8 ^ 5 * (Δ : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [h8] at h1
    have hU : (U G v r : ℝ) ≤ 8 ^ 5 * (Δ : ℝ) ^ 5 * M G v 5 r + 4 * c1 := by linarith
    have hpos : (0 : ℝ) ≤ 8 ^ 5 * (Δ : ℝ) ^ 5 := by positivity
    have : 8 ^ 5 * (Δ : ℝ) ^ 5 * M G v 5 r ≤ 8 ^ 5 * (Δ : ℝ) ^ 5 * (400 * (1 + ell)) := by
      apply mul_le_mul_of_nonneg_left _ hpos
      simp only [c2] at hM; nlinarith
    have hc1 : 4 * c1 ≤ 8 * (Δ : ℝ) ^ 5 * (1 + ell) := by
      simp only [c1]; nlinarith
    have : (U G v r : ℝ) ≤ K * (Δ : ℝ) ^ 5 * (1 + ell) := by
      rw [hK]; nlinarith
    linarith
  have hSmeas : MeasurableSet S :=
    measurableSet_lt measurable_const (measurable_U G v)
  have hforced : forcedLaw v S ≤ ENNReal.ofReal (Real.exp (-ell)) := by
    calc forcedLaw v S ≤ forcedLaw v _ + forcedLaw v _ :=
          (measure_mono hSsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (Real.exp (-ell) / 2) + ENNReal.ofReal (Real.exp (-ell) / 2) :=
          add_le_add t1 t2
      _ = ENNReal.ofReal (Real.exp (-ell)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  rw [forcedLaw, Measure.map_apply (measurable_forceRoot v) hSmeas] at hforced
  calc rankLaw n {r | 2 * K * (Δ : ℝ) ^ (6 : ℕ) * (1 + ell) < (Q G lists v r : ℝ)}
      ≤ rankLaw n (forceRoot v ⁻¹' S ∪ {r | 1 < r v}) := by
        apply measure_mono
        intro r hr
        simp only [Set.mem_ofPred_eq] at hr
        by_contra hc
        simp only [Set.mem_union, Set.mem_preimage, hS, Set.mem_ofPred_eq, not_or, not_lt] at hc
        obtain ⟨h1, h2⟩ := hc
        have hU := U_le_forceRoot G v r h2
        have hQ := Q_le G lists Δ hdeg v r
        have hU' : (U G v r : ℝ) ≤ U G v (forceRoot v r) := by exact_mod_cast hU
        have hUb : (U G v r : ℝ) ≤ K * (Δ : ℝ) ^ 5 * (1 + ell) := hU'.trans h1
        have hU0 : (0 : ℝ) ≤ (U G v r : ℝ) := Nat.cast_nonneg _
        have hm : (1 + (Δ : ℝ)) * (U G v r : ℝ) ≤ (2 * Δ) * (K * (Δ : ℝ) ^ 5 * (1 + ell)) :=
          mul_le_mul (by linarith) hUb hU0 (by linarith)
        have he : (2 * (Δ : ℝ)) * (K * (Δ : ℝ) ^ 5 * (1 + ell)) =
            2 * K * (Δ : ℝ) ^ (6 : ℕ) * (1 + ell) := by ring
        linarith
    _ ≤ rankLaw n (forceRoot v ⁻¹' S) + rankLaw n {r | 1 < r v} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-ell)) := by
        rw [rankLaw_root_gt_one, add_zero]; exact hforced

end LPM


open MeasureTheory
open scoped BigOperators Classical
noncomputable section
open LocalProbeMIS871.Greedy

theorem solution : ∃ C : ℝ, 0 < C ∧
    ∀ (n Δ : ℕ), 2 ≤ Δ → ∀ G : SimpleGraph (Fin n), (∀ u, G.degree u ≤ Δ) →
    ∀ lists : AdjacencyLists G, ∀ v : Fin n, ∀ ell : ℝ, 0 ≤ ell →
      rankLaw n {r | C * (Δ : ℝ) ^ (6 : ℕ) * (1 + ell) < (Q G lists v r : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-ell)) :=
  LPM.theorem_3_1_proof

