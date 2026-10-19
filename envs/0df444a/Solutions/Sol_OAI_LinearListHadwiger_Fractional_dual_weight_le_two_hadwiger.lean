-- Prove2me | solution 1 for OAI.LinearListHadwiger.Fractional.dual_weight_le_two_hadwiger
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:46:51.471303+00:00
-- url     : https://prove2.me/submissions/80c85e98-71dd-42a6-990d-73eae3e1a420

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_OAIQWLLH000

section
-- module Solutions.OAIQW_ListHadwiger.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

theorem cliqueMinor_order_le_card {V : Type} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (h : HasCliqueMinor G t) : t ≤ Fintype.card V := by
  classical
  obtain ⟨B, hc, hd, _⟩ := h
  have hb : ∀ i, ∃ v, v ∈ B i := fun i => by
    obtain ⟨v⟩ := (hc i).nonempty
    exact ⟨v.val, v.property⟩
  choose v hv using hb
  have hi : Function.Injective v := by
    intro i j hij
    by_contra hn
    exact Set.disjoint_left.mp (hd i j hn) (hv i) (by
      rw [hij]
      exact hv j)
  simpa using Fintype.card_le_of_injective v hi

theorem hadwiger_bddAbove {V : Type} [Fintype V] (G : SimpleGraph V) :
    BddAbove {t : ℕ | HasCliqueMinor G t} :=
  ⟨Fintype.card V, fun _ h => cliqueMinor_order_le_card h⟩

theorem cliqueMinor_le_hadwigerNumber {V : Type} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (h : HasCliqueMinor G t) : t ≤ hadwigerNumber G :=
  le_csSup (hadwiger_bddAbove G) h

theorem cliqueMinor_one {V : Type} [Nonempty V] (G : SimpleGraph V) :
    HasCliqueMinor G 1 := by
  classical
  let v : V := Classical.choice inferInstance
  refine ⟨fun _ => {v}, ?_, ?_, ?_⟩
  · intro i
    exact SimpleGraph.Connected.of_subsingleton
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

theorem one_le_hadwigerNumber {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : 1 ≤ hadwigerNumber G :=
  cliqueMinor_le_hadwigerNumber (cliqueMinor_one G)

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.EggCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ReedSeymour
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V}

lemma loops_even_of_cycles_even
    (h : ∀ (v : V) (p : G.Walk v v), p.IsCycle → Even p.length) :
    ∀ (v : V) (p : G.Walk v v), Even p.length := by
  suffices ∀ n (v : V) (p : G.Walk v v), p.length = n → Even p.length by
    intro v p
    exact this p.length v p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v p hn
    cases p with
    | nil => simp
    | @cons _ a b hab q =>
      by_cases hp : q.IsPath
      · by_cases hl : 3 ≤ (q.cons hab).length
        · exact h _ _ (Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨by simpa using hp, hl⟩)
        · have hpos : 0 < q.length := by
            by_contra hnot
            have hh : q.Nil := by simpa using (show q.length = 0 by omega)
            exact hab.ne hh.eq.symm
          have hh : (q.cons hab).length = 2 := by simp only [Walk.length_cons] at *; omega
          simp [hh]
      · rw [Walk.isPath_iff_isSubwalk_imp_nil] at hp
        push Not at hp
        obtain ⟨x, c, ⟨a, b, hq⟩, hc⟩ := hp
        have hcpos : 0 < c.length := by
          by_contra hh
          apply hc
          simpa using (show c.length = 0 by omega)
        have heq : n = a.length + c.length + b.length + 1 := by
          rw [hq, Walk.length_cons, Walk.length_append, Walk.length_append] at hn
          omega
        have ec := ih c.length (by omega) x c rfl
        have er := ih ((b.append (a.cons hab)).length) (by
          simp only [Walk.length_append, Walk.length_cons]; omega) x
          (b.append (a.cons hab)) rfl
        rw [hq]
        simp only [Walk.length_cons, Walk.length_append] at er ⊢
        rw [Nat.even_iff] at ec er ⊢
        omega

lemma two_colorable_of_cycles_even
    (h : ∀ (v : V) (p : G.Walk v v), p.IsCycle → Even p.length) :
    G.Colorable 2 :=
  SimpleGraph.two_colorable_iff_forall_loop_even.mpr (loops_even_of_cycles_even h)

lemma Shortest.adj_indices {a b : V} {p : G.Walk a b} (hp : Shortest p)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (he : G.Adj (p.getVert i) (p.getVert j)) : i + 1 = j ∨ j + 1 = i := by
  have hf : ∀ {i j : ℕ}, i ≤ p.length → j ≤ p.length → i < j →
      G.Adj (p.getVert i) (p.getVert j) → i + 1 = j := by
    intro i j hi hj hij he
    have hh := hp ((p.take i).append (he.toWalk.append (p.drop j)))
    simp only [Walk.length_append, Walk.take_length, Walk.drop_length,
      Adj.length_toWalk, Nat.min_eq_left hi] at hh
    omega
  rcases lt_trichotomy i j with hij | hij | hij
  · exact Or.inl (hf hi hj hij he)
  · exact (he.ne (congrArg p.getVert hij)).elim
  · exact Or.inr (hf hj hi hij he.symm)

lemma ReachOn.right {S : Set V} {a b : V} (h : ReachOn G S a b) : b ∈ S :=
  h.choose_spec b h.choose.end_mem_support
lemma ReachOn.refl {S : Set V} {a : V} (h : a ∈ S) : ReachOn G S a a :=
  ⟨.nil, by simpa using h⟩

lemma component_subset (S : Set V) (a : V) : component G S a ⊆ S :=
  fun _ hb => hb.right

lemma component_connected {S : Set V} {a : V} (ha : a ∈ S) :
    (G.induce (component G S a)).Connected := by
  refine connected_iff_reachOn.mpr ⟨⟨a, ReachOn.refl ha⟩, ?_⟩
  intro x hx y hy
  obtain ⟨p, hp⟩ := hx.symm.trans hy
  refine ⟨p, fun z hz => ?_⟩
  classical
  have hreach : ReachOn G S x z := ⟨p.takeUntil z hz, fun t ht =>
    hp t (p.support_takeUntil_subset_support hz ht)⟩
  exact hx.trans hreach

lemma cycle_delete_connected_root {a : V} {p : G.Walk a a} (hp : p.IsCycle) :
    (G.induce ({v | v ∈ p.support} \ {a})).Connected := by
  cases p with
  | nil => exact (Walk.not_isCycle_nil hp).elim
  | @cons _ b c hab q =>
    have hq : q.IsPath := (Walk.cons_isCycle_iff q hab).mp hp |>.1
    have hn : ¬q.Nil := Walk.not_nil_of_isCycle_cons hp
    have hd := hq.support_nodup
    rw [← q.support_dropLast_concat hn, List.nodup_append] at hd
    have ha : a ∉ q.dropLast.support := by simpa using hd.2.2 a
    have he : ({v | v ∈ (q.cons hab).support} \ {a} : Set V) =
        {v | v ∈ q.dropLast.support} := by
      ext v
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
        Walk.support_cons, List.mem_cons, ← q.support_dropLast_concat hn,
        List.mem_append]
      have hh : v ∈ q.dropLast.support → v ≠ a := by rintro hv rfl; exact ha hv
      tauto
    rw [he]
    exact q.dropLast.connected_induce_support

lemma cycle_delete_connected {a v : V} {p : G.Walk a a} (hp : p.IsCycle)
    (hv : v ∈ p.support) : (G.induce ({x | x ∈ p.support} \ {v})).Connected := by
  classical
  have he : {x | x ∈ (p.rotate v hv).support} = {x | x ∈ p.support} := by
    ext x
    exact Walk.mem_support_rotate_iff p v hv
  have hh := cycle_delete_connected_root (hp.rotate hv)
  rwa [he] at hh

lemma exists_betweenMin (hG : G.Connected) {A B : Set V} (hA : A.Nonempty)
    (hB : B.Nonempty) : ∃ (a b : V) (p : G.Walk a b), BetweenMin G A B a b p := by
  have hex : ∃ n : ℕ, ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b, p.length = n := by
    obtain ⟨a,ha⟩ := hA
    obtain ⟨b,hb⟩ := hB
    obtain ⟨p⟩ := hG a b
    exact ⟨p.length,a,ha,b,hb,p,rfl⟩
  classical
  obtain ⟨a,ha,b,hb,p,hp⟩ := Nat.find_spec hex
  refine ⟨a,b,p,ha,hb,?_⟩
  intro x hx y hy q
  rw [hp]
  exact Nat.find_min' hex ⟨x,hx,y,hy,q,rfl⟩

lemma BetweenMin.shortest {A B : Set V} {a b : V} {p : G.Walk a b}
    (h : BetweenMin G A B a b p) : Shortest p :=
  h.minimal a h.source b h.target

lemma BetweenMin.source_only {A B : Set V} {a b x : V} {p : G.Walk a b}
    (h : BetweenMin G A B a b p) (hx : x ∈ p.support) (hxA : x ∈ A) : x = a := by
  obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  have hh := h.minimal _ hxA b h.target (p.drop i)
  simp only [Walk.drop_length] at hh
  have : i = 0 := by omega
  simp [this]

lemma BetweenMin.target_only {A B : Set V} {a b x : V} {p : G.Walk a b}
    (h : BetweenMin G A B a b p) (hx : x ∈ p.support) (hxB : x ∈ B) : x = b := by
  obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  have hh := h.minimal a h.source _ hxB (p.take i)
  simp only [Walk.take_length, Nat.min_eq_left hi] at hh
  have : i = p.length := by omega
  simp [this]

lemma Shortest.isPath {a b : V} {p : G.Walk a b} (hp : Shortest p) : p.IsPath := by
  obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
  apply p.isPath_of_length_eq_dist
  exact le_antisymm (hq ▸ hp q) (SimpleGraph.dist_le p)

lemma MinimalConnector.cycle_gate {ι : Type*} {N : ι → Set V}
    (h : MinimalConnector G N) {a v : V} {p : G.Walk a a}
    (hp : p.IsCycle) (hv : v ∈ p.support) :
    ∃ i, Gate G (N i) {x | x ∈ p.support} v := by
  have hc := cycle_delete_connected hp hv
  obtain ⟨b, hb⟩ := (connected_iff_reachOn.mp hc).1
  let D := component G {x | x ≠ v} b
  have hdconn : (G.induce D).Connected := component_connected (by simpa using hb.2)
  have hdproper : D ≠ Set.univ := by
    intro he
    have hh : v ∈ D := he ▸ Set.mem_univ v
    exact (component_subset _ _ hh) rfl
  obtain ⟨i, hi⟩ := h.minimal D hdconn hdproper
  refine ⟨i, ?_⟩
  intro x hx y hy hr
  have hy' : y ∈ ({x | x ∈ p.support} \ {v} : Set V) := ⟨hy, hr.right⟩
  have hby : ReachOn G {x | x ≠ v} b y :=
    (connected_reachOn hc hb hy').mono (fun _ hz => hz.2)
  exact Set.disjoint_left.mp hi (hby.trans hr.symm) hx

lemma Gate.mem_support {N C : Set V} {v a b : V} (h : Gate G N C v)
    (ha : a ∈ N) (hb : b ∈ C) (p : G.Walk a b) : v ∈ p.support := by
  by_contra hn
  exact h a ha b hb ⟨p, fun x hx he => hn (he ▸ hx)⟩

lemma exists_tail {ι : Type*} {N : ι → Set V} (h : MinimalConnector G N)
    {C : Set V} (hC : C.Nonempty) {v : V} (hv : v ∈ C)
    (hg : ∃ i, Gate G (N i) C v) :
    Nonempty (Tail G N C v) := by
  obtain ⟨i,hi⟩ := hg
  obtain ⟨a,b,p,hp⟩ := exists_betweenMin h.connected (h.interfaces i) hC
  have he : v = b := hp.target_only (hi.mem_support hp.source hp.target p) hv
  subst b
  exact ⟨⟨i,a,p,hp,hi⟩⟩

lemma Tail.avoid {ι : Type*} {N : ι → Set V} {C : Set V} {v w : V}
    (t : Tail G N C v) (hw : w ∈ C) (hwv : w ≠ v) : w ∉ t.path.support :=
  fun h => hwv (t.minimum.target_only h hw)

lemma Tail.index_ne {ι : Type*} {N : ι → Set V} {C : Set V} {v w : V}
    (t : Tail G N C v) (s : Tail G N C w) (hv : v ∈ C) (hw : w ∈ C)
    (hvw : v ≠ w) : t.index ≠ s.index := by
  intro he
  have hh := s.gate.mem_support (he ▸ t.minimum.source) hv t.path
  exact t.avoid hw hvw.symm hh

lemma Tail.disjoint {ι : Type*} {N : ι → Set V} {C : Set V} {v w : V}
    (t : Tail G N C v) (s : Tail G N C w) (hv : v ∈ C)
    (hvw : v ≠ w) : Disjoint ({x | x ∈ t.path.support} : Set V)
      {x | x ∈ s.path.support} := by
  classical
  refine Set.disjoint_left.mpr ?_
  intro x hx hy
  have hxv : x ≠ v := by rintro rfl; exact s.avoid hv hvw hy
  have hp := Walk.endpoint_notMem_support_takeUntil t.minimum.shortest.isPath hx (Ne.symm hxv)
  have hs := s.avoid hv hvw
  have hh := t.gate.mem_support t.minimum.source s.minimum.target
    ((t.path.takeUntil x hx).append (s.path.dropUntil x hy))
  rcases (Walk.mem_support_append_iff ..).mp hh with hh | hh
  · exact hp hh
  · exact hs (s.path.support_dropUntil_subset_support hy hh)

lemma Tail.cross_edges {ι : Type*} {N : ι → Set V} {C : Set V} {v w x y : V}
    (t : Tail G N C v) (s : Tail G N C w) (hv : v ∈ C) (hw : w ∈ C)
    (hvw : v ≠ w) (hx : x ∈ t.path.support) (hy : y ∈ s.path.support)
    (hxy : G.Adj x y) : x = v ∧ y = w := by
  classical
  have hf : ∀ {v w x y : V} (t : Tail G N C v) (s : Tail G N C w),
      v ∈ C → v ≠ w → x ∈ t.path.support → y ∈ s.path.support →
      G.Adj x y → x = v := by
    intro v w x y t s hv hvw hx hy hxy
    by_contra hxv
    have hp := Walk.endpoint_notMem_support_takeUntil t.minimum.shortest.isPath hx (Ne.symm hxv)
    have hs := s.avoid hv hvw
    have hh := t.gate.mem_support t.minimum.source s.minimum.target
      ((t.path.takeUntil x hx).append ((s.path.dropUntil y hy).cons hxy))
    rcases (Walk.mem_support_append_iff ..).mp hh with hh | hh
    · exact hp hh
    · simp only [Walk.support_cons, List.mem_cons] at hh
      exact hh.elim (fun he => hxv he.symm)
        (fun hh => hs (s.path.support_dropUntil_subset_support hy hh))
  exact ⟨hf t s hv hvw hx hy hxy, hf s t hw hvw.symm hy hx hxy.symm⟩

lemma Tail.interface_avoid {ι : Type*} {N : ι → Set V} {C : Set V} {v w x : V}
    (t : Tail G N C v) (s : Tail G N C w) (hv : v ∈ C) (hvw : v ≠ w)
    (hx : x ∈ s.path.support) : x ∉ N t.index := by
  classical
  intro hn
  have hh := t.gate.mem_support hn s.minimum.target (s.path.dropUntil x hx)
  exact s.avoid hv hvw (s.path.support_dropUntil_subset_support hx hh)

lemma parity_adj (n : ℕ) : parity n ≠ parity (n+1) := by
  intro he
  have hh := congrArg Fin.val he
  simp only [parity] at hh
  omega

lemma Shortest.idxOf_getVert [DecidableEq V] {a b : V} {p : G.Walk a b}
    (hp : Shortest p) {n : ℕ} (hn : n ≤ p.length) : p.support.idxOf (p.getVert n) = n := by
  rw [p.getVert_eq_support_getElem hn]
  exact hp.isPath.support_nodup.idxOf_getElem n _

lemma Shortest.idxOf_endpoint [DecidableEq V] {a b : V} {p : G.Walk a b}
    (hp : Shortest p) : p.support.idxOf b = p.length := by
  simpa using hp.idxOf_getVert (le_refl p.length)

lemma Shortest.idxOf_start [DecidableEq V] {a b : V} {p : G.Walk a b}
    (hp : Shortest p) : p.support.idxOf a = 0 := by
  simpa using hp.idxOf_getVert (Nat.zero_le p.length)

lemma Shortest.parity_proper [DecidableEq V] {a b x y : V} {p : G.Walk a b}
    (hp : Shortest p) (hx : x ∈ p.support) (hy : y ∈ p.support) (hxy : G.Adj x y)
    (offset : ℕ) : parity (p.support.idxOf x + offset) ≠
      parity (p.support.idxOf y + offset) := by
  have hix : p.support.idxOf x ≤ p.length := by
    have := List.idxOf_lt_length_iff.mpr hx
    simpa only [Walk.length_support, Nat.lt_succ_iff] using this
  have hiy : p.support.idxOf y ≤ p.length := by
    have := List.idxOf_lt_length_iff.mpr hy
    simpa only [Walk.length_support, Nat.lt_succ_iff] using this
  have hh := hp.adj_indices hix hiy (by
    rw [p.getVert_support_idxOf hx, p.getVert_support_idxOf hy]; exact hxy)
  intro he
  have he' := congrArg Fin.val he
  simp only [parity] at he'
  rcases hh with hh | hh <;> omega

lemma tails_split {ι : Type*} {N : ι → Set V} {C : Set V} {v w : V}
    (t : Tail G N C v) (s : Tail G N C w) (hv : v ∈ C) (hw : w ∈ C)
    (hvw : G.Adj v w) (he : parity t.path.length = parity s.path.length) :
    Nonempty (SplitConnector G N) := by
  classical
  let A : Set V := {x | x ∈ t.path.support}
  let B : Set V := {x | x ∈ s.path.support}
  have hd : Disjoint A B := t.disjoint s hv hvw.ne
  let c : V → Fin 2 := fun x => if x ∈ A then parity (t.path.support.idxOf x)
    else parity (s.path.support.idxOf x + 1)
  have hcA : ∀ x ∈ A, c x = parity (t.path.support.idxOf x) :=
    fun x hx => ite_eq_left hx
  have hcB : ∀ x ∈ B, c x = parity (s.path.support.idxOf x + 1) :=
    fun x hx => ite_eq_right (fun hh => Set.disjoint_left.mp hd hh hx)
  refine ⟨{
    left := t.index, right := s.index,
    distinct := t.index_ne s hv hw hvw.ne, carrier := A ∪ B,
    connected := connected_union_of_adj t.path.connected_induce_support
      s.path.connected_induce_support t.path.end_mem_support s.path.end_mem_support hvw,
    color := c, proper := ?_, meets_left := ?_, meets_right := ?_,
    left_color := ?_, right_color := ?_ }⟩
  · intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hcA x hx, hcA y hy]
      simpa using t.minimum.shortest.parity_proper hx hy hxy 0
    · obtain ⟨hxv,hyw⟩ := t.cross_edges s hv hw hvw.ne hx hy hxy
      subst x; subst y
      rw [hcA v hx, hcB w hy, t.minimum.shortest.idxOf_endpoint,
        s.minimum.shortest.idxOf_endpoint, he]
      exact parity_adj _
    · obtain ⟨hxw,hyv⟩ := s.cross_edges t hw hv hvw.ne.symm hx hy hxy
      subst x; subst y
      rw [hcB w hx, hcA v hy, t.minimum.shortest.idxOf_endpoint,
        s.minimum.shortest.idxOf_endpoint, he]
      exact (parity_adj _).symm
    · rw [hcB x hx, hcB y hy]
      exact s.minimum.shortest.parity_proper hx hy hxy 1
  · exact ⟨t.start,Or.inl t.path.start_mem_support,t.minimum.source⟩
  · exact ⟨s.start,Or.inr s.path.start_mem_support,s.minimum.source⟩
  · intro x hx hn
    rcases hx with hx | hx
    · have hh := t.minimum.source_only hx hn
      subst x
      rw [hcA t.start hx, t.minimum.shortest.idxOf_start]
      rfl
    · exact (t.interface_avoid s hv hvw.ne hx hn).elim
  · intro x hx hn
    rcases hx with hx | hx
    · exact (s.interface_avoid t hw hvw.ne.symm hx hn).elim
    · have hh := s.minimum.source_only hx hn
      subst x
      rw [hcB s.start hx, s.minimum.shortest.idxOf_start]
      rfl

lemma MinimalConnector.two_colorable_or_split {ι : Type*} {N : ι → Set V}
    (h : MinimalConnector G N) : G.Colorable 2 ∨ Nonempty (SplitConnector G N) := by
  classical
  by_cases hs : Nonempty (SplitConnector G N)
  · exact Or.inr hs
  left
  apply two_colorable_of_cycles_even
  intro a p hp
  let C : Set V := {x | x ∈ p.support}
  have hC : C.Nonempty := ⟨a,p.start_mem_support⟩
  have ht : ∀ v : C, Nonempty (Tail G N C v) := fun v =>
    exists_tail h hC v.property (h.cycle_gate hp v.property)
  let tails : (v : C) → Tail G N C v := fun v => Classical.choice (ht v)
  have hc : (G.induce C).Colorable 2 := ⟨Coloring.mk
    (fun v => parity (tails v).path.length) (fun {v w} hvw he =>
      hs (tails_split (tails v) (tails w) v.property w.property hvw he))⟩
  have hh := SimpleGraph.two_colorable_iff_forall_loop_even.mp hc
    ⟨a,p.start_mem_support⟩ (p.induce C (fun _ hx => hx))
  have hl := Walk.length_map (p := p.induce C (fun _ hx => hx))
    (f := (Embedding.induce C).toHom)
  rw [Walk.map_induce] at hl
  exact hl.symm ▸ hh

lemma colorable_induce_iff_total {S : Set V} : (G.induce S).Colorable 2 ↔
    ∃ c : V → Fin 2, ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → c x ≠ c y := by
  constructor
  · rintro ⟨c⟩
    refine ⟨extendColor S c, fun x hx y hy hxy => ?_⟩
    simpa only [extendColor_apply c hx, extendColor_apply c hy] using
      c.valid (show (G.induce S).Adj ⟨x,hx⟩ ⟨y,hy⟩ from hxy)
  · rintro ⟨c,hc⟩
    exact ⟨Coloring.mk (fun x => c x) (fun {x y} hxy => hc x x.property y y.property hxy)⟩

lemma colorable_image_val {U : Set V} {S : Set U}
    (h : ((G.induce U).induce S).Colorable 2) :
    (G.induce (Subtype.val '' S)).Colorable 2 := by
  obtain ⟨c,hc⟩ := colorable_induce_iff_total.mp h
  apply colorable_induce_iff_total.mpr
  refine ⟨extendColor U c, ?_⟩
  rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩ hxy
  simpa only [extendColor_apply c a.property, extendColor_apply c b.property] using
    hc a ha b hb hxy

lemma SplitConnector.lift_subset {ι : Type*} {U : Set V} {N : ι → Set V}
    (s : SplitConnector (G.induce U) (fun i => {x | x.val ∈ N i})) :
    s.lift.carrier ⊆ U := by
  rintro x ⟨a,ha,rfl⟩
  exact a.property

lemma exists_minimal_transversal [Finite V] {ι : Type*} {N : ι → Set V}
    (hG : G.Connected) (hN : ∀ i, (N i).Nonempty) :
    ∃ U : Set V, (∀ i, (U ∩ N i).Nonempty) ∧
      MinimalConnector (G.induce U) (fun i => {x | x.val ∈ N i}) := by
  classical
  have := hG.nonempty
  let P : Set V → Prop := fun U => (G.induce U).Connected ∧ ∀ i, (U ∩ N i).Nonempty
  have hp : P Set.univ := by
    refine ⟨?_, fun i => by simpa using hN i⟩
    apply connected_iff_reachOn.mpr
    refine ⟨Set.univ_nonempty, fun a _ b _ => ?_⟩
    obtain ⟨p⟩ := hG a b
    exact ⟨p,fun _ _ => trivial⟩
  have hex : ∃ n : ℕ, ∃ U : Set V, P U ∧ U.ncard = n :=
    ⟨(Set.univ : Set V).ncard,Set.univ,hp,rfl⟩
  obtain ⟨U,hU,hu⟩ := Nat.find_spec hex
  have hmin : ∀ T : Set V, P T → U.ncard ≤ T.ncard := by
    intro T hT
    rw [hu]
    exact Nat.find_min' hex ⟨T,hT,rfl⟩
  refine ⟨U,hU.2,⟨hU.1,?_,?_⟩⟩
  · intro i
    obtain ⟨a,ha,hn⟩ := hU.2 i
    exact ⟨⟨a,ha⟩,hn⟩
  · intro S hS hproper
    by_contra hmiss
    push Not at hmiss
    have hmeet : ∀ i, ((Subtype.val '' S) ∩ N i).Nonempty := by
      intro i
      have hh := Set.not_disjoint_iff.mp (hmiss i)
      obtain ⟨a,ha,hn⟩ := hh
      exact ⟨a,⟨a,ha,rfl⟩,hn⟩
    have him : (Subtype.val '' S : Set V) ⊆ U := by
      rintro _ ⟨a,ha,rfl⟩
      exact a.property
    have hstrict : (Subtype.val '' S : Set V) ⊂ U := by
      refine ⟨him, ?_⟩
      intro he
      apply hproper
      apply Set.eq_univ_of_forall
      intro a
      obtain ⟨b,hb,hab⟩ := he a.property
      have : b = a := Subtype.ext hab
      simpa [this] using hb
    have hc : (Subtype.val '' S : Set V).ncard < U.ncard :=
      Set.ncard_lt_ncard hstrict
    have hh := hmin (Subtype.val '' S) ⟨connected_image_val hS,hmeet⟩
    omega

lemma connected_transversal_or_split [Finite V] {ι : Type*} {N : ι → Set V}
    (hG : G.Connected) (hN : ∀ i, (N i).Nonempty) :
    (∃ U : Set V, (G.induce U).Connected ∧ (∀ i, (U ∩ N i).Nonempty) ∧
      (G.induce U).Colorable 2) ∨ Nonempty (SplitConnector G N) := by
  obtain ⟨U,hU,hm⟩ := exists_minimal_transversal hG hN
  rcases hm.two_colorable_or_split with hc | hs
  · exact Or.inl ⟨U,hm.connected,hU,hc⟩
  · exact Or.inr ⟨(Classical.choice hs).lift⟩

lemma connected_transversal_or_split_on [Finite V] {ι : Type*} {N : ι → Set V}
    {X : Set V} (hX : (G.induce X).Connected)
    (hN : ∀ i, (X ∩ N i).Nonempty) :
    (∃ U : Set V, U ⊆ X ∧ (G.induce U).Connected ∧ (∀ i, (U ∩ N i).Nonempty) ∧
      (G.induce U).Colorable 2) ∨
    ∃ s : SplitConnector G N, s.carrier ⊆ X := by
  have hN' : ∀ i, ({x : X | x.val ∈ N i} : Set X).Nonempty := by
    intro i
    obtain ⟨a,ha,hn⟩ := hN i
    exact ⟨⟨a,ha⟩,hn⟩
  rcases connected_transversal_or_split hX hN' with ⟨U,hU,hn,hc⟩ | hs
  · left
    refine ⟨Subtype.val '' U, ?_,connected_image_val hU,?_,colorable_image_val hc⟩
    · rintro _ ⟨a,ha,rfl⟩
      exact a.property
    · intro i
      obtain ⟨a,ha,hn⟩ := hn i
      exact ⟨a,⟨a,ha,rfl⟩,hn⟩
  · let s := Classical.choice hs
    exact Or.inr ⟨s.lift,s.lift_subset⟩

end ReedSeymour

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.WeightedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ReedSeymour
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V}

section Weights
variable [Fintype V]

lemma mass_univ (w : V → ℝ) : mass w Set.univ = ∑ v, w v := by simp [mass]

lemma mass_two_colors (w : V → ℝ) (S : Set V) (c : V → Fin 2) :
    mass w S = mass w {v | v ∈ S ∧ c v = 0} + mass w {v | v ∈ S ∧ c v = 1} := by
  classical
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have hc : c v = 0 ∨ c v = 1 := by omega
  rcases hc with hc | hc <;> by_cases hv : v ∈ S <;> simp [hc,hv]

lemma heavy_color (w : V → ℝ) (S : Set V) (c : V → Fin 2) :
    ∃ q : Fin 2, mass w S ≤ 2 * mass w {v | v ∈ S ∧ c v = q} := by
  have hh := mass_two_colors w S c
  by_cases he : mass w {v | v ∈ S ∧ c v = 0} ≤ mass w {v | v ∈ S ∧ c v = 1}
  · exact ⟨1,by linarith⟩
  · exact ⟨0,by linarith⟩

lemma independent_color_class {V : Type u} {G : SimpleGraph V} [Fintype V] {S : Set V} {c : V → Fin 2}
    (hc : ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → c x ≠ c y) (q : Fin 2) :
    Independent G {v | v ∈ S ∧ c v = q} := by
  rintro x ⟨hx,hcx⟩ y ⟨hy,hcy⟩ hxy
  exact hc x hx y hy hxy (hcx.trans hcy.symm)

lemma EggCover.component_region {w : V → ℝ} {k : ℕ} (P : EggCover G w k)
    {a : V} (ha : a ∈ Outside P.bag) : Region P (component G (Outside P.bag) a) := by
  refine ⟨component_subset _ _, component_connected ha, ?_⟩
  intro x hx y hy hxy
  exact hx.trans (ReachOn.adj hx.right hy hxy)

lemma outside_update_strict [DecidableEq V] {B : V → Set V} {i : V} {S : Set V}
    (hi : B i ⊆ S) (hnew : (S ∩ Outside B).Nonempty) :
    Outside (Function.update B i S) ⊂ Outside B := by
  refine ⟨outside_update_subset hi, ?_⟩
  intro hback
  obtain ⟨x,hxS,hxO⟩ := hnew
  have hh := hback hxO i
  simp only [Function.update_self] at hh
  exact hh hxS

lemma outside_update_ncard_lt [DecidableEq V] {B : V → Set V} {i : V} {S : Set V}
    (hi : B i ⊆ S) (hnew : (S ∩ Outside B).Nonempty) :
    (Outside (Function.update B i S)).ncard < (Outside B).ncard :=
  Set.ncard_lt_ncard (outside_update_strict hi hnew)

lemma EggCover.absorb_improves {w : V → ℝ} {k : ℕ}
    (P : EggCover G w k) {X : Set V} (hX : Region P X) (i : V)
    (Q J : Set V) (hQX : Q ⊆ X) (hQ : (G.induce Q).Connected)
    (ht : Touch G Q (P.bag i)) (hJ : J ⊆ Q) (hstable : Independent G J)
    (hhalf : mass w Q ≤ 2 * mass w J) (hnot : ¬Touch G (P.yolk i) J) :
    ∃ P' : EggCover G w k, (Outside P'.bag).ncard < (Outside P.bag).ncard := by
  classical
  let P' := P.absorb hX i Q J hQX hQ ht hJ hstable hhalf hnot
  refine ⟨P', ?_⟩
  change (Outside (Function.update P.bag i (P.bag i ∪ Q))).ncard < (Outside P.bag).ncard
  apply outside_update_ncard_lt Set.subset_union_left
  obtain ⟨x,hx⟩ := (connected_iff_reachOn.mp hQ).1
  exact ⟨x,Or.inr hx,hX.subset (hQX hx)⟩

lemma EggCover.free_color {w : V → ℝ} {k : ℕ} (P : EggCover G w k)
    (hb : CliqueBound G k) {X U : Set V} (hX : Region P X)
    (hUX : U ⊆ X) (hU : (G.induce U).Connected)
    (ht : ∀ i, Touch G X (P.bag i) → Touch G U (P.bag i)) :
    ∃ c : Fin k, ∀ i, Touch G X (P.bag i) → c ≠ P.color i := by
  classical
  let I := {i : V // Touch G X (P.bag i)}
  let B : Option I → Set V := fun o => o.elim U (fun i => P.bag i.val)
  have hconn : ∀ o, (G.induce (B o)).Connected := by
    intro o
    cases o with
    | none => exact hU
    | some i => exact P.connected i i.property.right_nonempty
  have hdisj : ∀ a b, a ≠ b → Disjoint (B a) (B b) := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact (hab rfl).elim
      | some j => exact P.outside_disjoint (hUX.trans hX.subset) j
    | some i =>
      cases b with
      | none => exact (P.outside_disjoint (hUX.trans hX.subset) i).symm
      | some j => exact P.disjoint i j (fun he => hab (congrArg some (Subtype.ext he)))
  have htouch : ∀ a b, a ≠ b → Touch G (B a) (B b) := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact (hab rfl).elim
      | some j => exact ht j j.property
    | some i =>
      cases b with
      | none => exact (ht i i.property).symm
      | some j =>
        exact P.frontier X hX.subset hX.connected i j
          (fun he => hab (congrArg some (Subtype.ext he))) i.property j.property
  have hcard : Fintype.card I < k := by
    have hh := hb (Option I) B hconn hdisj htouch
    simp only [Fintype.card_option] at hh
    omega
  have hn : ¬Function.Surjective (fun i : I => P.color i) := by
    intro hs
    have hh := Fintype.card_le_of_surjective _ hs
    simp only [Fintype.card_fin] at hh
    omega
  simp only [Function.Surjective, not_forall, not_exists] at hn
  obtain ⟨c,hc⟩ := hn
  exact ⟨c, fun i hi => Ne.symm (hc ⟨i,hi⟩)⟩

lemma EggCover.add_improves {w : V → ℝ} {k : ℕ}
    (P : EggCover G w k) (hb : CliqueBound G k) {X : Set V} (hX : Region P X)
    (U J : Set V) (hUX : U ⊆ X) (hU : (G.induce U).Connected)
    (ht : ∀ i, Touch G X (P.bag i) → Touch G U (P.bag i))
    (hJ : J ⊆ U) (hstable : Independent G J) (hhalf : mass w U ≤ 2 * mass w J) :
    ∃ P' : EggCover G w k, (Outside P'.bag).ncard < (Outside P.bag).ncard := by
  classical
  obtain ⟨u,hu⟩ := (connected_iff_reachOn.mp hU).1
  have huO := hX.subset (hUX hu)
  have hbag : P.bag u = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact huO u (P.root u ⟨x,hx⟩)
  have hinc : P.bag u ⊆ U := by simp [hbag]
  obtain ⟨c,hc⟩ := P.free_color hb hX hUX hU ht
  have hproper : ∀ j, u ≠ j → Touch G U (P.bag j) → c ≠ P.color j :=
    fun j _ hj => hc j (hj.mono hUX Set.Subset.rfl)
  have hfront : ∀ D : Set V, D ⊆ Outside (Function.update P.bag u U) →
      (G.induce D).Connected → ∀ j, u ≠ j →
      Touch G D U → Touch G D (P.bag j) → Touch G U (P.bag j) := by
    intro D hD hDconn j _ hDU hDj
    have hDX := hX.contains_of_touch (hD.trans (outside_update_subset hinc)) hDconn hUX hDU
    exact ht j (hDj.mono hDX Set.Subset.rfl)
  let P' := P.replace u U J c hinc (fun _ => hu) hU
    (fun j _ => P.outside_disjoint (hUX.trans hX.subset) j)
    hJ hstable hhalf hproper hfront
  refine ⟨P', ?_⟩
  change (Outside (Function.update P.bag u U)).ncard < (Outside P.bag).ncard
  exact outside_update_ncard_lt hinc ⟨u,hu,huO⟩

lemma touch_iff_interface {V : Type u} {G : SimpleGraph V} [Fintype V] {A B : Set V} : Touch G A B ↔ (A ∩ Interface G B).Nonempty := by
  rfl

lemma EggCover.improve_region {w : V → ℝ} {k : ℕ}
    (P : EggCover G w k) (hb : CliqueBound G k) {X : Set V} (hX : Region P X) :
    ∃ P' : EggCover G w k, (Outside P'.bag).ncard < (Outside P.bag).ncard := by
  classical
  let I := {i : V // Touch G X (P.bag i)}
  let N : I → Set V := fun i => Interface G (P.bag i)
  have hN : ∀ i, (X ∩ N i).Nonempty := fun i => touch_iff_interface.mp i.property
  rcases connected_transversal_or_split_on hX.connected hN with ⟨U,hUX,hU,hmeet,hcolor⟩ | ⟨s,hsX⟩
  · obtain ⟨c,hc⟩ := colorable_induce_iff_total.mp hcolor
    obtain ⟨q,hq⟩ := heavy_color w U c
    refine P.add_improves hb hX U {v | v ∈ U ∧ c v = q} hUX hU ?_
      (fun _ h => h.1) (independent_color_class hc q) hq
    intro i hi
    exact touch_iff_interface.mpr (hmeet ⟨i,hi⟩)
  · obtain ⟨q,hq⟩ := heavy_color w s.carrier s.color
    have hJ := independent_color_class s.proper q
    by_cases he : q = 0
    · refine P.absorb_improves hX s.right.val s.carrier
        {v | v ∈ s.carrier ∧ s.color v = q} hsX s.connected
        (touch_iff_interface.mpr s.meets_right) (fun _ h => h.1) hJ hq ?_
      rintro ⟨a,ha,b,⟨hb,hbq⟩,hab⟩
      have hbi : b ∈ N s.right := ⟨a,P.yolk_subset s.right.val ha,hab.symm⟩
      have hh := s.right_color b hb hbi
      rw [he] at hbq
      exact (show (0 : Fin 2) ≠ 1 by decide) (hbq.symm.trans hh)
    · have he' : q = 1 := by omega
      refine P.absorb_improves hX s.left.val s.carrier
        {v | v ∈ s.carrier ∧ s.color v = q} hsX s.connected
        (touch_iff_interface.mpr s.meets_left) (fun _ h => h.1) hJ hq ?_
      rintro ⟨a,ha,b,⟨hb,hbq⟩,hab⟩
      have hbi : b ∈ N s.left := ⟨a,P.yolk_subset s.left.val ha,hab.symm⟩
      have hh := s.left_color b hb hbi
      rw [he'] at hbq
      exact (show (1 : Fin 2) ≠ 0 by decide) (hbq.symm.trans hh)

theorem exists_complete_egg_cover (w : V → ℝ) {k : ℕ} (hk : 0 < k)
    (hb : CliqueBound G k) : ∃ P : EggCover G w k, Outside P.bag = ∅ := by
  classical
  have hex : ∃ n : ℕ, ∃ P : EggCover G w k, (Outside P.bag).ncard = n :=
    ⟨_,EggCover.empty G w hk,rfl⟩
  obtain ⟨P,hP⟩ := Nat.find_spec hex
  refine ⟨P, ?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨P',hP'⟩ := P.improve_region hb (P.component_region ha)
  have hh := Nat.find_min' hex ⟨P',rfl⟩
  omega

lemma mass_iUnion {I : Type*} [Fintype I] (w : V → ℝ) (A : I → Set V)
    (hd : ∀ i j, i ≠ j → Disjoint (A i) (A j)) :
    mass w (⋃ i, A i) = ∑ i, mass w (A i) := by
  classical
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : ∃ i, v ∈ A i
  · obtain ⟨i,hi⟩ := hv
    rw [ite_eq_left (Set.mem_iUnion.mpr ⟨i,hi⟩)]
    symm
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hj : v ∉ A j := fun hj => Set.disjoint_left.mp (hd j i hji) hj hi
      simp [hj]
    · simp
  · have hn : v ∉ ⋃ i, A i := by simpa using hv
    simp only [hn,ite_false]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => hv ⟨i,hi⟩)

lemma EggCover.bag_mass {w : V → ℝ} {k : ℕ} (P : EggCover G w k)
    (hP : Outside P.bag = ∅) : (∑ v, w v) = ∑ i, mass w (P.bag i) := by
  have hcov : (⋃ i, P.bag i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    by_contra hv
    have hout : v ∈ Outside P.bag := fun i hi => hv (Set.mem_iUnion.mpr ⟨i,hi⟩)
    rw [hP] at hout
    exact hout
  rw [← mass_iUnion w P.bag P.disjoint,hcov,mass_univ]

lemma EggCover.colorYolk_independent {w : V → ℝ} {k : ℕ} (P : EggCover G w k)
    (c : Fin k) : Independent G (P.colorYolk c) := by
  rintro x hx y hy hxy
  obtain ⟨i,hxi,hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j,hyj,hj⟩ := Set.mem_iUnion.mp hy
  by_cases he : i = j
  · subst j
    exact P.stable i x hxi y hyj hxy
  · exact P.proper i j he ⟨x,P.yolk_subset i hxi,y,P.yolk_subset j hyj,hxy⟩
      (hi.trans hj.symm)

lemma EggCover.colorYolk_mass {w : V → ℝ} {k : ℕ} (P : EggCover G w k) (c : Fin k) :
    mass w (P.colorYolk c) = ∑ i, if P.color i = c then mass w (P.yolk i) else 0 := by
  classical
  rw [colorYolk,mass_iUnion]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : P.color i = c
    · simp [hi]
    · simp [hi,mass_empty]
  · intro i j hij
    exact (P.disjoint i j hij).mono (fun _ h => P.yolk_subset i h.1)
      (fun _ h => P.yolk_subset j h.1)

lemma EggCover.sum_yolk_mass {w : V → ℝ} {k : ℕ} (P : EggCover G w k) :
    (∑ c : Fin k, mass w (P.colorYolk c)) = ∑ i, mass w (P.yolk i) := by
  classical
  simp_rw [P.colorYolk_mass]
  rw [Finset.sum_comm]
  simp

theorem dual_weight_bound (w : V → ℝ) {k : ℕ} (hk : 0 < k) (hb : CliqueBound G k)
    (hw : ∀ S : Set V, Independent G S → mass w S ≤ 1) : (∑ v, w v) ≤ 2 * k := by
  classical
  obtain ⟨P,hP⟩ := exists_complete_egg_cover w hk hb
  have hsum : (∑ i, mass w (P.yolk i)) ≤ (k : ℝ) := by
    rw [← P.sum_yolk_mass]
    calc
      (∑ c : Fin k, mass w (P.colorYolk c)) ≤ ∑ _c : Fin k, (1 : ℝ) :=
        Finset.sum_le_sum (fun c _ => hw _ (P.colorYolk_independent c))
      _ = k := by simp
  calc
    (∑ v, w v) = ∑ i, mass w (P.bag i) := P.bag_mass hP
    _ ≤ ∑ i, 2 * mass w (P.yolk i) := Finset.sum_le_sum (fun i _ => P.half i)
    _ = 2 * ∑ i, mass w (P.yolk i) := by rw [Finset.mul_sum]
    _ ≤ 2 * k := by linarith

end Weights
end ReedSeymour

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

lemma cliqueBound_hadwiger {V : Type} [Fintype V] (G : SimpleGraph V) :
    ReedSeymour.CliqueBound G (hadwigerNumber G) := by
  classical
  intro I _ B hconn hdisj htouch
  apply cliqueMinor_le_hadwigerNumber
  let e := (Fintype.equivFin I).symm
  refine ⟨fun i => B (e i),fun i => hconn (e i),?_,?_⟩
  · intro i j hij
    exact hdisj _ _ (fun hh => hij (e.injective hh))
  · intro i j hij
    exact htouch _ _ (fun hh => hij (e.injective hh))

namespace Fractional
variable {V : Type} [Fintype V] [DecidableEq V]

theorem dual_weight_le_two_hadwiger_oai (G : SimpleGraph V) (w : V → ℝ)
    (hw : ∀ I : Finset V, (∀ v ∈ I, ∀ u ∈ I, ¬G.Adj v u) → ∑ v ∈ I, w v ≤ 1) :
    ∑ v, w v ≤ 2 * (hadwigerNumber G : ℝ) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    let := h
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    positivity
  | inr h =>
    let := h
    refine ReedSeymour.dual_weight_bound w (by have hh := one_le_hadwigerNumber G; omega)
      (cliqueBound_hadwiger G) (fun S hS => ?_)
    have hs : Stable G (Finset.univ.filter (· ∈ S)) := by
      intro v hv z hz
      exact hS v (Finset.mem_filter.mp hv).2 z (Finset.mem_filter.mp hz).2
    simpa [ReedSeymour.mass,Finset.sum_filter] using hw _ hs

end Fractional

end LinearListHadwiger

end OAI
end

theorem solution : type_of% @OAI.LinearListHadwiger.Fractional.dual_weight_le_two_hadwiger_oai := @OAI.LinearListHadwiger.Fractional.dual_weight_le_two_hadwiger_oai
