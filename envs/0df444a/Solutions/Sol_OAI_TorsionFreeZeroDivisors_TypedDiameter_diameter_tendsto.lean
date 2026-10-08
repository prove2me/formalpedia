-- Prove2me | solution 1 for OAI.TorsionFreeZeroDivisors.TypedDiameter.diameter_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T15:19:59.818624+00:00
-- url     : https://prove2.me/submissions/94cf2372-1850-4000-9b8c-e0e3815caede

import Mathlib
import Definitions.Def_TorsionFreeZeroDivisorsConstruction
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PortSubdivision

namespace PortGraph
variable {V D : Type*} (Γ : PortGraph V D)

@[simp] theorem adj_original (v w : V) : ¬ Γ.subdivision.Adj (.inl v) (.inl w) := id
@[simp] theorem adj_original_port (v : V) (d : D) :
    Γ.subdivision.Adj (.inl v) (.inr d) ↔ Γ.origin d = v := Iff.rfl
@[simp] theorem adj_port_original (v : V) (d : D) :
    Γ.subdivision.Adj (.inr d) (.inl v) ↔ Γ.origin d = v := Iff.rfl
@[simp] theorem adj_ports (d e : D) :
    Γ.subdivision.Adj (.inr d) (.inr e) ↔ Γ.reverse d = e := Iff.rfl

theorem port_adj_iff (d : D) (a : V ⊕ D) :
    Γ.subdivision.Adj (.inr d) a ↔ a = .inl (Γ.origin d) ∨ a = .inr (Γ.reverse d) := by
  cases a <;> simp [eq_comm]

/-- Every cycle through a port uses its middle edge, since the other port
neighbor is unique and the cycle cannot immediately backtrack. -/
theorem cycle_middle_at_port (d : D) (p : Γ.subdivision.Walk (.inr d) (.inr d))
    (hp : p.IsCycle) : s(Sum.inr d,Sum.inr (Γ.reverse d)) ∈ p.edges := by
  have ha := (Γ.port_adj_iff d p.snd).mp (p.adj_snd hp.not_nil)
  have hb := (Γ.port_adj_iff d p.penultimate).mp (p.adj_penultimate hp.not_nil).symm
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact False.elim (hp.snd_ne_penultimate (ha.trans hb.symm))
    · have he := p.mk_penultimate_end_mem_edges hp.not_nil
      rw [hb,Sym2.eq_swap] at he
      exact he
  · simpa only [ha] using p.mk_start_snd_mem_edges hp.not_nil

/-- No cycle lives entirely in the spokes; a short cycle always gives a
middle edge eligible for a matching transposition. -/
theorem cycle_has_middle [DecidableEq V] [DecidableEq D] {a : V ⊕ D}
    (p : Γ.subdivision.Walk a a) (hp : p.IsCycle) :
    ∃ d, s(Sum.inr d,Sum.inr (Γ.reverse d)) ∈ p.edges := by
  have hex : ∃ d, Sum.inr d ∈ p.support := by
    cases a with
    | inr d => exact ⟨d,p.start_mem_support⟩
    | inl v =>
      have ha := p.adj_snd hp.not_nil
      cases hs : p.snd with
      | inl w => rw [hs] at ha; exact False.elim ha
      | inr d => exact ⟨d,hs ▸ p.snd_mem_support_of_mem_edges (p.mk_start_snd_mem_edges hp.not_nil)⟩
  obtain ⟨d,hd⟩ := hex
  refine ⟨d,?_⟩
  have he := Γ.cycle_middle_at_port d (p.rotate (.inr d) hd) (hp.rotate hd)
  exact (p.rotate_edges (.inr d) hd).mem_iff.mp he

/-- The neighbor fiber at an original vertex is exactly its port fiber. -/
def originalNeighborEquiv (v : V) :
    Γ.subdivision.neighborSet (.inl v) ≃ {d : D // Γ.origin d = v} where
  toFun n := match n with
    | ⟨.inl _,h⟩ => False.elim h
    | ⟨.inr d,h⟩ => ⟨d,h⟩
  invFun d := ⟨.inr d.val,d.property⟩
  left_inv n := by rcases n with ⟨v|d,h⟩; exact False.elim h; rfl
  right_inv _ := rfl

/-- A port has exactly two neighbors: its original vertex and its reverse port.
They lie in disjoint summands even when the original edge is a graph loop. -/
def portNeighborEquiv (d : D) : Γ.subdivision.neighborSet (.inr d) ≃ Bool where
  toFun n := match n.val with | .inl _ => false | .inr _ => true
  invFun b := if b then ⟨.inr (Γ.reverse d),rfl⟩ else ⟨.inl (Γ.origin d),rfl⟩
  left_inv n := by
    rcases n with ⟨v|e,h⟩
    · apply Subtype.ext
      exact congrArg Sum.inl h
    · apply Subtype.ext
      exact congrArg Sum.inr h
  right_inv b := by cases b <;> rfl

theorem card_original_neighbors (v : V) :
    Nat.card (Γ.subdivision.neighborSet (.inl v)) =
      Nat.card {d : D // Γ.origin d = v} := Nat.card_congr (Γ.originalNeighborEquiv v)

theorem card_port_neighbors (d : D) : Nat.card (Γ.subdivision.neighborSet (.inr d)) = 2 := by
  rw [Nat.card_congr (Γ.portNeighborEquiv d)]
  simp

/-- Conjugating the reversal while keeping port origins fixed is a
matching switch, not a relabeling of the original graph. -/
def moveMatches (σ : Equiv.Perm D) : PortGraph V D where
  origin := Γ.origin
  reverse d := σ (Γ.reverse (σ.symm d))
  reverse_reverse d := by simp
  reverse_ne d := by
    intro h
    have h' := congrArg σ.symm h
    simp only [Equiv.symm_apply_apply] at h'
    exact Γ.reverse_ne (σ.symm d) h'

section Switching
variable [DecidableEq D]

/-- Transpose two equally oriented ports. Their reverse ports are not moved. -/
def switch (d e : D) : PortGraph V D := Γ.moveMatches (Equiv.swap d e)

@[simp] theorem switch_origin (d e f : D) : (Γ.switch d e).origin f = Γ.origin f := rfl

/-- The subdivision changes exactly the two middle edges, preserving every
origin-port incidence, including incidences belonging to original loops. -/
theorem switch_adj (d e : D) (hde : d ≠ e) (hdr : d ≠ Γ.reverse e)
    (a b : V ⊕ D) :
    (Γ.switch d e).subdivision.Adj a b ↔
      (Γ.subdivision.Adj a b ∧ s(a,b) ≠ s(Sum.inr d,Sum.inr (Γ.reverse d)) ∧
        s(a,b) ≠ s(Sum.inr e,Sum.inr (Γ.reverse e))) ∨
      s(a,b) = s(Sum.inr d,Sum.inr (Γ.reverse e)) ∨
      s(a,b) = s(Sum.inr e,Sum.inr (Γ.reverse d)) := by
  have hrd : Γ.reverse d ≠ d := Γ.reverse_ne d
  have hre : Γ.reverse e ≠ e := Γ.reverse_ne e
  have hrd_e : Γ.reverse d ≠ e := by
    intro h
    apply hdr
    rw [← h,Γ.reverse_reverse]
  have hrev : Γ.reverse d ≠ Γ.reverse e := fun h => hde (Γ.reverse_reverse.injective h)
  cases a with
  | inl a =>
    cases b <;> simp [subdivision,switch_origin]
  | inr f =>
    cases b with
    | inl b => simp [subdivision,switch_origin]
    | inr g =>
      change (Equiv.swap d e) (Γ.reverse ((Equiv.swap d e) f)) = g ↔ _
      simp only [adj_ports,Sym2.eq_iff,Sum.inr.injEq]
      by_cases hfd : f = d
      · subst f
        simp only [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne hdr.symm hre]
        grind
      · by_cases hfe : f = e
        · subst f
          simp only [Equiv.swap_apply_right,Equiv.swap_apply_of_ne_of_ne hrd hrd_e]
          grind
        · by_cases hfrd : f = Γ.reverse d
          · subst f
            simp only [Equiv.swap_apply_of_ne_of_ne hrd hrd_e,reverse_reverse_apply,
              Equiv.swap_apply_left]
            grind
          · by_cases hfre : f = Γ.reverse e
            · subst f
              simp only [Equiv.swap_apply_of_ne_of_ne hdr.symm hre,reverse_reverse_apply,
                Equiv.swap_apply_right]
              grind
            · have hrfd : Γ.reverse f ≠ d := by
                intro h
                apply hfrd
                rw [← h,Γ.reverse_reverse]
              have hrfe : Γ.reverse f ≠ e := by
                intro h
                apply hfre
                rw [← h,Γ.reverse_reverse]
              simp [Equiv.swap_apply_of_ne_of_ne hfd hfe,
                Equiv.swap_apply_of_ne_of_ne hrfd hrfe,hfd,hfe,hfrd,hfre]

/-- Transposing two occurrences of the same label preserves every port label. -/
theorem label_swap {T : Type*} (label : D → T) (d e : D) (h : label d = label e)
    (f : D) : label ((Equiv.swap d e) f) = label f := by
  by_cases hfd : f = d
  · subst f; simpa using h.symm
  · by_cases hfe : f = e
    · subst f; simpa using h
    · rw [Equiv.swap_apply_of_ne_of_ne hfd hfe]

theorem switch_preserves_labels {T : Type*} (label : D → T) (bar : T → T)
    (hlabel : ∀ f, label (Γ.reverse f) = bar (label f))
    (d e : D) (h : label d = label e) (f : D) :
    label ((Γ.switch d e).reverse f) = bar (label f) := by
  change label ((Equiv.swap d e) (Γ.reverse ((Equiv.swap d e) f))) = bar (label f)
  rw [label_swap label d e h, hlabel, label_swap label d e h]

end Switching

namespace Walk
variable {Γ} {a b c : V}

end Walk
end PortGraph
end TorsionFreeZeroDivisors.PortSubdivision

/-!
Quantitative edge switching for the girth conditioning in types.tex 116–147.
The simple-graph lemmas are also applicable to the canonical threefold
subdivision of a port multigraph (loops become triangles). No random-graph
existence or cone-topology conclusion is assumed in these lemmas.
-/

namespace TorsionFreeZeroDivisors.GirthSwitch

open SimpleGraph
open scoped ENNReal

variable {V : Type*} {G H : SimpleGraph V} {a b x y : V}

/-- Decompose at a specified edge occurrence, with its actual orientation. -/
theorem split_at_edge (p : G.Walk a b) (e : Sym2 V) (he : e ∈ p.edges) :
    ∃ (x y : V) (hxy : G.Adj x y) (p₁ : G.Walk a x) (p₂ : G.Walk y b),
      s(x,y) = e ∧ p = p₁.append (.cons hxy p₂) := by
  induction p with
  | nil => simp at he
  | @cons u v w huv p ih =>
    simp only [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · exact ⟨u,v,huv,.nil,p,he.symm,rfl⟩
    · obtain ⟨x,y,hxy,p₁,p₂,hxe,hp⟩ := ih he
      exact ⟨x,y,hxy,.cons huv p₁,p₂,hxe,by rw [hp]; rfl⟩

/-- Removing an edge of a closed trail leaves an alternate walk one shorter,
without using the removed edge. -/
theorem alternate_walk (p : G.Walk a a) (hp : p.IsTrail)
    (e : Sym2 V) (he : e ∈ p.edges) :
    ∃ (x y : V) (q : G.Walk x y),
      s(x,y) = e ∧ e ∉ q.edges ∧ q.length + 1 = p.length := by
  obtain ⟨x,y,hxy,p₁,p₂,hxe,hpdecomp⟩ := split_at_edge p e he
  subst p
  have hn := hp.edges_nodup
  simp only [Walk.edges_append, Walk.edges_cons, List.nodup_append,
    List.nodup_cons] at hn
  have hleft : e ∉ p₁.edges := by
    intro ht
    exact hn.2.2 e ht e (by simp [hxe]) rfl
  have hright : e ∉ p₂.edges := by simpa only [hxe] using hn.2.1.1
  refine ⟨y,x,p₂.append p₁,?_,?_,?_⟩
  · simpa only [Sym2.eq_swap] using hxe
  · simp only [Walk.edges_append, List.mem_append, not_or]
    exact ⟨hright,hleft⟩
  · simp only [Walk.length_append, Walk.length_cons]
    omega

/-- Adjoining one new edge. -/
def addEdge (G : SimpleGraph V) (x y : V) : SimpleGraph V :=
  G ⊔ SimpleGraph.fromEdgeSet {s(x,y)}

@[simp] theorem addEdge_adj (u v : V) :
    (addEdge G x y).Adj u v ↔ G.Adj u v ∨ (s(u,v) = s(x,y) ∧ u ≠ v) := by
  simp [addEdge, SimpleGraph.fromEdgeSet_adj]

/-- A walk avoiding the newly adjoined edge lies in the old graph. -/
theorem transfer_addEdge (p : (addEdge G x y).Walk a b)
    (hp : s(x,y) ∉ p.edges) :
    ∃ q : G.Walk a b, q.length = p.length := by
  refine ⟨p.transfer G ?_,Walk.length_transfer ..⟩
  intro e he
  have hg := p.edges_subset_edgeSet he
  simp only [addEdge, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hg
  rcases hg with hg | ⟨rfl,_⟩
  · exact hg
  · exact False.elim (hp he)

/-- Adding an edge whose endpoints have no short old connecting path preserves
the lower girth bound. The path hypothesis includes either orientation. -/
theorem girth_addEdge (L : ℕ) (hG : (L : ℕ∞) ≤ G.egirth)
    (hx : ∀ p : G.Walk x y, L ≤ p.length + 1) :
    (L : ℕ∞) ≤ (addEdge G x y).egirth := by
  classical
  rw [SimpleGraph.le_egirth]
  intro a p hp
  by_cases he : s(x,y) ∈ p.edges
  · obtain ⟨u,v,q,huv,hqe,hql⟩ := alternate_walk p hp.isTrail _ he
    obtain ⟨q',hq'⟩ := transfer_addEdge q hqe
    have ho : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
      simpa only [Sym2.eq_iff] using huv
    have hl : L ≤ q'.length + 1 := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hx q'
      · simpa only [Walk.length_reverse] using hx q'.reverse
    rw [hq',hql] at hl
    exact_mod_cast hl
  · have htransfer : ∀ e, e ∈ p.edges → e ∈ G.edgeSet := by
      intro e he'
      have hg := p.edges_subset_edgeSet he'
      simp only [addEdge, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet,
        Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hg
      rcases hg with hg | ⟨rfl,_⟩
      · exact hg
      · exact False.elim (he he')
    have hh := SimpleGraph.le_egirth.mp hG a (p.transfer G htransfer) (hp.transfer htransfer)
    simpa only [Walk.length_transfer] using hh

/-- Before the first occurrence of a new edge, a walk lies wholly in G.
No simplicity assumption is required for this decomposition. -/
theorem first_new_edge (p : (addEdge G x y).Walk a b) :
    (∃ q : G.Walk a b, q.length ≤ p.length) ∨
    (∃ q : G.Walk a x, q.length + 1 ≤ p.length) ∨
    (∃ q : G.Walk a y, q.length + 1 ≤ p.length) := by
  induction p with
  | nil => exact Or.inl ⟨.nil,le_rfl⟩
  | @cons u v w huv p ih =>
    rcases (addEdge_adj u v).mp huv with hold | ⟨he,_⟩
    · rcases ih with ⟨q,hq⟩ | ⟨q,hq⟩ | ⟨q,hq⟩
      · exact Or.inl ⟨.cons hold q, by simpa only [Walk.length_cons] using Nat.add_le_add_right hq 1⟩
      · exact Or.inr (Or.inl ⟨.cons hold q, by simp only [Walk.length_cons]; omega⟩)
      · exact Or.inr (Or.inr ⟨.cons hold q, by simp only [Walk.length_cons]; omega⟩)
    · have ho : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
        simpa only [Sym2.eq_iff] using he
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inr (Or.inl ⟨.nil,by simp⟩)
      · exact Or.inr (Or.inr ⟨.nil,by simp⟩)

/-- In a graph of girth at least L, an alternate path across an old edge
has length at least L-1. This is precisely the nonbad-edge input to the
matching transposition argument. -/
theorem girth_alternate_lower (L : ℕ) (hG : (L : ℕ∞) ≤ G.egirth)
    (hxy : G.Adj x y) (p : (G.deleteEdges {s(x,y)}).Walk x y) :
    L ≤ p.length + 1 := by
  classical
  let hp := p.mapLe (SimpleGraph.deleteEdges_le {s(x,y)})
  have he : s(x,y) ∉ hp.edges := by
    intro he
    have hmem : s(x,y) ∈ p.edges := by simpa only [hp,Walk.edges_mapLe_eq_edges] using he
    have hg := p.edges_subset_edgeSet hmem
    simp at hg
  have hc := hp.toPath.cons_isCycle hxy.symm (by
    rw [Sym2.eq_swap]
    exact fun h => he (Walk.edges_toPath_subset_edges hp h))
  have hh := SimpleGraph.le_egirth.mp hG y (.cons hxy.symm hp.toPath) hc
  have hlen := hp.length_bypass_le_length
  have hh' : L ≤ hp.bypass.length + 1 := by exact_mod_cast hh
  simpa only [hp,Walk.length_mapLe] using hh'.trans (Nat.add_le_add_right hlen 1)

/-- Two-switching in a simple graph: delete xy and uz, then add xz and uy.
The distance condition is the manuscript's separation of the two endpoint
sets. All previous prescribed edges survive provided neither deleted edge
was among those prescriptions. -/
theorem girth_switch (L : ℕ) {x y u z : V}
    (hG : (L : ℕ∞) ≤ G.egirth) (huz : G.Adj u z)
    (hfar : ∀ a ∈ ({x,y} : Set V), ∀ b ∈ ({u,z} : Set V),
      ∀ p : G.Walk a b, 2 * L < p.length) :
    (L : ℕ∞) ≤
      (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y).egirth := by
  let H := G.deleteEdges {s(x,y),s(u,z)}
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le _
  have hH : (L : ℕ∞) ≤ H.egirth := hG.trans (SimpleGraph.egirth_anti hHG)
  have hxz (p : H.Walk x z) : L ≤ p.length + 1 := by
    have hf := hfar x (by simp) z (by simp) (p.mapLe hHG)
    simp only [Walk.length_mapLe] at hf
    omega
  have hg1 := girth_addEdge L hH hxz
  apply girth_addEdge L hg1
  intro p
  rcases first_new_edge p with ⟨q,hq⟩ | ⟨q,hq⟩ | ⟨q,hq⟩
  · have hf := hfar y (by simp) u (by simp) ((q.mapLe hHG).reverse)
    simp only [Walk.length_reverse,Walk.length_mapLe] at hf
    omega
  · have hf := hfar x (by simp) u (by simp) ((q.mapLe hHG).reverse)
    simp only [Walk.length_reverse,Walk.length_mapLe] at hf
    omega
  · have hdel : H ≤ G.deleteEdges {s(u,z)} := by
      apply SimpleGraph.deleteEdges_anti
      simp only [Set.singleton_subset_iff,Set.mem_insert_iff,Set.mem_singleton_iff]
      simp
    have hl := girth_alternate_lower L hG huz (q.mapLe hdel)
    simp only [Walk.length_mapLe] at hl
    omega

/-- Short cycles in an edge-adjoined graph descend to the old graph whenever
there is no short alternate path. This needs no girth assumption on the old
graph, and so also applies during the initial bad-edge repair algorithm. -/
theorem short_cycle_descends_add (L : ℕ)
    (hx : ∀ p : G.Walk x y, L ≤ p.length + 1)
    (p : (addEdge G x y).Walk a a) (hp : p.IsCycle) (hlen : p.length < L) :
    ∃ q : G.Walk a a, q.IsCycle ∧ q.edges = p.edges ∧ q.length = p.length := by
  classical
  have he : s(x,y) ∉ p.edges := by
    intro he
    obtain ⟨u,v,q,huv,hqe,hql⟩ := alternate_walk p hp.isTrail _ he
    obtain ⟨q',hq'⟩ := transfer_addEdge q hqe
    have ho : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
      simpa only [Sym2.eq_iff] using huv
    have hl : L ≤ q'.length + 1 := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hx q'
      · simpa only [Walk.length_reverse] using hx q'.reverse
    omega
  have ht : ∀ e, e ∈ p.edges → e ∈ G.edgeSet := by
    intro e he'
    have hg := p.edges_subset_edgeSet he'
    simp only [addEdge, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet,
      Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hg
    rcases hg with hg | ⟨rfl,_⟩
    · exact hg
    · exact False.elim (he he')
  exact ⟨p.transfer G ht,hp.transfer ht,Walk.edges_transfer ..,Walk.length_transfer ..⟩

/-- At the shortest-cycle threshold, no nonbadness requirement is needed
on the auxiliary edge: a new cycle using both new edges is strictly longer
than the old girth. This permits deterministic girth repair. -/
theorem shortest_cycle_descends_switch (L : ℕ) {x y u z : V}
    (hG : (L : ℕ∞) ≤ G.egirth) (huz : G.Adj u z)
    (hfar : ∀ a ∈ ({x,y} : Set V), ∀ b ∈ ({u,z} : Set V),
      ∀ p : G.Walk a b, 2 * (L+1) < p.length)
    (p : (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y).Walk a a)
    (hp : p.IsCycle) (hlen : p.length < L+1) :
    ∃ q : (G.deleteEdges {s(x,y),s(u,z)}).Walk a a,
      q.IsCycle ∧ q.edges = p.edges ∧ q.length = p.length := by
  let H := G.deleteEdges {s(x,y),s(u,z)}
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le _
  have hxz (p : H.Walk x z) : L+1 ≤ p.length + 1 := by
    have hf := hfar x (by simp) z (by simp) (p.mapLe hHG)
    simp only [Walk.length_mapLe] at hf
    omega
  have huy (p : (addEdge H x z).Walk u y) : L+1 ≤ p.length + 1 := by
    rcases first_new_edge p with ⟨q,hq⟩ | ⟨q,hq⟩ | ⟨q,hq⟩
    · have hf := hfar y (by simp) u (by simp) ((q.mapLe hHG).reverse)
      simp only [Walk.length_reverse,Walk.length_mapLe] at hf
      omega
    · have hf := hfar x (by simp) u (by simp) ((q.mapLe hHG).reverse)
      simp only [Walk.length_reverse,Walk.length_mapLe] at hf
      omega
    · have hdel : H ≤ G.deleteEdges {s(u,z)} := by
        apply SimpleGraph.deleteEdges_anti
        simp
      have hl := girth_alternate_lower L hG huz (q.mapLe hdel)
      simp only [Walk.length_mapLe] at hl
      omega
  obtain ⟨q,hq,hqe,hql⟩ := short_cycle_descends_add (L+1) huy p hp hlen
  obtain ⟨q',hq',hq'e,hq'l⟩ := short_cycle_descends_add (L+1) hxz q hq (by omega)
  exact ⟨q',hq',hq'e.trans hqe,hq'l.trans hql⟩

/-- The exact set minimized by the finite repair argument. -/
def badEdges (G : SimpleGraph V) (L : ℕ) : Set (Sym2 V) :=
  {e | ∃ (a : V) (p : G.Walk a a), p.IsCycle ∧ p.length < L ∧ e ∈ p.edges}

/-- Edgewise transfer of short cycles strictly reduces the bad edge set
as soon as a specified old bad edge has been deleted. -/
theorem badEdges_strict {L : ℕ} [Fintype V] (e : Sym2 V) (he : e ∈ badEdges G L)
    (hdesc : ∀ a (p : H.Walk a a), p.IsCycle → p.length < L →
      ∃ q : G.Walk a a, q.IsCycle ∧ q.edges = p.edges ∧ q.length = p.length)
    (hdel : e ∉ badEdges H L) :
    (badEdges H L).toFinite.toFinset.card < (badEdges G L).toFinite.toFinset.card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro f hf
    have hf' : f ∈ badEdges H L := by simpa using hf
    obtain ⟨a,p,hp,hl,hf'⟩ := hf'
    obtain ⟨q,hq,hqe,hql⟩ := hdesc a p hp hl
    simpa using (show f ∈ badEdges G L from ⟨a,q,hq,by omega,hqe ▸ hf'⟩)
  · intro heq
    have heH : e ∈ (badEdges H L).toFinite.toFinset := by
      rw [heq]
      simpa using he
    have heH' : e ∈ badEdges H L := by simpa using heH
    exact hdel heH'

/-- Finite extremal repair raises the girth by one. Unlike the manuscript's
probabilistic initialization, this argument only needs the uniform far-edge
supply; all objects and the final girth condition are unchanged. -/
theorem girth_improve_one [Fintype V] (L : ℕ) (P : SimpleGraph V → Prop)
    (hne : ∃ G, P G ∧ (L : ℕ∞) ≤ G.egirth)
    (hswitch : ∀ G, P G → ∀ a (p : G.Walk a a), p.IsCycle →
      ∃ x y u z, s(x,y) ∈ p.edges ∧ G.Adj u z ∧
        (∀ a ∈ ({x,y} : Set V), ∀ b ∈ ({u,z} : Set V),
          ∀ p : G.Walk a b, 2 * (L+1) < p.length) ∧
        P (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y)) :
    ∃ G, P G ∧ ((L+1 : ℕ) : ℕ∞) ≤ G.egirth := by
  classical
  let S : Set (SimpleGraph V) := {G | P G ∧ (L : ℕ∞) ≤ G.egirth}
  obtain ⟨G,hGP,hmin⟩ := S.exists_min_image
    (fun G => (badEdges G (L+1)).toFinite.toFinset.card) S.toFinite hne
  refine ⟨G,hGP.1,?_⟩
  by_contra hn
  rw [SimpleGraph.le_egirth] at hn
  push Not at hn
  obtain ⟨a,p,hp,hl⟩ := hn
  have hlen : p.length < L+1 := by exact_mod_cast hl
  obtain ⟨x,y,u,z,he,huz,hfar,hP⟩ := hswitch G hGP.1 a p hp
  let e := s(x,y)
  let H := addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y
  have hdesc (a : V) (q : H.Walk a a) (hq : q.IsCycle) (hl : q.length < L+1) :=
    shortest_cycle_descends_switch L hGP.2 huz hfar q hq hl
  have hstrict : (badEdges H (L+1)).toFinite.toFinset.card <
      (badEdges G (L+1)).toFinite.toFinset.card := by
    apply badEdges_strict e ⟨a,p,hp,hlen,he⟩
    · intro a q hq hl
      obtain ⟨q',hq',hqe,hql⟩ := hdesc a q hq hl
      exact ⟨q'.mapLe (SimpleGraph.deleteEdges_le _), hq'.mapLe _,
        (Walk.edges_mapLe_eq_edges ..).trans hqe,(Walk.length_mapLe ..).trans hql⟩
    · rintro ⟨a,q,hq,hl,heq⟩
      obtain ⟨q',hq',hqe,hql⟩ := hdesc a q hq hl
      have hg := q'.edges_subset_edgeSet (hqe ▸ heq)
      change s(x,y) ∈ (G.deleteEdges {s(x,y),s(u,z)}).edgeSet at hg
      simp at hg
  have hHg : (L : ℕ∞) ≤ H.egirth := girth_switch L hGP.2 huz (by
    intro a ha b hb q
    have hh := hfar a ha b hb q
    omega)
  exact (not_lt_of_ge (hmin H ⟨hP,hHg⟩)) hstrict

/-- Arbitrarily specified finite girth follows by finitely many exact
transpositions if the family has a uniform distant auxiliary edge supply. -/
theorem exists_large_girth [Fintype V] (N : ℕ) (P : SimpleGraph V → Prop)
    (hne : ∃ G, P G)
    (hswitch : ∀ G, P G → ∀ a (p : G.Walk a a), p.IsCycle →
      ∃ x y u z, s(x,y) ∈ p.edges ∧ G.Adj u z ∧
        (∀ a ∈ ({x,y} : Set V), ∀ b ∈ ({u,z} : Set V),
          ∀ p : G.Walk a b, 2 * N < p.length) ∧
        P (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y)) :
    ∃ G, P G ∧ (N : ℕ∞) ≤ G.egirth := by
  have hstep : ∀ k ≤ N, ∃ G, P G ∧ (k : ℕ∞) ≤ G.egirth := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨G,hG⟩ := hne
      exact ⟨G,hG,zero_le⟩
    | succ k ih =>
      intro hk
      apply girth_improve_one k P (ih (by omega))
      intro G hG a p hp
      obtain ⟨x,y,u,z,he,huz,hfar,hP⟩ := hswitch G hG a p hp
      refine ⟨x,y,u,z,he,huz,?_,hP⟩
      intro a ha b hb p
      have hf := hfar a ha b hb p
      omega
  exact hstep N le_rfl

end TorsionFreeZeroDivisors.GirthSwitch

/-! ### Typed matching families have nonempty large-girth spaces. -/

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedCycles
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {u v : V}

end TorsionFreeZeroDivisors.WeightedCycles
namespace TorsionFreeZeroDivisors.WeightedMoore
open scoped BigOperators

instance {D : Type*} [Fintype D] (k : ℕ) : Fintype (Chain D k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype D)
  | succ k ih => exact inferInstanceAs (Fintype (D × Chain D k))

variable {D : Type*} [Fintype D] (T : D → D → ℝ)

variable {T}

namespace PortWalk

variable {V : Type*} (origin : D → V) (rev : D → D)
    (hinv : Function.Involutive rev)

open scoped Classical

include hinv

end PortWalk

end TorsionFreeZeroDivisors.WeightedMoore

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MultiplicityBound
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

end TorsionFreeZeroDivisors.MultiplicityBound

namespace TorsionFreeZeroDivisors.PathMultiplicity
open SimpleGraph WeightedMoore
open PortSubdivision SuppressedMoore
open scoped Classical
variable {V D : Type*} (Γ : PortGraph V D)
local instance : BEq (V ⊕ D) := instBEqOfDecidableEq

end TorsionFreeZeroDivisors.PathMultiplicity

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore SuppressedMoore
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "len" => chainLength Γ mark h2

end TorsionFreeZeroDivisors.ChainPaths

namespace TorsionFreeZeroDivisors.PathMultiplicity
open PortSubdivision
open scoped BigOperators Classical
variable {V D I : Type*} (Γ : PortGraph V D) [Fintype I]

end TorsionFreeZeroDivisors.PathMultiplicity

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore SuppressedMoore
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "B" => {d : D // τ d=d}

end TorsionFreeZeroDivisors.ChainPaths

namespace TorsionFreeZeroDivisors.IncidenceStages
open scoped Classical BigOperators
open EntropyStages
variable {O D V : Type*} [Fintype O] [Fintype D] [Fintype V]

namespace Passages
variable {origin : D → V} {port : O → D}

end Passages
end TorsionFreeZeroDivisors.IncidenceStages

end

end OAI
end

section
namespace OAI



section

/-!
The uniform maximum-degree exclusion bound for finite graph balls.
This treats labelled port graphs too: `neighbors` forgets multiplicities;
loops and multiple edges only decrease the number of distinct vertices.
-/

namespace TorsionFreeZeroDivisors.BallCount

open scoped BigOperators
noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Endpoints of walks of exactly k steps. -/
def ends (neighbors : V → Finset V) (x : V) : ℕ → Finset V
  | 0 => {x}
  | k + 1 => (ends neighbors x k).biUnion neighbors

/-- Finite closed combinatorial ball. -/
def ball (neighbors : V → Finset V) (x : V) (r : ℕ) : Finset V :=
  (Finset.range (r + 1)).biUnion (ends neighbors x)

theorem card_ends_le (neighbors : V → Finset V) (d : ℕ)
    (hd : ∀ v, (neighbors v).card ≤ d) (x : V) (k : ℕ) :
    (ends neighbors x k).card ≤ d ^ k := by
  induction k with
  | zero => simp [ends]
  | succ k ih =>
    calc
      (ends neighbors x (k+1)).card ≤
          ∑ v ∈ ends neighbors x k, (neighbors v).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ ends neighbors x k, d := Finset.sum_le_sum fun v _ => hd v
      _ = (ends neighbors x k).card * d := by simp
      _ ≤ d^k * d := Nat.mul_le_mul_right d ih
      _ = d^(k+1) := (pow_succ d k).symm

/-- A non-asymptotic geometric-sum bound. -/
theorem sum_powers_le (d r : ℕ) (hd : 2 ≤ d) :
    ∑ k ∈ Finset.range (r+1), d^k ≤ 2 * d^r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hp : 0 < d^r := pow_pos (by omega) _
    have hm : 2 * d^r ≤ d^r*d := by nlinarith
    omega

theorem card_ball_le (neighbors : V → Finset V) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, (neighbors v).card ≤ d) (x : V) (r : ℕ) :
    (ball neighbors x r).card ≤ d^(r+1) := by
  calc
    (ball neighbors x r).card ≤ ∑ k ∈ Finset.range (r+1), (ends neighbors x k).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (r+1), d^k :=
      Finset.sum_le_sum fun k _ => card_ends_le neighbors d hd x k
    _ ≤ 2 * d^r - 1 := sum_powers_le d r h2
    _ ≤ d^(r+1) := by
      rw [pow_succ]
      have hm : 2*d^r ≤ d^r*d := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left (d^r) h2
      omega

@[simp] theorem mem_ball_iff (neighbors : V → Finset V) (x y : V) (r : ℕ) :
    y ∈ ball neighbors x r ↔ ∃ k ≤ r, y ∈ ends neighbors x k := by
  simp [ball]

/-- The ordinary finite neighbor set, with its classical finiteness data fixed. -/
def graphNeighbors [Fintype V] (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact G.neighborFinset v

omit [DecidableEq V] in
@[simp] theorem mem_graphNeighbors [Fintype V] (G : SimpleGraph V) (a b : V) :
    b ∈ graphNeighbors G a ↔ G.Adj a b := by
  classical
  simp [graphNeighbors]

omit [DecidableEq V] in
theorem card_graphNeighbors [Fintype V] (G : SimpleGraph V) (v : V) :
    (graphNeighbors G v).card = Nat.card (G.neighborSet v) := by
  classical
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
  exact SimpleGraph.card_neighborFinset_eq_degree G v

/-- The finite combinatorial balls contain all walk endpoints, not just paths. -/
theorem mem_ends_of_walk [Fintype V] (G : SimpleGraph V) {a b : V} (p : G.Walk a b) :
    b ∈ ends (graphNeighbors G) a p.length := by
  classical
  induction p using SimpleGraph.Walk.concatRec with
  | Hnil => simp [ends]
  | @Hconcat a b c p h ih =>
    simp only [SimpleGraph.Walk.length_concat,ends,Finset.mem_biUnion]
    exact ⟨b,ih,by simpa using h⟩

theorem mem_ball_of_walk [Fintype V] (G : SimpleGraph V) {a b : V}
    (p : G.Walk a b) (r : ℕ) (hr : p.length ≤ r) : b ∈ ball (graphNeighbors G) a r := by
  exact mem_ball_iff _ _ _ _ |>.mpr ⟨p.length,hr,mem_ends_of_walk G p⟩

theorem far_of_not_mem_ball [Fintype V] (G : SimpleGraph V) {a b : V} (r : ℕ)
    (h : b ∉ ball (graphNeighbors G) a r) (p : G.Walk a b) : r < p.length := by
  by_contra hn
  exact h (mem_ball_of_walk G p r (by omega))

section Matchings
variable {X Y : Type*} [Fintype X] [DecidableEq X]

/-- Removing source and target ports in a bad vertex set discards at most twice
its cardinality, since each labelled carrier embeds in the vertex set. -/
theorem matching_bad_card (f : X ≃ Y) (locX : X → V) (locY : Y → V)
    (hX : Function.Injective locX) (hY : Function.Injective locY) (B : Finset V) :
    (Finset.univ.filter (fun u => locX u ∈ B ∨ locY (f u) ∈ B)).card ≤ 2 * B.card := by
  classical
  have hx : (Finset.univ.filter (fun u => locX u ∈ B)).card ≤ B.card := by
    apply Finset.card_le_card_of_injOn locX
    · intro u hu; exact (Finset.mem_filter.mp hu).2
    · exact hX.injOn
  have hy : (Finset.univ.filter (fun u => locY (f u) ∈ B)).card ≤ B.card := by
    apply Finset.card_le_card_of_injOn (fun u => locY (f u))
    · intro u hu; exact (Finset.mem_filter.mp hu).2
    · exact (hY.comp f.injective).injOn
  rw [Finset.filter_or]
  exact (Finset.card_union_le _ _).trans (by omega)

/-- A labelled matching has uniformly many choices outside both endpoint balls
and outside a prescribed set. This is the quantitative geometric input to the
conditioned transposition injection. -/
theorem admissible_card (f : X ≃ Y) (locX : X → V) (locY : Y → V)
    (hX : Function.Injective locX) (hY : Function.Injective locY)
    (neighbors : V → Finset V) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, (neighbors v).card ≤ d) (x y : V) (r : ℕ) (P : Finset X) :
    Fintype.card X - P.card - 4*d^(r+1) ≤
      (Finset.univ.filter (fun u => u ∉ P ∧
        locX u ∉ ball neighbors x r ∪ ball neighbors y r ∧
        locY (f u) ∉ ball neighbors x r ∪ ball neighbors y r)).card := by
  classical
  let B := ball neighbors x r ∪ ball neighbors y r
  let bad := Finset.univ.filter (fun u => locX u ∈ B ∨ locY (f u) ∈ B)
  have hb : bad.card ≤ 4*d^(r+1) := by
    have hb' := matching_bad_card f locX locY hX hY B
    have hB : B.card ≤ 2*d^(r+1) :=
      (Finset.card_union_le _ _).trans (by
        have hx := card_ball_le neighbors d h2 hd x r
        have hy := card_ball_le neighbors d h2 hd y r
        omega)
    exact hb'.trans (by omega)
  have he : Finset.univ.filter (fun u => u ∉ P ∧ locX u ∉ B ∧ locY (f u) ∉ B) =
      Finset.univ \ (P ∪ bad) := by
    ext u
    simp [bad, not_or]
  change _ ≤ (Finset.univ.filter (fun u => u ∉ P ∧ locX u ∉ B ∧ locY (f u) ∉ B)).card
  rw [he,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
  have hu := Finset.card_union_le P bad
  omega

end Matchings
end
end TorsionFreeZeroDivisors.BallCount


/-!
A faithful simple-graph encoding of the manuscript's labelled multigraphs.
An original edge has two opposite ports, and its threefold subdivision is
original vertex -- port -- opposite port -- original vertex. Loops become
triangles and parallel edges remain distinct, so neither is silently discarded.
-/

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MatchingGraphs
open PortSubdivision BallCount GirthSwitch
variable {V D T : Type*} [Fintype V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- All degrees are controlled by the fixed port fibers. -/
theorem subdivision_degree (Γ : PortGraph V D) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // Γ.origin e = v} ≤ d) (a : V ⊕ D) :
    (graphNeighbors Γ.subdivision a).card ≤ d := by
  classical
  rw [card_graphNeighbors]
  cases a with
  | inl v => rw [Γ.card_original_neighbors]; exact hd v
  | inr e => rw [Γ.card_port_neighbors]; exact h2

/-- Uniformly many ports of one label lie outside both endpoint neighborhoods. -/
theorem exists_far_port (Γ : PortGraph V D) (label : D → T)
    (d R : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // Γ.origin e = v} ≤ d)
    (x : D) (hbig : 4*d^(R+1) < Nat.card {e : D // label e = label x}) :
    ∃ e : D, label e = label x ∧
      ∀ a ∈ ({Sum.inr x,Sum.inr (Γ.reverse x)} : Set (V ⊕ D)),
      ∀ b ∈ ({Sum.inr e,Sum.inr (Γ.reverse e)} : Set (V ⊕ D)),
      ∀ p : Γ.subdivision.Walk a b, R < p.length := by
  classical
  let X := {e : D // label e = label x}
  let locX : X → V ⊕ D := fun e => .inr e.val
  let locY : X → V ⊕ D := fun e => .inr (Γ.reverse e.val)
  have hX : Function.Injective locX := by
    intro a b h; exact Subtype.ext (Sum.inr.inj h)
  have hY : Function.Injective locY := by
    intro a b h
    exact Subtype.ext (Γ.reverse_reverse.injective (Sum.inr.inj h))
  let B := ball (graphNeighbors Γ.subdivision) (Sum.inr x) R ∪
    ball (graphNeighbors Γ.subdivision) (Sum.inr (Γ.reverse x)) R
  have hB : B.card ≤ 2*d^(R+1) := by
    have ha := card_ball_le (graphNeighbors Γ.subdivision) d h2
      (subdivision_degree Γ d h2 hd) (Sum.inr x) R
    have hb := card_ball_le (graphNeighbors Γ.subdivision) d h2
      (subdivision_degree Γ d h2 hd) (Sum.inr (Γ.reverse x)) R
    exact (Finset.card_union_le _ _).trans (by omega)
  have hbad := matching_bad_card (Equiv.refl X) locX locY hX hY B
  have hlt : (Finset.univ.filter (fun e : X => locX e ∈ B ∨ locY e ∈ B)).card <
      Fintype.card X := by
    rw [Nat.card_eq_fintype_card] at hbig
    change _ < Fintype.card X at hbig
    exact lt_of_le_of_lt (hbad.trans (by omega)) hbig
  obtain ⟨e,he,hebad⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := Finset.univ.filter (fun e : X => locX e ∈ B ∨ locY e ∈ B))
    (t := (Finset.univ : Finset X)) (by simpa only [Finset.card_univ] using hlt)
  have he' : locX e ∉ B ∧ locY e ∉ B := by simpa only [Finset.mem_filter,
    Finset.mem_univ,true_and,not_or] using hebad
  refine ⟨e.val,e.property,?_⟩
  intro a ha b hb p
  have hn : b ∉ ball (graphNeighbors Γ.subdivision) a R := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact fun h => he'.1 (Finset.mem_union_left _ h)
    · exact fun h => he'.2 (Finset.mem_union_left _ h)
    · exact fun h => he'.1 (Finset.mem_union_right _ h)
    · exact fun h => he'.2 (Finset.mem_union_right _ h)
  exact far_of_not_mem_ball Γ.subdivision R hn p

omit [Fintype V] [Fintype D] in
/-- The conjugation switch is exactly the graph two-switch used in girth repair. -/
theorem subdivision_switch (Γ : PortGraph V D) (x e : D)
    (hxe : x ≠ e) (hxr : x ≠ Γ.reverse e) :
    (Γ.switch x e).subdivision =
      addEdge (addEdge (Γ.subdivision.deleteEdges
        {s(Sum.inr x,Sum.inr (Γ.reverse x)),s(Sum.inr e,Sum.inr (Γ.reverse e))})
        (Sum.inr x) (Sum.inr (Γ.reverse e))) (Sum.inr e) (Sum.inr (Γ.reverse x)) := by
  ext a b
  rw [Γ.switch_adj x e hxe hxr]
  simp only [addEdge_adj,SimpleGraph.deleteEdges_adj,Set.mem_insert_iff,
    Set.mem_singleton_iff,not_or]
  have her : e ≠ Γ.reverse x := by
    intro h
    apply hxr
    rw [h,Γ.reverse_reverse]
  have h1 : s(a,b) = s(Sum.inr x,Sum.inr (Γ.reverse e)) → a ≠ b := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simpa using hxr
    · simpa using Ne.symm hxr
  have h2 : s(a,b) = s(Sum.inr e,Sum.inr (Γ.reverse x)) → a ≠ b := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simpa using her
    · simpa using Ne.symm her
  tauto

end TorsionFreeZeroDivisors.MatchingGraphs

namespace TorsionFreeZeroDivisors.ConditionedMatchings
open PortSubdivision BallCount GirthSwitch MatchingGraphs
variable {V D T : Type*}

namespace Matching
variable {label : D → T} {bar : T → T}
instance : CoeFun (Matching label bar) (fun _ => D → D) := ⟨fun r => r.val⟩
instance : DecidableEq (Matching label bar) := Classical.decEq _

theorem label_reverse (r : Matching label bar) (x : D) :
    label (r x) = bar (label x) := r.property.2.2 x

@[ext] theorem ext {r s : Matching label bar} (h : ∀ x, r x = s x) : r = s :=
  Subtype.ext (Equiv.ext h)

variable [DecidableEq D]

/-- Conjugating by the transposition of equally labelled ports. -/
def switch (r : Matching label bar) (x e : D) (he : label x = label e) : Matching label bar :=
  ⟨(Equiv.swap x e).trans (r.val.trans (Equiv.swap x e)),by
    constructor
    · intro f; simp
    constructor
    · intro f h
      have h' := congrArg (Equiv.swap x e) h
      simp only [Equiv.trans_apply,Equiv.swap_apply_self] at h'
      exact r.property.2.1 ((Equiv.swap x e) f) h'
    · intro f
      change label ((Equiv.swap x e) (r ((Equiv.swap x e) f))) = bar (label f)
      rw [PortGraph.label_swap label x e he, r.label_reverse,PortGraph.label_swap label x e he]⟩

@[simp] theorem switch_apply (r : Matching label bar) (x e : D) (he : label x = label e) (f : D) :
    r.switch x e he f = (Equiv.swap x e) (r ((Equiv.swap x e) f)) := rfl

@[simp] theorem switch_switch (r : Matching label bar) (x e : D) (he : label x = label e) :
    (r.switch x e he).switch x e he = r := by
  ext f
  simp

theorem graph_switch (r : Matching label bar) (origin : D → V)
    (x e : D) (he : label x = label e) :
    (r.switch x e he).graph origin = (r.graph origin).switch x e := rfl

/-- Given the new matching and the fixed old pair x,y, the auxiliary port
is forced. This is the reconstructibility behind the conditional estimate. -/
theorem switch_recover (r : Matching label bar) (x y e : D)
    (he : label x = label e) (hxy : r x = y)
    (hbar : ∀ t, bar t ≠ t) : r.switch x e he y = e := by
  have hyx : y ≠ x := hxy ▸ r.property.2.1 x
  have hye : y ≠ e := by
    intro h
    have hl := r.label_reverse x
    rw [hxy,h,← he] at hl
    exact hbar (label x) hl.symm
  simp only [switch_apply,Equiv.swap_apply_of_ne_of_ne hyx hye]
  rw [← hxy,r.reverse_reverse,Equiv.swap_apply_left]

/-- Distinct input-matching/auxiliary-port pairs always give distinct outputs. -/
theorem switch_injective (x y : D) (hbar : ∀ t, bar t ≠ t) :
    Function.Injective (fun p : {r : Matching label bar // r x = y} ×
      {e : D // label x = label e} => p.1.val.switch x p.2.val p.2.property) := by
  rintro ⟨⟨r,hr⟩,⟨e,he⟩⟩ ⟨⟨s,hs⟩,⟨f,hf⟩⟩ h
  have hef : e = f := by
    simpa only [switch_recover r x y e he hr hbar,switch_recover s x y f hf hs hbar]
      using congrArg (fun r : Matching label bar => r y) h
  subst f
  have hrs : r = s := by
    simpa only [switch_switch] using congrArg (fun r : Matching label bar => r.switch x e he) h
  subst s
  rfl

omit [DecidableEq D] in
/-- A signed label chooses a unique orientation of each matching edge. -/
theorem edge_name_injective (r : Matching label bar) (x : D)
    (hbar : ∀ t, bar t ≠ t) :
    Function.Injective (fun e : {e : D // label e = label x} => s(e.val,r e.val)) := by
  rintro ⟨e,he⟩ ⟨f,hf⟩ h
  rcases Sym2.eq_iff.mp h with ⟨hef,_⟩ | ⟨hef,_⟩
  · exact Subtype.ext hef
  · have hh := congrArg label hef
    rw [r.label_reverse,he,hf] at hh
    exact False.elim (hbar (label x) hh.symm)

/-- Switching two edges disjoint from the prior prescriptions preserves them. -/
theorem switch_contains (r : Matching label bar) (C : Finset (Sym2 D))
    (hC : r.Contains C) (x e : D) (he : label x = label e)
    (hxC : s(x,r x) ∉ C) (heC : s(e,r e) ∉ C) : (r.switch x e he).Contains C := by
  intro a b hab
  have hr := hC a b hab
  have hax : a ≠ x := by intro h; subst a; exact hxC (hr ▸ hab)
  have hae : a ≠ e := by intro h; subst a; exact heC (hr ▸ hab)
  have hbx : b ≠ x := by
    intro h
    have hra : r x = a := by rw [← h,← hr,r.reverse_reverse]
    exact hxC (by simpa only [hra,h,Sym2.eq_swap] using hab)
  have hbe : b ≠ e := by
    intro h
    have hra : r e = a := by rw [← h,← hr,r.reverse_reverse]
    exact heC (by simpa only [hra,h,Sym2.eq_swap] using hab)
  simp only [switch_apply,Equiv.swap_apply_of_ne_of_ne hax hae,hr,
    Equiv.swap_apply_of_ne_of_ne hbx hbe]

variable [Fintype V] [Fintype D]

/-- All allowed transpositions for the distinguished port, omitting prior
edges and both radius-R endpoint balls. -/
def admissible (r : Matching label bar) (origin : D → V) (x : D)
    (R : ℕ) (C : Finset (Sym2 D)) : Finset {e : D // label e = label x} := by
  classical
  let Γ := r.graph origin
  let B := ball (graphNeighbors Γ.subdivision) (Sum.inr x) R ∪
    ball (graphNeighbors Γ.subdivision) (Sum.inr (r x)) R
  exact Finset.univ.filter fun e => s(e.val,r e.val) ∉ C ∧
    Sum.inr e.val ∉ B ∧ Sum.inr (r e.val) ∉ B

/-- The excluded prior set costs exactly one port per prior edge, not two. -/
theorem admissible_card (r : Matching label bar) (origin : D → V)
    (hbar : ∀ t, bar t ≠ t) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (x : D) (R : ℕ) (C : Finset (Sym2 D)) :
    Nat.card {e : D // label e = label x} - C.card - 4*d^(R+1) ≤
      (r.admissible origin x R C).card := by
  classical
  let X := {e : D // label e = label x}
  let P : Finset X := Finset.univ.filter fun e => s(e.val,r e.val) ∈ C
  have hP : P.card ≤ C.card := by
    apply Finset.card_le_card_of_injOn (fun e : X => s(e.val,r e.val))
    · intro e he; exact (Finset.mem_filter.mp he).2
    · exact (r.edge_name_injective x hbar).injOn
  have hbound := BallCount.admissible_card (Equiv.refl X)
    (fun e : X => (Sum.inr e.val : V ⊕ D)) (fun e : X => (Sum.inr (r e.val) : V ⊕ D))
    (by intro a b h; exact Subtype.ext (Sum.inr.inj h))
    (by intro a b h; exact Subtype.ext (r.val.injective (Sum.inr.inj h)))
    (graphNeighbors (r.graph origin).subdivision) d h2
    (subdivision_degree (r.graph origin) d h2 hd) (Sum.inr x) (Sum.inr (r x)) R P
  have ht : Fintype.card X - P.card - 4*d^(R+1) ≤
      (r.admissible origin x R C).card := by
    convert hbound using 1
    congr 1
    ext e
    simp [admissible,P]
  rw [Nat.card_eq_fintype_card]
  exact (Nat.sub_le_sub_right (Nat.sub_le_sub_left hP _) _).trans ht

/-- The girth condition is preserved by each counted auxiliary port. -/
theorem admissible_preserves (r : Matching label bar) (origin : D → V)
    (x : D) (N : ℕ) (C : Finset (Sym2 D))
    (hC : r.Contains C) (hxC : s(x,r x) ∉ C)
    (hg : (N : ℕ∞) ≤ (r.graph origin).subdivision.egirth)
    (e : {e : D // label e = label x}) (he : e ∈ r.admissible origin x (2*N) C) :
    (r.switch x e.val e.property.symm).Contains C ∧
      (N : ℕ∞) ≤ ((r.switch x e.val e.property.symm).graph origin).subdivision.egirth := by
  classical
  have he' := Finset.mem_filter.mp he |>.2
  change s(e.val,r e.val) ∉ C ∧ _ at he'
  have hfar : ∀ a ∈ ({Sum.inr x,Sum.inr (r x)} : Set (V ⊕ D)),
      ∀ b ∈ ({Sum.inr e.val,Sum.inr (r e.val)} : Set (V ⊕ D)),
      ∀ p : (r.graph origin).subdivision.Walk a b, 2*N < p.length := by
    intro a ha b hb p
    apply far_of_not_mem_ball (r.graph origin).subdivision (2*N) _ p
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact fun h => he'.2.1 (Finset.mem_union_left _ h)
    · exact fun h => he'.2.2 (Finset.mem_union_left _ h)
    · exact fun h => he'.2.1 (Finset.mem_union_right _ h)
    · exact fun h => he'.2.2 (Finset.mem_union_right _ h)
  have far_ne {a b : V ⊕ D}
      (hf : ∀ p : (r.graph origin).subdivision.Walk a b, 2*N < p.length) : a ≠ b := by
    intro h
    subst b
    have hh := hf SimpleGraph.Walk.nil
    simp at hh
  have hxe : x ≠ e.val := by
    intro h
    exact far_ne (hfar (.inr x) (by simp) (.inr e.val) (by simp)) (congrArg Sum.inr h)
  have hxr : x ≠ r e.val := by
    intro h
    exact far_ne (hfar (.inr x) (by simp) (.inr (r e.val)) (by simp)) (congrArg Sum.inr h)
  refine ⟨r.switch_contains C hC x e.val e.property.symm hxC he'.1,?_⟩
  rw [graph_switch,subdivision_switch (r.graph origin) x e.val hxe hxr]
  exact girth_switch N hg rfl hfar

/-- Direct double counting on the whole tuple space, with all other matchings
retained in the output. No independence after conditioning is used. -/
theorem conditioned_count (origin : D → V) (N : ℕ) (C : Finset (Sym2 D))
    (hbar : ∀ t, bar t ≠ t) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (x y : D) (hxy : s(x,y) ∉ C) :
    ((conditioned (label := label) (bar := bar) origin N C).filter (fun r => r x = y)).card *
      (Nat.card {e : D // label e = label x} - C.card - 4*d^(2*N+1)) ≤
      (conditioned (label := label) (bar := bar) origin N C).card := by
  classical
  let Ω := conditioned (label := label) (bar := bar) origin N C
  let r₀ := Nat.card {e : D // label e = label x} - C.card - 4*d^(2*N+1)
  let F := {r : Matching label bar // r ∈ Ω ∧ r x = y}
  let S := (r : F) × {e : {e : D // label e = label x} //
    e ∈ r.val.admissible origin x (2*N) C}
  have hm (r : F) : r.val.Contains C ∧
      (N : ℕ∞) ≤ (r.val.graph origin).subdivision.egirth := by
    have h := r.property.1
    simpa only [Ω,conditioned,Finset.mem_filter,Finset.mem_univ,true_and] using h
  let out : S → {r : Matching label bar // r ∈ Ω} := fun p =>
    ⟨p.1.val.switch x p.2.val.val p.2.val.property.symm,by
      have hh := p.1.val.admissible_preserves origin x N C (hm p.1).1
        (by simpa only [p.1.property.2] using hxy) (hm p.1).2 p.2.val p.2.property
      simpa only [Ω,conditioned,Finset.mem_filter,Finset.mem_univ,true_and] using hh⟩
  have hout : Function.Injective out := by
    intro p q h
    have hs : p.1.val.switch x p.2.val.val p.2.val.property.symm =
        q.1.val.switch x q.2.val.val q.2.val.property.symm := congrArg Subtype.val h
    have hi := switch_injective (label := label) (bar := bar) x y hbar
      (a₁ := (⟨p.1.val,p.1.property.2⟩,⟨p.2.val.val,p.2.val.property.symm⟩))
      (a₂ := (⟨q.1.val,q.1.property.2⟩,⟨q.2.val.val,q.2.val.property.symm⟩)) hs
    have hr : p.1 = q.1 := Subtype.ext (congrArg (fun z => z.1.val) hi)
    cases p with
    | mk r e =>
      cases q with
      | mk s f =>
        dsimp at hr
        subst s
        have hef : e = f := Subtype.ext (Subtype.ext (congrArg (fun z => z.2.val) hi))
        subst f
        rfl
  have hc := Fintype.card_le_of_injective out hout
  have hsource : Fintype.card S = ∑ r : F, (r.val.admissible origin x (2*N) C).card := by
    simp only [S,Fintype.card_sigma,Fintype.card_coe]
  have htarget : Fintype.card {r : Matching label bar // r ∈ Ω} = Ω.card := Fintype.card_coe Ω
  have hF : Fintype.card F = (Ω.filter (fun r => r x = y)).card := by
    change Fintype.card {r : Matching label bar // r ∈ Ω ∧ r x = y} = _
    rw [Fintype.card_subtype]
    congr 1
    ext r
    simp
  have hsum : Fintype.card F * r₀ ≤ ∑ r : F, (r.val.admissible origin x (2*N) C).card := by
    calc
      Fintype.card F * r₀ = ∑ _r : F, r₀ := by simp
      _ ≤ ∑ r : F, (r.val.admissible origin x (2*N) C).card :=
        Finset.sum_le_sum fun r _ => r.val.admissible_card origin hbar d h2 hd x (2*N) C
  rw [hsource,htarget] at hc
  rw [hF] at hsum
  exact hsum.trans hc

omit [Fintype D] in
/-- Adding one undirected prescription is exactly one matching-coordinate
condition; the reverse orientation is automatic, not an extra constraint. -/
theorem contains_insert (r : Matching label bar) (C : Finset (Sym2 D)) (x y : D) :
    r.Contains (insert s(x,y) C) ↔ r.Contains C ∧ r x = y := by
  classical
  constructor
  · intro h
    exact ⟨fun a b hab => h a b (Finset.mem_insert_of_mem hab),h x y (by simp)⟩
  · rintro ⟨hC,hxy⟩ a b hab
    rcases Finset.mem_insert.mp hab with h | h
    · rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hxy
      · rw [← hxy,r.reverse_reverse]
    · exact hC a b h

omit [Fintype V] in
theorem conditioned_insert (origin : D → V) (N : ℕ) (C : Finset (Sym2 D))
    (x y : D) :
    conditioned (label := label) (bar := bar) origin N (insert s(x,y) C) =
      (conditioned (label := label) (bar := bar) origin N C).filter (fun r => r x = y) := by
  classical
  ext r
  simp only [conditioned,Finset.mem_filter,Finset.mem_univ,true_and,contains_insert]
  tauto

/-- The simultaneous-prescription bound obtained by successive conditioning.
No independence is asserted, even for prescriptions on distinct labels. -/
theorem prescriptions_count (origin : D → V) (N : ℕ)
    (hbar : ∀ t, bar t ≠ t) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (R : ℕ) (C : Finset (Sym2 D))
    (hR : ∀ x, R + C.card + 4*d^(2*N+1) ≤ Nat.card {e : D // label e = label x}) :
    (conditioned (label := label) (bar := bar) origin N C).card * R^C.card ≤
      (conditioned (label := label) (bar := bar) origin N ∅).card := by
  classical
  induction C using Finset.induction with
  | empty => simp
  | @insert e C he ih =>
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hR' : ∀ z, R + C.card + 4*d^(2*N+1) ≤
          Nat.card {e : D // label e = label z} := by
        intro z
        have hh := hR z
        rw [Finset.card_insert_of_notMem he] at hh
        omega
      have hstep := conditioned_count (label := label) (bar := bar)
        origin N C hbar d h2 hd x y he
      have hsmall : R ≤ Nat.card {e : D // label e = label x} - C.card - 4*d^(2*N+1) := by
        have := hR' x
        omega
      have hstep' : (conditioned (label := label) (bar := bar) origin N (insert s(x,y) C)).card * R ≤
          (conditioned (label := label) (bar := bar) origin N C).card := by
        rw [conditioned_insert]
        exact (Nat.mul_le_mul_left _ hsmall).trans hstep
      rw [Finset.card_insert_of_notMem he,pow_succ,← mul_assoc,mul_right_comm]
      exact (Nat.mul_le_mul_right _ hstep').trans (ih hR')

end Matching
end TorsionFreeZeroDivisors.ConditionedMatchings

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PatternCount
open scoped Classical
open ConditionedMatchings
variable {V D T F E A : Type*} [Fintype V] [Fintype D] [Fintype F] [Fintype E]
variable (label : D → T) (bar : T → T)

end TorsionFreeZeroDivisors.PatternCount

namespace TorsionFreeZeroDivisors.PatternEmbeddings
open scoped BigOperators Classical
open PortSubdivision ConditionedMatchings
variable {PV PD TV T : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]

variable (Γ : PortGraph PV PD) (plabel : PD → T) (outgoing : TV → Finset T)
  (allowed : PV → Finset TV)
  (hallowed : ∀ v x, x ∈ allowed v → ∀ d, Γ.origin d = v → plabel d ∈ outgoing x)

end TorsionFreeZeroDivisors.PatternEmbeddings

/-!
Exact finite geometry and type system over the field with 128 elements.
-/

namespace TorsionFreeZeroDivisors
namespace Types

open scoped LinearAlgebra.Projectivization
open Configuration

instance : DecidableEq Field128 := Classical.decEq _

theorem order_eq : ProjectivePlane.order Point Line = 128 := by
  have h := ProjectivePlane.card_points Point Line
  rw [point_card] at h
  have hi : (16513 : ℤ) = (ProjectivePlane.order Point Line : ℤ) ^ 2 +
      (ProjectivePlane.order Point Line : ℤ) + 1 := by exact_mod_cast h
  have hf : ((ProjectivePlane.order Point Line : ℤ) - 128) *
      ((ProjectivePlane.order Point Line : ℤ) + 129) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with h1 | h1 <;> omega

def linesOn (p : Point) : Finset Line := Finset.univ.filter (p ∈ ·)

@[simp] theorem mem_pointsOn {p : Point} {l : Line} : p ∈ pointsOn l ↔ p ∈ l := by
  simp [pointsOn]

@[simp] theorem mem_linesOn {p : Point} {l : Line} : l ∈ linesOn p ↔ p ∈ l := by
  simp [linesOn]

theorem pointsOn_card (l : Line) : (pointsOn l).card = 129 := by
  have h := ProjectivePlane.pointCount_eq Point l
  rw [order_eq] at h
  simpa [pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype, pointsOn] using h

theorem linesOn_card (p : Point) : (linesOn p).card = 129 := by
  have h := ProjectivePlane.lineCount_eq Line p
  rw [order_eq] at h
  simpa [lineCount, Nat.card_eq_fintype_card, Fintype.card_subtype, linesOn] using h

/-- Counting a predicate depending only on the first coordinate. -/
theorem card_prod_fst {U V : Type*} [Fintype U] [Fintype V]
    (p : U → Prop) [DecidablePred p] :
    Fintype.card {x : U × V // p x.1} = Fintype.card {u : U // p u} * Fintype.card V := by
  let e : {x : U × V // p x.1} ≃ {u : U // p u} × V :=
    { toFun := fun x => (⟨x.val.1, x.property⟩, x.val.2)
      invFun := fun x => ⟨(x.1.val, x.2), x.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod]

theorem card_prod_snd {U V : Type*} [Fintype U] [Fintype V]
    (p : V → Prop) [DecidablePred p] :
    Fintype.card {x : U × V // p x.2} = Fintype.card U * Fintype.card {v : V // p v} := by
  let e : {x : U × V // p x.2} ≃ U × {v : V // p v} :=
    { toFun := fun x => (x.val.1, ⟨x.val.2, x.property⟩)
      invFun := fun x => ⟨(x.1, x.2.val), x.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod]

/-! The empirical type slots. Each line has exactly 33026 slots on each
side, before the admissible replication parameter is applied. -/

theorem card_slotA : Fintype.card SlotA = 33026 := by
  simp [SlotA]

theorem card_slotB : Fintype.card SlotB = 33026 := by
  simp [SlotB]

theorem card_vertexA (N : ℕ) : Fintype.card (VertexA N) = 2 * 16513 ^ 2 * N := by
  simp only [Fintype.card_prod, card_slotA, Fintype.card_fin, point_card]
  ring

theorem card_vertexB (N : ℕ) : Fintype.card (VertexB N) = 2 * 16513 ^ 2 * N := by
  simp only [Fintype.card_prod, card_slotB, Fintype.card_fin, point_card]
  ring

theorem degreeA_bounds {N : ℕ} (x : VertexA N) :
    129 ≤ (outgoingA x).card ∧ (outgoingA x).card ≤ 132 := by
  rw [outgoingA, Finset.card_disjSum, pointsOn_card]
  rcases x.2.1 with ⟨i,j⟩ | k <;> simp [extrasA, Finset.card_erase_of_mem]

theorem degreeB_bounds {N : ℕ} (y : VertexB N) :
    129 ≤ (outgoingB y).card ∧ (outgoingB y).card ≤ 132 := by
  rw [outgoingB, Finset.card_disjSum, pointsOn_card]
  cases y.2.1 <;> simp [extrasB]

theorem slotA_extra_frequency (e : Fin 3) :
    Fintype.card {a : SlotA // e ∈ extrasA a} = 258 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  have hz : (∑ a : Fin 32639, if e ∈ extrasA (.inr a) then 1 else 0) = 0 := by
    simp [extrasA]
  rw [hz, add_zero, Fintype.sum_prod_type]
  have hi (i : Fin 3) :
      (∑ j : Fin 129, if e ∈ extrasA (.inl (i,j)) then 1 else 0) =
        129 * (if e ≠ i then 1 else 0) := by
    by_cases h : e = i <;> simp [extrasA, h]
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_boole]
  have hc : (Finset.univ.filter fun i : Fin 3 => e ≠ i) = Finset.univ.erase e := by ext i; simp [ne_comm]
  rw [hc]
  simp

theorem slotB_extra_frequency (e : Fin 3) :
    Fintype.card {b : SlotB // e ∈ extrasB b} = 258 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp [extrasB]

/-- Each of the 16516 letters has exactly np carriers on each side. -/
theorem letter_frequencyA (N : ℕ) (t : Letter) :
    Fintype.card {x : VertexA N // t ∈ outgoingA x} = 4260354 * N := by
  cases t with
  | inl p =>
    have he : (fun x : VertexA N => Sum.inl p ∈ outgoingA x) =
        (fun x => p ∈ x.1) := by funext x; simp [outgoingA]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => iff_of_eq (congrFun he x))),
      card_prod_fst (V := SlotA × Fin N) (fun l : Line => p ∈ l), Fintype.card_prod, card_slotA, Fintype.card_fin]
    have hc : Fintype.card {l : Line // p ∈ l} = 129 := by
      rw [Fintype.card_subtype]
      exact linesOn_card p
    rw [hc]
    ring
  | inr e =>
    have he : (fun x : VertexA N => Sum.inr e ∈ outgoingA x) =
        (fun x => e ∈ extrasA x.2.1) := by funext x; simp [outgoingA]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => iff_of_eq (congrFun he x))),
      card_prod_snd (U := Line) (fun x : SlotA × Fin N => e ∈ extrasA x.1),
      card_prod_fst (V := Fin N) (fun a : SlotA => e ∈ extrasA a),
      point_card, slotA_extra_frequency,
      Fintype.card_fin]
    ring

theorem letter_frequencyB (N : ℕ) (t : Letter) :
    Fintype.card {x : VertexB N // t ∈ outgoingB x} = 4260354 * N := by
  cases t with
  | inl p =>
    have he : (fun x : VertexB N => Sum.inl p ∈ outgoingB x) =
        (fun x => p ∈ x.1) := by funext x; simp [outgoingB]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => iff_of_eq (congrFun he x))),
      card_prod_fst (V := SlotB × Fin N) (fun l : Line => p ∈ l), Fintype.card_prod, card_slotB, Fintype.card_fin]
    have hc : Fintype.card {l : Line // p ∈ l} = 129 := by
      rw [Fintype.card_subtype]
      exact linesOn_card p
    rw [hc]
    ring
  | inr e =>
    have he : (fun x : VertexB N => Sum.inr e ∈ outgoingB x) =
        (fun x => e ∈ extrasB x.2.1) := by funext x; simp [outgoingB]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => iff_of_eq (congrFun he x))),
      card_prod_snd (U := Line) (fun x : SlotB × Fin N => e ∈ extrasB x.1),
      card_prod_fst (V := Fin N) (fun b : SlotB => e ∈ extrasB b),
      point_card, slotB_extra_frequency,
      Fintype.card_fin]
    ring

/-! ### The fixed inverse pairing and the actual space of graph matchings -/

@[simp] theorem inverse_signed (g : Generator) (b : Bool) :
    inverse (signedLetter (g,b)) = signedLetter (g,!b) := by simp [inverse]

@[simp] theorem inverse_inverse (t : Letter) : inverse (inverse t) = t := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  simp

theorem inverse_ne (t : Letter) : inverse t ≠ t := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  intro he
  cases b <;> simp only [inverse_signed, Bool.not_true, Bool.not_false] at he <;>
    cases signedLetter.injective he

variable {V : Type*} (outgoing : V → Finset Letter)

/-- Each inverse pair receives a bijection between its two carrier sets. -/
def MatchingTuple := (g : Generator) →
  {x : V // signedLetter (g,true) ∈ outgoing x} ≃
    {x : V // signedLetter (g,false) ∈ outgoing x}

/-- Exact empirical balance ensures the finite matching space is nonempty. -/
theorem matchingTuple_nonempty [Fintype V]
    (hfreq : ∀ t u, Fintype.card {x : V // t ∈ outgoing x} =
      Fintype.card {x : V // u ∈ outgoing x}) : Nonempty (MatchingTuple outgoing) := by
  exact ⟨fun g => Fintype.equivOfCardEq (hfreq _ _)⟩

/-- The direction of a step is given by the signed letter. Non-carrier
values are immaterial and are defined to fix the vertex. -/
def nextSigned (M : MatchingTuple outgoing) (x : V) : Signed → V
  | (g,true) => if hx : signedLetter (g,true) ∈ outgoing x then (M g ⟨x,hx⟩).val else x
  | (g,false) => if hx : signedLetter (g,false) ∈ outgoing x then ((M g).symm ⟨x,hx⟩).val else x

def next (M : MatchingTuple outgoing) (x : V) (t : Letter) : V :=
  nextSigned outgoing M x (signedLetter.symm t)

@[simp] theorem next_signed (M : MatchingTuple outgoing) (x : V) (g : Generator) (b : Bool) :
    next outgoing M x (signedLetter (g,b)) = nextSigned outgoing M x (g,b) := by
  simp [next]

theorem next_reverse_mem (M : MatchingTuple outgoing) (x : V) (t : Letter)
    (ht : t ∈ outgoing x) : inverse t ∈ outgoing (next outgoing M x t) := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  cases b <;> simp only [inverse_signed, Bool.not_true, Bool.not_false, next_signed]
  · simpa [nextSigned, ht] using ((M g).symm ⟨x,ht⟩).property
  · simpa [nextSigned, ht] using (M g ⟨x,ht⟩).property

theorem next_reverse_next (M : MatchingTuple outgoing) (x : V) (t : Letter)
    (ht : t ∈ outgoing x) : next outgoing M (next outgoing M x t) (inverse t) = x := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  cases b <;> simp only [inverse_signed, Bool.not_true, Bool.not_false, next_signed]
  · simp only [nextSigned, dif_pos ht]
    have hc := ((M g).symm ⟨x,ht⟩).property
    rw [dif_pos hc]
    exact congrArg Subtype.val ((M g).apply_symm_apply ⟨x,ht⟩)
  · simp only [nextSigned, dif_pos ht]
    have hc := (M g ⟨x,ht⟩).property
    rw [dif_pos hc]
    exact congrArg Subtype.val ((M g).symm_apply_apply ⟨x,ht⟩)

/-- In particular both source sides have an actual matching space. This
makes no girth or arrangement claim about a chosen point in that space. -/
theorem matchingA_nonempty (N : ℕ) : Nonempty (MatchingTuple (@outgoingA N)) :=
  matchingTuple_nonempty _ (fun t u => (letter_frequencyA N t).trans (letter_frequencyA N u).symm)

theorem matchingB_nonempty (N : ℕ) : Nonempty (MatchingTuple (@outgoingB N)) :=
  matchingTuple_nonempty _ (fun t u => (letter_frequencyB N t).trans (letter_frequencyB N u).symm)

/-! Joint type incidences for internal-chain vertex counts.
These derive the turn weights from the actual prescribed types. -/

end Types
end TorsionFreeZeroDivisors

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ListPassages
open scoped Classical BigOperators

variable {D : Type*} (p : List D) (hp : p ≠ [])

end TorsionFreeZeroDivisors.ListPassages
namespace TorsionFreeZeroDivisors.ChainPathTransport
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open WeightedMoore
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "w" => word Γ mark h2

end TorsionFreeZeroDivisors.ChainPathTransport
namespace TorsionFreeZeroDivisors.ListStageExponents
open scoped Classical BigOperators
open PortSubdivision WeightedMoore
variable {V D I : Type*} [Fintype V] [Fintype D] [Fintype I]
    (Γ : PortGraph V D) (p : I → List D) (hp : ∀ i,p i ≠ [])
    (cyclic : I → Bool)
    (hc : ∀ i,(p i).IsChain (PortWalk.step Γ.origin Γ.reverse))
    (hclose : ∀ i,cyclic i=true → ∀ᵉ (x∈(p i).getLast?) (y∈(p i).head?),
      PortWalk.step Γ.origin Γ.reverse x y)

end TorsionFreeZeroDivisors.ListStageExponents

/-! A choice of one direction for each unoriented edge of a finite port graph.
The reversal has no fixed points. No graph is assumed bipartite or loop-free. -/
namespace TorsionFreeZeroDivisors.InvolutionOrientation
open scoped Classical BigOperators
variable {D : Type*} [Fintype D] (σ : D → D)

variable (hσ : Function.Involutive σ) (hne : ∀d,σ d≠d)

include hσ hne

@[simp] lemma equiv_false (c : Representative σ) : equiv σ hσ hne (c,false) = c.val := rfl
@[simp] lemma equiv_true (c : Representative σ) : equiv σ hσ hne (c,true) = σ c.val := rfl

end TorsionFreeZeroDivisors.InvolutionOrientation
namespace TorsionFreeZeroDivisors.ChainIsomorphism
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => InvolutionOrientation.Representative (PortGraph.reverse (suppressed Γ mark h2))
local notation "len" => chainLength Γ mark h2

variable [Fintype V]

end TorsionFreeZeroDivisors.ChainIsomorphism

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageRealization
open scoped Classical
open PortSubdivision
end TorsionFreeZeroDivisors.StageRealization

namespace TorsionFreeZeroDivisors.ChainRealization
open scoped Classical BigOperators
open TorsionFreeZeroDivisors.Types
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C V : Type*} [Fintype C] [Fintype V]
variable (len : C → ℕ) (first last : C → V)

end TorsionFreeZeroDivisors.ChainRealization

namespace TorsionFreeZeroDivisors.ChainWeights
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len : C → ℕ)

end TorsionFreeZeroDivisors.ChainWeights

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageExpectation
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
section
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C V TV : Type*} [Fintype C] [Fintype V] [Fintype TV]
variable (s : ℝ) (hs : 0 < s) (len : C → ℕ) (first last : C → V)

end

section Active
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ) (j : ℕ)

end Active
variable {C V TV : Type*} [Fintype C] [Fintype V] [Fintype TV]
variable (s : ℝ) (hs : 0 < s) (len : C → ℕ) (first last : C → V)
local instance : DecidableEq Types.Letter := Classical.decEq _

end TorsionFreeZeroDivisors.StageExpectation

/-! Finite Fubini for the product of the separately girth-conditioned sides.
The label set here is global: it is not replaced by the product of its two
projections. This is the independence actually used in entropy.tex 396–435. -/
namespace TorsionFreeZeroDivisors.TwoSideMean
open scoped BigOperators Classical

variable {A B W : Type*}

end TorsionFreeZeroDivisors.TwoSideMean

namespace TorsionFreeZeroDivisors.TwoSideStage
open scoped Classical BigOperators
open PatternEmbeddings ConditionedMatchings BlockAlignment ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _

variable (s : ℝ) (hs : 0 < s)

variable {W : Type*}

end TorsionFreeZeroDivisors.TwoSideStage

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TwoSideFullStage
open scoped Classical BigOperators
open RepeatedBlocks BlockAlignment ComparedBlocks WordEstimate
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {A B E VA VB TA TB : Type} [Fintype A] [Fintype B] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : A ⊕ B → ℕ) (j : ℕ)

variable (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter) (pinA : VA → Option TA) (pinB : VB → Option TB)

end TorsionFreeZeroDivisors.TwoSideFullStage

namespace TorsionFreeZeroDivisors.MatchingGraphs
open PortSubdivision BallCount GirthSwitch
variable {V D T : Type*} [Fintype V] [Fintype D] [DecidableEq D]

/-- Nonemptiness of the exact typed matching family conditioned on girth.
The numerical hypothesis is an explicit finite-size bound, not a new standing
hypothesis for the main existential theorem. -/
theorem exists_typed_large_girth (origin : D → V) (label : D → T) (bar : T → T)
    (Γ₀ : PortGraph V D) (ho : Γ₀.origin = origin)
    (hlabel : ∀ f, label (Γ₀.reverse f) = bar (label f))
    (d N : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (hbig : ∀ x, 4*d^(2*N+1) < Nat.card {e : D // label e = label x}) :
    ∃ Γ : PortGraph V D, Γ.origin = origin ∧
      (∀ f, label (Γ.reverse f) = bar (label f)) ∧
      (N : ℕ∞) ≤ Γ.subdivision.egirth := by
  classical
  let P : SimpleGraph (V ⊕ D) → Prop := fun G =>
    ∃ Γ : PortGraph V D, Γ.origin = origin ∧
      (∀ f, label (Γ.reverse f) = bar (label f)) ∧ G = Γ.subdivision
  have hne : ∃ G, P G := ⟨Γ₀.subdivision,Γ₀,ho,hlabel,rfl⟩
  have hsw : ∀ G, P G → ∀ a (p : G.Walk a a), p.IsCycle →
      ∃ x y u z, s(x,y) ∈ p.edges ∧ G.Adj u z ∧
        (∀ a ∈ ({x,y} : Set (V ⊕ D)), ∀ b ∈ ({u,z} : Set (V ⊕ D)),
          ∀ p : G.Walk a b, 2*N < p.length) ∧
        P (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y) := by
    rintro G ⟨Γ,hΓo,hΓl,rfl⟩ a p hp
    obtain ⟨x,hx⟩ := Γ.cycle_has_middle p hp
    have hd' : ∀ v, Nat.card {e : D // Γ.origin e = v} ≤ d := by rw [hΓo]; exact hd
    obtain ⟨e,hel,hfar⟩ := exists_far_port Γ label d (2*N) h2 hd' x (hbig x)
    have hxe : x ≠ e := by
      intro h
      have hf := hfar (.inr x) (by simp) (.inr e) (by simp)
      subst e
      have hh := hf SimpleGraph.Walk.nil
      simp at hh
    have hxr : x ≠ Γ.reverse e := by
      intro h
      have hf := hfar (.inr x) (by simp) (.inr (Γ.reverse e)) (by simp)
      rw [h] at hf
      have hh := hf SimpleGraph.Walk.nil
      simp at hh
    refine ⟨.inr x,.inr (Γ.reverse x),.inr e,.inr (Γ.reverse e),hx,rfl,hfar,?_⟩
    refine ⟨Γ.switch x e,hΓo,Γ.switch_preserves_labels label bar hΓl x e hel.symm,?_⟩
    exact (subdivision_switch Γ x e hxe hxr).symm
  obtain ⟨G,⟨Γ,hΓo,hΓl,hG⟩,hg⟩ := exists_large_girth N P hne hsw
  exact ⟨Γ,hΓo,hΓl,hG ▸ hg⟩

end TorsionFreeZeroDivisors.MatchingGraphs

namespace TorsionFreeZeroDivisors.TypedGraphs
open TorsionFreeZeroDivisors.Types PortSubdivision ConditionedMatchings MatchingGraphs
variable {V : Type*} (outgoing : V → Finset Letter)

def reverse (M : MatchingTuple outgoing) (e : Dart outgoing) : Dart outgoing :=
  ⟨(next outgoing M e.val.1 e.val.2,inverse e.val.2),
    next_reverse_mem outgoing M e.val.1 e.val.2 e.property⟩

theorem reverse_involutive (M : MatchingTuple outgoing) :
    Function.Involutive (reverse outgoing M) := by
  intro e
  apply Subtype.ext
  exact Prod.ext (next_reverse_next outgoing M e.val.1 e.val.2 e.property)
    (inverse_inverse e.val.2)

def matching (M : MatchingTuple outgoing) : Matching (label outgoing) inverse :=
  ⟨(reverse_involutive outgoing M).toPerm (reverse outgoing M),
    reverse_involutive outgoing M,by
      intro e he
      exact inverse_ne e.val.2 (congrArg (label outgoing) he),fun _ => rfl⟩

/-- An origin fibre is exactly the prescribed outgoing type. -/
def originFiber (v : V) : {e : Dart outgoing // origin outgoing e = v} ≃
    {t : Letter // t ∈ outgoing v} where
  toFun e := ⟨e.val.val.2,by
    have h := e.val.property
    simpa only [← e.property,origin,label] using h⟩
  invFun t := ⟨⟨(v,t.val),t.property⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext e.property.symm rfl
  right_inv _ := rfl

/-- A letter fibre is exactly its empirical carrier set on this side. -/
def labelFiber (t : Letter) : {e : Dart outgoing // label outgoing e = t} ≃
    {v : V // t ∈ outgoing v} where
  toFun e := ⟨e.val.val.1,by
    have h := e.val.property
    simpa only [← e.property,origin,label] using h⟩
  invFun v := ⟨⟨(v.val,t),v.property⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl e.property.symm
  right_inv _ := rfl

theorem origin_card (v : V) :
    Nat.card {e : Dart outgoing // origin outgoing e = v} = (outgoing v).card := by
  rw [Nat.card_congr (originFiber outgoing v), Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

theorem label_card [Fintype V] (t : Letter) :
    Nat.card {e : Dart outgoing // label outgoing e = t} =
      Fintype.card {v : V // t ∈ outgoing v} := by
  rw [Nat.card_congr (labelFiber outgoing t),Nat.card_eq_fintype_card]

theorem exists_conditioned [Fintype V] (M : MatchingTuple outgoing) (N : ℕ)
    (hd : ∀ v, (outgoing v).card ≤ 132)
    (hsize : ∀ t, 4*132^(2*N+1) < Fintype.card {v : V // t ∈ outgoing v}) :
    (Matching.conditioned (label := label outgoing) (bar := inverse)
      (origin outgoing) N ∅).Nonempty := by
  classical
  let r := matching outgoing M
  obtain ⟨Γ,hΓo,hΓl,hg⟩ := exists_typed_large_girth
    (origin outgoing) (label outgoing) inverse (r.graph (origin outgoing)) rfl
    (fun e => r.label_reverse e) 132 N (by norm_num)
    (fun v => by rw [origin_card]; exact hd v)
    (fun e => by rw [label_card]; exact hsize _)
  let r' : Matching (label outgoing) inverse :=
    ⟨Γ.reverse_reverse.toPerm Γ.reverse,Γ.reverse_reverse,Γ.reverse_ne,hΓl⟩
  refine ⟨r',Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩⟩
  · intro a b h
    exact False.elim (Finset.notMem_empty _ h)
  · have he : r'.graph (origin outgoing) = Γ := by
      cases Γ
      simp_all only [Matching.graph]
      rfl
    rw [he]
    exact hg

/-- The actual prescribed A-side graph space has nonzero cardinality. -/
theorem conditionedA_nonempty (rep N : ℕ) (hsize : 4*132^(2*N+1) < 4260354*rep) :
    (Matching.conditioned (label := label (@outgoingA rep)) (bar := inverse)
      (origin (@outgoingA rep)) N ∅).Nonempty := by
  classical
  exact exists_conditioned _ (Classical.choice (matchingA_nonempty rep)) N
    (fun v => (degreeA_bounds v).2)
    (fun t => by rw [letter_frequencyA]; exact hsize)

theorem conditionedB_nonempty (rep N : ℕ) (hsize : 4*132^(2*N+1) < 4260354*rep) :
    (Matching.conditioned (label := label (@outgoingB rep)) (bar := inverse)
      (origin (@outgoingB rep)) N ∅).Nonempty := by
  classical
  exact exists_conditioned _ (Classical.choice (matchingB_nonempty rep)) N
    (fun v => (degreeB_bounds v).2)
    (fun t => by rw [letter_frequencyB]; exact hsize)

end TorsionFreeZeroDivisors.TypedGraphs

namespace TorsionFreeZeroDivisors.GirthAsymptotics
open Filter
open scoped Topology

theorem log132_lt : Real.log 132 < 8 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  have h : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_lt_pow_left₀ h (by norm_num : (0 : ℝ) ≤ 2) (by decide : 8 ≠ 0)
  have he : Real.exp (8 : ℝ) = Real.exp 1 ^ 8 := by
    simp [← Real.exp_nat_mul]
  rw [he]
  norm_num at hp ⊢
  linarith

theorem exclusion_bound (n : ℕ) (hn : 1 ≤ n) :
    (exclusion n : ℝ) ≤ 4 * Real.exp 8 * (n : ℝ) ^ (1/2 : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hl : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hf : (L n : ℝ) ≤ Real.log n / 100 := Nat.floor_le (by positivity)
  have he : ((6 * L n + 1 : ℕ) : ℝ) * Real.log 132 ≤ Real.log n / 2 + 8 := by
    push_cast
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt log132_lt)
      (show 0 ≤ 6 * (L n : ℝ) + 1 by positivity)
    nlinarith
  rw [exclusion, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat]
  have hpow : (132 : ℝ) ^ (6 * L n + 1) =
      Real.exp (((6 * L n + 1 : ℕ) : ℝ) * Real.log 132) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 132)]
  rw [hpow,Real.rpow_def_of_pos hn0]
  calc
    4 * Real.exp (↑(6 * L n + 1) * Real.log 132) ≤
        4 * Real.exp (Real.log n / 2 + 8) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num)
    _ = 4 * Real.exp 8 * Real.exp (Real.log n * (1/2)) := by
      rw [Real.exp_add]
      rw [div_eq_mul_inv]
      ring_nf

theorem exclusion_ratio : Tendsto (fun n : ℕ => (exclusion n : ℝ) / n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1/2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
  have ht' := ht.const_mul (4 * Real.exp 8)
  simp only [mul_zero] at ht'
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) _ ht'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    (exclusion n : ℝ) / n ≤ (4 * Real.exp 8 * (n : ℝ) ^ (1/2 : ℝ)) / n :=
      div_le_div_of_nonneg_right (exclusion_bound n hn) (le_of_lt hn0)
    _ = 4 * Real.exp 8 * (n : ℝ) ^ (-(1/2 : ℝ)) := by
      rw [show -(1/2 : ℝ) = 1/2-1 by norm_num,Real.rpow_sub hn0,Real.rpow_one]
      ring

theorem L_tendsto : Tendsto L atTop atTop := by
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ) / 100) atTop atTop := by
    simpa only [div_eq_mul_inv, Function.comp_apply] using
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_mul_const
        (by norm_num : (0 : ℝ) < (100 : ℝ)⁻¹)
  exact tendsto_nat_floor_atTop.comp hl

theorem eventual_small (p : ℝ) (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, (exclusion n : ℝ) < p * n := by
  filter_upwards [exclusion_ratio.eventually_lt_const hp,eventually_ge_atTop 1] with n h hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact (div_lt_iff₀ hn0).mp h

end TorsionFreeZeroDivisors.GirthAsymptotics

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypedGraphs
open Filter GirthAsymptotics TorsionFreeZeroDivisors.Types ConditionedMatchings PortSubdivision
open scoped Topology

theorem size_tendsto : Tendsto size atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => n) _ tendsto_id
  intro n
  dsimp [size]
  omega

theorem eventual_carrier : ∀ᶠ rep : ℕ in atTop,
    4 * 132 ^ (2 * (3 * L (size rep)) + 1) < 4260354 * rep := by
  have h := size_tendsto.eventually (eventual_small (4260354 / (2 * 16513^2)) (by norm_num))
  filter_upwards [h] with rep hr
  have he : (4260354 / (2 * 16513^2) : ℝ) * (size rep : ℝ) = 4260354 * rep := by
    simp only [size,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  rw [he] at hr
  have hr' : exclusion (size rep) < 4260354 * rep := by exact_mod_cast hr
  simpa only [exclusion, show 2 * (3 * L (size rep)) = 6 * L (size rep) by omega] using hr'

/-- Both jointly conditioned graph spaces really exist for all sufficiently
large admissible sizes; no high-girth existence is a standing assumption. -/
theorem eventual_nonempty : ∀ᶠ rep : ℕ in atTop,
    (Matching.conditioned (label := label (@outgoingA rep)) (bar := inverse)
      (origin (@outgoingA rep)) (3 * L (size rep)) ∅).Nonempty ∧
    (Matching.conditioned (label := label (@outgoingB rep)) (bar := inverse)
      (origin (@outgoingB rep)) (3 * L (size rep)) ∅).Nonempty := by
  filter_upwards [eventual_carrier] with rep hr
  exact ⟨conditionedA_nonempty _ _ hr,conditionedB_nonempty _ _ hr⟩

end TorsionFreeZeroDivisors.TypedGraphs

namespace TorsionFreeZeroDivisors.TypedStage
open scoped Classical BigOperators Topology
open TorsionFreeZeroDivisors.Types TwoSideStage GirthAsymptotics Filter
local instance : DecidableEq Types.Letter := Classical.decEq _

variable {C V : Type} [Fintype C] [Fintype V]
variable (rep : ℕ) (len : C → ℕ) (first last : C → V)

end TorsionFreeZeroDivisors.TypedStage

namespace TorsionFreeZeroDivisors.StageCost
open scoped BigOperators

end TorsionFreeZeroDivisors.StageCost

namespace TorsionFreeZeroDivisors.StageDenominator

section
open scoped Topology
open Filter GirthAsymptotics TypedGraphs

end

open scoped BigOperators Topology
open Filter GirthAsymptotics TypedGraphs TwoSideStage

variable {C V : Type} [Fintype C] [Fintype V]

end TorsionFreeZeroDivisors.StageDenominator

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageEntropy

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0<s) (len m : C → ℕ) (err : ℕ)

end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate TwoSideFullStage
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {A B E VA VB TA TB : Type} [Fintype A] [Fintype B] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : A ⊕ B → ℕ) (j : ℕ)
variable (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter) (pinA : VA → Option TA) (pinB : VB → Option TB)

end TorsionFreeZeroDivisors.StageEntropy

namespace TorsionFreeZeroDivisors.OccurrenceMatching.Data
open scoped Classical
variable {Ω B B' E : Type*}

variable [Fintype B]
end TorsionFreeZeroDivisors.OccurrenceMatching.Data

namespace TorsionFreeZeroDivisors.StageMass

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0<s) (len m : C → ℕ) (err : ℕ)

variable [Fintype E]

end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks
variable {C E : Type*} [Fintype C] [Fintype E] (s : ℝ) (hs : 0<s) (len m : C → ℕ) (err : ℕ)

end TorsionFreeZeroDivisors.StageMass

namespace TorsionFreeZeroDivisors.BinProfiles
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate

variable {C : Type*} [Fintype C]
end TorsionFreeZeroDivisors.BinProfiles

namespace TorsionFreeZeroDivisors.GridAsymptotics
open Filter Topology
open scoped Classical

end TorsionFreeZeroDivisors.GridAsymptotics

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.RealizationTransport
open scoped Classical
open PortSubdivision ConditionedMatchings PatternEmbeddings
variable {PV PD TV T QV QD : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]
    [Fintype QV] [Fintype QD]
variable {Γ : PortGraph PV PD} {plabel : PD → T} {outgoing : TV → Finset T}
    {pin : PV → Option TV} {bar : T → T} {r : Matching (label outgoing) bar}
    (e : Embedding Γ plabel outgoing pin bar r)

end TorsionFreeZeroDivisors.RealizationTransport

namespace TorsionFreeZeroDivisors.ActualStageRealization
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)
local notation "S" => suppressed Γ mark h2
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)

variable [Fintype V] {TV : Type} [Fintype TV]
    {outgoing : TV → Finset Types.Letter} {pin : V → Option TV}
    {r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) Types.inverse}

end TorsionFreeZeroDivisors.ActualStageRealization

namespace TorsionFreeZeroDivisors.ActualStageFeasibility
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate

variable {C : Type*} [Fintype C] (s : ℝ) (len : C → ℕ)

variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "m" => ChunkComparisons.multiplicity (ChainChunkTransport.color Γ mark h2 paths)

variable {E : Type*}
    (cmp : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (lo hi : E → ℤ) (hlo : ∀ e,cmp.lo e=(lo e:ℝ)) (hhi : ∀ e,cmp.hi e=(hi e:ℝ))

end TorsionFreeZeroDivisors.ActualStageFeasibility

namespace TorsionFreeZeroDivisors.StagePartition
open scoped Classical BigOperators
open RepeatedBlocks BlockAlignment ComparedBlocks WordEstimate
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C E VA VB TA TB : Type} [Fintype C] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : C → ℕ) (side : C → Bool) (j : ℕ)

variable (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter) (pinA : VA → Option TA) (pinB : VB → Option TB)

end TorsionFreeZeroDivisors.StagePartition

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PartitionEntropy
open scoped Classical BigOperators
open StageEntropy BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate StagePartition
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C E VA VB TA TB : Type} [Fintype C] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : C → ℕ) (side : C → Bool) (j : ℕ)
variable (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter) (pinA : VA → Option TA) (pinB : VB → Option TB)

end TorsionFreeZeroDivisors.PartitionEntropy

namespace TorsionFreeZeroDivisors.SideRestriction
open scoped Classical
open PortSubdivision
variable {V D : Type*} (Γ : PortGraph V D) (side : V → Bool)
    (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d)) (b : Bool)

variable {QV QD : Type*} (Q : PortGraph QV QD) (fv : QV ↪ V) (fd : QD ↪ D)
    (ho : ∀ d,fv (Q.origin d)=Γ.origin (fd d))
    (hr : ∀ d,fd (Q.reverse d)=Γ.reverse (fd d))
    (hf : ∀ v,side (fv v)=b)

variable [Fintype V] [Fintype D] [Fintype QV] [Fintype QD]
    {TV T : Type*} [Fintype TV] [Fintype T]
    (label : D → T) (outgoing : TV → Finset T) (pin : Vertex side b → Option TV)
    (bar : T → T) (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) bar)

end TorsionFreeZeroDivisors.SideRestriction

namespace TorsionFreeZeroDivisors.StageSideEmbedding
open scoped Classical BigOperators
variable {C V : Type*} (len m : C → ℕ) (j : ℕ) (side : C → Bool) (vside : V → Bool)
    (first last : {c // j < m c} → V)
    (hf : ∀ c,vside (first c)=side c.val) (hl : ∀ c,vside (last c)=side c.val) (b : Bool)

variable [Fintype C] [Fintype V]

end TorsionFreeZeroDivisors.StageSideEmbedding

namespace TorsionFreeZeroDivisors.ChainSide
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "S" => suppressed Γ mark h2
local notation "R" => Rep Γ mark h2

variable {P : Type*} [Fintype P]
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)

end TorsionFreeZeroDivisors.ChainSide

namespace TorsionFreeZeroDivisors.ActualSideRealization
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons
variable {V D : Type} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    {P : Type} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ) (b : Bool)
local notation "S" => suppressed Γ mark h2
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)

variable [Fintype V] {TV : Type} [Fintype TV]
    (label : D → Types.Letter) (outgoing : TV → Finset Types.Letter)
    (pin : SideRestriction.Vertex side b → Option TV)
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) Types.inverse)

end TorsionFreeZeroDivisors.ActualSideRealization

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SidePins
open scoped Classical BigOperators
variable {V TA TB : Type*} [Fintype V] (side : V → Bool)

end TorsionFreeZeroDivisors.SidePins

namespace TorsionFreeZeroDivisors.StageRoot
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)

end TorsionFreeZeroDivisors.StageRoot

namespace TorsionFreeZeroDivisors.RootPins
open scoped Classical
variable {V T : Type*}
end TorsionFreeZeroDivisors.RootPins

namespace TorsionFreeZeroDivisors.SidePins
open scoped Classical
variable {V : Type*} (side : V → Bool)
end TorsionFreeZeroDivisors.SidePins

namespace TorsionFreeZeroDivisors.StageRoot
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D P : Type} [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
local notation "S" => suppressed Γ mark h2

variable (side : V → Bool)

end TorsionFreeZeroDivisors.StageRoot

namespace TorsionFreeZeroDivisors.ActualStagePair
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking
open ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2

variable {E : Type}

end TorsionFreeZeroDivisors.ActualStagePair

namespace TorsionFreeZeroDivisors.ActualPatternEvent
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking
open ComparedBlocks RepeatedBlocks

variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2

variable [Fintype E]

end TorsionFreeZeroDivisors.ActualPatternEvent

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.RawDecomposition
open scoped Classical BigOperators
open PortSubdivision DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open GirthAsymptotics TypedGraphs
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (raw : P → List D) (hp : ∀ p,raw p≠[])
    (hc : ∀ p,(raw p).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))

end TorsionFreeZeroDivisors.RawDecomposition

namespace TorsionFreeZeroDivisors.ComparisonGeometry

section
open scoped Classical
open ComparedBlocks ChunkComparisons
variable {P E : Type} {l l' : P → ℕ}

variable [Fintype P]
end
open scoped Classical
open ComparedBlocks ChunkComparisons
variable {P E : Type} {l l' : P → ℕ}
end TorsionFreeZeroDivisors.ComparisonGeometry

namespace TorsionFreeZeroDivisors.RawSourcePattern

section
open scoped Classical BigOperators
open PortSubdivision DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open GirthAsymptotics TypedGraphs ActualPatternEvent

namespace Data
variable {B K I rep : ℕ}

end Data
end
open scoped Classical
open GirthAsymptotics TypedGraphs ActualPatternEvent Filter

end TorsionFreeZeroDivisors.RawSourcePattern
namespace TorsionFreeZeroDivisors.DiameterCounting
open scoped BigOperators Classical
open ConditionedMatchings
variable {V D T : Type*} [Fintype V] [Fintype D]
variable (origin : D → V)

def ports (S : Finset V) : Finset D := Finset.univ.filter (fun e => origin e ∈ S)

omit [Fintype V] in
@[simp] lemma mem_ports (S : Finset V) (e : D) : e ∈ ports origin S ↔ origin e ∈ S := by
  simp [ports]

omit [Fintype V] in
lemma card_ports (S : Finset V) :
    (ports origin S).card = ∑ v ∈ S, Nat.card {e : D // origin e=v} := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := origin) (t := S)]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    congr 1
    ext e
    simp only [Finset.mem_filter,mem_ports,Finset.mem_univ,true_and]
    exact ⟨fun h => h.2,fun h => ⟨h ▸ hv,h⟩⟩
  · intro e he
    exact (mem_ports origin S e).mp he

omit [Fintype V] in
lemma card_ports_le (d : ℕ) (hd : ∀ v, Nat.card {e : D // origin e=v} ≤ d)
    (S : Finset V) : (ports origin S).card ≤ S.card*d := by
  rw [card_ports]
  calc
    _ ≤ ∑ _v ∈ S, d := Finset.sum_le_sum fun v _ => hd v
    _ = _ := by simp

omit [Fintype V] in
lemma card_ports_ge (d : ℕ) (hd : ∀ v, d ≤ Nat.card {e : D // origin e=v})
    (S : Finset V) : S.card*d ≤ (ports origin S).card := by
  rw [card_ports]
  calc
    _ = ∑ _v ∈ S, d := by simp
    _ ≤ _ := Finset.sum_le_sum fun v _ => hd v

/-- All potential unordered prescribed matching pairs within a vertex set.
Keeping infeasible ones is a harmless overcount. -/
def possible (S : Finset V) : Finset (Sym2 D) :=
  ((ports origin S) ×ˢ (ports origin S)).image fun p => s(p.1,p.2)

omit [Fintype V] in
lemma mk_mem_possible {S : Finset V} {a b : D}
    (ha : origin a ∈ S) (hb : origin b ∈ S) : s(a,b) ∈ possible origin S := by
  exact Finset.mem_image.mpr ⟨(a,b),by simpa using And.intro ha hb,rfl⟩

omit [Fintype V] in
lemma possible_card (d : ℕ) (hd : ∀ v, Nat.card {e : D // origin e=v} ≤ d)
    (S : Finset V) : (possible origin S).card ≤ (S.card*d)^2 := by
  calc
    _ ≤ ((ports origin S) ×ˢ (ports origin S)).card := Finset.card_image_le
    _ = (ports origin S).card^2 := by rw [Finset.card_product]; ring
    _ ≤ _ := Nat.pow_le_pow_left (card_ports_le origin d hd S) _

variable {label : D → T} {bar : T → T}

def closedNeighbors (r : Matching label bar) (S : Finset V) : Finset V :=
  S ∪ (ports origin S).image (fun e => origin (r e))

def incidentEdges (r : Matching label bar) (S : Finset V) : Finset (Sym2 D) :=
  (ports origin S).image (fun e => s(e,r e))

omit [Fintype V] in
lemma incident_possible (r : Matching label bar) (S U : Finset V)
    (hU : closedNeighbors origin r S ⊆ U) : incidentEdges origin r S ⊆ possible origin U := by
  intro p hp
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
  have hs : origin e ∈ S := (mem_ports origin S e).mp he
  apply mk_mem_possible origin
  · exact hU (Finset.mem_union_left _ hs)
  · exact hU (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he))

omit [Fintype V] in
lemma contains_incident (r : Matching label bar) (S : Finset V) :
    r.Contains (incidentEdges origin r S) := by
  intro a b hab
  obtain ⟨e,_,he⟩ := Finset.mem_image.mp hab
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rw [← h1,← h2]
  · rw [← h1,← h2,r.reverse_reverse]

omit [Fintype V] in
lemma twice_incident (r : Matching label bar) (S : Finset V) :
    (ports origin S).card ≤ 2*(incidentEdges origin r S).card := by
  apply Finset.card_le_mul_card_image
  intro p hp
  obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hp
  have hsub : ((ports origin S).filter (fun a => s(a,r a)=s(e,r e))) ⊆ {e,r e} := by
    intro a ha
    have he := (Finset.mem_filter.mp ha).2
    rcases Sym2.eq_iff.mp he with ⟨h,_⟩ | ⟨h,_⟩
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
  have hp : ({e,r e} : Finset D).card ≤ 2 := by
    calc
      _ ≤ ({r e} : Finset D).card+1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  exact (Finset.card_le_card hsub).trans hp

/-- The literal dense set forced by a failure of the required doubling.
It keeps distinct matching prescriptions rather than counting occurrences. -/
theorem dense_witness (r : Matching label bar) (k d₀ : ℕ)
    (hd₀ : ∀ v, d₀ ≤ Nat.card {e : D // origin e=v})
    (hk : 2*k ≤ Fintype.card V) (S : Finset V) (hS : S.card=k)
    (hfail : (closedNeighbors origin r S).card ≤ 2*k) :
    ∃ U : Finset V, U.card=2*k ∧
      ∃ C : Finset (Sym2 D), C ⊆ possible origin U ∧
        C.card=(d₀*k+1)/2 ∧ r.Contains C := by
  obtain ⟨U,hU,hUc⟩ := Finset.exists_superset_card_eq hfail hk
  have he : (d₀*k+1)/2 ≤ (incidentEdges origin r S).card := by
    have h := (card_ports_ge origin d₀ hd₀ S).trans (twice_incident origin r S)
    rw [hS,Nat.mul_comm k d₀] at h
    omega
  obtain ⟨C,hC,hCc⟩ := Finset.exists_subset_card_eq he
  refine ⟨U,hUc,C,hC.trans (incident_possible origin r S U hU),hCc,?_⟩
  intro a b hab
  exact contains_incident origin r S a b (hC hab)

/-- Union of all dense witnesses of a fixed vertex and prescription size. -/
def denseEvent (N m t : ℕ) : Finset (Matching label bar) :=
  (Finset.univ.powersetCard m).biUnion fun U =>
    ((possible origin U).powersetCard t).biUnion fun C =>
      Matching.conditioned (label := label) (bar := bar) origin N C

/-- The exact finite union bound in the girth-conditioned space. The two
binomial factors count sets, avoiding the spurious extra power of k that
would arise if one counted ordered lists of edge prescriptions. -/
theorem dense_count (N m t d R : ℕ) (hbar : ∀ t, bar t ≠ t) (h2 : 2≤d)
    (hd : ∀ v, Nat.card {e : D // origin e=v} ≤ d)
    (hR : ∀ x, R+t+4*d^(2*N+1) ≤ Nat.card {e : D // label e=label x}) :
    (denseEvent (label := label) (bar := bar) origin N m t).card * R^t ≤
      (Fintype.card V).choose m * ((m*d)^2).choose t *
        (Matching.conditioned (label := label) (bar := bar) origin N ∅).card := by
  let Ω := Matching.conditioned (label := label) (bar := bar) origin N ∅
  let Us : Finset (Finset V) := Finset.univ.powersetCard m
  have hU (U : Finset V) (hu : U∈Us) :
      (((possible origin U).powersetCard t).biUnion fun C =>
        Matching.conditioned (label := label) (bar := bar) origin N C).card * R^t ≤
      ((m*d)^2).choose t * Ω.card := by
    have hcU : U.card=m := (Finset.mem_powersetCard.mp hu).2
    calc
      _ ≤ (∑ C ∈ (possible origin U).powersetCard t,
          (Matching.conditioned (label := label) (bar := bar) origin N C).card) * R^t :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ C ∈ (possible origin U).powersetCard t,
          (Matching.conditioned (label := label) (bar := bar) origin N C).card * R^t :=
        Finset.sum_mul _ _ _
      _ ≤ ∑ _C ∈ (possible origin U).powersetCard t, Ω.card := by
        apply Finset.sum_le_sum
        intro C hC
        have hc : C.card=t := (Finset.mem_powersetCard.mp hC).2
        have h := Matching.prescriptions_count (label := label) (bar := bar)
          origin N hbar d h2 hd R C (by intro x; rw [hc]; exact hR x)
        simpa only [hc] using h
      _ = (possible origin U).card.choose t * Ω.card := by simp
      _ ≤ ((m*d)^2).choose t * Ω.card := by
        apply Nat.mul_le_mul_right
        apply Nat.choose_le_choose
        simpa only [hcU] using possible_card origin d hd U
  calc
    _ ≤ (∑ U ∈ Us, (((possible origin U).powersetCard t).biUnion fun C =>
        Matching.conditioned (label := label) (bar := bar) origin N C).card) * R^t :=
      Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ U ∈ Us, (((possible origin U).powersetCard t).biUnion fun C =>
        Matching.conditioned (label := label) (bar := bar) origin N C).card * R^t :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ _U ∈ Us, ((m*d)^2).choose t * Ω.card := Finset.sum_le_sum hU
    _ = _ := by simp [Us,Ω,Nat.mul_assoc]

/-- A failing set in an actual girth-conditioned sample occurs in the counted
union. No labels, vertex names or repeated traversals have been discarded. -/
theorem mem_dense_of_failure (N k d₀ : ℕ) (r : Matching label bar)
    (hr : r∈Matching.conditioned (label := label) (bar := bar) origin N ∅)
    (hd₀ : ∀ v, d₀ ≤ Nat.card {e : D // origin e=v})
    (hk : 2*k ≤ Fintype.card V) (S : Finset V) (hS : S.card=k)
    (hfail : (closedNeighbors origin r S).card ≤ 2*k) :
    r∈denseEvent (label := label) (bar := bar) origin N (2*k) ((d₀*k+1)/2) := by
  obtain ⟨U,hUc,C,hC,hCc,hrC⟩ := dense_witness origin r k d₀ hd₀ hk S hS hfail
  apply Finset.mem_biUnion.mpr
  refine ⟨U,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hUc⟩,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨C,Finset.mem_powersetCard.mpr ⟨hC,hCc⟩,?_⟩
  simp only [Matching.conditioned,Finset.mem_filter,Finset.mem_univ,true_and] at hr ⊢
  exact ⟨hrC,hr.2⟩

end TorsionFreeZeroDivisors.DiameterCounting

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ExpansionDiameter
open scoped Classical BigOperators
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def ball (v : V) (r : ℕ) : Finset V :=
  Finset.univ.filter fun w => G.edist v w  ≤  r

@[simp] lemma mem_ball (v w : V) (r : ℕ) : w∈ball G v r ↔ G.edist v w  ≤  r := by
  simp [ball]

lemma self_mem_ball (v : V) (r : ℕ) : v∈ball G v r := by simp

lemma ball_mono (v : V) {r s : ℕ} (h : r ≤ s) : ball G v r ⊆ ball G v s := by
  intro w hw
  exact (mem_ball G v w s).mpr (((mem_ball G v w r).mp hw).trans (by exact_mod_cast h))

def neighbors (S : Finset V) : Finset V :=
  S ∪ Finset.univ.filter fun w => ∃ v∈S, G.Adj v w

lemma neighbors_ball (v : V) (r : ℕ) : neighbors G (ball G v r) ⊆ ball G v (r+1) := by
  intro w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · exact ball_mono G v (Nat.le_succ r) hw
  · obtain ⟨z,hz,hzw⟩ := (Finset.mem_filter.mp hw).2
    apply (mem_ball G v w (r+1)).mpr
    calc
      G.edist v w  ≤  G.edist v z + G.edist z w := G.edist_triangle
      _  ≤  (r:ℕ∞)+1 := by
        apply add_le_add
        · exact (mem_ball G v z r).mp hz
        · exact (SimpleGraph.edist_eq_one_iff_adj.mpr hzw).le
      _ = _ := by simp

/-- Doubling small sets forces every logarithmic-radius ball above the
expansion threshold, uniformly over all connected components. -/
theorem ball_large (B R : ℕ)
    (hexp : ∀ S : Finset V, S.Nonempty → S.card ≤ B → 2*S.card  ≤  (neighbors G S).card)
    (hR : B<2^R) (v : V) : B<(ball G v R).card := by
  have hstep (r : ℕ) : B<(ball G v r).card ∨ 2^r  ≤  (ball G v r).card := by
    induction r with
    | zero => exact Or.inr (by simpa using Finset.card_pos.mpr ⟨v,self_mem_ball G v 0⟩)
    | succ r ih =>
      have hmono := Finset.card_le_card (ball_mono G v (Nat.le_succ r))
      rcases ih with h | h
      · exact Or.inl (h.trans_le hmono)
      · by_cases ht : B<(ball G v r).card
        · exact Or.inl (ht.trans_le hmono)
        · right
          have hh := (hexp (ball G v r) ⟨v,self_mem_ball G v r⟩ (Nat.le_of_not_gt ht)).trans
            (Finset.card_le_card (neighbors_ball G v r))
          calc
            2^(r+1) = 2*2^r := by rw [pow_succ,Nat.mul_comm]
            _  ≤  2*(ball G v r).card := Nat.mul_le_mul_left _ h
            _  ≤  _ := hh
  rcases hstep R with h | h
  · exact h
  · exact hR.trans_le h

omit [Fintype V] in
lemma shortest_prefix {u v : V} (p : G.Walk u v)
    (hp : p.length=G.dist u v) (i : ℕ) (hi : i ≤ p.length) :
    G.edist u (p.getVert i) = i := by
  have hd := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
  have hdi : G.dist u (p.getVert i)=i := by
    rw [← hd,SimpleGraph.Walk.take_length,inf_eq_left.mpr hi]
  rw [← (p.take i).reachable.coe_dist_eq_edist,hdi]

lemma spaced_balls_disjoint {u v : V} (p : G.Walk u v)
    (hp : p.length=G.dist u v) (R i j : ℕ) (hij : i<j)
    (hj : j*(2*R+1) ≤ p.length) :
    Disjoint (ball G (p.getVert (i*(2*R+1))) R)
      (ball G (p.getVert (j*(2*R+1))) R) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have hi : i*(2*R+1) ≤ p.length :=
    (Nat.mul_le_mul_right _ (Nat.le_of_lt hij)).trans hj
  have hzz : G.edist (p.getVert (i*(2*R+1))) (p.getVert (j*(2*R+1)))  ≤  (2*R:ℕ) := by
    calc
      _  ≤  G.edist (p.getVert (i*(2*R+1))) z +
          G.edist z (p.getVert (j*(2*R+1))) := G.edist_triangle
      _  ≤  (R:ℕ∞)+R := add_le_add ((mem_ball G _ _ _).mp hz)
        (by rw [G.edist_comm]; exact (mem_ball G _ _ _).mp hz')
      _ = _ := by push_cast; ring
  have htri := G.edist_triangle (u:=u) (v:=p.getVert (i*(2*R+1)))
    (w:=p.getVert (j*(2*R+1)))
  rw [shortest_prefix G p hp _ hi,shortest_prefix G p hp _ hj] at htri
  have hle := htri.trans (add_le_add le_rfl hzz)
  have hle' : j*(2*R+1) ≤ i*(2*R+1)+2*R := by exact_mod_cast hle
  have hgap := Nat.mul_le_mul_right (2*R+1) (Nat.succ_le_of_lt hij)
  rw [Nat.succ_mul] at hgap
  omega

/-- Quantitative packing: a shortest walk carries disjoint large balls at
uniformly spaced centers. -/
theorem diameter_bound (B R : ℕ)
    (hexp : ∀ S : Finset V, S.Nonempty → S.card ≤ B → 2*S.card  ≤  (neighbors G S).card)
    (hR : B<2^R) {u v : V} (huv : G.Reachable u v) :
    G.dist u v < (Fintype.card V/(B+1)+1)*(2*R+1) := by
  obtain ⟨p,hp⟩ := huv.exists_walk_length_eq_dist
  let step := 2*R+1
  let q := p.length/step+1
  let centers (i : Fin q) := p.getVert (i.val*step)
  have hpos : 0<step := by dsimp [step]; omega
  have hcenter (i : Fin q) : i.val*step ≤ p.length := by
    have hi : i.val ≤ p.length/step := by have := i.isLt; dsimp [q] at this; omega
    exact (Nat.mul_le_mul_right _ hi).trans (Nat.div_mul_le_self _ _)
  have hdis : (↑(Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint (fun i => ball G (centers i) R) := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
    · exact spaced_balls_disjoint G p hp R i.val j.val hlt (hcenter j)
    · exact (spaced_balls_disjoint G p hp R j.val i.val hlt (hcenter i)).symm
  have hpack : q*(B+1)  ≤  Fintype.card V := by
    calc
      _ = ∑ _i : Fin q, (B+1) := by simp
      _  ≤  ∑ i : Fin q, (ball G (centers i) R).card := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.succ_le_of_lt (ball_large G B R hexp hR (centers i))
      _ = (Finset.univ.biUnion (fun i : Fin q => ball G (centers i) R)).card :=
        (Finset.card_biUnion hdis).symm
      _  ≤  Fintype.card V := Finset.card_le_univ _
  have hq : q ≤ Fintype.card V/(B+1) := (Nat.le_div_iff_mul_le (by omega)).mpr hpack
  have hpq : p.length < q*step := by
    dsimp [q]
    simpa [Nat.mul_comm] using Nat.lt_mul_div_succ p.length hpos
  rw [← hp]
  exact hpq.trans_le (Nat.mul_le_mul_right _ (hq.trans (Nat.le_succ _)))

end TorsionFreeZeroDivisors.ExpansionDiameter

/-! Quantitative probability estimates for dense witnesses in conditioned
matchings. -/
namespace TorsionFreeZeroDivisors.DiameterProbability
open scoped BigOperators Topology Classical
open Filter

lemma choose_bound (n r : ℕ) (hr : 0<r) :
    (n.choose r : ℝ) ≤ (3*n/r)^r := by
  have hr0 : (0:ℝ)<r := by exact_mod_cast hr
  have hpow : (r:ℝ)^r/(r.factorial:ℝ) ≤ Real.exp (r:ℝ) :=
    Real.pow_div_factorial_le_exp _ (le_of_lt hr0) _
  have he : Real.exp (r:ℝ) ≤ (3:ℝ)^r := by
    rw [show (r:ℝ)=(r:ℝ)*1 by ring,Real.exp_nat_mul]
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1))
      (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) r
  calc
    (n.choose r : ℝ) ≤ (n:ℝ)^r/(r.factorial:ℝ) := Nat.choose_le_pow_div _ _
    _ = ((n:ℝ)/r)^r * ((r:ℝ)^r/(r.factorial:ℝ)) := by
      rw [div_pow]
      field_simp
    _ ≤ ((n:ℝ)/r)^r * (3:ℝ)^r :=
      mul_le_mul_of_nonneg_left (hpow.trans he) (by positivity)
    _ = (3*n/r)^r := by rw [← mul_pow]; congr 1; ring

/-- A summable envelope with exponent 62, sufficient to obtain an o(1) event. -/
lemma witness_envelope (n k r : ℕ) (d p R : ℝ)
    (hk : 0<k) (hn : (k:ℝ) ≤ n) (hd : 1 ≤ d) (hp : 0<p) (hp1 : p ≤ 1) (hR : p*n ≤ R)
    (hr₁ : 64*k ≤ r) (hr₂ : r ≤ 65*k) (hm : ℕ) (hhm : (hm:ℝ) ≤ (2*k*d)^2) :
    (n.choose (2*k):ℝ)*(hm.choose r:ℝ)/R^r ≤
      (9*(12*d^2/p)^65*((k:ℝ)/n)^62)^k := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  have hn0 : (0:ℝ)<n := hk0.trans_le hn
  have hR0 : (0:ℝ)<R := (mul_pos hp hn0).trans_le hR
  have hr0 : 0<r := by omega
  have hr0' : (0:ℝ)<r := by exact_mod_cast hr0
  have hkr : (k:ℝ) ≤ r := by exact_mod_cast (show k ≤ r by omega)
  have ha : (0:ℝ) ≤ 3*n/(2*k) := by positivity
  have hb : (0:ℝ) ≤ 12*d^2*k/(p*n) := by positivity
  have hc : (0:ℝ) ≤ (hm.choose r:ℝ) := by positivity
  have hterm : (n.choose (2*k):ℝ)*(hm.choose r:ℝ)/R^r ≤
      (3*n/(2*k))^(2*k)*(12*d^2*k/(p*n))^r := by
    calc
      _ ≤ (3*n/(2*k))^(2*k) * (3*hm/r)^r / R^r := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul (by simpa using choose_bound n (2*k) (by omega))
          (choose_bound hm r hr0) hc (by positivity)
      _ = (3*n/(2*k))^(2*k) * (3*hm/r/R)^r := by rw [div_pow]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        apply (div_le_iff₀ hR0).mpr
        have hh : 3*(hm:ℝ)/r ≤ 12*d^2*k := by
          apply (div_le_iff₀ hr0').mpr
          have hkk := mul_le_mul_of_nonneg_left hkr (show 0 ≤ 12*d^2*k by positivity)
          nlinarith
        calc
          _ ≤ 12*d^2*k := hh
          _ = (12*d^2*k/(p*n))*(p*n) := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hR hb
  -- Keep constants independent of n,k and use 64k≤r≤65k.
  have ht : 0 ≤ (k:ℝ)/n := by positivity
  have ht1 : (k:ℝ)/n ≤ 1 := (div_le_one hn0).mpr hn
  have hC : 1 ≤ 12*d^2/p := (le_div_iff₀ hp).mpr (by nlinarith [sq_nonneg d])
  have hbase : (12*d^2*k/(p*n))^r ≤ (12*d^2/p)^(65*k)*((k:ℝ)/n)^(64*k) := by
    rw [show 12*d^2*k/(p*n)=(12*d^2/p)*((k:ℝ)/n) by ring,mul_pow]
    apply mul_le_mul
    · exact pow_le_pow_right₀ hC hr₂
    · exact pow_le_pow_of_le_one ht ht1 hr₁
    · positivity
    · positivity
  calc
    _ ≤ (3*n/(2*k))^(2*k)*((12*d^2/p)^(65*k)*((k:ℝ)/n)^(64*k)) :=
      hterm.trans (mul_le_mul_of_nonneg_left hbase (by positivity))
    _ ≤ (3*n/k)^(2*k)*((12*d^2/p)^(65*k)*((k:ℝ)/n)^(64*k)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      apply div_le_div_of_nonneg_left (by positivity) hk0
      nlinarith
    _ = _ := by
      rw [pow_mul,pow_mul,pow_mul,← mul_pow,← mul_pow]
      congr 1
      rw [show (64:ℕ)=2+62 by norm_num,pow_add]
      have hi : (3*(n:ℝ)/k)^2*((k:ℝ)/n)^2=9 := by
        rw [← mul_pow]
        have he : (3*(n:ℝ)/k)*((k:ℝ)/n)=3 := by
          field_simp
        rw [he]
        norm_num
      calc
        _ = ((3*(n:ℝ)/k)^2*((k:ℝ)/n)^2)*
            ((12*d^2/p)^65*((k:ℝ)/n)^62) := by ring
        _ = _ := by rw [hi]; ring

noncomputable def witnessTerm (C ρ : ℝ) (n k : ℕ) : ℝ :=
  if 0<k ∧ (k:ℝ) ≤ ρ*n then (C*((k:ℝ)/n)^62)^k else 0

lemma witnessTerm_nonneg {C ρ : ℝ} (hC : 0 ≤ C) (n k : ℕ) :
    0 ≤ witnessTerm C ρ n k := by
  unfold witnessTerm
  split_ifs <;> positivity

lemma witnessTerm_majorant {C ρ : ℝ} (hC : 0 ≤ C)
    (hsmall : C*ρ^62 ≤ 1/2) (n k : ℕ) (hn : 0<n) :
    ‖witnessTerm C ρ n k‖ ≤ (1/2:ℝ)^k := by
  rw [Real.norm_eq_abs,abs_of_nonneg (witnessTerm_nonneg hC n k)]
  unfold witnessTerm
  split_ifs with h
  · apply pow_le_pow_left₀ (by positivity)
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have ht : (k:ℝ)/n ≤ ρ := (div_le_iff₀ hn0).mpr h.2
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) ht 62) hC).trans hsmall
  · positivity

lemma witnessTerm_tendsto {C ρ : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    Tendsto (fun n : ℕ => witnessTerm C ρ n k) atTop (𝓝 0) := by
  by_cases hk : k=0
  · subst k
    simp [witnessTerm]
  · have ht : Tendsto (fun n : ℕ => (k:ℝ)/n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R:=ℝ))
    have ht' : Tendsto (fun n : ℕ => (C*((k:ℝ)/n)^62)^k) atTop (𝓝 0) := by
      simpa [hk] using ((ht.pow 62).const_mul C).pow k
    apply squeeze_zero (witnessTerm_nonneg hC · k) _ ht'
    intro n
    unfold witnessTerm
    split_ifs
    · exact le_rfl
    · positivity

/-- The full varying-size union bound tends to zero by dominated convergence. -/
theorem witness_sum_tendsto {C ρ : ℝ} (hC : 0 ≤ C)
    (hsmall : C*ρ^62 ≤ 1/2) :
    Tendsto (fun n : ℕ => ∑' k : ℕ, witnessTerm C ρ n k) atTop (𝓝 0) := by
  have hsum : Summable (fun k : ℕ => (1/2:ℝ)^k) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hh := tendsto_tsum_of_dominated_convergence hsum (witnessTerm_tendsto hC)
    (show ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, ‖witnessTerm C ρ n k‖ ≤ (1/2:ℝ)^k from by
      filter_upwards [eventually_gt_atTop 0] with n hn k
      exact witnessTerm_majorant hC hsmall n k hn)
  simpa using hh

end TorsionFreeZeroDivisors.DiameterProbability

namespace TorsionFreeZeroDivisors.MatchingDiameter
open scoped Classical BigOperators
open ConditionedMatchings DiameterCounting
variable {V D T : Type*} [Fintype V] [Fintype D]
variable (origin : D → V) {label : D → T} {bar : T → T}

lemma neighbors_eq (r : Matching label bar) (S : Finset V) :
    ExpansionDiameter.neighbors (simpleGraph origin r) S = closedNeighbors origin r S := by
  ext v
  simp only [ExpansionDiameter.neighbors,closedNeighbors,Finset.mem_union,
    Finset.mem_image,mem_ports,Finset.mem_filter,Finset.mem_univ,true_and]
  change (v ∈ S ∨ ∃ w ∈ S, w ≠ v ∧ ∃ e, origin e = w ∧ origin (r e) = v) ↔ _
  constructor
  · rintro (h | ⟨w,hw,_,e,he,hef⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e,he ▸ hw,hef⟩
  · rintro (h | ⟨e,he,hef⟩)
    · exact Or.inl h
    · by_cases h : origin e=v
      · exact Or.inl (h ▸ he)
      · exact Or.inr ⟨origin e,he,h,e,rfl,hef⟩

def Expands (B : ℕ) (r : Matching label bar) : Prop :=
  ∀ S : Finset V, S.Nonempty → S.card ≤ B → 2*S.card ≤ (closedNeighbors origin r S).card

def failure (B N : ℕ) : Finset (Matching label bar) :=
  (Matching.conditioned (label:=label) (bar:=bar) origin N ∅).filter (fun r => ¬Expands origin B r)

theorem failure_subset_dense (B N : ℕ) (hd : ∀ v, 129 ≤ Nat.card {e : D // origin e=v})
    (hB : 2*B ≤ Fintype.card V) :
    failure (label:=label) (bar:=bar) origin B N ⊆
      (Finset.Icc 1 B).biUnion (fun k => denseEvent (label:=label) (bar:=bar) origin N
        (2*k) ((129*k+1)/2)) := by
  intro r hr
  obtain ⟨hr,hf⟩ := Finset.mem_filter.mp hr
  simp only [Expands,not_forall,not_le] at hf
  obtain ⟨S,hS,hSB,hfail⟩ := hf
  apply Finset.mem_biUnion.mpr
  refine ⟨S.card,Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr hS,hSB⟩,?_⟩
  exact mem_dense_of_failure origin N S.card 129 r hr hd
    ((Nat.mul_le_mul_left 2 hSB).trans hB) S rfl (le_of_lt hfail)

lemma r_bounds (k : ℕ) (hk : 0<k) :
    64*k ≤ (129*k+1)/2 ∧ (129*k+1)/2 ≤ 65*k := by omega

/-- A failure of doubling in the actual conditioned port graph is bounded
by the summable analytic witness envelope. -/
theorem failure_probability_bound (B N d R : ℕ) (p ρ : ℝ)
    (hbar : ∀ t, bar t ≠ t) (hd2 : 2 ≤ d)
    (hd₀ : ∀ v, 129 ≤ Nat.card {e : D // origin e=v})
    (hd : ∀ v, Nat.card {e : D // origin e=v} ≤ d)
    (hB : 2*B ≤ Fintype.card V) (hBρ : (B:ℝ) ≤ ρ*Fintype.card V)
    (hp : 0<p) (hp1 : p ≤ 1) (hρ : ρ ≤ 1)
    (hRreal : p*Fintype.card V ≤ R) (hR0 : 0<R)
    (hR : ∀ x, R+65*B+4*d^(2*N+1) ≤ Nat.card {e : D // label e=label x})
    (hΩ : (Matching.conditioned (label:=label) (bar:=bar) origin N ∅).Nonempty)
    (hsum : Summable (fun k : ℕ => DiameterProbability.witnessTerm
      (9*(12*(d:ℝ)^2/p)^65) ρ (Fintype.card V) k)) :
    (failure (label:=label) (bar:=bar) origin B N).card /
      ((Matching.conditioned (label:=label) (bar:=bar) origin N ∅).card:ℝ) ≤
      ∑' k : ℕ, DiameterProbability.witnessTerm
        (9*(12*(d:ℝ)^2/p)^65) ρ (Fintype.card V) k := by
  let Ω := Matching.conditioned (label:=label) (bar:=bar) origin N ∅
  let event := fun k => denseEvent (label:=label) (bar:=bar) origin N (2*k) ((129*k+1)/2)
  have hΩ0 : (0:ℝ)<Ω.card := by exact_mod_cast Finset.card_pos.mpr hΩ
  have hR0' : (0:ℝ)<R := by exact_mod_cast hR0
  have hkbound (k : ℕ) (hk : k∈Finset.Icc 1 B) :
      (event k).card/(Ω.card:ℝ) ≤ DiameterProbability.witnessTerm
        (9*(12*(d:ℝ)^2/p)^65) ρ (Fintype.card V) k := by
    have hk0 : 0<k := (Finset.mem_Icc.mp hk).1
    have hkB := (Finset.mem_Icc.mp hk).2
    have hkρ : (k:ℝ) ≤ ρ*Fintype.card V :=
      (show (k:ℝ) ≤ B by exact_mod_cast hkB).trans hBρ
    have hkn : (k:ℝ) ≤ Fintype.card V := hkρ.trans (by
      simpa using mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg (Fintype.card V)))
    have hr := r_bounds k hk0
    have hprob := dense_count (label:=label) (bar:=bar) origin N (2*k) ((129*k+1)/2)
      d R hbar hd2 hd (by
        intro x
        have hrr := hr.2.trans (Nat.mul_le_mul_left 65 hkB)
        exact (Nat.add_le_add_right (Nat.add_le_add_left hrr R) _).trans (hR x))
    have hprob' : (event k).card/(Ω.card:ℝ) ≤
        ((Fintype.card V).choose (2*k):ℝ)*((((2*k)*d)^2).choose ((129*k+1)/2):ℝ)/
          (R:ℝ)^((129*k+1)/2) := by
      apply (div_le_div_iff₀ hΩ0 (pow_pos hR0' _)).mpr
      exact_mod_cast hprob
    have hh := DiameterProbability.witness_envelope (Fintype.card V) k ((129*k+1)/2)
      (d:ℝ) p (R:ℝ) hk0 hkn (by exact_mod_cast (show 1 ≤ d by omega)) hp hp1
      hRreal hr.1 hr.2 (((2*k)*d)^2) (by push_cast; rfl)
    unfold DiameterProbability.witnessTerm
    rw [if_pos (show 0 < k ∧ (k:ℝ) ≤ ρ*Fintype.card V from ⟨hk0,hkρ⟩)]
    exact hprob'.trans hh
  calc
    _ ≤ ((Finset.Icc 1 B).biUnion event).card/(Ω.card:ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hΩ0)
      exact_mod_cast Finset.card_le_card (failure_subset_dense origin B N hd₀ hB)
    _ ≤ (∑ k∈Finset.Icc 1 B, (event k).card:ℕ)/(Ω.card:ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hΩ0)
      exact_mod_cast (Finset.card_biUnion_le : ((Finset.Icc 1 B).biUnion event).card ≤ _)
    _ = ∑ k∈Finset.Icc 1 B, (event k).card/(Ω.card:ℝ) := by
      push_cast
      rw [Finset.sum_div]
    _ ≤ ∑ k∈Finset.Icc 1 B, DiameterProbability.witnessTerm
        (9*(12*(d:ℝ)^2/p)^65) ρ (Fintype.card V) k := Finset.sum_le_sum hkbound
    _ ≤ _ := Summable.sum_le_tsum (Finset.Icc 1 B)
      (fun k _ => DiameterProbability.witnessTerm_nonneg (by positivity) _ k) hsum

/-- On the complement of the counted event the diameter conclusion follows
with an explicit bound, including components of disconnected graphs. -/
theorem diameter_of_not_failure (B N R : ℕ) (r : Matching label bar)
    (hr : r∈Matching.conditioned (label:=label) (bar:=bar) origin N ∅)
    (hf : r∉failure (label:=label) (bar:=bar) origin B N) (hR : B<2^R)
    {u v : V} (huv : (simpleGraph origin r).Reachable u v) :
    (simpleGraph origin r).dist u v < (Fintype.card V/(B+1)+1)*(2*R+1) := by
  have hexp : Expands origin B r := by
    by_contra h
    exact hf (Finset.mem_filter.mpr ⟨hr,h⟩)
  apply ExpansionDiameter.diameter_bound _ B R _ hR huv
  intro S hs hSB
  rw [neighbors_eq]
  exact hexp S hs hSB

end TorsionFreeZeroDivisors.MatchingDiameter

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypedDiameter
open Filter ConditionedMatchings MatchingDiameter DiameterProbability
open GirthAsymptotics TypedGraphs TorsionFreeZeroDivisors.Types
open scoped Topology Classical BigOperators

def B (n : ℕ) : ℕ := ⌊ρ*n⌋₊
def R (rep : ℕ) : ℕ := 2130177*rep

theorem p₀_pos : 0<p₀ := by norm_num [p₀]
theorem p₀_le_one : p₀ ≤ 1 := by norm_num [p₀]
theorem C₀_pos : 0<C₀ := by unfold C₀; have := p₀_pos; positivity

theorem ρ_pos : 0<ρ := by
  unfold ρ
  exact lt_min (by norm_num) (lt_min (div_pos p₀_pos (by norm_num))
    (div_pos (by norm_num) (by have := C₀_pos; positivity)))

theorem ρ_le_quarter : ρ ≤ 1/4 := min_le_left _ _
theorem ρ_le_one : ρ ≤ 1 := ρ_le_quarter.trans (by norm_num)
theorem ρ_small : C₀*ρ^62 ≤ 1/2 := by
  have hle : ρ ≤ 1/(2*C₀+2) := (min_le_right _ _).trans (min_le_right _ _)
  have hmul : C₀*ρ ≤ 1/2 := by
    have hx := (le_div_iff₀ (show 0<2*C₀+2 by have := C₀_pos; positivity)).mp hle
    have := ρ_pos
    nlinarith
  have hpow : ρ^62 ≤ ρ := by
    simpa only [pow_one] using (pow_le_pow_of_le_one (le_of_lt ρ_pos) ρ_le_one (by norm_num : 1 ≤ 62))
  exact (mul_le_mul_of_nonneg_left hpow (le_of_lt C₀_pos)).trans hmul

theorem B_le (n : ℕ) : (B n:ℝ) ≤ ρ*n := Nat.floor_le (by have := ρ_pos; positivity)

theorem twice_B_le (n : ℕ) : 2*B n ≤ n := by
  have h := B_le n
  have hg := mul_le_mul_of_nonneg_right ρ_le_quarter (Nat.cast_nonneg n)
  have : (2:ℝ)*B n ≤ n := by linarith
  exact_mod_cast this

theorem sixtyfive_B_le (n : ℕ) : (65*B n:ℝ) ≤ p₀*n := by
  have hρ : ρ ≤ p₀/65 := (min_le_right _ _).trans (min_le_left _ _)
  have h := B_le n
  have hg := mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg n)
  linarith

theorem R_eq (rep : ℕ) : (R rep:ℝ) = 2*p₀*size rep := by
  unfold R p₀ size
  push_cast
  ring

theorem carrier_eq (rep : ℕ) : (4260354*rep:ℝ) = 4*p₀*size rep := by
  unfold p₀ size
  push_cast
  ring

theorem eventual_denom : ∀ᶠ rep : ℕ in atTop,
    R rep+65*B (size rep)+4*132^(2*(3*L (size rep))+1) ≤ 4260354*rep := by
  filter_upwards [size_tendsto.eventually (eventual_small p₀ p₀_pos)] with rep h
  have he : (4*132^(2*(3*L (size rep))+1):ℝ) < p₀*size rep := by
    simpa only [exclusion,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
      show 2*(3*L (size rep))=6*L (size rep) by omega] using h
  have hr := R_eq rep
  have hc := carrier_eq rep
  have hb := sixtyfive_B_le (size rep)
  have hh : (R rep:ℝ)+65*B (size rep)+4*132^(2*(3*L (size rep))+1) ≤
      4260354*rep := by linarith
  exact_mod_cast hh

theorem witness_summable (n : ℕ) (hn : 0<n) :
    Summable (fun k : ℕ => witnessTerm C₀ ρ n k) := by
  apply Summable.of_norm_bounded (summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1))
  intro k
  exact witnessTerm_majorant (le_of_lt C₀_pos) ρ_small n k hn

def badA (rep : ℕ) := failure
  (label:=TypedGraphs.label (@outgoingA rep)) (bar:=inverse)
  (TypedGraphs.origin (@outgoingA rep)) (B (size rep)) (3*L (size rep))
def badB (rep : ℕ) := failure
  (label:=TypedGraphs.label (@outgoingB rep)) (bar:=inverse)
  (TypedGraphs.origin (@outgoingB rep)) (B (size rep)) (3*L (size rep))

/-- Instantiation retains the actual vertex types, degree range, letter
carriers and prescribed girth conditioning. -/
theorem typed_bound {V : Type*} [Fintype V] (outgoing : V → Finset Letter)
    (rep : ℕ) (hrep : 0<rep) (hc : Fintype.card V=size rep)
    (hd : ∀ v, 129 ≤ (outgoing v).card ∧ (outgoing v).card ≤ 132)
    (hl : ∀ t, Fintype.card {v : V // t∈outgoing v}=4260354*rep)
    (hden : R rep+65*B (size rep)+4*132^(2*(3*L (size rep))+1) ≤ 4260354*rep)
    (hΩ : (Matching.conditioned (label:=TypedGraphs.label outgoing) (bar:=inverse)
      (TypedGraphs.origin outgoing) (3*L (size rep)) ∅).Nonempty) :
    (failure (label:=TypedGraphs.label outgoing) (bar:=inverse)
      (TypedGraphs.origin outgoing) (B (size rep)) (3*L (size rep))).card /
      ((Matching.conditioned (label:=TypedGraphs.label outgoing) (bar:=inverse)
        (TypedGraphs.origin outgoing) (3*L (size rep)) ∅).card:ℝ) ≤
      ∑' k : ℕ, witnessTerm C₀ ρ (size rep) k := by
  have hn : 0<size rep := by unfold size; positivity
  have hh := failure_probability_bound (TypedGraphs.origin outgoing)
    (B (size rep)) (3*L (size rep)) 132 (R rep) p₀ ρ
    inverse_ne (by norm_num)
    (fun v => by rw [origin_card]; exact (hd v).1)
    (fun v => by rw [origin_card]; exact (hd v).2)
    (by rw [hc]; exact twice_B_le _)
    (by rw [hc]; exact B_le _)
    p₀_pos p₀_le_one ρ_le_one
    (by rw [hc,R_eq]; have := p₀_pos; nlinarith [Nat.cast_nonneg (α:=ℝ) (size rep)])
    (by unfold R; positivity)
    (fun x => by rw [label_card,hl]; exact hden)
    hΩ (by rw [hc]; exact witness_summable _ hn)
  simpa only [hc,C₀,Nat.cast_ofNat] using hh

theorem eventual_bound : ∀ᶠ rep : ℕ in atTop,
    (badA rep).card/((ΩA rep).card:ℝ) ≤ ∑' k : ℕ, witnessTerm C₀ ρ (size rep) k ∧
    (badB rep).card/((ΩB rep).card:ℝ) ≤ ∑' k : ℕ, witnessTerm C₀ ρ (size rep) k := by
  filter_upwards [eventual_denom,eventual_nonempty,eventually_gt_atTop 0] with rep hd hΩ hr
  exact ⟨typed_bound _ rep hr (card_vertexA rep) degreeA_bounds (letter_frequencyA rep) hd hΩ.1,
    typed_bound _ rep hr (card_vertexB rep) degreeB_bounds (letter_frequencyB rep) hd hΩ.2⟩

theorem failureA_tendsto : Tendsto (fun rep : ℕ => (badA rep).card/((ΩA rep).card:ℝ))
    atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (by intro rep; positivity))
    (eventual_bound.mono (fun _ h => h.1))
  exact (witness_sum_tendsto (le_of_lt C₀_pos) ρ_small).comp size_tendsto

theorem failureB_tendsto : Tendsto (fun rep : ℕ => (badB rep).card/((ΩB rep).card:ℝ))
    atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (by intro rep; positivity))
    (eventual_bound.mono (fun _ h => h.2))
  exact (witness_sum_tendsto (le_of_lt C₀_pos) ρ_small).comp size_tendsto

theorem packing_bound (n : ℕ) : n/(B n+1) ≤ A₀ := by
  have hfloor : ρ*n ≤ (B n:ℝ)+1 := (Nat.lt_floor_add_one (ρ*n)).le
  have hceil : 1/ρ ≤ (A₀:ℝ) := Nat.le_ceil _
  have hi : 1 ≤ ρ*(A₀:ℝ) := by
    have := (div_le_iff₀ ρ_pos).mp hceil
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg (α:=ℝ) n)
  have h2 := mul_le_mul_of_nonneg_right hfloor (Nat.cast_nonneg (α:=ℝ) A₀)
  have h3 : (n:ℝ) ≤ ((B n:ℝ)+1)*A₀ := by nlinarith
  apply Nat.div_le_of_le_mul
  exact_mod_cast h3

theorem log_radius_bound (n : ℕ) (hL : 1 ≤ L n) :
    2*(Nat.log 2 n+1)+1 ≤ 803*L n := by
  have hlog : (Nat.log 2 n:ℝ)*Real.log 2 ≤ Real.log n := by
    have := Real.natLog_le_logb n 2
    rw [Real.logb] at this
    norm_num only [Nat.cast_ofNat] at this
    exact (le_div_iff₀ (by linarith [Real.log_two_gt_d9])).mp this
  have hg := mul_le_mul_of_nonneg_left
    (show (1/2:ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
    (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 n))
  have hl : Real.log n/100 < (L n:ℝ)+1 := Nat.lt_floor_add_one _
  have hL' : (1:ℝ) ≤ L n := by exact_mod_cast hL
  have hr : (Nat.log 2 n:ℝ) ≤ 400*L n := by nlinarith
  have hr' : Nat.log 2 n ≤ 400*L n := by exact_mod_cast hr
  omega

/-- This is the precise fixed-constant O(L) conclusion on the expansion
complement, with no degree or matching independence assumption. -/
theorem component_diameter {V D T : Type*} [Fintype V] [Fintype D]
    (origin : D → V) {label : D → T} {bar : T → T} (n N : ℕ)
    (hc : Fintype.card V=n) (hL : 1 ≤ L n) (r : Matching label bar)
    (hr : r∈Matching.conditioned (label:=label) (bar:=bar) origin N ∅)
    (hf : r∉failure (label:=label) (bar:=bar) origin (B n) N)
    {u v : V} (huv : (simpleGraph origin r).Reachable u v) :
    (simpleGraph origin r).dist u v ≤ D₀*L n := by
  have hpow : B n < 2^(Nat.log 2 n+1) :=
    (show B n ≤ n by have := twice_B_le n; omega).trans_lt
      (Nat.lt_pow_succ_log_self (by norm_num) n)
  have hh := diameter_of_not_failure origin (B n) N (Nat.log 2 n+1) r hr hf hpow huv
  rw [hc] at hh
  have hm := Nat.mul_le_mul (Nat.add_le_add_right (packing_bound n) 1)
    (log_radius_bound n hL)
  unfold D₀
  calc
    _ ≤ (n/(B n+1)+1)*(2*(Nat.log 2 n+1)+1) := hh.le
    _ ≤ (A₀+1)*(803*L n) := hm
    _ = _ := by ring

theorem diameterBadA_subset (rep : ℕ) (hL : 1 ≤ L (size rep)) :
    diameterBadA rep ⊆ badA rep := by
  intro r hr
  obtain ⟨hr,u,v,huv,hlt⟩ := Finset.mem_filter.mp hr
  by_contra hf
  exact (not_lt_of_ge (component_diameter _ _ _ (card_vertexA rep) hL r hr hf huv)) hlt

theorem diameterBadB_subset (rep : ℕ) (hL : 1 ≤ L (size rep)) :
    diameterBadB rep ⊆ badB rep := by
  intro r hr
  obtain ⟨hr,u,v,huv,hlt⟩ := Finset.mem_filter.mp hr
  by_contra hf
  exact (not_lt_of_ge (component_diameter _ _ _ (card_vertexB rep) hL r hr hf huv)) hlt

/-- Diameter bound for the literal A empirical type table. -/
theorem diameterA_tendsto :
    Tendsto (fun rep : ℕ => (diameterBadA rep).card/((ΩA rep).card:ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (by intro rep; positivity)) _ failureA_tendsto
  filter_upwards [(L_tendsto.comp size_tendsto).eventually_ge_atTop 1] with rep hL
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (diameterBadA_subset rep hL)

/-- Diameter bound for the literal B empirical type table. -/
theorem diameterB_tendsto :
    Tendsto (fun rep : ℕ => (diameterBadB rep).card/((ΩB rep).card:ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (by intro rep; positivity)) _ failureB_tendsto
  filter_upwards [(L_tendsto.comp size_tendsto).eventually_ge_atTop 1] with rep hL
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (diameterBadB_subset rep hL)

end TorsionFreeZeroDivisors.TypedDiameter
namespace TorsionFreeZeroDivisors.FiniteJointAvoidance
open scoped Classical
end TorsionFreeZeroDivisors.FiniteJointAvoidance

namespace TorsionFreeZeroDivisors.MatchingAlias
open scoped Classical
end TorsionFreeZeroDivisors.MatchingAlias

namespace TorsionFreeZeroDivisors.GraphSample
open scoped Classical
open GirthAsymptotics TypedGraphs ActualPatternEvent Filter

end TorsionFreeZeroDivisors.GraphSample

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.FiniteClusters
open scoped Classical BigOperators
variable {V : Type} [Fintype V] (G : SimpleGraph V)
local instance : Fintype G.ConnectedComponent := Fintype.ofFinite _

end TorsionFreeZeroDivisors.FiniteClusters

namespace TorsionFreeZeroDivisors.PairingClusters
open scoped Classical BigOperators
variable {O T : Type} [Fintype O] [Fintype T]
    (f : O → T) (α : O → O) (hα : Function.Involutive α) (keep : T → Prop)
end TorsionFreeZeroDivisors.PairingClusters

/-! Arithmetic localization of finite-cluster mass and comparison bounds. -/
namespace TorsionFreeZeroDivisors.PlanarLocalization
open scoped Classical BigOperators

end TorsionFreeZeroDivisors.PlanarLocalization

namespace TorsionFreeZeroDivisors.ClusterLocalization
open scoped Classical BigOperators
open ComparedBlocks
variable {T E : Type} [Fintype T] {len : T → ℕ}
    (C : Comparisons (E:=E) len) (keep : T → Prop)

end TorsionFreeZeroDivisors.ClusterLocalization

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap)
    (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords
namespace TorsionFreeZeroDivisors.SingleException
open scoped Classical BigOperators
variable {T : Type} [Fintype T] (root : Option T) (f : T → ℕ) (L : ℕ)
end TorsionFreeZeroDivisors.SingleException
namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y) (U : ℕ) (hU : 3≤U)
    (hL : 1≤L (size rep)) (hcap : 6≤U*L (size rep))
    (hd : GraphSample.Diameters rep r) (hr : r∈samples rep)
    (hordinary : ∃t,s.root≠some t)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords

/-! Finite rotation systems. The Euler inequality here
is explicitly an input from a planar realization; no PL realization or planar
separator theorem is asserted by this file. The face cycles and bad-gap count,
however, are computed from the actual boundary and pairing permutations. -/
namespace TorsionFreeZeroDivisors.PermutationCycles
open scoped Classical BigOperators
variable {O : Type} [Fintype O] (f : Equiv.Perm O)
instance : Fintype (Cycle f) := Fintype.ofFinite _

end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.PlanarRotation
open scoped Classical BigOperators
open PermutationCycles

variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.PlanarRotation
namespace TorsionFreeZeroDivisors.PlanarRuns
open scoped Classical BigOperators
open PlanarRotation
variable {O : Type}

namespace CutSystem
variable {σ : Equiv.Perm O} (S : CutSystem σ)

namespace Paired
variable {S}
variable {α : Equiv.Perm O} (P : S.Paired α)
include P

end Paired
namespace PairOrbit
variable {A : Type} (r : A→A) (hr : Function.Involutive r)
variable [Fintype A]
end PairOrbit

namespace Paired
variable {S} {α : Equiv.Perm O} (P : S.Paired α)
end Paired

end CutSystem
end TorsionFreeZeroDivisors.PlanarRuns

namespace TorsionFreeZeroDivisors.PlanarIntervals
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks PlanarRuns PlanarRuns.CutSystem
variable {T : Type} {len : T→ℕ} {σ α : Equiv.Perm (Position len)}
    (S : CutSystem σ) (P : S.Paired α)
    (hstep : ∀ x,x∉S.cut → (σ x).1=x.1 ∧ (σ x).2.val=x.2.val+1)

include hstep
end TorsionFreeZeroDivisors.PlanarIntervals
namespace TorsionFreeZeroDivisors.ExtendComparisons
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T E : Type} {len more : T → ℕ} (C : Comparisons (E:=E) len)
    (hle : ∀ t,len t ≤ more t)

variable (hupper : ∀ e,C.hi e≤len (C.source e))

variable [Fintype T]
end TorsionFreeZeroDivisors.ExtendComparisons
namespace TorsionFreeZeroDivisors.WordPositions

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T : Type} (len : T → ℕ)
variable {A : Type} (w : T → List A)

variable (cap : ℕ) (hc : 0<cap)
end
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T : Type} [Fintype T] (len : T → ℕ)
variable {A : Type} (w v : T → List A)
variable {E : Type} (C : Comparisons (E:=E) (fun t=>(w t).length))
end TorsionFreeZeroDivisors.WordPositions

namespace TorsionFreeZeroDivisors.SampleGraph.ClosedWords
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs WeightedMoore BlockAlignment ComparedBlocks
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} (s : PathSystem rep r x y) (cap : ℕ) (hc : 0<cap) (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r) {E : Type} [Fintype E] (lo hi : E → ℕ) (hle : ∀ e,lo e≤hi e)
end TorsionFreeZeroDivisors.SampleGraph.ClosedWords

namespace TorsionFreeZeroDivisors.BoundaryRotation

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T : Type} (len : T → ℕ)
variable [Fintype T]
end

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T A : Type} [Fintype T] (len : T → ℕ) (root : Option T) (label : Position len → A) (bar : A → A) (α : Equiv.Perm (Position len)) (hr : Function.Involutive α) (hcomp : ∀ x,label (α x)=bar (label x))
end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions
variable {T : Type} (len : T → ℕ)
variable {A : Type} (w : T → List A) (R : A → A → Prop)
end TorsionFreeZeroDivisors.BoundaryRotation

namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions BoundaryRotation WeightedMoore ActualPatternEvent GirthAsymptotics
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} (s : PathSystem rep r x y)
end TorsionFreeZeroDivisors.SampleGraph.PathSystem

namespace TorsionFreeZeroDivisors.PermutationTransport
variable {A B : Type} (e : A ≃ B) (f : Equiv.Perm A)
end TorsionFreeZeroDivisors.PermutationTransport

namespace TorsionFreeZeroDivisors.BalancedRotation
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks WordPositions PermutationCycles
variable {T A : Type} [Fintype T] (w : T → List A) (cap : ℕ) (hc : 0<cap)
end TorsionFreeZeroDivisors.BalancedRotation

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
namespace FullPairing
variable {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap)
end FullPairing
end TorsionFreeZeroDivisors.SampleGraph

namespace TorsionFreeZeroDivisors.PermutationTransport
open PermutationCycles
variable {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (f : Equiv.Perm A)
end TorsionFreeZeroDivisors.PermutationTransport

namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing

section
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent PermutationCycles PlanarRotation
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap)
end

open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (cap : ℕ) (hc : 0<cap) (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
end TorsionFreeZeroDivisors.SampleGraph.FullPairing

/-! Recursive separation. This is the actual deletion-set
construction and sharp charging estimate. The one-step Lipton–Tarjan theorem
is kept as an explicit dependency, not asserted from an unspecified planar
predicate.  No claim of a completed planar realization is made here. -/
namespace TorsionFreeZeroDivisors.RecursiveSeparator
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] (R : V → V → Prop)

namespace Split
variable {R} {S : Finset V} (P : Split R S)
end Split

namespace Split
variable {R} {S : Finset V} (P : Split R S) (D : Finset V → Finset V)
end Split

end TorsionFreeZeroDivisors.RecursiveSeparator

namespace TorsionFreeZeroDivisors.PlanarParameters
open scoped Classical
open RecursiveSeparator
variable (ε : ℝ) (D : ℕ)
end TorsionFreeZeroDivisors.PlanarParameters

namespace TorsionFreeZeroDivisors.LocalizationCounts
open scoped Classical BigOperators
open ComparedBlocks BlockAlignment
variable {T E : Type} [Fintype T] {len : T → ℕ} (C : Comparisons (E:=E) len) (keep : T → Prop) (old : T → ℕ)

end TorsionFreeZeroDivisors.LocalizationCounts

namespace TorsionFreeZeroDivisors.SampleGraph.PathSystem
open scoped Classical BigOperators
open GirthAsymptotics ActualPatternEvent TypedGraphs ComparedBlocks
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : PathSystem rep r x y)
local instance : Fintype s.P := s.fP
local instance : Fintype s.E := s.fE

end TorsionFreeZeroDivisors.SampleGraph.PathSystem

namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep} {s : PathSystem rep r x y} (hL : 2≤L (size rep)) (hd : GraphSample.Diameters rep r)
end TorsionFreeZeroDivisors.SampleGraph.FullPairing

namespace TorsionFreeZeroDivisors.PermutationCycles
variable {O B : Type} [Fintype O] (f : Equiv.Perm O)
end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.InsertedRotation
open scoped Classical
open PermutationCycles
variable {O : Type} (σ α : Equiv.Perm O) (p : O)

variable [Fintype O]

end TorsionFreeZeroDivisors.InsertedRotation

namespace TorsionFreeZeroDivisors.SwapCycles

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p q : O)
variable [Fintype O]

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p q : O)

variable [Fintype O]

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p q : O)
end

open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (f : Equiv.Perm O) (p q : O)
end TorsionFreeZeroDivisors.SwapCycles

namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]

end TorsionFreeZeroDivisors.ComponentEuler

namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]
variable (σ α : Equiv.Perm O) (l : List (O×O))
    (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α)
    (he : ∀e∈l,α e.1=e.2)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.ComponentEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O]
end TorsionFreeZeroDivisors.ComponentEuler
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.PairingFactors
open scoped Classical
variable {O : Type} (α : Equiv.Perm O) (hi : Function.Involutive α) (p : O)
end TorsionFreeZeroDivisors.PairingFactors
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.DeleteCycle

section
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p : O)
variable [Fintype O]
end
open scoped Classical
open PermutationCycles
variable {O : Type} (f : Equiv.Perm O) (p : O)
variable [Fintype O]
end TorsionFreeZeroDivisors.DeleteCycle
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
variable {O B : Type} (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.MapDeletion

section
open scoped Classical
open MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p) (hs : σ p≠p)
end
open scoped Classical
open MapEuler PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open PermutationCycles
variable {O A : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)

variable (hs : σ p≠p)
end TorsionFreeZeroDivisors.BandEuler
namespace TorsionFreeZeroDivisors.MapEuler
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
end TorsionFreeZeroDivisors.BandEuler

/-! Actual finite noncrossing word matchings, the cancellation part of the
cone-picture construction. An ear is inserted at two adjacent positions.
This file asserts no sphere realization or asphericity theorem. -/
namespace TorsionFreeZeroDivisors.WordPairing

section
variable {A : Type*} {n : ℕ}

namespace Ear
variable (k : ℕ)

variable {inv : A → A} {label : Fin n → A}
end Ear
end

section
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

namespace Data
end Data

namespace Ear
variable (k : ℕ) (hk : k≤n) (a : A)
end Ear

namespace ListInsert
variable (u v : List A) (a b : A)
end ListInsert

end
variable {A : Type*}
namespace ListInsert
variable (u v : List A) (inv : A → A) (a : A)
end ListInsert

end TorsionFreeZeroDivisors.WordPairing
namespace TorsionFreeZeroDivisors.WordPairing.Ear
open PermutationCycles
variable {A : Type*} {n : ℕ} {inv : A → A} {label : Fin n → A}
variable (k : ℕ) (hk : k≤n) (hn : 0<n)

end TorsionFreeZeroDivisors.WordPairing.Ear

namespace TorsionFreeZeroDivisors.PermutationCycles
variable (O : Type) [Fintype O]
end TorsionFreeZeroDivisors.PermutationCycles

namespace TorsionFreeZeroDivisors.WordPairing

section
open PermutationCycles
variable {A : Type*} {n m : ℕ} {inv : A → A} {label : Fin n → A}

namespace Ear
variable (k : ℕ) (hk : k≤n)
end Ear

namespace ListInsert
variable (u v : List A) (inv : A → A) (a : A)
end ListInsert

end
open scoped Classical
variable {A : Type*} {n : ℕ} {inv : A → A} {label : Fin n → A}
end TorsionFreeZeroDivisors.WordPairing
namespace TorsionFreeZeroDivisors.WordPairing.EraseEar
open scoped Classical
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin (n+2)→A} (k : ℕ) (hk : k≤n)
end TorsionFreeZeroDivisors.WordPairing.EraseEar
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
variable {A : Type*} {inv : A → A}
end TorsionFreeZeroDivisors.WordPairing

namespace TorsionFreeZeroDivisors.MapEuler
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler
namespace TorsionFreeZeroDivisors.WordPairing
open scoped Classical
open MapEuler PermutationCycles
variable {A : Type*} {n : ℕ} {inv : A→A} {label : Fin n→A}
end TorsionFreeZeroDivisors.WordPairing

namespace TorsionFreeZeroDivisors.DeleteCycle
open scoped Classical
variable {O : Type} (σ : Equiv.Perm O) (p : O)
end TorsionFreeZeroDivisors.DeleteCycle
namespace TorsionFreeZeroDivisors.IsolatedDeletion
open scoped Classical
open MapEuler
variable {O : Type} (σ α : Equiv.Perm O) (p : O) (hs : σ p=p) (ha : α p=p)
variable [Fintype O]
end TorsionFreeZeroDivisors.IsolatedDeletion
namespace TorsionFreeZeroDivisors.MapDeletion
open scoped Classical
open MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion

namespace TorsionFreeZeroDivisors.BandEuler
open scoped Classical
open MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (p q : O) (hpq : p≠q) (hpair : α p=q)
end TorsionFreeZeroDivisors.BandEuler
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O)
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.BoundarySurgery
open scoped Classical
variable {O V : Type} [Fintype O] (σ : Equiv.Perm O) (before after : O→V)
variable (p q : O) (hpq : p≠q)
end TorsionFreeZeroDivisors.BoundarySurgery

namespace TorsionFreeZeroDivisors.VertexSplit
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p q : O) (l : List (O×O)) (hl : (l.map (fun e=>Equiv.swap e.1 e.2)).prod=α) (he : ∀e∈l,α e.1=e.2)
local notation "σ'" => Equiv.swap p q*σ
local notation "L'" => (α p,α q)::l
end TorsionFreeZeroDivisors.VertexSplit
namespace TorsionFreeZeroDivisors.MapEuler
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
end TorsionFreeZeroDivisors.MapEuler

namespace TorsionFreeZeroDivisors.MapConjugation
open scoped Classical
open MapEuler PermutationCycles
variable {A B : Type} (e : A ≃ B) (σ α : Equiv.Perm A)
local notation "σ'" => e.permCongr σ
local notation "α'" => e.permCongr α
variable [Fintype A] [Fintype B]
end TorsionFreeZeroDivisors.MapConjugation

/-! The finite matching operation for the same-lifted-edge band surgery.
Deleting two inverse occurrences splices their partners unless they were already
paired. Labels, involutivity and the absence of fixed points are proved from the
actual matching. This file does not assert a surface realization or essentiality.
-/
namespace TorsionFreeZeroDivisors.MatchingSurgery
open scoped Classical
variable {O A : Type*} (α : Equiv.Perm O) (hi : Function.Involutive α)
  (hf : ∀x,α x≠x) (p q : O) (hpq : p≠q)

variable (inv : A→A) (hinv : Function.Involutive inv) (label : O→A)
  (hl : ∀x,label (α x)=inv (label x)) (hlabel : label q=inv (label p))

end TorsionFreeZeroDivisors.MatchingSurgery
namespace TorsionFreeZeroDivisors.Smoothing
open scoped Classical
variable {O : Type} (σ α : Equiv.Perm O)
  (hi : Function.Involutive α) (hf : ∀x,α x≠x)
  (p q : O) (hpq : p≠q) (hsp : σ p=q) (hsq : σ q=p)

variable [Fintype O]

end TorsionFreeZeroDivisors.Smoothing
namespace TorsionFreeZeroDivisors.Tightening
open scoped Classical
open PermutationCycles
variable {O V : Type} (σ : Equiv.Perm O) (p q : O) (hpq : p≠q) (hsp : σ p=q)

variable [Fintype O] (α : Equiv.Perm O) (hi : Function.Involutive α) (hf : ∀x,α x≠x)

variable (before after : O→V)
end TorsionFreeZeroDivisors.Tightening

/-! The finite matching operation for the same-lifted-edge band surgery.
Deleting two inverse occurrences splices their partners unless they were already
paired. Labels, involutivity and the absence of fixed points are proved from the
actual matching. This file does not assert a surface realization or essentiality.
-/
namespace TorsionFreeZeroDivisors.PartialMatchingSurgery
open scoped Classical
variable {O A : Type*} (α : Equiv.Perm O) (hi : Function.Involutive α)
  (p q : O) (hpq : p≠q) (hfp : α p≠p) (hfq : α q≠q)

variable (inv : A→A) (hinv : Function.Involutive inv) (label : O→A)
  (hl : ∀x,label (α x)=inv (label x)) (hlabel : label q=inv (label p))

end TorsionFreeZeroDivisors.PartialMatchingSurgery
namespace TorsionFreeZeroDivisors.PartialSmoothing
open scoped Classical
variable {O : Type} (σ α : Equiv.Perm O)
  (hi : Function.Involutive α)
  (p q : O) (hpq : p≠q) (hfp : α p≠p) (hfq : α q≠q) (hsp : σ p=q) (hsq : σ q=p)

variable [Fintype O]

end TorsionFreeZeroDivisors.PartialSmoothing
namespace TorsionFreeZeroDivisors.Tightening
open scoped Classical
variable {O : Type} [Fintype O] (σ : Equiv.Perm O) (p q : O) (hpq : p≠q) (hsp : σ p=q)
  (α : Equiv.Perm O) (hi : Function.Involutive α) (hfp : α p≠p) (hfq : α q≠q)
end TorsionFreeZeroDivisors.Tightening
namespace TorsionFreeZeroDivisors.FinitePicture
open scoped Classical
open PortSubdivision
variable {V D A O : Type} (Γ : PortGraph V D) (label : D→A) (inv : A→A) (x y : V) [Fintype O]
namespace Data
variable {Γ label inv x y}

variable {O' : Type} [Fintype O']

variable (p q : O) (hpq : p≠q)
end Data
end TorsionFreeZeroDivisors.FinitePicture

namespace TorsionFreeZeroDivisors.PermutationCycles
open scoped Classical BigOperators
variable {O : Type} [Fintype O] (f : Equiv.Perm O)
end TorsionFreeZeroDivisors.PermutationCycles
namespace TorsionFreeZeroDivisors.FinitePicture.Data
open scoped Classical
open MapEuler PermutationCycles
variable {V D A O : Type} [Fintype O] {Γ : PortSubdivision.PortGraph V D} {label : D→A} {inv : A→A} {x y : V}
variable (hxy : x≠y)
end TorsionFreeZeroDivisors.FinitePicture.Data

/-! Exact finite permutation cycles, including singleton cycles, as nonempty
lists with their literal successor. This is the coordinate bridge from marked
picture surgery to boundary words; it asserts no geometric realization. -/

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
variable {A : Type*}
open FreeGroup

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.AlgebraicPictures
open FreeGroup
variable {A I : Type*} (rel : I→List (A×Bool))

end TorsionFreeZeroDivisors.AlgebraicPictures

namespace TorsionFreeZeroDivisors.GraphPresentation
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)

namespace Path
variable {Γ} {a b c : V}
@[simp] lemma eval_nil {G : Type*} [_root_.Group G] (label : D→G) (v : V) :
    (Path.nil (Γ:=Γ) v).eval label=1 := rfl
@[simp] lemma eval_cons {G : Type*} [_root_.Group G] (label : D→G) (d : D)
    (p : Path Γ (Γ.origin (Γ.reverse d)) b) :
    (Path.cons d p).eval label=label d*p.eval label := rfl
@[simp] lemma eval_append {G : Type*} [_root_.Group G] (label : D→G)
    (p : Path Γ a b) (q : Path Γ b c) :
    (p.append q).eval label=p.eval label*q.eval label := by
  induction p with
  | nil v => simp [append]
  | cons d p ih => simp only [append,eval_cons,ih,mul_assoc]
@[simp] lemma eval_single {G : Type*} [_root_.Group G] (label : D→G) (d : D) :
    (single (Γ:=Γ) d).eval label=label d := by simp [single]
@[simp] lemma eval_cast {G : Type*} [_root_.Group G] (label : D→G)
    {a b a' b' : V} (ha : a=a') (hb : b=b') (p : Path Γ a b) :
    (p.cast ha hb).eval label=p.eval label := by
  subst a'; subst b'; rfl

end Path
end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.GraphPresentation.Path
open PortSubdivision
variable {V D : Type} {Γ : PortGraph V D} {a b c : V}
variable {A : Type*} (label : D→A×Bool)

end TorsionFreeZeroDivisors.GraphPresentation.Path
namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
variable {D A : Type*} (label : D→A)

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.MapDeletion
open scoped Classical
open MapEuler PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (p : O) (ha : α p=p)
end TorsionFreeZeroDivisors.MapDeletion
namespace TorsionFreeZeroDivisors.MarkerInsertion
open scoped Classical
variable {O : Type} (σ α : Equiv.Perm O) (p : O)
variable [Fintype O]

end TorsionFreeZeroDivisors.MarkerInsertion
namespace TorsionFreeZeroDivisors.FinitePicture
open scoped Classical
open PortSubdivision
variable {V D A O : Type} [Fintype O] (Γ : PortGraph V D) (label : D→A) (inv : A→A) (x y : V)
  (σ α : Equiv.Perm O) (hi : Function.Involutive α) (hf : ∀i,α i≠i)
  (edge : O→D) (p : O)
  (hc : ∀i,label (edge (α i))=inv (label (edge i)))
  (hj : ∀i,σ i≠p → Γ.origin (Γ.reverse (edge i))=Γ.origin (edge (σ i)))
  (hp : Γ.origin (edge p)=x)
  (he : ∀i,σ i=p → Γ.origin (Γ.reverse (edge i))=y)
  (hz : MapEuler.GenusZero σ α)

end TorsionFreeZeroDivisors.FinitePicture

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GraphPresentation.Path
open PortSubdivision
variable {V D : Type} {Γ : PortGraph V D} {a b : V}

end TorsionFreeZeroDivisors.GraphPresentation.Path
namespace TorsionFreeZeroDivisors.WordBlocks
open scoped Classical
open PortSubdivision GraphPresentation
variable {V D A : Type} (Γ : PortGraph V D) (label : D→A) (inv : A→A)
variable {x y : V} (p : Path Γ x y) (hxy : x≠y) (ws : List (List D))

end TorsionFreeZeroDivisors.WordBlocks
namespace TorsionFreeZeroDivisors.AlgebraicPictures
variable {A I : Type*} (rel : I→List (A×Bool))
open FreeGroup
end TorsionFreeZeroDivisors.AlgebraicPictures
namespace TorsionFreeZeroDivisors.InitialPicture
open scoped Classical
open PortSubdivision GraphPresentation
variable {V D A I : Type} (Γ : PortGraph V D) (label : D→A×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
variable {x y : V} (p : Path Γ x y)

end TorsionFreeZeroDivisors.InitialPicture

namespace TorsionFreeZeroDivisors.GraphPresentation

section
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)

variable {S : Type*} (letters : D→FreeGroup S) (R : Routes Γ)

instance [Finite S] [Finite D] : _root_.Group.IsFinitelyPresented (Group Γ letters R) := by
  have : Finite (relations Γ letters R) := Set.finite_range (relator Γ letters R) |>.to_subtype
  infer_instance

end

open scoped Classical
open PortSubdivision
variable {V D A : Type} (Γ : PortGraph V D) (label : D→A×Bool)
  (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d)) (R : Routes Γ)

end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.FinitePicture.Data
open scoped Classical
variable {V D A B O : Type} [Fintype O] {Γ : PortSubdivision.PortGraph V D} {label : D→A} {inv : A→A} {x y : V} (f : A→B) (label' : D→B) (inv' : B→B) (hl : ∀d,label' d=f (label d)) (hf : ∀t,f (inv t)=inv' (f t))

end TorsionFreeZeroDivisors.FinitePicture.Data
namespace TorsionFreeZeroDivisors.GraphPresentation
open PortSubdivision
open scoped Classical
variable {V D : Type} (Γ : PortGraph V D)
namespace Path
variable {Γ}
end Path

end TorsionFreeZeroDivisors.GraphPresentation
namespace TorsionFreeZeroDivisors.ConcreteGroup

section
open scoped Classical BigOperators
open PortSubdivision TypedGraphs ConditionedMatchings SampleGraph
variable (rep : ℕ) (r : ActualPatternEvent.Match rep)
instance : Group.IsFinitelyPresented (G rep r) := inferInstance
end

open scoped Classical
open SampleGraph
variable {rep : ℕ} (r : ActualPatternEvent.Match rep)

end TorsionFreeZeroDivisors.ConcreteGroup

end

end OAI
end

section
namespace OAI



section
namespace TorsionFreeZeroDivisors.CellNorm
open scoped Classical BigOperators
noncomputable section
variable {H G I : Type} [CommGroup H] [_root_.Group G] [Fintype H]
  (φ : H→*G) (hφ : Function.Injective φ)
@[instance_reducible] def moduleAction : MulAction H (G×I) where
  smul h p := (φ h*p.1,p.2)
  one_smul p := by change (φ 1*p.1,p.2)=p; simp
  mul_smul h k p := by change (φ (h*k)*p.1,p.2)=(φ h*(φ k*p.1),p.2); rw [map_mul,mul_assoc]
end
end TorsionFreeZeroDivisors.CellNorm

end



end OAI
end

open scoped Classical in
open OAI.TorsionFreeZeroDivisors OAI.TorsionFreeZeroDivisors.TypedDiameter Filter Topology in
theorem solution :
    Tendsto (fun rep : ℕ => (diameterBadA rep).card/((ΩA rep).card:ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun rep : ℕ => (diameterBadB rep).card/((ΩB rep).card:ℝ)) atTop (𝓝 0) :=
  ⟨OAI.TorsionFreeZeroDivisors.TypedDiameter.diameterA_tendsto,
    OAI.TorsionFreeZeroDivisors.TypedDiameter.diameterB_tendsto⟩
