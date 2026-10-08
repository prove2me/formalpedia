-- Prove2me | solution 1 for OAI.TorsionFreeZeroDivisors.SampleGraph.exists_avoiding
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T15:19:59.726096+00:00
-- url     : https://prove2.me/submissions/a077e4c9-21fb-46ce-b0d5-ff58c72ed373

import Mathlib
import Definitions.Def_TorsionFreeZeroDivisorsConstruction
import Theorems.Thm_OAI_TorsionFreeZeroDivisors_BoundedPattern_probability_union
import Theorems.Thm_OAI_TorsionFreeZeroDivisors_TypedDiameter_diameter_tendsto
section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.AffineIntervals
open scoped Classical
open BlockAlignment

end TorsionFreeZeroDivisors.AffineIntervals
namespace TorsionFreeZeroDivisors.ChunkComparisons
open scoped Classical
open BlockAlignment ComparedBlocks AffineIntervals EntropyStages

variable {P T E : Type*} {lp : P → ℕ} {lt : T → ℕ}

lemma position_ext {x y : Position lp} (hs : x.1=y.1) (hc : x.2.val=y.2.val) : x=y := by
  rcases x with ⟨x,q⟩; rcases y with ⟨y,r⟩
  dsimp at hs hc
  subst y
  congr 1
  exact Subtype.ext hc

namespace Chunking
variable (C : Comparisons (E := E) lp)

variable (lo hi : E → ℤ)

variable (hlo : ∀ e, C.lo e=(lo e : ℝ)) (hhi : ∀ e, C.hi e=(hi e : ℝ))

end Chunking
end TorsionFreeZeroDivisors.ChunkComparisons

namespace TorsionFreeZeroDivisors.FiniteChunking
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks AffineIntervals ChunkComparisons

variable {n : ℕ}

variable {P : Type*} [Fintype P] (chunks : P → ℕ)
  (len : (p : P) → Fin (chunks p) → ℕ) (rev : (p : P) → Fin (chunks p) → Bool)

end TorsionFreeZeroDivisors.FiniteChunking

end

end OAI
end

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

/-- Expanded length, attached to undirected edges. -/
def weight (w : Sym2 V → ℝ) (p : G.Walk u v) : ℝ := (p.edges.map w).sum

@[simp] theorem weight_nil (w : Sym2 V → ℝ) (u : V) : weight w (G := G) (Walk.nil : G.Walk u u) = 0 := rfl
@[simp] theorem weight_cons (w : Sym2 V → ℝ) {a b c : V} (h : G.Adj a b)
    (p : G.Walk b c) : weight w (Walk.cons h p) = w s(a,b) + weight w p := rfl
@[simp] theorem weight_append (w : Sym2 V → ℝ) {a b c : V}
    (p : G.Walk a b) (q : G.Walk b c) : weight w (p.append q) = weight w p + weight w q := by
  simp [weight]
@[simp] theorem weight_reverse (w : Sym2 V → ℝ) (p : G.Walk u v) :
    weight w p.reverse = weight w p := by simp [weight]

theorem weight_nonneg (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) (p : G.Walk u v) :
    0 ≤ weight w p := by
  induction p with
  | nil => simp
  | cons h p ih => exact add_nonneg (hw _) ih

theorem weight_le_of_subwalk (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {a b : V} {p : G.Walk u v} {q : G.Walk a b} (h : p.IsSubwalk q) :
    weight w p ≤ weight w q := by
  obtain ⟨l,r,rfl⟩ := h
  simp only [weight_append]
  linarith [weight_nonneg w hw l,weight_nonneg w hw r]

/-- A nonbacktracking walk with a repeated vertex contains a cycle of no
greater weight. Zero weights are permitted. -/
theorem reduced_not_path_cycle (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (r : G.Walk u v) (hrr : r.edges.IsChain (· ≠ ·)) (hn : ¬r.IsPath) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ weight w c ≤ weight w r := by
  classical
  induction r with
  | nil => exact False.elim (hn (by simp))
  | @cons a b c h r ih =>
    have hcc := List.isChain_cons.mp (Walk.edges_cons _ _ ▸ hrr)
    by_cases hpath : r.IsPath
    · have hh : a ∈ r.support := by
        by_contra hh
        exact hn (Walk.cons_isPath_iff h r |>.mpr ⟨hpath,hh⟩)
      have hz : 0 < r.length := by
        by_contra hz
        have hrnil := Walk.length_eq_zero_iff.mp (by omega : r.length = 0)
        have he : a = b := by simpa [Walk.nil_iff_support_eq.mp hrnil] using hh
        exact h.ne he
      have hc : (Walk.cons h (r.takeUntil a hh)).IsCycle := by
        simp only [Walk.isCycle_def,Walk.isTrail_def,Walk.edges_cons,List.nodup_cons,
          ne_eq,reduceCtorEq,not_false_eq_true,Walk.support_cons,List.tail_cons,true_and]
        have ht : (Walk.cons h (r.takeUntil a hh)).support.tail.Nodup :=
          r.isPath_def.mp hpath |>.sublist <| List.IsInfix.sublist
            ⟨[],(r.dropUntil a hh).support.tail,by simp [← Walk.support_append]⟩
        refine ⟨⟨?_,Walk.edges_nodup_of_support_nodup ht⟩,ht⟩
        by_contra he
        refine hcc.1 s(a,b) ?_ rfl
        rw [← r.cons_tail_eq (by simp [Walk.not_nil_iff_lt_length,hz])]
        have hh' := Walk.IsPath.mk' ht |>.eq_snd_of_mem_edges (Sym2.eq_swap ▸ he)
        simp [hh',Walk.snd_takeUntil h.ne]
      refine ⟨a,_,hc,?_⟩
      simpa only [weight_cons] using
        (add_le_add (le_refl (w s(a,b))) (weight_le_of_subwalk w hw (r.isSubwalk_takeUntil hh)))
    · obtain ⟨a',c',hc',hle⟩ := ih hcc.2 hpath
      exact ⟨a',c',hc',by rw [weight_cons]; linarith [hw s(a,b)]⟩

/-- Two distinct immersed walks having the same endpoints contain a cycle
whose expanded length is no greater than their combined expanded length. -/
theorem distinct_reduced_cycle (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : G.Walk u v) (hne : p ≠ q)
    (hp : p.edges.IsChain (· ≠ ·)) (hq : q.edges.IsChain (· ≠ ·)) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ weight w c ≤ weight w p + weight w q := by
  classical
  by_cases hpp : p.IsPath
  · by_cases hqq : q.IsPath
    · obtain ⟨a,b,p',q',hsubp,hsubq,hc⟩ := hpp.exists_isCycle_of_ne hqq hne
      exact ⟨a,p'.append q'.reverse,hc,by
        simp only [weight_append,weight_reverse]
        exact add_le_add (weight_le_of_subwalk w hw hsubp) (weight_le_of_subwalk w hw hsubq)⟩
    · obtain ⟨a,c,hc,hle⟩ := reduced_not_path_cycle w hw q hq hqq
      exact ⟨a,c,hc,by linarith [weight_nonneg w hw p]⟩
  · obtain ⟨a,c,hc,hle⟩ := reduced_not_path_cycle w hw p hp hpp
    exact ⟨a,c,hc,by linarith [weight_nonneg w hw q]⟩

end TorsionFreeZeroDivisors.WeightedCycles
namespace TorsionFreeZeroDivisors.WeightedMoore
open scoped BigOperators

instance {D : Type*} [Fintype D] (k : ℕ) : Fintype (Chain D k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype D)
  | succ k ih => exact inferInstanceAs (Fintype (D × Chain D k))

def head {D : Type*} : {k : ℕ} → Chain D k → D
  | 0, p => p
  | _+1, p => p.1

def last {D : Type*} : {k : ℕ} → Chain D k → D
  | 0, p => p
  | _+1, p => last p.2

def cost {D : Type*} (len : D → ℝ) : {k : ℕ} → Chain D k → ℝ
  | 0, p => len p
  | _+1, p => len p.1 + cost len p.2

def mass {D : Type*} [Fintype D] (T : D → D → ℝ) : {k : ℕ} → Chain D k → ℝ
  | 0, _ => 1 / Fintype.card D
  | _+1, p => T p.1 (head p.2) * mass T p.2

variable {D : Type*} [Fintype D] (T : D → D → ℝ)

/-- A doubly stochastic transition rule, with no entry exceeding one half. -/
structure Transition : Prop where
  nonneg : ∀ d e, 0 ≤ T d e
  row_sum : ∀ d, ∑ e, T d e = 1
  col_sum : ∀ e, ∑ d, T d e = 1
  half : ∀ d e, T d e ≤ 1/2

variable {T}

theorem mass_nonneg (ht : Transition T) {k : ℕ} (p : Chain D k) :
    0 ≤ mass T p := by
  induction k with
  | zero => exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  | succ k ih => exact mul_nonneg (ht.nonneg _ _) (ih p.2)

/-- Stationarity of uniform directed-edge measure, proved by finite summation. -/
theorem head_expectation (ht : Transition T) (k : ℕ) (f : D → ℝ) :
    ∑ p : Chain D k, mass T p * f (head p) = (∑ d, f d) / Fintype.card D := by
  induction k generalizing f with
  | zero =>
    change (∑ p : D, (1 / Fintype.card D) * f p) = _
    rw [← Finset.mul_sum]
    ring
  | succ k ih =>
    change (∑ p : D × Chain D k, T p.1 (head p.2) * mass T p.2 * f p.1) = _
    rw [Fintype.sum_prod_type]
    have he (d : D) :
        (∑ q : Chain D k, T d (head q) * mass T q * f d) = f d / Fintype.card D := by
      have hi := ih (fun e => T d e)
      rw [ht.row_sum] at hi
      calc
        _ = (∑ q : Chain D k, mass T q * T d (head q)) * f d := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro q _
          ring
        _ = _ := by rw [hi]; ring
    simp_rw [he]
    exact (Finset.sum_div _ _ _).symm

theorem mass_sum [Nonempty D] (ht : Transition T) (k : ℕ) :
    ∑ p : Chain D k, mass T p = 1 := by
  simpa [Fintype.card_ne_zero] using head_expectation ht k (fun _ => (1:ℝ))

theorem cost_expectation (ht : Transition T) (k : ℕ) (len : D → ℝ) :
    ∑ p : Chain D k, mass T p * cost len p =
      (k+1:ℝ) * (∑ d, len d) / Fintype.card D := by
  induction k with
  | zero => simpa [cost,head] using head_expectation ht 0 len
  | succ k ih =>
    change (∑ p : D × Chain D k,
      (T p.1 (head p.2)*mass T p.2)*(len p.1+cost len p.2)) = _
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    have hf := head_expectation ht (k+1) len
    change (∑ p : D × Chain D k,
      T p.1 (head p.2)*mass T p.2*len p.1) = _ at hf
    rw [hf]
    have hs : (∑ p : D × Chain D k,
        T p.1 (head p.2)*mass T p.2*cost len p.2) =
        ∑ q : Chain D k, mass T q * cost len q := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      calc
        _ = (∑ d, T d (head q)) * (mass T q * cost len q) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro d _
          ring
        _ = _ := by rw [ht.col_sum]; ring
    rw [hs,ih]
    push_cast
    ring

theorem mass_upper (ht : Transition T) {k : ℕ} (p : Chain D k) :
    mass T p ≤ (1 / Fintype.card D) * (1/2:ℝ)^k := by
  induction k with
  | zero => simp [mass]
  | succ k ih =>
    change T p.1 (head p.2)*mass T p.2 ≤ _
    calc
      _ ≤ (1/2:ℝ)*((1 / Fintype.card D)*(1/2:ℝ)^k) :=
        mul_le_mul (ht.half _ _) (ih p.2) (mass_nonneg ht p.2) (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- Finite Markov without probability-space infrastructure: at least half the
mass has cost at most twice the expectation; zero-mass chains are irrelevant. -/
theorem short_mass {P : Type*} [Fintype P] (w c : P → ℝ)
    (hw : ∀ p, 0 ≤ w p) (hc : ∀ p, 0 ≤ c p)
    (hs : ∑ p, w p = 1) (B : ℝ) (hB : 0 < B)
    (hm : ∑ p, w p*c p ≤ B) :
    1/2 ≤ ∑ p ∈ Finset.univ.filter (fun p => c p ≤ 2*B ∧ 0 < w p), w p := by
  classical
  let S := Finset.univ.filter (fun p => c p ≤ 2*B ∧ 0 < w p)
  have hl : 2*B * (1 - ∑ p ∈ S, w p) ≤ B := by
    have hp : ∑ p ∈ Finset.univ \ S, w p = 1 - ∑ p ∈ S, w p := by
      have ht := Finset.sum_sdiff (f := w) (Finset.subset_univ S)
      rw [hs] at ht
      linarith
    rw [← hp, Finset.mul_sum]
    calc
      _ ≤ ∑ p ∈ Finset.univ \ S, w p*c p := by
        apply Finset.sum_le_sum
        intro p hp
        have hnot : ¬(c p ≤ 2*B ∧ 0 < w p) := by
          simpa [S] using (Finset.mem_sdiff.mp hp).2
        by_cases hz : w p = 0
        · simp [hz]
        · have hpos : 0 < w p := lt_of_le_of_ne (hw p) (Ne.symm hz)
          have hcp : 2*B < c p := lt_of_not_ge (fun h => hnot ⟨h,hpos⟩)
          nlinarith [mul_nonneg (hw p) (sub_nonneg.mpr hcp.le)]
      _ ≤ ∑ p, w p*c p := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.sdiff_subset) (fun p _ _ => mul_nonneg (hw p) (hc p))
      _ ≤ B := hm
  change 1/2 ≤ ∑ p ∈ S, w p
  nlinarith

omit [Fintype D] in
theorem cost_nonneg (len : D → ℝ) (hlen : ∀ d, 0 ≤ len d) {k : ℕ}
    (p : Chain D k) : 0 ≤ cost len p := by
  induction k with
  | zero => exact hlen p
  | succ k ih => exact add_nonneg (hlen p.1) (ih p.2)

/-- Entropy forces many short nonzero-probability nonbacktracking chains. -/
theorem many_short_chains [Nonempty D] (ht : Transition T) (k : ℕ)
    (len : D → ℝ) (hlen : ∀ d, 0 < len d) :
    ∃ S : Finset (Chain D k),
      (∀ p ∈ S, cost len p ≤ 2*(k+1:ℝ)*(∑ d, len d)/Fintype.card D ∧
        0 < mass T p) ∧
      (Fintype.card D : ℝ)*(2:ℝ)^k ≤ 2*S.card := by
  classical
  let B : ℝ := (k+1:ℝ)*(∑ d, len d)/Fintype.card D
  have hD : (0:ℝ) < Fintype.card D := Nat.cast_pos.mpr Fintype.card_pos
  have hs : 0 < ∑ d, len d := Finset.sum_pos (fun d _ => hlen d) Finset.univ_nonempty
  have hB : 0 < B := div_pos (mul_pos (by positivity) hs) hD
  have hc : ∀ p : Chain D k, 0 ≤ cost len p := cost_nonneg len (fun d => (hlen d).le)
  let S := Finset.univ.filter (fun p : Chain D k => cost len p ≤ 2*B ∧ 0 < mass T p)
  have hm : 1/2 ≤ ∑ p ∈ S, mass T p :=
    short_mass (mass T) (cost len) (mass_nonneg ht) hc (mass_sum ht k) B hB
      (cost_expectation ht k len).le
  refine ⟨S,?_,?_⟩
  · intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    refine ⟨?_,hp'.2⟩
    calc
      _ ≤ 2*B := hp'.1
      _ = _ := by dsimp [B]; ring
  · have hm' : (∑ p ∈ S, mass T p) ≤
        S.card*((1/Fintype.card D)*(1/2:ℝ)^k) := by
      calc
        _ ≤ ∑ _p ∈ S, (1/Fintype.card D)*(1/2:ℝ)^k :=
          Finset.sum_le_sum (fun p _ => mass_upper ht p)
        _ = _ := by simp
    have powpos : 0 < (2:ℝ)^k := pow_pos (by norm_num) _
    have hp : (1/2:ℝ)^k = 1/(2:ℝ)^k := by rw [one_div_pow]
    rw [hp] at hm'
    have he : (S.card:ℝ)*((1/Fintype.card D)*(1/(2:ℝ)^k)) =
        S.card/((Fintype.card D:ℝ)*(2:ℝ)^k) := by ring
    rw [he] at hm'
    have h := (le_div_iff₀ (mul_pos hD powpos)).mp (hm.trans hm')
    linarith

/-- More short chains than ordered endpoint pairs forces a collision. This uses
actual chains and their probabilities, not a hypothesis asserting path growth. -/
theorem short_collision [Nonempty D] (ht : Transition T) (k : ℕ)
    (len : D → ℝ) (hlen : ∀ d, 0 < len d)
    (hbig : 2*(Fintype.card D : ℝ) < (2:ℝ)^k) :
    ∃ p q : Chain D k, p ≠ q ∧ head p = head q ∧ last p = last q ∧
      0 < mass T p ∧ 0 < mass T q ∧
      cost len p + cost len q ≤ 4*(k+1:ℝ)*(∑ d, len d)/Fintype.card D := by
  classical
  obtain ⟨S,hS,hcard⟩ := many_short_chains ht k len hlen
  have hD : (0:ℝ) < Fintype.card D := Nat.cast_pos.mpr Fintype.card_pos
  have hlt : (Fintype.card D : ℝ)^2 < S.card := by
    have hmul := mul_lt_mul_of_pos_left hbig hD
    nlinarith
  have hn : (Finset.univ : Finset (D × D)).card < S.card := by
    simp only [Finset.card_univ,Fintype.card_prod]
    rw [pow_two] at hlt
    exact_mod_cast hlt
  obtain ⟨p,hp,q,hq,hne,he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hn
    (f := fun p : Chain D k => (head p,last p)) (fun _ _ => Finset.mem_univ _)
  refine ⟨p,q,hne,(Prod.mk.inj he).1,(Prod.mk.inj he).2,(hS p hp).2,(hS q hq).2,?_⟩
  have hp' := (hS p hp).1
  have hq' := (hS q hq).1
  calc
    _ ≤ _ := add_le_add hp' hq'
    _ = _ := by ring

/-- An explicit logarithmic number of transitions suffices. -/
theorem logarithmic_short_collision [Nonempty D] (ht : Transition T)
    (len : D → ℝ) (hlen : ∀ d, 0 < len d) :
    let k := Nat.log 2 (Fintype.card D) + 2
    ∃ p q : Chain D k, p ≠ q ∧ head p = head q ∧ last p = last q ∧
      0 < mass T p ∧ 0 < mass T q ∧
      cost len p + cost len q ≤ 4*(k+1:ℝ)*(∑ d, len d)/Fintype.card D := by
  apply short_collision ht _ len hlen
  have hn := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (Fintype.card D)
  have hn' : (Fintype.card D : ℝ) < (2:ℝ)^(Nat.log 2 (Fintype.card D)+1) := by
    exact_mod_cast hn
  rw [show Nat.log 2 (Fintype.card D)+2 = (Nat.log 2 (Fintype.card D)+1)+1 by omega,
    pow_succ]
  linarith

namespace PortWalk

variable {V : Type*} (origin : D → V) (rev : D → D)
    (hinv : Function.Involutive rev)

open scoped Classical

def out (v : V) : Finset D := Finset.univ.filter (fun d => origin d = v)
def choices (v : V) : ℕ := (out origin v).card - 1

def transition (d e : D) : ℝ :=
  if step origin rev d e then 1 / (choices origin (origin e) : ℝ) else 0

theorem succ_eq (d : D) :
    Finset.univ.filter (step origin rev d) = (out origin (origin (rev d))).erase (rev d) := by
  ext e
  simp [step,out,and_comm,eq_comm]

theorem succ_card (d : D) :
    (Finset.univ.filter (step origin rev d)).card = choices origin (origin (rev d)) := by
  rw [succ_eq,Finset.card_erase_of_mem (by simp [out])]
  rfl

include hinv

theorem pred_eq (e : D) :
    Finset.univ.filter (fun d => step origin rev d e) =
      ((out origin (origin e)).erase e).image rev := by
  ext d
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_image,Finset.mem_erase]
  constructor
  · intro h
    refine ⟨rev d,⟨Ne.symm h.2,?_⟩,hinv d⟩
    simpa [out] using h.1
  · rintro ⟨a,⟨ha,hoa⟩,rfl⟩
    change origin (rev (rev a)) = origin e ∧ e ≠ rev (rev a)
    rw [hinv a]
    refine ⟨?_,Ne.symm ha⟩
    simpa [out] using hoa

theorem pred_card (e : D) :
    (Finset.univ.filter (fun d => step origin rev d e)).card = choices origin (origin e) := by
  rw [pred_eq origin rev hinv, Finset.card_image_of_injective _ hinv.injective,
    Finset.card_erase_of_mem (by simp [out])]
  rfl

/-- The actual nonbacktracking chain on ports of a multigraph is stationary
on uniformly chosen darts, including loops and parallel edges. -/
theorem transition_law (hdeg : ∀ d, 3 ≤ (out origin (origin d)).card) :
    Transition (transition origin rev) := by
  have hchoice (d : D) : (2:ℝ) ≤ choices origin (origin d) := by
    have h := hdeg d
    have : 2 ≤ choices origin (origin d) := by dsimp [choices]; omega
    exact_mod_cast this
  have hpos (d : D) : (0:ℝ) < choices origin (origin d) := lt_of_lt_of_le (by norm_num) (hchoice d)
  refine ⟨?_,?_,?_,?_⟩
  · intro d e
    unfold transition
    split <;> positivity
  · intro d
    have he : (∑ e, transition origin rev d e) =
        ∑ e ∈ Finset.univ.filter (step origin rev d),
          1 / (choices origin (origin (rev d)) : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      unfold transition
      split_ifs with h
      · rw [h.1]
      · rfl
    rw [he]
    simp only [Finset.sum_const, nsmul_eq_mul, succ_card]
    exact mul_one_div_cancel (ne_of_gt (hpos (rev d)))
  · intro e
    change (∑ d, if step origin rev d e then _ else 0) = 1
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,pred_card origin rev hinv]
    exact mul_one_div_cancel (ne_of_gt (hpos e))
  · intro d e
    unfold transition
    split
    · exact one_div_le_one_div_of_le (by norm_num) (hchoice e)
    · norm_num

end PortWalk

end TorsionFreeZeroDivisors.WeightedMoore

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedPortMoore
open SimpleGraph WeightedMoore PortSubdivision WeightedCycles
variable {V D : Type*} (Γ : PortGraph V D)

/-- Validity as a chain of actual nonbacktracking directed edges. -/
def Good : {k : ℕ} → Chain D k → Prop
  | 0, _ => True
  | _+1, p => PortWalk.step Γ.origin Γ.reverse p.1 (head p.2) ∧ Good p.2

/-- The physical port walk, starting and ending at the first/last ports.
It has one middle edge per macro-edge, and two spokes between them. -/
def draw : {k : ℕ} → (p : Chain D k) → Good Γ p →
    Γ.subdivision.Walk (.inr (head p)) (.inr (Γ.reverse (last p)))
  | 0, d, _ => Walk.cons (show Γ.subdivision.Adj (.inr d) (.inr (Γ.reverse d)) from rfl) Walk.nil
  | _+1, p, h =>
    Walk.cons (show Γ.subdivision.Adj (.inr p.1) (.inr (Γ.reverse p.1)) from rfl)
      (Walk.cons (show Γ.subdivision.Adj (.inr (Γ.reverse p.1)) (.inl (Γ.origin (Γ.reverse p.1))) from rfl)
        (Walk.cons (show Γ.subdivision.Adj (.inl (Γ.origin (Γ.reverse p.1))) (.inr (head p.2)) from h.1.1.symm)
          (draw p.2 h.2)))

@[simp] theorem draw_head_edge {k : ℕ} (p : Chain D k) (hp : Good Γ p) :
    (draw Γ p hp).edges.head? = some s(Sum.inr (head p),Sum.inr (Γ.reverse (head p))) := by
  cases k <;> rfl

theorem middle_spoke_ne (d e : D) (v : V) :
    (s(Sum.inr d,Sum.inr (Γ.reverse d)) : Sym2 (V ⊕ D)) ≠ s(Sum.inr e,Sum.inl v) := by
  simp

theorem draw_reduced {k : ℕ} (p : Chain D k) (hp : Good Γ p) :
    (draw Γ p hp).edges.IsChain (· ≠ ·) := by
  induction k with
  | zero =>
    change ([s(Sum.inr p,Sum.inr (Γ.reverse p))] : List (Sym2 (V ⊕ D))).IsChain (· ≠ ·)
    exact List.IsChain.singleton _
  | succ k ih =>
    change ((s(Sum.inr p.1,Sum.inr (Γ.reverse p.1))) ::
      s(Sum.inr (Γ.reverse p.1),Sum.inl (Γ.origin (Γ.reverse p.1))) ::
      s(Sum.inl (Γ.origin (Γ.reverse p.1)),Sum.inr (head p.2)) ::
      (draw Γ p.2 hp.2).edges).IsChain (· ≠ ·)
    apply List.IsChain.cons_cons (middle_spoke_ne Γ _ _ _)
    apply List.IsChain.cons_cons
    · intro he
      have h := Sym2.eq_iff.mp he
      simp only [Sum.inr.injEq,reduceCtorEq,and_false,false_or] at h
      exact hp.1.2 h.1.symm
    · apply (ih p.2 hp.2).cons
      intro y hy
      rw [draw_head_edge] at hy
      have he : y = s(Sum.inr (head p.2),Sum.inr (Γ.reverse (head p.2))) := (Option.mem_some_iff.mp hy).symm
      subst y
      intro h
      exact middle_spoke_ne Γ (head p.2) (head p.2) (Γ.origin (Γ.reverse p.1))
        (h.symm.trans Sym2.eq_swap)

/-- Recording ports from the physical walk recovers each directed macro-edge. -/
def portWord : {k : ℕ} → Chain D k → List D
  | 0, d => [d,Γ.reverse d]
  | _+1, p => p.1 :: Γ.reverse p.1 :: portWord p.2

def onlyPort : V ⊕ D → Option D
  | .inl _ => none
  | .inr d => some d

theorem draw_portWord {k : ℕ} (p : Chain D k) (hp : Good Γ p) :
    (draw Γ p hp).support.filterMap onlyPort = portWord Γ p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change p.1 :: Γ.reverse p.1 :: (draw Γ p.2 hp.2).support.filterMap onlyPort =
      p.1 :: Γ.reverse p.1 :: portWord Γ p.2
    rw [ih p.2 hp.2]

/-- Nonnegative symmetric length on the subdivision; spokes cost zero. -/
def edgeWeight (len : D → ℝ) : Sym2 (V ⊕ D) → ℝ :=
  Sym2.lift ⟨fun a b => match a,b with
    | .inr d,.inr e => (len d+len e)/2
    | _,_ => 0, by intro a b; cases a <;> cases b <;> simp [add_comm]⟩

theorem edgeWeight_nonneg (len : D → ℝ) (hlen : ∀ d, 0 ≤ len d) :
    ∀ e, 0 ≤ edgeWeight (V := V) len e := by
  intro e
  induction e using Sym2.inductionOn with
  | _ a b =>
    cases a with
    | inl v => cases b <;> exact le_rfl
    | inr d =>
      cases b with
      | inl v => exact le_rfl
      | inr e => exact div_nonneg (add_nonneg (hlen d) (hlen e)) (by norm_num)

@[simp] theorem edgeWeight_spoke (len : D → ℝ) (v : V) (d : D) :
    edgeWeight len s(Sum.inl v,Sum.inr d) = 0 := rfl

@[simp] theorem edgeWeight_middle (len : D → ℝ) (hsym : ∀ d, len (Γ.reverse d) = len d) (d : D) :
    edgeWeight (V := V) len s(Sum.inr d,Sum.inr (Γ.reverse d)) = len d := by
  change (len d+len (Γ.reverse d))/2 = len d
  rw [hsym]; ring

theorem draw_weight (len : D → ℝ) (hsym : ∀ d, len (Γ.reverse d) = len d)
    {k : ℕ} (p : Chain D k) (hp : Good Γ p) :
    weight (edgeWeight len) (draw Γ p hp) = cost len p := by
  induction k with
  | zero =>
    change (len p+len (Γ.reverse p))/2+0 = len p
    rw [hsym]; ring
  | succ k ih =>
    change (len p.1+len (Γ.reverse p.1))/2 +
      (0+(0+weight (edgeWeight len) (draw Γ p.2 hp.2))) = len p.1+cost len p.2
    rw [hsym,ih p.2 hp.2]
    ring

/-- Positive chain mass certifies every actual allowed transition. -/
theorem positive_good [Fintype D]
    (ht : Transition (PortWalk.transition Γ.origin Γ.reverse))
    {k : ℕ} (p : Chain D k)
    (hp : 0 < mass (PortWalk.transition Γ.origin Γ.reverse) p) : Good Γ p := by
  induction k with
  | zero => trivial
  | succ k ih =>
    have hs : PortWalk.step Γ.origin Γ.reverse p.1 (head p.2) := by
      by_contra hn
      simp only [mass,PortWalk.transition,if_neg hn,zero_mul] at hp
      exact lt_irrefl _ hp
    have hne : mass (PortWalk.transition Γ.origin Γ.reverse) p.2 ≠ 0 := by
      intro he
      simp only [mass,he,mul_zero] at hp
      exact lt_irrefl _ hp
    exact ⟨hs,ih p.2 (lt_of_le_of_ne (mass_nonneg ht p.2) hne.symm)⟩

/-- The logarithmic Moore inequality bounds the number of darts uniformly in
all positive edge lengths and in the girth scale. -/
theorem logarithmic_inequality_bounded (A : ℝ) (hA : 0 ≤ A) :
    ∃ R : ℕ, ∀ n : ℕ, (n : ℝ) ≤ A*((Nat.log 2 n:ℝ)+3) → n ≤ R := by
  have ht : Filter.Tendsto (fun n : ℕ => A*(Real.logb 2 n+3)/(n:ℝ))
      Filter.atTop (nhds 0) := by
    have hlog : Filter.Tendsto (fun n : ℕ => Real.logb 2 n/(n:ℝ))
        Filter.atTop (nhds 0) := by
      simpa [Function.comp_def] using (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1
        one_ne_zero).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hinv : Filter.Tendsto (fun n : ℕ => (3:ℝ)/(n:ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 3
    convert (hlog.add hinv).const_mul A using 1 <;> simp [add_div,mul_div_assoc]
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const (by norm_num : (0:ℝ)<1))
  refine ⟨max R 1,fun n hn => ?_⟩
  by_contra hnR
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hl := hR n (by omega)
  have hb := mul_le_mul_of_nonneg_left (Real.natLog_le_logb n 2) hA
  norm_num only [Nat.cast_ofNat] at hb
  have hc : (n:ℝ) ≤ A*(Real.logb 2 n+3) := by nlinarith
  have hd := (div_lt_iff₀ hn0).mp hl
  linarith

end TorsionFreeZeroDivisors.WeightedPortMoore

namespace TorsionFreeZeroDivisors.ChainSuppression
open Function
open scoped Classical

variable {D : Type*} (σ τ : D → D)
    (hσ : Involutive σ) (hτ : Involutive τ)

include hσ hτ

variable [Finite D]

/-- Each directed edge can be traversed at most once among all oriented
maximal chains. This is the exact disjoint-interior count, not a bound supplied
as an extra hypothesis. -/
lemma chain_dart_injective :
    Injective (fun p : (x : {x : D // τ x=x}) × Fin (length σ τ hσ hτ x.val x.property) =>
      (next σ τ)^[p.2.val] p.1.val) := by
  intro ⟨x,i⟩ ⟨y,j⟩ he
  have hone (x y : {x : D // τ x=x})
      (i : Fin (length σ τ hσ hτ x.val x.property))
      (j : Fin (length σ τ hσ hτ y.val y.property))
      (hij : i.val ≤ j.val)
      (he : (next σ τ)^[i.val] x.val=(next σ τ)^[j.val] y.val) :
      x=y ∧ i.val=j.val := by
    have hji : j.val=i.val+(j.val-i.val) := by omega
    rw [hji,iterate_add_apply] at he
    have hr := ((next_injective σ τ hσ hτ).iterate i.val) he
    have hzero : j.val-i.val=0 := by
      by_contra hz
      have hf : τ ((next σ τ)^[j.val-i.val] y.val)=(next σ τ)^[j.val-i.val] y.val := by
        rw [← hr]; exact x.property
      exact no_internal_mark σ τ hσ hτ y.val y.property (Nat.pos_of_ne_zero hz)
        (by omega) hf
    have hexy : x=y := by
      apply Subtype.ext
      simpa only [hzero,iterate_zero,id_eq] using hr
    exact ⟨hexy,by omega⟩
  have hxy : x=y ∧ i.val=j.val := by
    rcases le_total i.val j.val with hij | hji
    · exact hone x y i j hij he
    · obtain ⟨hexy,hij⟩ := hone y x j i hji he.symm
      exact ⟨hexy.symm,hij.symm⟩
  obtain ⟨rfl,hij⟩ := hxy
  congr 1
  exact Fin.ext hij

lemma total_length_le [Fintype D] :
    ∑ x : {x : D // τ x=x}, length σ τ hσ hτ x.val x.property ≤ Fintype.card D := by
  classical
  simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_le_of_injective _
    (chain_dart_injective σ τ hσ hτ)

end TorsionFreeZeroDivisors.ChainSuppression

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.DegreeTwoSuppression
open Function
open scoped Classical
open TorsionFreeZeroDivisors ChainSuppression PortSubdivision
variable {V D : Type*} [Fintype D]

variable (o : D → V) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out o v).card=2)

lemma turn_origin (d : D) : o (turn o mark h2 d)=o d := by
  by_cases hd : mark (o d)
  · rw [turn_of_mark o mark h2 d hd]
  · exact (turn_of_unmarked o mark h2 d hd).1

lemma turn_fixed_iff (d : D) : turn o mark h2 d=d ↔ mark (o d) := by
  constructor
  · intro he
    by_contra hd
    exact (turn_of_unmarked o mark h2 d hd).2 he
  · exact turn_of_mark o mark h2 d

lemma chainLength_pos (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (d : {d : D // turn Γ.origin mark h2 d=d}) : 0 < chainLength Γ mark h2 d :=
  length_pos _ _ _ _ _ _

lemma chainLength_reverse (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (d : {d : D // turn Γ.origin mark h2 d=d}) :
    chainLength Γ mark h2 ((suppressed Γ mark h2).reverse d)=chainLength Γ mark h2 d :=
  length_endpoint _ _ _ _ _

lemma chainLength_total (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2) :
    ∑ d : {d : D // turn Γ.origin mark h2 d=d}, chainLength Γ mark h2 d ≤ Fintype.card D :=
  total_length_le _ _ _ _

lemma suppressed_degree (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (v : V) (hv : mark v) :
    (out (suppressed Γ mark h2).origin v).card = (out Γ.origin v).card := by
  classical
  apply Finset.card_bij (fun d _ => d.val)
  · intro d hd
    exact (mem_out Γ.origin v d.val).mpr ((mem_out _ v d).mp hd)
  · intro d _ e _ he
    exact Subtype.ext he
  · intro d hd
    have ho : Γ.origin d=v := (mem_out _ v d).mp hd
    let e : {d : D // turn Γ.origin mark h2 d=d} :=
      ⟨d,(turn_fixed_iff Γ.origin mark h2 d).mpr (ho ▸ hv)⟩
    exact ⟨e,(mem_out _ v e).mpr ho,rfl⟩

/-- Minimum degree two becomes minimum degree three whenever a component has
some branching. Pure circle components give no darts and are treated separately. -/
lemma suppressed_min_degree (Γ : PortGraph V D)
    (hmin : ∀ d, 2 ≤ (out Γ.origin (Γ.origin d)).card) :
    let mark := fun v => (out Γ.origin v).card≠2
    let h2 := fun v (h : ¬mark v) => Classical.not_not.mp h
    ∀ d, 3 ≤ (out (suppressed Γ mark h2).origin ((suppressed Γ mark h2).origin d)).card := by
  intro mark h2 d
  have hm : mark (Γ.origin d.val) := (turn_fixed_iff Γ.origin mark h2 d.val).mp d.property
  change 3 ≤ (out (suppressed Γ mark h2).origin (Γ.origin d.val)).card
  rw [suppressed_degree Γ mark h2 _ hm]
  have hc := hmin d.val
  dsimp [mark] at hm
  omega

end TorsionFreeZeroDivisors.DegreeTwoSuppression

namespace TorsionFreeZeroDivisors.SuppressedMoore
open Function SimpleGraph
open scoped Classical
open TorsionFreeZeroDivisors PortSubdivision WeightedMoore WeightedPortMoore
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)

local notation "τ" => DegreeTwoSuppression.turn Γ.origin mark h2
local notation "hτ" => DegreeTwoSuppression.turn_involutive Γ.origin mark h2
local notation "F" => ChainSuppression.next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "Γ'" => DegreeTwoSuppression.suppressed Γ mark h2
local notation "len" => DegreeTwoSuppression.chainLength Γ mark h2

omit [Fintype D] in
@[simp] lemma head_iterChain (f : D → D) (n : ℕ) (x : D) : head (iterChain f n x)=x := by
  cases n <;> rfl

omit [Fintype D] in
@[simp] lemma last_iterChain (f : D → D) (n : ℕ) (x : D) :
    last (iterChain f n x)=f^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change last (iterChain f n (f x))=f^[n+1] x
    rw [ih,iterate_succ_apply]

lemma iterChain_good (n : ℕ) (x : D)
    (hm : ∀ i : ℕ, 0 < i → i ≤ n → τ (F^[i] x) ≠ F^[i] x) :
    Good Γ (iterChain F n x) := by
  induction n generalizing x with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,?_⟩
    · change PortWalk.step Γ.origin Γ.reverse x (head (iterChain F n (F x)))
      rw [head_iterChain]
      have hne : F x ≠ Γ.reverse x := by
        intro he
        have h0 : τ (F x)=F x := by
          change τ (τ (Γ.reverse x))=F x
          rw [hτ,he]
        exact hm 1 (by omega) (by omega) (by simpa only [iterate_one] using h0)
      exact ⟨(DegreeTwoSuppression.turn_origin Γ.origin mark h2 (Γ.reverse x)).symm,hne⟩
    · apply ih (F x)
      intro i hi hin
      have his : i+1≤n+1 := by omega
      simpa only [iterate_succ_apply] using hm (i+1) (by omega) his

lemma chain_good (d : B) : Good Γ (iterChain F (len d-1) d.val) := by
  apply iterChain_good
  intro i hi hil
  exact ChainSuppression.no_internal_mark Γ.reverse τ Γ.reverse_reverse hτ d.val d.property hi
    (by change i < len d; have hp := DegreeTwoSuppression.chainLength_pos Γ mark h2 d; omega)

lemma chain_last (d : B) : Γ.reverse (last (iterChain F (len d-1) d.val)) = ((Γ').reverse d).val := by
  rw [last_iterChain]
  have hf := ((Γ').reverse d).property
  change τ (F^[len d] d.val)=F^[len d] d.val at hf
  have hk : len d=(len d-1)+1 := by
    have hp := DegreeTwoSuppression.chainLength_pos Γ mark h2 d
    omega
  conv_lhs at hf => rw [hk,iterate_succ_apply']
  change τ (τ (Γ.reverse (F^[len d-1] d.val)))=F^[len d] d.val at hf
  rw [hτ] at hf
  exact hf

omit [Fintype D] in
lemma cost_iterChain_one (f : D → D) (n : ℕ) (d : D) :
    cost (fun _ => (1:ℝ)) (iterChain f n d) = n+1 := by
  induction n generalizing d with
  | zero => simp [cost]
  | succ n ih =>
    change 1+cost (fun _ => (1:ℝ)) (iterChain f n (f d))=(n+1:ℕ)+1
    rw [ih]
    push_cast
    ring

omit [Fintype D] in
def join : {k : ℕ} → Chain D k → (Σ l, Chain D l) → (Σ l, Chain D l)
  | 0, d, ⟨l,q⟩ => ⟨l+1,(d,q)⟩
  | _+1, p, q => let r := join p.2 q; ⟨r.1+1,(p.1,r.2)⟩

omit [Fintype D] in
lemma join_head {k : ℕ} (p : Chain D k) (q : Σ l, Chain D l) :
    head (join p q).2 = head p := by cases k <;> rfl

omit [Fintype D] in
lemma join_last {k : ℕ} (p : Chain D k) (q : Σ l, Chain D l) :
    last (join p q).2 = last q.2 := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih p.2

omit [Fintype D] in
lemma join_cost (w : D → ℝ) {k : ℕ} (p : Chain D k) (q : Σ l, Chain D l) :
    cost w (join p q).2 = cost w p + cost w q.2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change w p.1+cost w (join p.2 q).2 = (w p.1+cost w p.2)+cost w q.2
    rw [ih]; ring

omit [Fintype D] in
lemma join_good {k : ℕ} (p : Chain D k) (q : Σ l, Chain D l)
    (hp : Good Γ p) (hq : Good Γ q.2)
    (hlink : PortWalk.step Γ.origin Γ.reverse (last p) (head q.2)) :
    Good Γ (join p q).2 := by
  induction k with
  | zero => exact ⟨hlink,hq⟩
  | succ k ih =>
    change PortWalk.step Γ.origin Γ.reverse p.1 (head (join p.2 q).2) ∧ _
    rw [join_head]
    exact ⟨hp.1,ih p.2 hp.2 hlink⟩

omit [Fintype D] in
lemma outWord_injective (k : ℕ) : Injective (@outWord D k) := by
  induction k with
  | zero => intro p q h; exact List.cons.inj h |>.1
  | succ k ih =>
    intro p q h
    exact Prod.ext (List.cons.inj h).1 (ih (List.cons.inj h).2)

omit [Fintype D] in
lemma outWord_join {k : ℕ} (p : Chain D k) (q : Σ l, Chain D l) :
    outWord (join p q).2 = outWord p ++ outWord q.2 := by
  induction k with
  | zero => rfl
  | succ k ih => change p.1 :: outWord (join p.2 q).2 = _; rw [ih]; rfl

omit [Fintype D] in
def pickEven : List D → List D
  | [] => []
  | [d] => [d]
  | d::_::ds => d::pickEven ds

omit [Fintype D] in
lemma pickEven_portWord {k : ℕ} (p : Chain D k) :
    pickEven (portWord Γ p) = outWord p := by
  induction k with
  | zero => rfl
  | succ k ih => change p.1::pickEven (portWord Γ p.2)=_; rw [ih]; rfl

lemma iterChain_no_marks (n : ℕ) (d : D)
    (hn : ∀ i : ℕ, i≤n → τ (F^[i] d) ≠ F^[i] d) :
    (outWord (iterChain F n d)).filter (fun d => τ d=d) = [] := by
  induction n generalizing d with
  | zero => simpa [outWord,iterChain] using hn 0 (by omega)
  | succ n ih =>
    change (d::outWord (iterChain F n (F d))).filter (fun d => τ d=d)=[]
    rw [List.filter_cons_of_neg (by simpa using hn 0 (by omega))]
    apply ih
    intro i hi
    simpa only [iterate_succ_apply] using hn (i+1) (by omega)

lemma chain_one_mark (d : B) :
    (outWord (iterChain F (len d-1) d.val)).filter (fun d => τ d=d) = [d.val] := by
  have hp := DegreeTwoSuppression.chainLength_pos Γ mark h2 d
  have hn (i : ℕ) (hi : 0 < i) (hil : i < len d) : τ (F^[i] d.val)≠F^[i] d.val :=
    ChainSuppression.no_internal_mark Γ.reverse τ Γ.reverse_reverse hτ d.val d.property hi hil
  generalize he : len d-1 = n
  cases n with
  | zero => simp [outWord,iterChain,d.property]
  | succ n =>
    change (d.val::outWord (iterChain F n (F d.val))).filter (fun d => τ d=d)=[d.val]
    rw [List.filter_cons_of_pos (by simpa using d.property)]
    rw [iterChain_no_marks]
    intro i hi
    simpa only [iterate_succ_apply] using hn (i+1) (by omega) (by omega)

/-- Expand every macro-edge, preserving the ordered path occurrence data. -/
def expand : {k : ℕ} → Chain B k → (Σ l, Chain D l)
  | 0, d => ⟨len d-1,iterChain F (len d-1) d.val⟩
  | _+1, p => join (iterChain F (len p.1-1) p.1.val) (expand p.2)

lemma expand_head {k : ℕ} (p : Chain B k) : head (expand Γ mark h2 p).2 = (head p).val := by
  cases k with
  | zero => exact head_iterChain F _ _
  | succ k => change head (join _ _).2 = p.1.val; rw [join_head,head_iterChain]

lemma expand_last {k : ℕ} (p : Chain B k) :
    Γ.reverse (last (expand Γ mark h2 p).2) = ((Γ').reverse (last p)).val := by
  induction k with
  | zero => exact chain_last Γ mark h2 p
  | succ k ih => change Γ.reverse (last (join _ _).2)=_; rw [join_last]; exact ih p.2

lemma expand_good {k : ℕ} (p : Chain B k) (hp : Good (Γ') p) :
    Good Γ (expand Γ mark h2 p).2 := by
  induction k with
  | zero => exact chain_good Γ mark h2 p
  | succ k ih =>
    apply join_good Γ _ _ (chain_good Γ mark h2 p.1) (ih p.2 hp.2)
    unfold PortWalk.step
    rw [chain_last,expand_head]
    exact ⟨hp.1.1,fun he => hp.1.2 (Subtype.ext he)⟩

lemma expand_cost {k : ℕ} (p : Chain B k) :
    cost (fun _ : D => (1:ℝ)) (expand Γ mark h2 p).2 = cost (fun d => (len d : ℝ)) p := by
  have hs (d : B) : cost (fun _ : D => (1:ℝ)) (iterChain F (len d-1) d.val) = len d := by
    rw [cost_iterChain_one]
    have hp := DegreeTwoSuppression.chainLength_pos Γ mark h2 d
    norm_cast
    omega
  induction k with
  | zero => exact hs p
  | succ k ih => change cost _ (join _ _).2 = _; rw [join_cost,hs,ih]; rfl

lemma expand_marks {k : ℕ} (p : Chain B k) :
    (outWord (expand Γ mark h2 p).2).filter (fun d => τ d=d) = (outWord p).map Subtype.val := by
  induction k with
  | zero => exact chain_one_mark Γ mark h2 p
  | succ k ih =>
    change (outWord (join _ _).2).filter _ = _
    rw [outWord_join,List.filter_append,chain_one_mark,ih]
    rfl

/-- The stationary Moore collision in the suppressed graph expands to a
literal original cycle. Girth is imposed only on the original graph. -/
theorem original_short_cycle [Nonempty B]
    (hdeg : ∀ d, 3 ≤ (PortWalk.out (Γ').origin ((Γ').origin d)).card) :
    let k := Nat.log 2 (Fintype.card B) + 2
    ∃ (a : V ⊕ D) (c : Γ.subdivision.Walk a a), c.IsCycle ∧
      WeightedCycles.weight (edgeWeight (fun _ : D => (1:ℝ))) c ≤
        4*(k+1:ℝ)*(∑ d : B, (len d : ℝ))/Fintype.card B := by
  let T := PortWalk.transition (Γ').origin (Γ').reverse
  have ht : Transition T := PortWalk.transition_law (Γ').origin (Γ').reverse
    (Γ').reverse_reverse hdeg
  have hlpos (d : B) : (0:ℝ) < len d := by
    exact_mod_cast DegreeTwoSuppression.chainLength_pos Γ mark h2 d
  obtain ⟨p,q,hne,hh,hl,hp,hq,hcost⟩ := logarithmic_short_collision ht (fun d => (len d : ℝ)) hlpos
  have hgp : Good (Γ') p := positive_good (Γ') ht p hp
  have hgq : Good (Γ') q := positive_good (Γ') ht q hq
  let ep := expand Γ mark h2 p
  let eq := expand Γ mark h2 q
  have hep : Good Γ ep.2 := expand_good Γ mark h2 p hgp
  have heq : Good Γ eq.2 := expand_good Γ mark h2 q hgq
  have heh : head eq.2 = head ep.2 := by
    change head (expand Γ mark h2 q).2=head (expand Γ mark h2 p).2
    rw [expand_head,expand_head,hh]
  have hel : Γ.reverse (last eq.2) = Γ.reverse (last ep.2) := by
    change Γ.reverse (last (expand Γ mark h2 q).2)=Γ.reverse (last (expand Γ mark h2 p).2)
    rw [expand_last,expand_last,hl]
  let qp : Γ.subdivision.Walk (.inr (head ep.2)) (.inr (Γ.reverse (last ep.2))) :=
    (draw Γ eq.2 heq).copy (congrArg Sum.inr heh) (congrArg Sum.inr hel)
  have hqp : draw Γ ep.2 hep ≠ qp := by
    intro he
    have hr := congrArg (fun r => r.support.filterMap onlyPort) he
    simp only [qp,Walk.support_copy,draw_portWord] at hr
    have ho := congrArg pickEven hr
    simp only [pickEven_portWord] at ho
    have hm := congrArg (fun ds => ds.filter (fun d => τ d=d)) ho
    change (outWord (expand Γ mark h2 p).2).filter _ =
      (outWord (expand Γ mark h2 q).2).filter _ at hm
    rw [expand_marks,expand_marks] at hm
    exact hne (outWord_injective _ ((List.map_inj_right (fun _ _ => Subtype.ext)).mp hm))
  have hqred : qp.edges.IsChain (· ≠ ·) := by
    simpa only [qp,Walk.edges_copy] using draw_reduced Γ eq.2 heq
  have hwp : WeightedCycles.weight (edgeWeight (fun _ : D => (1:ℝ))) (draw Γ ep.2 hep) =
      cost (fun d => (len d : ℝ)) p := by
    rw [draw_weight Γ _ (fun _ => rfl)]
    exact expand_cost Γ mark h2 p
  have hwq : WeightedCycles.weight (edgeWeight (fun _ : D => (1:ℝ))) qp =
      cost (fun d => (len d : ℝ)) q := by
    simp only [qp,WeightedCycles.weight,Walk.edges_copy]
    change WeightedCycles.weight (edgeWeight (fun _ : D => (1:ℝ))) (draw Γ eq.2 heq)=_
    rw [draw_weight Γ _ (fun _ => rfl)]
    exact expand_cost Γ mark h2 q
  obtain ⟨a,c,hc,hwc⟩ := WeightedCycles.distinct_reduced_cycle
    (edgeWeight (fun _ : D => (1:ℝ))) (edgeWeight_nonneg _ (fun _ => by norm_num))
    (draw Γ ep.2 hep) qp hqp (draw_reduced Γ ep.2 hep) hqred
  refine ⟨a,c,hc,?_⟩
  rw [hwp,hwq] at hwc
  exact hwc.trans hcost

/-- Actual branch-port complexity from original edge count and original girth,
without an a priori graph-rank or chain-count hypothesis. -/
theorem original_dart_inequality [Nonempty B]
    (hdeg : ∀ d, 3 ≤ (PortWalk.out (Γ').origin ((Γ').origin d)).card)
    (L C : ℝ) (hL : 0 < L)
    (htotal : (Fintype.card D : ℝ) ≤ 2*C*L)
    (hgirth : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
      L ≤ WeightedCycles.weight (edgeWeight (fun _ : D => (1:ℝ))) c) :
    (Fintype.card B : ℝ) ≤ 8*C*(Nat.log 2 (Fintype.card B)+3:ℝ) := by
  obtain ⟨a,c,hc,hbound⟩ := original_short_cycle Γ mark h2 hdeg
  have hD : (0:ℝ) < Fintype.card B := Nat.cast_pos.mpr Fintype.card_pos
  have he := (le_div_iff₀ hD).mp ((hgirth a c hc).trans hbound)
  have hs : (∑ d : B, (len d : ℝ)) ≤ Fintype.card D := by
    exact_mod_cast DegreeTwoSuppression.chainLength_total Γ mark h2
  have hn : (0:ℝ) ≤ 4*((Nat.log 2 (Fintype.card B)+2:ℕ)+1:ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_left (hs.trans htotal) hn
  push_cast at he hm
  nlinarith

omit [Fintype D] in
/-- Uniformly many branch ports in an actual finite graph of minimum degree
two with O(L) edges and girth L. Pure circles contribute no branch ports. -/
theorem bounded_branch_ports (C : ℝ) (hC : 0 ≤ C) :
    ∃ R : ℕ, ∀ {V D : Type} [Fintype D] (Γ : PortGraph V D)
      (_ : ∀ d, 2 ≤ (DegreeTwoSuppression.out Γ.origin (Γ.origin d)).card)
      (L : ℝ) (_ : 0 < L)
      (_ : (Fintype.card D : ℝ) ≤ 2*C*L)
      (_ : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
          L ≤ WeightedCycles.weight (edgeWeight (fun _ : D => (1:ℝ))) c),
      (Finset.univ.filter (fun d : D =>
        (DegreeTwoSuppression.out Γ.origin (Γ.origin d)).card≠2)).card ≤ R := by
  obtain ⟨R,hR⟩ := logarithmic_inequality_bounded (8*C) (by positivity)
  refine ⟨R,?_⟩
  intro V D _ Γ hmin L hL htotal hg
  let mark := fun v => (DegreeTwoSuppression.out Γ.origin v).card≠2
  let h2 := fun v (h : ¬mark v) => Classical.not_not.mp h
  let CoreD := {d : D // DegreeTwoSuppression.turn Γ.origin mark h2 d=d}
  have he : (Finset.univ.filter (fun d : D =>
      (DegreeTwoSuppression.out Γ.origin (Γ.origin d)).card≠2)).card = Fintype.card CoreD := by
    change (Finset.univ.filter (fun d : D => mark (Γ.origin d))).card = _
    simpa only [CoreD,Fintype.card_subtype] using congrArg Finset.card (show
      Finset.univ.filter (fun d : D => mark (Γ.origin d)) =
      Finset.univ.filter (fun d : D => DegreeTwoSuppression.turn Γ.origin mark h2 d=d) by
        ext d; simp [DegreeTwoSuppression.turn_fixed_iff])
  rw [he]
  cases isEmpty_or_nonempty CoreD with
  | inl hi => have := hi; rw [Fintype.card_eq_zero]; exact Nat.zero_le R
  | inr hi =>
    have := hi
    apply hR
    apply original_dart_inequality Γ mark h2 ?_ L C hL htotal hg
    exact DegreeTwoSuppression.suppressed_min_degree Γ hmin

end TorsionFreeZeroDivisors.SuppressedMoore

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.CoreStripping
open PortSubdivision
open scoped Classical
variable {V D : Type*} (Γ : PortGraph V D)

def degree (S : Finset D) (v : V) : ℕ := (S.filter (fun d => Γ.origin d=v)).card

def Symmetric (S : Finset D) : Prop := ∀ d ∈ S, Γ.reverse d ∈ S

def delete (S : Finset D) (d : D) : Finset D := (S.erase d).erase (Γ.reverse d)

lemma delete_subset (S : Finset D) (d : D) : delete Γ S d ⊆ S :=
  (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)

lemma degree_pos (S : Finset D) {d : D} (hd : d∈S) : 0 < degree Γ S (Γ.origin d) := by
  exact Finset.card_pos.mpr ⟨d,Finset.mem_filter.mpr ⟨hd,rfl⟩⟩

lemma leaf_unique (S : Finset D) {d : D} (hd : d∈S) (hleaf : degree Γ S (Γ.origin d)=1)
    {e : D} (he : e∈S) (ho : Γ.origin e=Γ.origin d) : e=d := by
  have hu := Finset.card_eq_one.mp hleaf
  obtain ⟨z,hz⟩ := hu
  have hd' : d∈S.filter (fun e => Γ.origin e=Γ.origin d) := by simp [hd]
  have he' : e∈S.filter (fun e => Γ.origin e=Γ.origin d) := by simp [he,ho]
  rw [hz] at hd' he'
  exact (Finset.mem_singleton.mp he').trans (Finset.mem_singleton.mp hd').symm

lemma leaf_not_loop (S : Finset D) (hs : Symmetric Γ S) {d : D} (hd : d∈S)
    (hleaf : degree Γ S (Γ.origin d)=1) : Γ.origin (Γ.reverse d)≠Γ.origin d := by
  intro he
  exact Γ.reverse_ne d (leaf_unique Γ S hd hleaf (hs d hd) he)

lemma delete_symmetric (S : Finset D) (hs : Symmetric Γ S) (d : D) :
    Symmetric Γ (delete Γ S d) := by
  intro e he
  simp only [delete,Finset.mem_erase] at he ⊢
  refine ⟨?_,?_,hs e he.2.2⟩
  · exact fun h => he.2.1 (Γ.reverse_reverse.injective h)
  · intro h
    have hh := congrArg Γ.reverse h
    rw [Γ.reverse_reverse] at hh
    exact he.1 hh

lemma delete_degree_leaf (S : Finset D) {d : D} (hd : d∈S)
    (hleaf : degree Γ S (Γ.origin d)=1) : degree Γ (delete Γ S d) (Γ.origin d)=0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,ho⟩ := Finset.mem_filter.mp he
  have heq := leaf_unique Γ S hd hleaf (delete_subset Γ S d he) ho
  exact (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).1 heq

lemma delete_degree_neighbor (S : Finset D) (hs : Symmetric Γ S) {d : D} (hd : d∈S)
    (hleaf : degree Γ S (Γ.origin d)=1) :
    degree Γ (delete Γ S d) (Γ.origin (Γ.reverse d))+1 = degree Γ S (Γ.origin (Γ.reverse d)) := by
  have hn := leaf_not_loop Γ S hs hd hleaf
  have he : (delete Γ S d).filter (fun e => Γ.origin e=Γ.origin (Γ.reverse d)) =
      (S.filter (fun e => Γ.origin e=Γ.origin (Γ.reverse d))).erase (Γ.reverse d) := by
    ext e
    simp only [delete,Finset.mem_filter,Finset.mem_erase]
    constructor
    · tauto
    · rintro ⟨he,hs',ho⟩
      refine ⟨⟨he,?_,hs'⟩,ho⟩
      intro hd'
      subst e
      exact hn ho.symm
  unfold degree
  rw [he]
  exact Finset.card_erase_add_one (by simp [hs d hd])

lemma delete_degree_other (S : Finset D) (d : D) {v : V}
    (hu : v≠Γ.origin d) (hv : v≠Γ.origin (Γ.reverse d)) :
    degree Γ (delete Γ S d) v=degree Γ S v := by
  unfold degree
  congr 1
  ext e
  simp only [delete,Finset.mem_filter,Finset.mem_erase]
  constructor
  · tauto
  · rintro ⟨he,ho⟩
    refine ⟨⟨?_,?_,he⟩,ho⟩
    · intro hh; subst e; exact hv ho.symm
    · intro hh; subst e; exact hu ho.symm

/-- Euler surplus without counting isolated vertices. It equals the sum of
branch excesses minus the number of leaves. -/
def surplus (n : ℕ) : ℤ := if n=0 then 0 else (n:ℤ)-2

lemma surplus_succ (n : ℕ) : surplus (n+1) ≤ surplus n+1 := by
  rcases n with _ | n
  · norm_num [surplus]
  · simp only [surplus,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,Nat.cast_add,Nat.cast_one]
    omega

variable [Fintype V]

def potential (S : Finset D) : ℤ := ∑ v, surplus (degree Γ S v)

lemma delete_potential (S : Finset D) (hs : Symmetric Γ S) {d : D} (hd : d∈S)
    (hleaf : degree Γ S (Γ.origin d)=1) : potential Γ S≤potential Γ (delete Γ S d) := by
  have hn := leaf_not_loop Γ S hs hd hleaf
  have hpoint (v : V) : surplus (degree Γ S v) ≤
      surplus (degree Γ (delete Γ S d) v) + (if v=Γ.origin (Γ.reverse d) then 1 else 0) -
        (if v=Γ.origin d then 1 else 0) := by
    by_cases hu : v=Γ.origin d
    · subst v
      rw [hleaf,delete_degree_leaf Γ S hd hleaf]
      simp [surplus,Ne.symm hn]
    · by_cases hv : v=Γ.origin (Γ.reverse d)
      · subst v
        rw [← delete_degree_neighbor Γ S hs hd hleaf]
        simpa only [if_pos rfl,if_neg hn,ite_true,sub_zero] using surplus_succ
          (degree Γ (delete Γ S d) (Γ.origin (Γ.reverse d)))
      · rw [delete_degree_other Γ S d hu hv,if_neg hu,if_neg hv,add_zero,sub_zero]
  have hsum := Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hpoint v)
  unfold potential
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,add_sub_cancel_right] using hsum

/-- Actual repeated leaf deletion. The terminal subgraph has minimum degree
two on every surviving dart; Euler surplus can only increase. -/
theorem exists_core (S : Finset D) (hs : Symmetric Γ S) :
    ∃ Q : Finset D, Q⊆S ∧ Symmetric Γ Q ∧
      (∀ d∈Q, 2≤degree Γ Q (Γ.origin d)) ∧ potential Γ S≤potential Γ Q := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hleaf : ∃ d∈S, degree Γ S (Γ.origin d)=1
    · obtain ⟨d,hd,hleaf⟩ := hleaf
      let S' := delete Γ S d
      have hlt : S'.card<n := by
        have he : S'.card≤(S.erase d).card := Finset.card_le_card (Finset.erase_subset _ _)
        have ht := Finset.card_erase_lt_of_mem hd
        omega
      obtain ⟨Q,hQS,hQ,hdeg,hpot⟩ := ih S'.card hlt S' (delete_symmetric Γ S hs d) rfl
      exact ⟨Q,hQS.trans (delete_subset Γ S d),hQ,hdeg,
        (delete_potential Γ S hs hd hleaf).trans hpot⟩
    · refine ⟨S,Finset.Subset.refl _,hs,?_,le_refl _⟩
      intro d hd
      have hp := degree_pos Γ S hd
      have hn : degree Γ S (Γ.origin d)≠1 := by aesop
      omega

end TorsionFreeZeroDivisors.CoreStripping

namespace TorsionFreeZeroDivisors.ImageComplexity
open PortSubdivision WeightedPortMoore WeightedCycles CoreStripping
open scoped BigOperators Classical
variable {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)

/-- The actual symmetric subgraph on a specified set of original darts. -/
def restrict (Q : Finset D) (hs : Symmetric Γ Q) : PortGraph V Q where
  origin d := Γ.origin d
  reverse d := ⟨Γ.reverse d,hs d d.property⟩
  reverse_reverse d := Subtype.ext (Γ.reverse_reverse d)
  reverse_ne d h := Γ.reverse_ne d (congrArg Subtype.val h)

def inclusion (Q : Finset D) (hs : Symmetric Γ Q) :
    (restrict Γ Q hs).subdivision →g Γ.subdivision where
  toFun := Sum.map id Subtype.val
  map_rel' := by
    intro a b h
    rcases a with a|a <;> rcases b with b|b
    · exact h
    · exact h
    · exact h
    · exact congrArg Subtype.val h

omit [Fintype V] [Fintype D] in
lemma inclusion_injective (Q : Finset D) (hs : Symmetric Γ Q) :
    Function.Injective (inclusion Γ Q hs) := Sum.map_injective.mpr ⟨Function.injective_id,Subtype.val_injective⟩

omit [Fintype V] [Fintype D] in
lemma restrict_degree (Q : Finset D) (hs : Symmetric Γ Q) (v : V) :
    (DegreeTwoSuppression.out (restrict Γ Q hs).origin v).card=degree Γ Q v := by
  classical
  unfold DegreeTwoSuppression.out degree
  apply Finset.card_bij (fun d _ => d.val)
  · intro d hd
    exact Finset.mem_filter.mpr ⟨d.property,(Finset.mem_filter.mp hd).2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro d hd
    refine ⟨⟨d,(Finset.mem_filter.mp hd).1⟩,?_,rfl⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact (Finset.mem_filter.mp hd).2

omit [Fintype V] [Fintype D] in
lemma inclusion_weight (Q : Finset D) (hs : Symmetric Γ Q) {a b : V ⊕ Q}
    (p : (restrict Γ Q hs).subdivision.Walk a b) :
    weight (edgeWeight (fun _ : D => (1:ℝ))) (p.map (inclusion Γ Q hs)) =
      weight (edgeWeight (fun _ : Q => (1:ℝ))) p := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.map_cons,weight_cons,weight_cons,ih]
    congr 1
    cases a <;> cases b <;> rfl

omit [Fintype D] in
/-- Vertexwise counting, including loops through their two different darts. -/
lemma fiber_count (S : Finset D) (P : V → Prop) [DecidablePred P] :
    ∑ v, (if P v then degree Γ S v else 0) = (S.filter (fun d => P (Γ.origin d))).card := by
  classical
  unfold degree
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  trans ∑ v, ∑ d ∈ S, if Γ.origin d=v ∧ P v then 1 else 0
  · apply Finset.sum_congr rfl
    intro v hv
    by_cases hh : P v <;> simp [hh]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  simp [ite_and]

lemma surplus_excess (n : ℕ) : surplus n = ((n-2:ℕ):ℤ) - (if n=1 then 1 else 0) := by
  unfold surplus
  split_ifs <;> omega

lemma surplus_le_branch (n : ℕ) : surplus n ≤ (if n=2 then (0:ℕ) else n) := by
  unfold surplus
  split_ifs <;> omega

omit [Fintype D] in
lemma excess_le_potential_add_leaves (S : Finset D) :
    ((∑ v, (degree Γ S v - 2) : ℕ):ℤ) ≤ potential Γ S +
      ((Finset.univ.filter (fun v => degree Γ S v=1)).card:ℤ) := by
  unfold potential
  simp only [surplus_excess,Finset.sum_sub_distrib,Nat.cast_sum]
  have he : (∑ v : V, (if degree Γ S v=1 then (1:ℤ) else 0)) =
      ((Finset.univ.filter (fun v => degree Γ S v=1)).card:ℤ) := by simp
  rw [he]
  omega

omit [Fintype D] in
lemma branch_degrees_bound_excess (S : Finset D) :
    (S.filter (fun d => 3 ≤ degree Γ S (Γ.origin d))).card ≤
      3 * (∑ v, (degree Γ S v - 2)) := by
  rw [← fiber_count Γ S (fun v => 3 ≤ degree Γ S v),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  split_ifs <;> omega

/-- Bounded branching in the actual image, not in a hypothesized bounded-rank
pattern. A bounded number of leaves is the only endpoint correction. -/
theorem bounded_image_branches (C : ℝ) (hC : 0 ≤ C) (leaves : ℕ) :
    ∃ R : ℕ, ∀ {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)
      (L : ℝ) (_ : 0 < L)
      (_ : (Fintype.card D:ℝ) ≤ 2*C*L)
      (_ : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
        L ≤ weight (edgeWeight (fun _ : D => (1:ℝ))) c)
      (_ : (Finset.univ.filter (fun v => degree Γ Finset.univ v=1)).card ≤ leaves),
      (Finset.univ.filter (fun d => 3≤degree Γ Finset.univ (Γ.origin d))).card ≤ R := by
  obtain ⟨R,hR⟩ := SuppressedMoore.bounded_branch_ports C hC
  refine ⟨3*(R+leaves),?_⟩
  intro V D _ _ Γ L hL htot hg hl
  obtain ⟨Q,_hQ,hs,hmin,hpot⟩ := exists_core Γ Finset.univ (by simp [CoreStripping.Symmetric])
  have hsub : (Fintype.card Q:ℝ)≤2*C*L := by
    exact (Nat.cast_le.mpr (by simpa using Finset.card_le_univ Q)).trans htot
  have hbound := hR (restrict Γ Q hs) (fun d => by
    rw [restrict_degree]; exact hmin d d.property) L hL hsub (by
      intro a c hc
      have hp := hg _ (c.map (inclusion Γ Q hs)) (hc.map (inclusion_injective Γ Q hs))
      rwa [inclusion_weight] at hp)
  have hc : (Q.filter (fun d => degree Γ Q (Γ.origin d)≠2)).card≤R := by
    have he : (Finset.univ.filter (fun d : Q =>
        (DegreeTwoSuppression.out (restrict Γ Q hs).origin ((restrict Γ Q hs).origin d)).card≠2)).card =
        (Q.filter (fun d => degree Γ Q (Γ.origin d)≠2)).card := by
      simp only [restrict_degree]
      apply Finset.card_bij (fun d _ => d.val)
      · intro d hd; exact Finset.mem_filter.mpr ⟨d.property,(Finset.mem_filter.mp hd).2⟩
      · intro a _ b _ h; exact Subtype.ext h
      · intro d hd
        exact ⟨⟨d,(Finset.mem_filter.mp hd).1⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hd).2⟩,rfl⟩
    rwa [he] at hbound
  have hpQ : potential Γ Q ≤ (R:ℤ) := by
    calc potential Γ Q ≤ ((∑ v : V, (if degree Γ Q v≠2 then degree Γ Q v else 0)):ℕ) := by
          rw [Nat.cast_sum]
          unfold potential
          apply Finset.sum_le_sum
          intro v hv
          simpa only [ite_not] using surplus_le_branch (degree Γ Q v)
      _ = ((Q.filter (fun d => degree Γ Q (Γ.origin d)≠2)).card:ℤ) := by
          rw [fiber_count]
      _ ≤ R := by exact_mod_cast hc
  have hex := excess_le_potential_add_leaves Γ Finset.univ
  have hle : (∑ v, (degree Γ Finset.univ v - 2))≤R+leaves := by
    have hl' : ((Finset.univ.filter (fun v => degree Γ Finset.univ v=1)).card:ℤ)≤leaves := by
      exact_mod_cast hl
    have hh : (((∑ v, (degree Γ Finset.univ v - 2)):ℕ):ℤ)≤(R:ℤ)+leaves := by omega
    exact_mod_cast hh
  exact (branch_degrees_bound_excess Γ Finset.univ).trans (Nat.mul_le_mul_left 3 hle)

end TorsionFreeZeroDivisors.ImageComplexity

namespace TorsionFreeZeroDivisors.SystemLeaves
open SimpleGraph PortSubdivision
open scoped Classical
variable {W : Type*} {G : SimpleGraph W}

variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)

variable [Fintype V]

end TorsionFreeZeroDivisors.SystemLeaves

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChainCoverage
open Function ChainSuppression
open scoped Classical
variable {D : Type*} [Finite D] (σ τ : D → D)
    (hσ : Involutive σ) (hτ : Involutive τ)

lemma covered_fixed {d : D} (hd : τ d=d) : Covered σ τ hσ hτ d := by
  exact ⟨⟨d,hd⟩, ⟨0,length_pos σ τ hσ hτ d hd⟩,rfl⟩

lemma covered_next {d : D} (hd : Covered σ τ hσ hτ d) :
    Covered σ τ hσ hτ (next σ τ d) := by
  obtain ⟨x,i,rfl⟩ := hd
  by_cases hi : i.val+1 < length σ τ hσ hτ x.val x.property
  · refine ⟨x,⟨i.val+1,hi⟩,?_⟩
    exact iterate_succ_apply' _ _ _
  · have he : i.val+1 = length σ τ hσ hτ x.val x.property := by omega
    apply covered_fixed
    rw [← iterate_succ_apply' (next σ τ) i.val x.val]
    change τ ((next σ τ)^[i.val+1] x.val) = (next σ τ)^[i.val+1] x.val
    rw [he]
    exact length_fixed σ τ hσ hτ x.val x.property

/-- Reversing an original dart stays in the opposite oriented marked chain. -/
lemma covered_reverse {d : D} (hd : Covered σ τ hσ hτ d) :
    Covered σ τ hσ hτ (σ d) := by
  obtain ⟨x,i,rfl⟩ := hd
  let k := length σ τ hσ hτ x.val x.property
  let e := endpoint σ τ hσ hτ x
  have hi : i.val < k := i.isLt
  have hk : length σ τ hσ hτ e.val e.property=k := length_endpoint σ τ hσ hτ x
  have hj : k-i.val-1 < length σ τ hσ hτ e.val e.property := by omega
  refine ⟨e,⟨k-i.val-1,hj⟩,?_⟩
  have hf := endpoint_reverse σ τ hσ hτ (x:=x) (i:=k-i.val) (by omega)
  have he : k-(k-i.val)=i.val := by omega
  have hs : k-i.val=(k-i.val-1)+1 := by omega
  change (next σ τ)^[k-i.val] e.val = τ ((next σ τ)^[k-(k-i.val)] x.val) at hf
  rw [he,hs,iterate_succ_apply'] at hf
  have h := congrArg τ hf
  change τ (τ (σ ((next σ τ)^[k-i.val-1] e.val))) = τ (τ ((next σ τ)^[i.val] x.val)) at h
  rw [hτ,hτ] at h
  have hh := congrArg σ h
  rwa [hσ] at hh

end TorsionFreeZeroDivisors.ChainCoverage

namespace TorsionFreeZeroDivisors.ActualMarkedChains
open Function PortSubdivision ChainSuppression DegreeTwoSuppression ChainCoverage
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)

lemma forced_turn {d e : D} (hst : WeightedMoore.PortWalk.step Γ.origin Γ.reverse d e)
    (he : ¬mark (Γ.origin e)) :
    turn Γ.origin mark h2 (Γ.reverse d)=e := by
  have hd : ¬mark (Γ.origin (Γ.reverse d)) := hst.1 ▸ he
  apply (unique_other Γ.origin (Γ.reverse d) (h2 _ hd)).unique
  · exact turn_of_unmarked Γ.origin mark h2 (Γ.reverse d) hd
  · exact ⟨hst.1.symm,hst.2⟩

lemma covered_step {d e : D}
    (hd : Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
      (turn_involutive Γ.origin mark h2) d)
    (hst : WeightedMoore.PortWalk.step Γ.origin Γ.reverse d e) :
    Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
      (turn_involutive Γ.origin mark h2) e := by
  by_cases he : mark (Γ.origin e)
  · exact covered_fixed _ _ _ _ (turn_of_mark Γ.origin mark h2 e he)
  · have hh := covered_next _ _ _ _ hd
    change Covered _ _ _ _ (turn Γ.origin mark h2 (Γ.reverse d)) at hh
    rwa [forced_turn Γ mark h2 hst he] at hh

lemma covered_path (p : List D)
    (hp : p.IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
    (hh : ∀ d∈p.head?, Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
      (turn_involutive Γ.origin mark h2) d) :
    ∀ d∈p, Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
      (turn_involutive Γ.origin mark h2) d := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have ha := hh a (by simp)
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ha
    · apply ih hp.tail ?_ d hd
      cases p with
      | nil => simp
      | cons b p =>
        intro e he
        have heb : b=e := by simpa using he
        subst e
        exact covered_step Γ mark h2 ha (List.isChain_cons_cons.mp hp).1

/-- Every dart of the actual image belongs to a marked chain. No circle
component is dropped: a path start is marked in every component. -/
theorem actual_image_covered {J : Type*} (paths : J → List D)
    (hpaths : ∀ j, (paths j).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
    (hstarts : ∀ j d, d∈(paths j).head? → mark (Γ.origin d))
    (himage : ∀ d : D, ∃ j, d∈paths j ∨ Γ.reverse d∈paths j) :
    ∀ d, Covered Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
      (turn_involutive Γ.origin mark h2) d := by
  intro d
  obtain ⟨j,hj⟩ := himage d
  have hp := covered_path Γ mark h2 (paths j) (hpaths j) (by
    intro e he
    exact covered_fixed _ _ _ _ (turn_of_mark Γ.origin mark h2 e (hstarts j e he)))
  rcases hj with hj|hj
  · exact hp d hj
  · have hh := covered_reverse _ _ _ _ (hp (Γ.reverse d) hj)
    rwa [Γ.reverse_reverse d] at hh

end TorsionFreeZeroDivisors.ActualMarkedChains

namespace TorsionFreeZeroDivisors.MarkedChainBound
open PortSubdivision DegreeTwoSuppression CoreStripping ImageComplexity
open scoped Classical BigOperators
variable {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)

/-- Mark all irregular vertices and the specified
start/end vertices. -/
def marks (M : Finset V) (v : V) : Prop := degree Γ Finset.univ v ≠ 2 ∨ v∈M

omit [Fintype V] in
lemma marks_degree_two (M : Finset V) (v : V) (hv : ¬marks Γ M v) :
    (out Γ.origin v).card=2 := by
  change degree Γ Finset.univ v=2
  exact Classical.not_not.mp (fun h => hv (Or.inl h))

lemma marked_dart_bound (M : Finset V) :
    (Finset.univ.filter (fun d => marks Γ M (Γ.origin d))).card ≤
      (Finset.univ.filter (fun d => 3≤degree Γ Finset.univ (Γ.origin d))).card +
      (Finset.univ.filter (fun v => degree Γ Finset.univ v=1)).card + 2*M.card := by
  rw [← fiber_count Γ Finset.univ (marks Γ M)]
  calc (∑ v, if marks Γ M v then degree Γ Finset.univ v else 0) ≤
      ∑ v, ((if 3≤degree Γ Finset.univ v then degree Γ Finset.univ v else 0) +
        (if degree Γ Finset.univ v=1 then 1 else 0) + (if v∈M then 2 else 0)) := by
        apply Finset.sum_le_sum
        intro v _
        by_cases hb : 3 ≤ degree Γ Finset.univ v <;>
          by_cases hl : degree Γ Finset.univ v = 1 <;>
          by_cases hm : v ∈ M <;>
          simp_all [marks] <;> split_ifs <;> omega
    _ = (Finset.univ.filter (fun d => 3≤degree Γ Finset.univ (Γ.origin d))).card +
      (Finset.univ.filter (fun v => degree Γ Finset.univ v=1)).card + 2*M.card := by
        rw [Finset.sum_add_distrib,Finset.sum_add_distrib,fiber_count]
        simp [Finset.sum_ite_mem,Nat.mul_comm]

omit [Fintype V] in
lemma chain_dart_card (M : Finset V) :
    Fintype.card {d : D // turn Γ.origin (marks Γ M) (marks_degree_two Γ M) d=d} =
      (Finset.univ.filter (fun d => marks Γ M (Γ.origin d))).card := by
  rw [Fintype.card_subtype]
  congr 1
  ext d
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,turn_fixed_iff]

end TorsionFreeZeroDivisors.MarkedChainBound

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore WeightedPortMoore SuppressedMoore ActualMarkedChains
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "len" => chainLength Γ mark h2

omit [Fintype D] in
lemma outWord_length {k : ℕ} (p : Chain D k) : (outWord p).length=k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [outWord,List.length_cons,Nat.succ_eq_add_one,Nat.add_right_cancel_iff] using ih p.2

omit [Fintype D] in
lemma outWord_last {k : ℕ} (p : Chain D k) : (outWord p).getLast?=some (last p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (p.1 :: outWord p.2).getLast? = some (last p.2)
    simp only [List.getLast?_cons,ih,Option.getD_some]

lemma word_length (d : B) : (word Γ mark h2 d).length=len d := by
  rw [word,outWord_length]
  have h := chainLength_pos Γ mark h2 d
  omega

lemma word_end (d : B) : ∀ e∈(word Γ mark h2 d).getLast?, mark (Γ.origin (Γ.reverse e)) := by
  intro e he
  rw [word,outWord_last] at he
  have he' : last (iterChain F (len d-1) d.val)=e := by simpa using he
  rw [←he',chain_last]
  exact (turn_fixed_iff Γ.origin mark h2 _).mp ((suppressed Γ mark h2).reverse d).property

/-- A reduced path cannot stop before the end of its current marked chain:
its prescribed last vertex is marked, while all interior chain vertices are not. -/
lemma iter_chain_prefix (n : ℕ) (x : D) (p : List D)
    (hp : p.IsChain (PortWalk.step Γ.origin Γ.reverse)) (hh : p.head?=some x)
    (ht : ∀ d∈p.getLast?, mark (Γ.origin (Γ.reverse d)))
    (hn : ∀ i : ℕ, 0 < i → i ≤ n → ¬mark (Γ.origin (F^[i] x))) :
    outWord (iterChain F n x) <+: p := by
  induction n generalizing x p with
  | zero =>
    cases p with
    | nil => simp at hh
    | cons a p =>
      have ha : a=x := Option.some.inj hh
      subst a
      exact ⟨p,rfl⟩
  | succ n ih =>
    cases p with
    | nil => simp at hh
    | cons a p =>
      have ha : a=x := Option.some.inj hh
      subst a
      cases p with
      | nil =>
        have ht' := ht x (by simp)
        have hu := hn 1 (by omega) (by omega)
        apply False.elim
        apply hu
        simpa only [iterate_one,next,comp_apply,turn_origin] using ht'
      | cons y p =>
        have hst := (List.isChain_cons_cons.mp hp).1
        have hy : ¬mark (Γ.origin y) := by
          have ho : Γ.origin (F x)=Γ.origin y := by
            exact (turn_origin Γ.origin mark h2 (Γ.reverse x)).trans hst.1
          have hu := hn 1 (by omega) (by omega)
          simpa only [iterate_one,ho] using hu
        have he : F x=y := forced_turn Γ mark h2 hst hy
        have htt : ∀ d∈(y::p).getLast?, mark (Γ.origin (Γ.reverse d)) := by
          simpa only [List.getLast?_cons_cons] using ht
        have hnn : ∀ i : ℕ, 0 < i → i ≤ n → ¬mark (Γ.origin (F^[i] y)) := by
          intro i hi hin
          have h := hn (i+1) (by omega) (by omega)
          simpa only [iterate_succ_apply,he] using h
        obtain ⟨q,hq⟩ := ih y (y::p) hp.tail rfl htt hnn
        refine ⟨q,?_⟩
        change x :: (outWord (iterChain F n (F x)) ++ q) = x :: y :: p
        rw [he,hq]

lemma word_prefix (d : B) (p : List D)
    (hp : p.IsChain (PortWalk.step Γ.origin Γ.reverse)) (hh : p.head?=some d.val)
    (ht : ∀ e∈p.getLast?, mark (Γ.origin (Γ.reverse e))) : word Γ mark h2 d <+: p := by
  apply iter_chain_prefix Γ mark h2 (len d-1) d.val p hp hh ht
  intro i hi hil
  rw [←turn_fixed_iff Γ.origin mark h2]
  apply no_internal_mark Γ.reverse τ Γ.reverse_reverse (turn_involutive Γ.origin mark h2)
    d.val d.property hi
  have h := chainLength_pos Γ mark h2 d
  change i<len d
  omega

/-- Every original path traverses whole marked chains.
This includes a path that returns to a mark, and does not require it embedded. -/
theorem path_decomposes (p : List D)
    (hp : p.IsChain (PortWalk.step Γ.origin Γ.reverse))
    (hs : ∀ d∈p.head?, mark (Γ.origin d))
    (ht : ∀ d∈p.getLast?, mark (Γ.origin (Γ.reverse d))) :
    ∃ ds : List B, ds.flatMap (word Γ mark h2)=p := by
  cases p with
  | nil => exact ⟨[],rfl⟩
  | cons a p =>
    let d : B := ⟨a, turn_of_mark Γ.origin mark h2 a (hs a (by simp))⟩
    obtain ⟨r,hr⟩ := word_prefix Γ mark h2 d (a::p) hp rfl ht
    have hparts := List.isChain_append.mp (hr.symm ▸ hp)
    have hsr : ∀ b∈r.head?, mark (Γ.origin b) := by
      intro b hb
      let e := last (iterChain F (len d-1) d.val)
      have he : e∈(word Γ mark h2 d).getLast? := by
        rw [word,outWord_last]
        exact rfl
      have hstep := hparts.2.2 e he b hb
      exact hstep.1 ▸ word_end Γ mark h2 d e he
    have htr : ∀ b∈r.getLast?, mark (Γ.origin (Γ.reverse b)) := by
      intro b hb
      have hrne : r≠[] := by intro he; simp [he] at hb
      apply ht b
      rw [←hr,List.getLast?_append_of_ne_nil _ hrne]
      exact hb
    have hlen : r.length < (a::p).length := by
      have h := congrArg List.length hr
      simp only [List.length_append,word_length] at h
      have hd := chainLength_pos Γ mark h2 d
      omega
    obtain ⟨ds,hds⟩ := path_decomposes r hparts.2.1 hsr htr
    refine ⟨d::ds,?_⟩
    simpa only [List.flatMap_cons,hds] using hr
termination_by p.length

omit [Fintype D] in
/-- Enumerating a chain lists precisely the forward iterates before its first mark. -/
lemma outWord_iterChain (f : D → D) (n : ℕ) (x : D) :
    outWord (iterChain f n x) = (List.range (n+1)).map (fun i => f^[i] x) := by
  induction n generalizing x with
  | zero => simp [iterChain,outWord]
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [iterChain,outWord,ih,List.map_cons,List.map_map,iterate_zero,id_eq]
    congr 1

lemma word_eq_range (d : B) :
    word Γ mark h2 d = (List.range (len d)).map (fun i => F^[i] d.val) := by
  rw [word,outWord_iterChain]
  have h := chainLength_pos Γ mark h2 d
  congr 2
  omega

lemma mem_word_iff (d : B) (x : D) :
    x∈word Γ mark h2 d ↔ ∃ i : Fin (len d), F^[i.val] d.val=x := by
  rw [word_eq_range,List.mem_map]
  constructor
  · rintro ⟨i,hi,hx⟩
    exact ⟨⟨i,List.mem_range.mp hi⟩,hx⟩
  · rintro ⟨i,hx⟩
    exact ⟨i.val,List.mem_range.mpr i.isLt,hx⟩

lemma word_nodup (d : B) : (word Γ mark h2 d).Nodup := by
  rw [word_eq_range]
  apply List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj he
  have h := chain_dart_injective Γ.reverse τ Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2)
    (a₁ := ⟨d,⟨i,List.mem_range.mp hi⟩⟩)
    (a₂ := ⟨d,⟨j,List.mem_range.mp hj⟩⟩) he
  exact congrArg (fun p => p.2.val) h

lemma words_disjoint {d e : B} (hne : d≠e) :
    List.Disjoint (word Γ mark h2 d) (word Γ mark h2 e) := by
  intro x hx hy
  obtain ⟨i,hi⟩ := (mem_word_iff Γ mark h2 d x).mp hx
  obtain ⟨j,hj⟩ := (mem_word_iff Γ mark h2 e x).mp hy
  have h := chain_dart_injective Γ.reverse τ Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2) (a₁ := ⟨d,i⟩) (a₂ := ⟨e,j⟩) (hi.trans hj.symm)
  exact hne (congrArg Sigma.fst h)

lemma count_word (d e : B) (x : D) (hx : x∈word Γ mark h2 d) :
    (word Γ mark h2 e).count x = if e=d then 1 else 0 := by
  by_cases he : e=d
  · subst e
    simpa using List.count_eq_one_of_mem (word_nodup Γ mark h2 d) hx
  · have hnot : x∉word Γ mark h2 e := by
      intro hy
      exact words_disjoint Γ mark h2 he hy hx
    simp [he,List.count_eq_zero.mpr hnot]

/-- Every directed edge in one chain has the same traversal multiplicity,
namely the number of occurrences of that oriented chain in the decomposition. -/
lemma multiplicity_constant (ds : List B) (d : B) (x : D)
    (hx : x∈word Γ mark h2 d) :
    (ds.flatMap (word Γ mark h2)).count x = ds.count d := by
  induction ds with
  | nil => rfl
  | cons e ds ih =>
    simp only [List.flatMap_cons,List.count_append,count_word Γ mark h2 d e x hx,ih]
    by_cases he : e=d <;> simp [he,Nat.add_comm]

end TorsionFreeZeroDivisors.ChainPaths

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MultiplicityBound
open SimpleGraph WeightedCycles
variable {V : Type*} {G : SimpleGraph V}

/-- Every nonempty reduced closed walk pays at least the cycle girth, even
when subdivision spokes have zero weight. -/
theorem closed_weight (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (L : ℝ) (hg : ∀ a (c : G.Walk a a), c.IsCycle → L ≤ weight w c)
    {a : V} (p : G.Walk a a) (hp : p.edges.IsChain (· ≠ ·)) (hne : ¬ p.Nil) :
    L ≤ weight w p := by
  have hn : ¬p.IsPath := fun h => hne (Walk.isPath_iff_nil.mp h)
  obtain ⟨b,c,hc,hcp⟩ := reduced_not_path_cycle w hw p hp hn
  exact (hg b c hc).trans hcp

/-- Vertex visits in any reduced walk are uniformly bounded in terms of
expanded length divided by girth. This counts occurrences, not just edges. -/
theorem visit_bound [DecidableEq V] (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ a (c : G.Walk a a), c.IsCycle → L ≤ weight w c)
    {a b : V} (p : G.Walk a b) (hp : p.edges.IsChain (· ≠ ·)) (x : V) :
    (p.support.count x : ℝ)*L ≤ weight w p + L := by
  induction hn : p.length using Nat.strong_induction_on generalizing a b p with
  | h n ih =>
    cases p with
    | nil =>
      by_cases hx : a=x
      · subst x; simp
      · simpa [hx] using hL
    | @cons a b c hab r =>
      have hr : r.edges.IsChain (· ≠ ·) := (List.isChain_cons.mp hp).2
      have il := ih r.length (by simp only [Walk.length_cons] at hn; omega)
        r hr rfl
      by_cases hax : a=x
      · subst x
        by_cases hmem : a ∈ r.support
        · let pref : G.Walk a a := Walk.cons hab (r.takeUntil a hmem)
          let suff := r.dropUntil a hmem
          have hsplit : pref.append suff = Walk.cons hab r := by
            simp only [pref,suff,Walk.cons_append,Walk.take_spec]
          have hpref : pref.edges.IsChain (· ≠ ·) := hp.prefix (by
            rw [← hsplit,Walk.edges_append]
            exact List.prefix_append _ _)
          have hsuff : suff.edges.IsChain (· ≠ ·) := hr.suffix (r.edges_dropUntil_suffix_edges hmem)
          have hpw : L ≤ weight w pref := closed_weight w hw L hg pref hpref (by simp [pref])
          have hsw := ih suff.length (by
            have hlen := r.length_dropUntil_le_length hmem
            simp only [Walk.length_cons] at hn
            dsimp [suff]
            omega) suff hsuff rfl
          have hcount : (Walk.cons hab r).support.count a = suff.support.count a + 1 := by
            have ht := r.count_support_takeUntil_eq_one hmem
            have hstart : suff.support = a :: suff.support.tail := by
              exact (List.cons_head_tail (by simp : suff.support ≠ [])).symm.trans (by simp)
            have hrc : r.support.count a = suff.support.count a := by
              conv_lhs => rw [← r.take_spec hmem]
              simp only [Walk.support_append,List.count_append,ht]
              change 1+suff.support.tail.count a=suff.support.count a
              have hh := congrArg (fun xs : List V => xs.count a) hstart
              simp only [List.count_cons_self] at hh
              omega
            simp [hrc,Nat.add_comm]
          have hweight : weight w (Walk.cons hab r)=weight w pref+weight w suff := by
            rw [← hsplit,weight_append]
          rw [hcount,hweight]
          push_cast
          nlinarith
        · have hz : r.support.count a=0 := List.count_eq_zero.mpr hmem
          simp only [Walk.support_cons,List.count_cons_self,hz,Nat.zero_add,Nat.cast_one,one_mul]
          linarith [weight_nonneg w hw (Walk.cons hab r)]
      · have hc : (Walk.cons hab r).support.count x=r.support.count x := by
          simp [hax]
        rw [hc,weight_cons]
        linarith [hw s(a,b)]

end TorsionFreeZeroDivisors.MultiplicityBound

namespace TorsionFreeZeroDivisors.PathMultiplicity
open SimpleGraph WeightedCycles WeightedMoore WeightedPortMoore
open PortSubdivision SuppressedMoore
open scoped Classical
variable {V D : Type*} (Γ : PortGraph V D)
local instance : BEq (V ⊕ D) := instBEqOfDecidableEq

/-- Convert a literal nonempty dart path to the dependent chain encoding. -/
def pathChain (x : D) : (xs : List D) → Chain D xs.length
  | [] => x
  | y::ys => (x,pathChain y ys)

@[simp] lemma pathChain_head (x : D) (xs : List D) : head (pathChain x xs)=x := by
  cases xs <;> rfl

@[simp] lemma pathChain_word (x : D) (xs : List D) : outWord (pathChain x xs)=x::xs := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih => exact congrArg (List.cons x) (ih y)

lemma pathChain_good (x : D) (xs : List D)
    (hr : (x::xs).IsChain (PortWalk.step Γ.origin Γ.reverse)) : Good Γ (pathChain x xs) := by
  induction xs generalizing x with
  | nil => trivial
  | cons y ys ih =>
    exact ⟨by simpa only [pathChain,pathChain_head] using (List.isChain_cons_cons.mp hr).1, ih y hr.tail⟩

/-- A port appears once per traversal of its undirected edge in the physical
subdivision walk, in either direction. Spoke vertices do not add occurrences. -/
lemma draw_count {k : ℕ} (p : Chain D k) (hp : Good Γ p) (x : D) :
    (draw Γ p hp).support.count (Sum.inr x) =
      (outWord p).count x + (outWord p).count (Γ.reverse x) := by
  classical
  induction k with
  | zero =>
    change ([Sum.inr p, Sum.inr (Γ.reverse p)] : List (V ⊕ D)).count (Sum.inr x) =
      [p].count x + [p].count (Γ.reverse x)
    have he : Γ.reverse p=x ↔ p=Γ.reverse x := by
      constructor
      · intro h; rw [←h,Γ.reverse_reverse]
      · intro h; rw [h,Γ.reverse_reverse]
    simp only [List.count_cons,List.count_nil,beq_iff_eq,Sum.inr.injEq,he]
    omega
  | succ k ih =>
    change (Sum.inr p.1 :: Sum.inr (Γ.reverse p.1) ::
      Sum.inl (Γ.origin (Γ.reverse p.1)) :: (draw Γ p.2 hp.2).support).count (Sum.inr x) =
      (p.1 :: outWord p.2).count x + (p.1 :: outWord p.2).count (Γ.reverse x)
    have he : Γ.reverse p.1=x ↔ p.1=Γ.reverse x := by
      constructor
      · intro h; rw [←h,Γ.reverse_reverse]
      · intro h; rw [h,Γ.reverse_reverse]
    simp only [List.count_cons,beq_iff_eq,Sum.inr.injEq,reduceCtorEq,he,ih]
    simp only [ite_false]
    omega

lemma pathChain_cost (x : D) (xs : List D) :
    cost (fun _ : D => (1:ℝ)) (pathChain x xs) = (x::xs).length := by
  induction xs generalizing x with
  | nil => simp [pathChain,cost]
  | cons y ys ih =>
    change 1+cost (fun _ : D => (1:ℝ)) (pathChain y ys) = ((x::y::ys).length:ℝ)
    rw [ih]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

/-- The undirected edge count for a literal port path bounds each orientation
in particular. -/
theorem path_edge_bound (L : ℝ) (hL : 0≤L)
    (hg : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
      L ≤ weight (edgeWeight (fun _ : D => 1)) c)
    (p : List D) (hp : p.IsChain (PortWalk.step Γ.origin Γ.reverse)) (x : D) :
    ((p.count x + p.count (Γ.reverse x):ℕ):ℝ)*L ≤ p.length + L := by
  cases p with
  | nil => simpa using hL
  | cons y ys =>
    let q := pathChain y ys
    have hq : Good Γ q := pathChain_good Γ y ys hp
    have h := MultiplicityBound.visit_bound (edgeWeight (fun _ : D => 1))
      (edgeWeight_nonneg _ (by intro d; norm_num)) L hL hg
      (draw Γ q hq) (draw_reduced Γ q hq) (Sum.inr x)
    rw [draw_count Γ q hq x,draw_weight Γ _ (by intro d; rfl)] at h
    simpa only [q,pathChain_word,pathChain_cost] using h

end TorsionFreeZeroDivisors.PathMultiplicity

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore WeightedPortMoore SuppressedMoore ActualMarkedChains
open scoped Classical
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "len" => chainLength Γ mark h2

lemma reverse_mem_word (d : B) (x : D) (hx : x∈word Γ mark h2 d) :
    Γ.reverse x∈word Γ mark h2 ((suppressed Γ mark h2).reverse d) := by
  obtain ⟨i,rfl⟩ := (mem_word_iff Γ mark h2 d x).mp hx
  let e := (suppressed Γ mark h2).reverse d
  let k := len d
  have hj : k-i.val-1 < len e := by
    rw [chainLength_reverse]
    have hi := i.isLt
    change i.val < k at hi
    omega
  rw [mem_word_iff]
  refine ⟨⟨k-i.val-1,hj⟩,?_⟩
  have hf := endpoint_reverse Γ.reverse τ Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2) (x:=d) (i:=k-i.val) (by change k-i.val ≤ k; omega)
  have he : k-(k-i.val)=i.val := by omega
  have hs : k-i.val=(k-i.val-1)+1 := by have hi := i.isLt; change i.val < k at hi; omega
  change F^[k-i.val] e.val = τ (F^[k-(k-i.val)] d.val) at hf
  rw [he,hs,iterate_succ_apply'] at hf
  have h := congrArg τ hf
  change τ (τ (Γ.reverse (F^[k-i.val-1] e.val))) = τ (τ (F^[i.val] d.val)) at h
  rw [turn_involutive Γ.origin mark h2,turn_involutive Γ.origin mark h2] at h
  have hh := congrArg Γ.reverse h
  rwa [Γ.reverse_reverse] at hh

end TorsionFreeZeroDivisors.ChainPaths

namespace TorsionFreeZeroDivisors.PathMultiplicity
open PortSubdivision WeightedCycles WeightedPortMoore
open scoped BigOperators Classical
variable {V D I : Type*} (Γ : PortGraph V D) [Fintype I]

/-- Summing the literal edge-multiplicity estimate over the given path system. -/
theorem total_edge_bound (L : ℝ) (hL : 0≤L)
    (hg : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
      L ≤ weight (edgeWeight (fun _ : D => 1)) c)
    (p : I → List D) (hp : ∀ i, (p i).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
    (x : D) :
    (∑ i, ((p i).count x + (p i).count (Γ.reverse x)):ℕ)*L ≤
      (∑ i, (p i).length : ℕ)+(Fintype.card I:ℝ)*L := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => path_edge_bound Γ L hL hg (p i) (hp i) x)
  rw [← Finset.sum_mul] at h
  simpa only [Nat.cast_sum,Nat.cast_add,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul] using h

end TorsionFreeZeroDivisors.PathMultiplicity

namespace TorsionFreeZeroDivisors.ChainPaths
open Function PortSubdivision ChainSuppression DegreeTwoSuppression
open WeightedMoore WeightedPortMoore SuppressedMoore ActualMarkedChains WeightedCycles
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "B" => {d : D // τ d=d}

lemma start_mem_word (d : B) : d.val∈word Γ mark h2 d := by
  rw [mem_word_iff]
  exact ⟨⟨0,chainLength_pos Γ mark h2 d⟩,rfl⟩

omit [Fintype D] in
lemma sum_count_eq_length {A : Type*} [Fintype A] [BEq A] [LawfulBEq A] (p : List A) :
    ∑ a, p.count a = p.length := by
  classical
  induction p with
  | nil => simp
  | cons b p ih =>
    simp only [List.count_cons,beq_iff_eq,Finset.sum_add_distrib,List.length_cons,ih]
    simp

/-- The number of chain traversals is bounded independently of their lengths. -/
theorem total_chain_bound {I : Type*} [Fintype I]
    (L : ℝ) (hL : 0≤L)
    (hg : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
      L ≤ weight (edgeWeight (fun _ : D => 1)) c)
    (ds : I → List B)
    (hp : ∀ i, ((ds i).flatMap (word Γ mark h2)).IsChain (PortWalk.step Γ.origin Γ.reverse)) :
    (∑ i, (ds i).length : ℕ)*L ≤ (Fintype.card B:ℝ)*
      ((∑ i, ((ds i).flatMap (word Γ mark h2)).length : ℕ)+(Fintype.card I:ℝ)*L) := by
  let H : ℝ := (∑ i, ((ds i).flatMap (word Γ mark h2)).length : ℕ)
  have hd (d : B) : (∑ i, (ds i).count d : ℕ)*L ≤ H+(Fintype.card I:ℝ)*L := by
    have h := PathMultiplicity.total_edge_bound Γ L hL hg
      (fun i => (ds i).flatMap (word Γ mark h2)) hp d.val
    have he : (∑ i, (ds i).count d : ℕ) ≤
        ∑ i, (((ds i).flatMap (word Γ mark h2)).count d.val +
          ((ds i).flatMap (word Γ mark h2)).count (Γ.reverse d.val)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [multiplicity_constant Γ mark h2 _ d d.val (start_mem_word Γ mark h2 d)]
      exact Nat.le_add_right _ _
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast he) hL).trans h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun d _ => hd d)
  rw [← Finset.sum_mul] at hs
  have he : ∑ d : B, (∑ i, (ds i).count d : ℕ) = ∑ i, (ds i).length := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact sum_count_eq_length (ds i)
  simpa only [← Nat.cast_sum,he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,H] using hs

/-- A uniform integer bound in terms of the length, path count, and chain count. -/
theorem bounded_chain_traversals {I : Type*} [Fintype I]
    (C : ℝ) (hC : 0≤C) (K R : ℕ) (hI : Fintype.card I≤K) (hB : Fintype.card B≤R)
    (L : ℝ) (hL : 0<L)
    (hg : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
      L ≤ weight (edgeWeight (fun _ : D => 1)) c)
    (ds : I → List B)
    (hp : ∀ i, ((ds i).flatMap (word Γ mark h2)).IsChain (PortWalk.step Γ.origin Γ.reverse))
    (hH : (∑ i, ((ds i).flatMap (word Γ mark h2)).length : ℕ) ≤ C*L) :
    ∑ i, (ds i).length ≤ ⌈(R:ℝ)*(C+K)⌉₊ := by
  have h := total_chain_bound Γ mark h2 L hL.le hg ds hp
  have hib : (Fintype.card I:ℝ) ≤ K := by exact_mod_cast hI
  have hbb : (Fintype.card B:ℝ) ≤ R := by exact_mod_cast hB
  have hh : (∑ i, (ds i).length : ℕ)*L ≤ (R:ℝ)*(C+(K:ℝ))*L := by
    calc
      _ ≤ (Fintype.card B:ℝ)*((C:ℝ)*L+(K:ℝ)*L) :=
        h.trans (mul_le_mul_of_nonneg_left
          (add_le_add hH (mul_le_mul_of_nonneg_right hib hL.le)) (Nat.cast_nonneg _))
      _ = (Fintype.card B:ℝ)*(C+K)*L := by ring
      _ ≤ (R:ℝ)*(C+K)*L := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbb (by positivity)) hL.le
  have he := (mul_le_mul_iff_left₀ hL).mp hh
  exact_mod_cast he.trans (Nat.le_ceil _)

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

variable [Fintype V] [Fintype D]

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

omit [Fintype D] in
lemma outWord_head {k : ℕ} (p : WeightedMoore.Chain D k) :
    (SuppressedMoore.outWord p).head?=some (WeightedMoore.head p) := by
  cases k <;> rfl

lemma word_head (d : B) : (w d).head?=some d.val := by
  rw [word,outWord_head,head_iterChain]

lemma word_last (d : B) : (w d).getLast?=some (Γ.reverse ((S).reverse d).val) := by
  rw [word,outWord_last]
  apply congrArg some
  exact Γ.reverse_reverse.injective (by rw [chain_last,Γ.reverse_reverse])

lemma word_ne_nil (d : B) : w d ≠ [] := by
  intro he
  have h := word_length Γ mark h2 d
  rw [he,List.length_nil] at h
  have hp := chainLength_pos Γ mark h2 d
  omega

/-- A genuine reduced original path transports to a genuine reduced path in
its suppressed graph. Adjacency is read from the actual last/first darts;
no graph path property is imposed on the decomposition as a hypothesis. -/
theorem isChain (ds : List B)
    (hp : (ds.flatMap w).IsChain (PortWalk.step Γ.origin Γ.reverse)) :
    ds.IsChain (PortWalk.step (S).origin (S).reverse) := by
  have hn : [] ∉ ds.map w := by
    intro he
    obtain ⟨d,_,hd⟩ := List.mem_map.mp he
    exact word_ne_nil Γ mark h2 d hd
  have hc := (List.isChain_flatten hn).mp hp
  have hc' := (List.isChain_map w).mp hc.2
  apply hc'.imp
  intro a b hab
  have he := hab _ (word_last Γ mark h2 a) _ (word_head Γ mark h2 b)
  simp only [PortWalk.step] at he
  rw [Γ.reverse_reverse] at he
  refine ⟨he.1,?_⟩
  intro hb
  exact he.2 (congrArg Subtype.val hb)

lemma flatMap_head (ds : List B) :
    (ds.flatMap w).head? = ds.head?.map Subtype.val := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    rw [List.flatMap_cons,List.head?_append_of_ne_nil _ (word_ne_nil Γ mark h2 d)]
    exact word_head Γ mark h2 d

lemma flatMap_last (ds : List B) :
    (ds.flatMap w).getLast? = ds.getLast?.map (fun d => Γ.reverse ((S).reverse d).val) := by
  induction ds using List.reverseRecOn with
  | nil => rfl
  | append_singleton ds d _ih =>
    simp only [List.flatMap_append,List.flatMap_singleton]
    rw [List.getLast?_append_of_ne_nil _ (word_ne_nil Γ mark h2 d)]
    simp only [List.getLast?_concat,Option.map_some,word_last]

/-- The closing passage of a cyclically immersed path survives suppression. -/
theorem closing (ds : List B)
    (hc : ∀ᵉ (x∈(ds.flatMap w).getLast?) (y∈(ds.flatMap w).head?),
      PortWalk.step Γ.origin Γ.reverse x y) :
    ∀ᵉ (a∈ds.getLast?) (b∈ds.head?),PortWalk.step (S).origin (S).reverse a b := by
  intro a ha b hb
  have hl : Γ.reverse ((S).reverse a).val ∈ (ds.flatMap w).getLast? := by
    rw [flatMap_last]
    exact Option.mem_map_of_mem _ ha
  have hh : b.val ∈ (ds.flatMap w).head? := by
    rw [flatMap_head]
    exact Option.mem_map_of_mem _ hb
  have he := hc _ hl _ hh
  simp only [PortWalk.step] at he
  rw [Γ.reverse_reverse] at he
  exact ⟨he.1,fun h => he.2 (congrArg Subtype.val h)⟩

/-- The decomposition retains all reduced passages and both geometric
endpoints. Cyclic closing passages therefore also transport unchanged. -/
theorem decomposes (p : List D)
    (hp : p.IsChain (PortWalk.step Γ.origin Γ.reverse))
    (hs : ∀ d∈p.head?,mark (Γ.origin d))
    (ht : ∀ d∈p.getLast?,mark (Γ.origin (Γ.reverse d))) :
    ∃ ds : List B, ds.flatMap w=p ∧
      ds.IsChain (PortWalk.step (S).origin (S).reverse) ∧
      ds.head?.map Subtype.val=p.head? ∧
      ds.getLast?.map (fun d => Γ.reverse ((S).reverse d).val)=p.getLast? := by
  obtain ⟨ds,hd⟩ := path_decomposes Γ mark h2 p hp hs ht
  refine ⟨ds,hd,isChain Γ mark h2 ds (hd.symm ▸ hp),?_,?_⟩
  · rw [←flatMap_head,hd]
  · rw [←flatMap_last,hd]

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

lemma same_word {a b : B} {x : D} (ha : x∈ChainPaths.word Γ mark h2 a)
    (hb : x∈ChainPaths.word Γ mark h2 b) : a=b := by
  by_contra h
  exact ChainPaths.words_disjoint Γ mark h2 h ha hb

variable [Fintype V]

end TorsionFreeZeroDivisors.ChainIsomorphism

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChunkComparisons
open scoped Classical
open ComparedBlocks
variable {P T U C : Type*} {lp : P → ℕ} {lt : T → ℕ}

namespace Chunking
end Chunking

variable [Fintype T] (color : T → C)

/-- Exact color-fibre enumeration, identifying the literal path traversals
with the multiplicity-indexed traversal type used in every stage estimate. -/
def enumeration : ((c : C) × Fin (multiplicity color c)) ≃ T :=
  (Equiv.sigmaCongrRight (fun c => (Fintype.equivFin {t // color t=c}).symm)).trans
    (Equiv.sigmaFiberEquiv color)

end TorsionFreeZeroDivisors.ChunkComparisons

namespace TorsionFreeZeroDivisors.ListChunkCoordinates
open scoped Classical BigOperators
open FiniteChunking
variable {A D : Type*} (ds : List A) (word : A → List D)

end TorsionFreeZeroDivisors.ListChunkCoordinates

namespace TorsionFreeZeroDivisors.ChainChunkTransport
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChunkComparisons FiniteChunking ComparedBlocks
open scoped Classical BigOperators
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "τ" => turn Γ.origin mark h2
local notation "F" => next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "S" => suppressed Γ mark h2
local notation "len" => chainLength Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "w" => word Γ mark h2

def reversed (b : B) : Bool := ((orientation Γ mark h2).symm b).2

lemma oriented (b : B) : b=if reversed Γ mark h2 b then (S).reverse (representative Γ mark h2 b).val
    else (representative Γ mark h2 b).val := (orientation Γ mark h2).apply_symm_apply b |>.symm

lemma oriented_length (b : B) : len b=len (representative Γ mark h2 b).val := by
  have h := oriented Γ mark h2 b
  conv_lhs => rw [h]
  split_ifs <;> simp only [chainLength_reverse]

variable {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})

omit [Fintype P] in
lemma originalDart_get (x : Position (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths))) :
    ((paths x.1).flatMap w)[x.2.val.toNat]?=some (originalDart Γ mark h2 paths x) :=
  List.getElem?_eq_getElem _

variable {E : Type*}
    (cmp : Comparisons (E:=E) (pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)))
    (lo hi : E → ℤ) (hlo : ∀ e,cmp.lo e=(lo e:ℝ)) (hhi : ∀ e,cmp.hi e=(hi e:ℝ))

end TorsionFreeZeroDivisors.ChainChunkTransport

namespace TorsionFreeZeroDivisors.ChainMultiplicity
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2

lemma representative_val (c : R) : representative Γ mark h2 c.val=c := by
  change ((orientation Γ mark h2).symm ((orientation Γ mark h2) (c,false))).1=c
  rw [Equiv.symm_apply_apply]

lemma reverse_oriented (b : B) :
    (S).reverse b=(orientation Γ mark h2) (representative Γ mark h2 b,!(reversed Γ mark h2 b)) := by
  have h := oriented Γ mark h2 b
  cases hr : reversed Γ mark h2 b
  · simp only [hr,Bool.false_eq_true,ite_false] at h
    change (S).reverse b=(S).reverse (representative Γ mark h2 b).val
    exact congrArg (S).reverse h
  · simp only [hr,ite_true] at h
    change (S).reverse b=(representative Γ mark h2 b).val
    calc
      _ = (S).reverse ((S).reverse (representative Γ mark h2 b).val) := congrArg (S).reverse h
      _ = _ := (S).reverse_reverse _

lemma representative_reverse (b : B) : representative Γ mark h2 ((S).reverse b)=representative Γ mark h2 b := by
  rw [reverse_oriented]
  change ((orientation Γ mark h2).symm ((orientation Γ mark h2) _)).1=_
  rw [Equiv.symm_apply_apply]

variable {P : Type*} [Fintype P]
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d})

local notation "col" => color Γ mark h2 paths
local notation "tp" => Traversal (chunks Γ mark h2 paths)

end TorsionFreeZeroDivisors.ChainMultiplicity

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChainActiveStages
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "col" => color Γ mark h2 paths

variable [Fintype V]

end TorsionFreeZeroDivisors.ChainActiveStages

namespace TorsionFreeZeroDivisors.SubdivisionRestriction
open scoped Classical
variable {C V : Type*} (len : C → ℕ) (first last : C → V)
    (active : C → Prop) (incident : V → Prop)
    (hf : ∀ c,active c → incident (first c))
    (hl : ∀ c,active c → incident (last c))

end TorsionFreeZeroDivisors.SubdivisionRestriction

namespace TorsionFreeZeroDivisors.ChainStageEmbedding
open scoped Classical BigOperators
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    {P : Type*} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)
local notation "S" => suppressed Γ mark h2
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "col" => color Γ mark h2 paths

end TorsionFreeZeroDivisors.ChainStageEmbedding

namespace TorsionFreeZeroDivisors.RootPins
open scoped Classical BigOperators
variable {V T : Type*} [Fintype V]

omit [Fintype V] in
lemma respects {root : Option V} {target : T} (f : V → T)
    (h : ∀ v,root=some v → f v=target) :
    ∀ v y,pin root target v=some y → f v=y := by
  intro v y hy
  unfold pin at hy
  split_ifs at hy with hv
  · cases Option.some.inj hy
    exact h v hv

end TorsionFreeZeroDivisors.RootPins

namespace TorsionFreeZeroDivisors.ActiveRoot
open scoped Classical
open PortSubdivision
variable {V D P : Type*} [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (paths : P → List D) (hp : ∀ p,paths p≠[])

end TorsionFreeZeroDivisors.ActiveRoot

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

theorem carrier_eq (rep : ℕ) : (carrier rep : ℝ) = (size rep : ℝ)*(129/16513) := by
  simp only [carrier,size,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring

theorem L_ratio : Tendsto (fun n : ℕ => (L n : ℝ)/n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one,one_mul,add_zero,Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have h := hlog.div_const 100
  simp only [zero_div] at h
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ h
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hL : (L n:ℝ)≤Real.log (n:ℝ)/100 := Nat.floor_le (by positivity [Real.log_nonneg hn'])
  calc
    (L n:ℝ)/n ≤ (Real.log (n:ℝ)/100)/n := div_le_div_of_nonneg_right hL (by positivity)
    _ = (Real.log (n:ℝ)/n)/100 := by ring

theorem spent_ratio (K : ℕ) : Tendsto
    (fun rep => ((K*L (size rep)+exclusion (size rep):ℕ):ℝ)/(size rep)) atTop (𝓝 0) := by
  have h := ((L_ratio.comp size_tendsto).const_mul (K:ℝ)).add (exclusion_ratio.comp size_tendsto)
  simpa only [mul_zero,add_zero,Nat.cast_add,Nat.cast_mul,add_div,mul_div_assoc,Function.comp_def] using h

theorem eventually_room (K : ℕ) : ∀ᶠ rep in atTop,
    K*L (size rep)+exclusion (size rep)<carrier rep := by
  have h := (spent_ratio K).eventually_lt_const (by norm_num : (0:ℝ)<129/16513)
  filter_upwards [h,size_tendsto.eventually (eventually_ge_atTop 1)] with rep hh hn
  have hn0 : (0:ℝ)<size rep := by exact_mod_cast (show 0<size rep by omega)
  have hh' := (div_lt_iff₀ hn0).mp hh
  rw [mul_comm (129/16513:ℝ) (size rep),← carrier_eq] at hh'
  exact_mod_cast hh'

theorem denominator_ratio (K : ℕ) : Tendsto
    (fun rep => (denominator K rep:ℝ)/(size rep)) atTop (𝓝 (129/16513)) := by
  have h := (tendsto_const_nhds (x := (129/16513:ℝ))).sub (spent_ratio K)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_room K,size_tendsto.eventually (eventually_ge_atTop 1)] with rep hr hn
  have hn0 : (size rep:ℝ)≠0 := by exact_mod_cast (show size rep≠0 by omega)
  change (129/16513:ℝ) - _ = _
  rw [denominator,Nat.cast_sub hr.le,sub_div,carrier_eq,mul_div_cancel_left₀ _ hn0]

theorem relative_ratio (K : ℕ) : Tendsto
    (fun rep => ((size rep:ℝ)*(129/16513))/(denominator K rep)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (129/16513:ℝ))).div (denominator_ratio K) (by norm_num)
  norm_num only [div_self (by norm_num : (129/16513:ℝ)≠0)] at h
  apply h.congr'
  apply Eventually.of_forall
  intro rep
  change (129/16513:ℝ) / ((denominator K rep:ℝ)/(size rep)) = _
  rw [div_div_eq_mul_div]
  ring

theorem penalty_tendsto (K : ℕ) : Tendsto (penalty K) atTop (𝓝 0) := by
  change Tendsto (fun rep => Real.log ((size rep:ℝ)*(129/16513)/(denominator K rep))) _ _
  have h := (Real.continuousAt_log one_ne_zero).tendsto.comp (relative_ratio K)
  simpa only [Real.log_one,Function.comp_def] using h

theorem error_ratio (K Q : ℕ) : Tendsto
    (fun rep => error K Q rep / (L (size rep):ℝ)) atTop (𝓝 0) := by
  have hL : Tendsto (fun rep => (L (size rep):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (L_tendsto.comp size_tendsto)
  have hconst := (tendsto_inv_atTop_zero.comp hL).const_mul ((Q:ℝ)*(-Real.log (129/16513)))
  have hpen := (penalty_tendsto K).const_mul (K:ℝ)
  have h := hconst.add hpen
  simp only [mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [(L_tendsto.comp size_tendsto).eventually (eventually_ge_atTop 1)] with rep hn
  change 1≤L (size rep) at hn
  have hn0 : (L (size rep):ℝ)≠0 := by exact_mod_cast (show L (size rep)≠0 by omega)
  simp only [error,Function.comp_def]
  field_simp

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

theorem R_pos (d : ℕ) {L : ℝ} (hL : 1 ≤ L) : 0 < R d L := by
  apply Nat.floor_pos.mpr
  apply Real.le_sqrt_of_sq_le
  norm_num
  exact_mod_cast N_pos d hL

theorem R_le_N (d : ℕ) {L : ℝ} (hL : 1 ≤ L) : R d L ≤ N d L := by
  apply Nat.floor_le_of_le
  apply Real.sqrt_le_iff.mpr
  have hn : (1 : ℝ) ≤ N d L := by exact_mod_cast N_pos d hL
  constructor <;> nlinarith

theorem denominator_le_sqrt (d : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    ((N d L : ℝ)^d * R d L) ≤ Real.sqrt L := by
  have hn : (N d L : ℝ) ≤ L ^ exponent d := Nat.floor_le (Real.rpow_nonneg (by linarith) _)
  have hr : (R d L : ℝ) ≤ N d L := by exact_mod_cast R_le_N d hL
  calc
    _ ≤ (N d L : ℝ)^d * N d L := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = (N d L : ℝ)^(d+1) := (pow_succ _ _).symm
    _ ≤ (L ^ exponent d)^(d+1) := pow_le_pow_left₀ (by positivity) hn _
    _ = L ^ ((1:ℝ)/2) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0 ≤ L)]
      congr 1
      push_cast
      unfold exponent
      field_simp
    _ = Real.sqrt L := (Real.sqrt_eq_rpow _).symm

theorem scale_bounds (d : ℕ) {L : ℝ} (hL : 1 ≤ L) {u : ℕ}
    (hu : 1 ≤ u) (hub : u ≤ (N d L)^d) :
    Real.sqrt L ≤ scale d L u ∧ scale d L u / L ≤ 1/(R d L : ℝ) := by
  have hLp : 0 < L := by linarith
  have hRp : (0 : ℝ) < R d L := by exact_mod_cast R_pos d hL
  have hup : (0 : ℝ) < u := by exact_mod_cast hu
  have huR : ((u : ℝ)*R d L) ≤ Real.sqrt L := by
    have hubr : (u : ℝ) ≤ (N d L : ℝ)^d := by exact_mod_cast hub
    apply le_trans (mul_le_mul_of_nonneg_right hubr hRp.le)
    simpa using denominator_le_sqrt d hL
  constructor
  · unfold scale
    apply (le_div_iff₀ (mul_pos hup hRp)).mpr
    have hs := Real.sq_sqrt hLp.le
    have ht := mul_le_mul_of_nonneg_left huR (Real.sqrt_nonneg L)
    nlinarith
  · have hs : scale d L u ≤ L / (R d L : ℝ) := by
      unfold scale
      apply div_le_div_of_nonneg_left hLp.le hRp
      have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
      nlinarith
    apply (div_le_iff₀ hLp).mpr
    simpa [div_eq_mul_inv,mul_comm] using hs

theorem N_tendsto (d : ℕ) : Tendsto (fun L : ℝ => (N d L : ℝ)) atTop atTop := by
  exact (tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop).comp
    (tendsto_rpow_atTop (exponent_pos d))

theorem R_tendsto (d : ℕ) : Tendsto (fun L : ℝ => (R d L : ℝ)) atTop atTop := by
  exact (tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop).comp
    (Real.tendsto_sqrt_atTop.comp (N_tendsto d))

theorem alignment_error_tendsto (d : ℕ) :
    Tendsto (fun L : ℝ => (R d L : ℝ)/(N d L : ℝ)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun L : ℝ => 1 / Real.sqrt (N d L)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (N_tendsto d))
  apply squeeze_zero' (Eventually.of_forall (fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    (eventually_atTop.mpr ⟨1,fun L hL => ?_⟩) hupper
  have hn : (0 : ℝ) < N d L := by exact_mod_cast N_pos d hL
  have hs := Real.sqrt_pos.mpr hn
  have hr : (R d L : ℝ) ≤ Real.sqrt (N d L) := Nat.floor_le (Real.sqrt_nonneg _)
  apply (div_le_div_iff₀ hn hs).mpr
  have ht := mul_le_mul_of_nonneg_right hr hs.le
  have he := Real.sq_sqrt hn.le
  nlinarith

theorem chosen_spec (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    Compatible d L offset (chosenU d L offset) := by
  unfold chosenU
  rw [dif_pos hL]
  exact Nat.find_spec _

theorem chosen_min (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) {v : ℕ}
    (hv : Compatible d L offset v) : chosenU d L offset ≤ v := by
  unfold chosenU
  rw [dif_pos hL]
  exact Nat.find_min' _ hv

theorem chosen_bound (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    chosenU d L offset ≤ (N d L)^d := by
  obtain ⟨u,hu,hub,z,hz⟩ := BlockGrid.simultaneous (N_pos d hL) (fun i => (offset i : ℝ)/L)
  exact (chosen_min d hL offset ⟨hu,z,hz⟩).trans hub

theorem chosenScale_pos (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    0 < chosenScale d L offset := by
  exact lt_of_lt_of_le (Real.sqrt_pos.mpr (by linarith))
    (scale_bounds d hL (chosen_spec d hL offset).1 (chosen_bound d hL offset)).1

theorem letterError_bounds (d : ℕ) {L : ℝ} (hL : 1 ≤ L) (offset : Fin d → ℤ) :
    2*((R d L : ℝ)/(N d L))*chosenScale d L offset+4 ≤ letterError d L offset ∧
    (letterError d L offset : ℝ) ≤
      2*((R d L : ℝ)/(N d L))*chosenScale d L offset+5 := by
  constructor
  · exact Nat.le_ceil _
  · have hs := chosenScale_pos d hL offset
    have hh := Nat.ceil_lt_add_one (show 0 ≤
        2*((R d L : ℝ)/(N d L))*chosenScale d L offset+4 by
        positivity)
    dsimp only [letterError]
    linarith

end TorsionFreeZeroDivisors.GridAsymptotics

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GridUniform
open scoped Topology BigOperators
open Filter GridAsymptotics

theorem rate_tendsto (d : ℕ) : Tendsto (rate d) atTop (𝓝 0) := by
  have hr : Tendsto (fun L : ℝ => 1/(R d L:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (R_tendsto d)
  have hs : Tendsto (fun L : ℝ => 1/Real.sqrt L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hi : Tendsto (fun L : ℝ => 1/L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  unfold rate
  simpa only [add_zero] using ((hr.add hs).add (alignment_error_tendsto d)).add hi

/-- A single offset-independent rate controls every scalar rounding loss. -/
theorem bounds (d : ℕ) {L : ℝ} (hL : 1≤L) (offset : Fin d → ℤ) :
    chosenScale d L offset/L ≤ rate d L ∧
    1/chosenScale d L offset ≤ rate d L ∧
    (letterError d L offset:ℝ)/chosenScale d L offset ≤ 5*rate d L ∧
    1/L ≤ rate d L := by
  have hL0 : 0<L := by linarith
  have hs := chosenScale_pos d hL offset
  have hroot := Real.sqrt_pos.mpr hL0
  have hb := scale_bounds d hL (chosen_spec d hL offset).1 (chosen_bound d hL offset)
  change Real.sqrt L ≤ chosenScale d L offset ∧
    chosenScale d L offset/L ≤ 1/(R d L:ℝ) at hb
  have hi : 1/chosenScale d L offset ≤ 1/Real.sqrt L :=
    one_div_le_one_div_of_le hroot hb.1
  have he : (letterError d L offset:ℝ)/chosenScale d L offset ≤
      2*((R d L:ℝ)/(N d L))+5/chosenScale d L offset := by
    apply (div_le_iff₀ hs).mpr
    have hh := (letterError_bounds d hL offset).2
    have hh' : (2*((R d L:ℝ)/(N d L))+5/chosenScale d L offset)*chosenScale d L offset =
        2*((R d L:ℝ)/(N d L))*chosenScale d L offset+5 := by field_simp
    rwa [hh']
  have hr : 0 ≤ 1/(R d L:ℝ) := by positivity
  have hn : 0 ≤ (R d L:ℝ)/(N d L) := by positivity
  have hlo : 0 ≤ 1/L := by positivity
  have hso : 0 ≤ 1/Real.sqrt L := by positivity
  unfold rate
  simp only [div_eq_mul_inv,one_mul] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

/-- Unlike a chosen offset sequence, this statement is uniform over ALL
integer comparison offsets at each common length scale. -/
theorem eventually_geometry (d : ℕ) : ∀ᶠ L in atTop, ∀ offset : Fin d → ℤ,
    3003 ≤ chosenScale d L offset ∧
    2*(letterError d L offset:ℝ) < chosenScale d L offset-1 := by
  have hr := (rate_tendsto d).eventually_lt_const (by norm_num : (0:ℝ)<1/12)
  have hroot := Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (3003:ℝ))
  filter_upwards [hr,hroot,eventually_ge_atTop (1:ℝ)] with L hr hroot hL offset
  have hb := bounds d hL offset
  have hs := chosenScale_pos d hL offset
  have hlo := (scale_bounds d hL (chosen_spec d hL offset).1 (chosen_bound d hL offset)).1
  change Real.sqrt L ≤ chosenScale d L offset at hlo
  have he := (div_le_iff₀ hs).mp hb.2.2.1
  have hi := (div_le_iff₀ hs).mp hb.2.1
  refine ⟨hroot.trans hlo,?_⟩
  nlinarith
end TorsionFreeZeroDivisors.GridUniform
namespace TorsionFreeZeroDivisors.StageUniform
open scoped Classical BigOperators Topology
open BlockAlignment ComparedBlocks RepeatedBlocks GridAsymptotics Filter

variable {C E : Type*} [Fintype C] [Fintype E]

open GirthAsymptotics TypedGraphs

end TorsionFreeZeroDivisors.StageUniform
namespace TorsionFreeZeroDivisors.GridUniform
open scoped Topology BigOperators
open Filter GridAsymptotics

theorem binRate_tendsto : Tendsto binRate atTop (𝓝 0) := by
  have hc : Tendsto (fun L : ℝ => Real.log 257/Real.sqrt L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  have he : (fun L : ℝ => Real.log L / L^(1/2:ℝ)) =
      (fun L : ℝ => Real.log L/Real.sqrt L) := by
    funext L
    rw [Real.sqrt_eq_rpow]
  rw [he] at hl
  unfold binRate
  simpa only [add_div,add_zero] using hc.add hl

end TorsionFreeZeroDivisors.GridUniform
namespace TorsionFreeZeroDivisors.BinProfiles
open scoped Classical
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C E : Type*} [Fintype C] [Fintype E]

end TorsionFreeZeroDivisors.BinProfiles

namespace TorsionFreeZeroDivisors.RealizationTransport
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings PatternEmbeddings
variable {PV PD TV T : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]

variable {Γ : PortGraph PV PD} {plabel : PD → T} {outgoing : TV → Finset T}
    {pin : PV → Option TV} {bar : T → T} {r : Matching (label outgoing) bar}
    (e : Embedding Γ plabel outgoing pin bar r)

variable {PV' PD' : Type*} [Fintype PV'] [Fintype PD']

end TorsionFreeZeroDivisors.RealizationTransport

namespace TorsionFreeZeroDivisors.TwoSideStage
open scoped Classical BigOperators
variable {W : Type*}

end TorsionFreeZeroDivisors.TwoSideStage

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

/-- Restriction needs only injectivity, not a bijection onto the whole image.
In particular, inactive marked vertices are never carried into a stage. -/
def restrict (Q : PortGraph QV QD) (fv : QV ↪ PV) (fd : QD ↪ PD)
    (ho : ∀ d,fv (Q.origin d)=Γ.origin (fd d))
    (hr : ∀ d,fd (Q.reverse d)=Γ.reverse (fd d)) (pin' : QV → Option TV)
    (hp : ∀ v y,pin' v=some y → pin (fv v)=some y) :
    Embedding Q (plabel ∘ fd) outgoing pin' bar r where
  vertex := fv.trans e.vertex
  port := fd.trans e.port
  origin_eq d := by simpa only [Function.Embedding.trans_apply,ho] using e.origin_eq (fd d)
  label_eq d := e.label_eq (fd d)
  reverse_eq d := by simpa only [Function.Embedding.trans_apply,hr] using e.reverse_eq (fd d)
  pin_eq v y hy := e.pin_eq (fv v) y (hp v y hy)

end TorsionFreeZeroDivisors.RealizationTransport

namespace TorsionFreeZeroDivisors.ActualStageRealization
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
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
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
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
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons
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
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
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
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking
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

namespace TorsionFreeZeroDivisors.PatternUniform
open scoped Classical Topology BigOperators
open Filter GridAsymptotics GirthAsymptotics TypedGraphs

theorem eventually_ready (K M Q J : ℕ) (hM : 0<M) :
    ∀ᶠ rep in atTop,Ready K M Q J rep := by
  have hL : Tendsto (fun rep => (L (size rep):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (L_tendsto.comp size_tendsto)
  have hb := (GridUniform.binRate_tendsto.comp hL).eventually_lt_const
    (show (0:ℝ)<1/(4800*M:ℝ) by positivity)
  have hd (d : Fin (J+1)) : ∀ᶠ rep in atTop,
      StageUniform.coefficient d.val K M Q*GridUniform.rate d.val (L (size rep))+
        M*StageDenominator.error K Q rep/(L (size rep):ℝ) ≤ 1/4800 ∧
      ∀ offset : Fin d.val → ℤ,3003≤chosenScale d.val (L (size rep)) offset ∧
        2*(letterError d.val (L (size rep)) offset:ℝ)<chosenScale d.val (L (size rep)) offset-1 := by
    have hr := ((GridUniform.rate_tendsto d.val).comp hL).const_mul
      (StageUniform.coefficient d.val K M Q)
    have he := (StageDenominator.error_ratio K Q).const_mul (M:ℝ)
    have ht := hr.add he
    simp only [mul_zero,add_zero] at ht
    have hevent := ht.eventually_lt_const (by norm_num : (0:ℝ)<1/4800)
    filter_upwards [hevent,hL.eventually (GridUniform.eventually_geometry d.val)] with rep hr hg
    refine ⟨?_,hg⟩
    simpa only [Function.comp_def,mul_div_assoc] using hr.le
  filter_upwards [eventually_all.mpr hd,hb,StageDenominator.eventually_room K,
    hL.eventually (eventually_ge_atTop (1:ℝ)),size_tendsto.eventually (eventually_ge_atTop 1)]
    with rep hd hb hr hL hn
  exact ⟨hL,by omega,hr,hb.le,fun d hd' => hd ⟨d,by omega⟩⟩

variable {C E : Type*} [Fintype C] [Fintype E]

end TorsionFreeZeroDivisors.PatternUniform

namespace TorsionFreeZeroDivisors.ActualPatternEvent
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking
open ComparedBlocks RepeatedBlocks GridAsymptotics GirthAsymptotics TypedGraphs
variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2

variable [Fintype E]

end TorsionFreeZeroDivisors.ActualPatternEvent

namespace TorsionFreeZeroDivisors.OriginalPattern
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking
open ComparedBlocks RepeatedBlocks GridAsymptotics GirthAsymptotics TypedGraphs ActualPatternEvent
variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "pl" => pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)

variable [Fintype E]

end TorsionFreeZeroDivisors.OriginalPattern

namespace TorsionFreeZeroDivisors.ComparisonGeometry
open scoped Classical
open BlockAlignment ComparedBlocks ChunkComparisons
variable {P P' E E' : Type*} {len : P → ℕ} {len' : P' → ℕ}

def position (e : P ≃ P') (hl : ∀ p,len p=len' (e p)) : Position len ≃ Position len' :=
  Equiv.sigmaCongr e (fun p => Equiv.subtypeEquivRight (fun q => by rw [hl p]))

structure Iso (C : Comparisons (E:=E) len) (C' : Comparisons (E:=E') len') where
  path : P ≃ P'
  comparison : E ≃ E'
  length_eq : ∀ p,len p=len' (path p)
  flip_eq : ∀ j,comparison (C.flip j)=C'.flip (comparison j)
  source_eq : ∀ j,path (C.source j)=C'.source (comparison j)
  lo_eq : ∀ j,C.lo j=C'.lo (comparison j)
  hi_eq : ∀ j,C.hi j=C'.hi (comparison j)
  reverse_eq : ∀ j,C.reverse j=C'.reverse (comparison j)
  offset_eq : ∀ j,C.offset j=C'.offset (comparison j)

namespace Iso
variable {C : Comparisons (E:=E) len} {C' : Comparisons (E:=E') len'} (f : Iso C C')

lemma side_some (x : Position len) (j : E) :
    C'.side ((position f.path f.length_eq) x)=some (f.comparison j) ↔ C.side x=some j := by
  rw [C'.side_iff,C.side_iff]
  change (f.path x.1=C'.source (f.comparison j) ∧ x.2.val∈positions (C'.lo (f.comparison j)) (C'.hi (f.comparison j))) ↔ _
  rw [←f.source_eq,←f.lo_eq,←f.hi_eq,f.path.injective.eq_iff]

lemma side_eq (x : Position len) :
    C'.side ((position f.path f.length_eq) x)=(C.side x).map f.comparison := by
  cases h : C.side x with
  | some j => simpa only [Option.map_some] using (f.side_some x j).mpr h
  | none =>
    simp only [Option.map_none]
    cases h' : C'.side ((position f.path f.length_eq) x) with
    | none => rfl
    | some j =>
      have hh := (f.side_some x (f.comparison.symm j)).mp (by simpa only [Equiv.apply_symm_apply] using h')
      rw [h] at hh
      contradiction

lemma partner_eq (x : Position len) :
    position f.path f.length_eq (C.pairing.partner x)=
      C'.pairing.partner (position f.path f.length_eq x) := by
  cases h : C.side x with
  | none =>
    have h' : C'.side (position f.path f.length_eq x)=none := by rw [f.side_eq,h]; rfl
    rw [(C.none_iff x).mp h,(C'.none_iff _).mp h']
  | some j =>
    have h' := (f.side_some x j).mpr h
    apply position_ext
    · change f.path (C.pairing.partner x).1=_
      rw [C.partner_source _ _ h,C'.partner_source _ _ h',←f.flip_eq,f.source_eq]
    · change (C.pairing.partner x).2.val=_
      rw [C.partner_coordinate _ _ h,C'.partner_coordinate _ _ h',f.reverse_eq,f.offset_eq]
      rfl

end Iso
end TorsionFreeZeroDivisors.ComparisonGeometry

namespace TorsionFreeZeroDivisors.PortSubdivision

namespace Iso
variable {V D V' D' V'' D'' : Type*} {Γ : PortGraph V D} {Γ' : PortGraph V' D'} {Γ'' : PortGraph V'' D''}
end Iso
end TorsionFreeZeroDivisors.PortSubdivision

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PatternTotalCoding
open scoped Classical
open PatternCoding

variable {D V P E D' V' P' E' : Type*}
    [Fintype D] [Fintype V] [Fintype P] [Fintype E]
    [Fintype D'] [Fintype V'] [Fintype P'] [Fintype E']
    (R K T I H : ℕ) (hR : 0<R) (hK : 0<K) (hI : 0<I)
    (hD : Fintype.card D≤R) (hV : Fintype.card V≤R)
    (hP : Fintype.card P≤K) (hE : Fintype.card E≤I)

variable (hD' : Fintype.card D'≤R) (hV' : Fintype.card V'≤R)
    (hP' : Fintype.card P'≤K) (hE' : Fintype.card E'≤I)

end TorsionFreeZeroDivisors.PatternTotalCoding

namespace TorsionFreeZeroDivisors.BoundedPattern
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks

attribute [instance] Data.fV Data.fD Data.fP Data.fE

namespace Data
variable {R K T I H : ℕ} (a : Data R K T I H)

end Data
end TorsionFreeZeroDivisors.BoundedPattern

namespace TorsionFreeZeroDivisors.PatternFiniteUnion
open scoped Classical

end TorsionFreeZeroDivisors.PatternFiniteUnion

namespace TorsionFreeZeroDivisors.BoundedPattern.Data

section
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
variable {R K T I H : ℕ} (a b : Data R K T I H)

end

open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks ActualPatternEvent
open GridAsymptotics GirthAsymptotics TypedGraphs
variable {R K T I H : ℕ} (a : Data R K T I H)

end TorsionFreeZeroDivisors.BoundedPattern.Data

namespace TorsionFreeZeroDivisors.BoundedPattern
open scoped Classical
open ActualPatternEvent GirthAsymptotics TypedGraphs

end TorsionFreeZeroDivisors.BoundedPattern

namespace TorsionFreeZeroDivisors.ActualComplexity
open scoped Classical BigOperators
open PortSubdivision DegreeTwoSuppression CoreStripping ImageComplexity
open ChainSuppression SuppressedMoore ChainPaths ChainIsomorphism ChainChunkTransport
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P] (Γ : PortGraph V D)

omit [Fintype V] in
lemma leaf_unique {v : V} (hv : degree Γ Finset.univ v=1) {a b : D}
    (ha : Γ.origin a=v) (hb : Γ.origin b=v) : a=b := by
  obtain ⟨d,hd⟩ := Finset.card_eq_one.mp hv
  have hma : a∈Finset.univ.filter (fun d => Γ.origin d=v) := by simp [ha]
  have hmb : b∈Finset.univ.filter (fun d => Γ.origin d=v) := by simp [hb]
  change Finset.univ.filter (fun d => Γ.origin d=v)={d} at hd
  rw [hd] at hma hmb
  exact (Finset.mem_singleton.mp hma).trans (Finset.mem_singleton.mp hmb).symm

omit [Fintype V] in
lemma step_not_leaf {a b : D} (h : WeightedMoore.PortWalk.step Γ.origin Γ.reverse a b) :
    degree Γ Finset.univ (Γ.origin b)≠1 ∧ degree Γ Finset.univ (Γ.origin (Γ.reverse a))≠1 := by
  constructor <;> intro he
  · exact h.2 (leaf_unique Γ he rfl h.1)
  · exact h.2 (leaf_unique Γ he h.1.symm rfl)

omit [Fintype V] in
lemma origin_leaf_head (p : List D)
    (hp : p.IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
    {d : D} (hd : d∈p) (hv : degree Γ Finset.univ (Γ.origin d)=1) : d∈p.head? := by
  induction p with
  | nil => simp at hd
  | cons a p ih =>
    rcases List.mem_cons.mp hd with rfl|hd
    · simp
    · have hh := ih hp.tail hd
      cases p with
      | nil => simp at hd
      | cons b p =>
        have he : b=d := by simpa using hh
        subst d
        exact ((step_not_leaf Γ (List.isChain_cons_cons.mp hp).1).1 hv).elim

omit [Fintype V] in
lemma target_leaf_last (p : List D)
    (hp : p.IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
    {d : D} (hd : d∈p) (hv : degree Γ Finset.univ (Γ.origin (Γ.reverse d))=1) :
    d∈p.getLast? := by
  induction p with
  | nil => simp at hd
  | cons a p ih =>
    cases p with
    | nil => simpa only [List.getLast?_singleton,Option.mem_some_iff] using (List.mem_singleton.mp hd).symm
    | cons b p =>
      rcases List.mem_cons.mp hd with rfl|hd
      · exact ((step_not_leaf Γ (List.isChain_cons_cons.mp hp).1).2 hv).elim
      · simpa only [List.getLast?_cons_cons] using ih hp.tail hd

variable (paths : P → List D) (hp : ∀ p,paths p≠[])
def start (p : P) : D := (paths p).head (hp p)
def finish (p : P) : D := (paths p).getLast (hp p)
def endpoints : Finset V :=
  (Finset.univ.image fun p => Γ.origin (start paths hp p)) ∪
    (Finset.univ.image fun p => Γ.origin (Γ.reverse (finish paths hp p)))

omit [Fintype V] [Fintype D] in
lemma endpoints_card : (endpoints Γ paths hp).card≤2*Fintype.card P := by
  exact (Finset.card_union_le _ _).trans (by
    have ha := Finset.card_image_le (s:=Finset.univ) (f:=fun p => Γ.origin (start paths hp p))
    have hb := Finset.card_image_le (s:=Finset.univ) (f:=fun p => Γ.origin (Γ.reverse (finish paths hp p)))
    rw [Finset.card_univ] at ha hb
    omega)

omit [Fintype V] [Fintype D] in
lemma start_mem (p : P) {d : D} (hd : d∈(paths p).head?) : Γ.origin d∈endpoints Γ paths hp := by
  have he : start paths hp p=d := by
    simpa only [start,List.head?_eq_some_head (hp p),Option.mem_some_iff] using hd
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,congrArg Γ.origin he⟩

omit [Fintype V] [Fintype D] in
lemma finish_mem (p : P) {d : D} (hd : d∈(paths p).getLast?) :
    Γ.origin (Γ.reverse d)∈endpoints Γ paths hp := by
  have he : finish paths hp p=d := by
    simpa only [finish,List.getLast?_eq_some_getLast (hp p),Option.mem_some_iff] using hd
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,congrArg (fun d => Γ.origin (Γ.reverse d)) he⟩

include hp in
lemma leaf_bound
    (hc : ∀ p,(paths p).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
    (hi : ∀ d,∃ p,d∈paths p ∨ Γ.reverse d∈paths p) :
    (Finset.univ.filter (fun v => degree Γ Finset.univ v=1)).card≤2*Fintype.card P := by
  apply (Finset.card_le_card ?_).trans (endpoints_card Γ paths hp)
  intro v hv
  have hv := (Finset.mem_filter.mp hv).2
  obtain ⟨d,hd⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter (fun d => Γ.origin d=v)).card by
    change 0<degree Γ Finset.univ v
    omega)
  have ho := (Finset.mem_filter.mp hd).2
  obtain ⟨p,hp'⟩ := hi d
  rcases hp' with hm|hm
  · exact ho ▸ start_mem Γ paths hp p (origin_leaf_head Γ _ (hc p) hm (ho ▸ hv))
  · have he : degree Γ Finset.univ (Γ.origin (Γ.reverse (Γ.reverse d)))=1 := by simpa [ho] using hv
    have ht := finish_mem Γ paths hp p (target_leaf_last Γ _ (hc p) hm he)
    rw [Γ.reverse_reverse d,ho] at ht
    exact ht

omit [Fintype V] in
lemma dart_count (hi : ∀ d,∃ p,d∈paths p ∨ Γ.reverse d∈paths p) :
    Fintype.card D≤2*∑ p,(paths p).length := by
  let f : ((p : P) × Fin (paths p).length) × Bool → D := fun o =>
    if o.2 then Γ.reverse ((paths o.1.1).get o.1.2) else (paths o.1.1).get o.1.2
  have hs : Function.Surjective f := by
    intro d
    obtain ⟨p,hp⟩ := hi d
    rcases hp with hp|hp
    · obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
      exact ⟨(⟨p,i⟩,false),hi⟩
    · obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
      refine ⟨(⟨p,i⟩,true),?_⟩
      change Γ.reverse ((paths p).get i)=d
      rw [hi,Γ.reverse_reverse]
  have hh := Fintype.card_le_of_surjective f hs
  simpa only [Fintype.card_prod,Fintype.card_bool,Fintype.card_sigma,Fintype.card_fin,Nat.mul_comm] using hh

lemma marked_vertices_le (mark : V → Prop)
    (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (hv : Function.Surjective Γ.origin) :
    Fintype.card (Mark mark)≤Fintype.card {d : D // turn Γ.origin mark h2 d=d} := by
  let f : {d : D // turn Γ.origin mark h2 d=d} → Mark mark := fun d =>
    ⟨Γ.origin d.val,(turn_fixed_iff Γ.origin mark h2 d.val).mp d.property⟩
  apply Fintype.card_le_of_surjective f
  intro v
  obtain ⟨d,hd⟩ := hv v.val
  refine ⟨⟨d,turn_of_mark Γ.origin mark h2 d (hd ▸ v.property)⟩,?_⟩
  exact Subtype.ext hd

end TorsionFreeZeroDivisors.ActualComplexity

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ChainUsage
open scoped Classical BigOperators
open PortSubdivision DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity
variable {V D P : Type} [Fintype D] [Fintype P] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
local notation "B" => {d : D // turn Γ.origin mark h2 d=d}
local notation "S" => suppressed Γ mark h2
local notation "R" => Rep Γ mark h2
local notation "w" => word Γ mark h2
variable (paths : P → List {d : D // turn Γ.origin mark h2 d=d})
local notation "col" => color Γ mark h2 paths
local notation "m" => ChunkComparisons.multiplicity col

def Used : Prop := ∀ d,∃ p,d∈(paths p).flatMap w ∨ Γ.reverse d∈(paths p).flatMap w

omit [Fintype P] in
lemma representative_used (hu : Used Γ mark h2 paths) (c : R) :
    ∃ p b,b∈paths p ∧ representative Γ mark h2 b=c := by
  obtain ⟨p,hp⟩ := hu c.val.val
  rcases hp with hp|hp
  · obtain ⟨b,hb,he⟩ := List.mem_flatMap.mp hp
    have heq := same_word Γ mark h2 he (start_mem_word Γ mark h2 c.val)
    exact ⟨p,b,hb,heq ▸ representative_val Γ mark h2 c⟩
  · obtain ⟨b,hb,he⟩ := List.mem_flatMap.mp hp
    have heq := same_word Γ mark h2 he
      (reverse_mem_word Γ mark h2 c.val c.val.val (start_mem_word Γ mark h2 c.val))
    exact ⟨p,b,hb,by rw [heq,representative_reverse,representative_val]⟩

lemma multiplicity_pos (hu : Used Γ mark h2 paths) (c : R) : 1 ≤ m c := by
  simp only [ChunkComparisons.multiplicity,Fintype.card_eq_nat_card]
  obtain ⟨p,b,hb,he⟩ := representative_used Γ mark h2 paths hu c
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hb
  have hn : Nonempty {t // col t=c} := by
    refine ⟨⟨⟨p,i⟩,?_⟩⟩
    change representative Γ mark h2 ((paths p).get i)=c
    rw [hi,he]
  exact Nat.card_pos

lemma traversal_card : Fintype.card (RepeatedBlocks.Traversal m)=∑p,(paths p).length := by
  rw [Fintype.card_congr (ChunkComparisons.enumeration col)]
  simp only [FiniteChunking.Traversal,chunks]
  exact (Fintype.card_sigma (α:=fun p : P => Fin (paths p).length)).trans (Finset.sum_congr rfl (fun p _ => Fintype.card_fin _))

lemma multiplicity_le (c : R) : m c≤∑p,(paths p).length := by
  simp only [ChunkComparisons.multiplicity,Fintype.card_eq_nat_card]
  have h := Nat.card_le_card_of_injective (Subtype.val : {t // col t=c} → _)
    Subtype.val_injective
  simpa only [FiniteChunking.Traversal,chunks,Nat.card_sigma,Nat.card_fin] using h

omit [Fintype D] [Fintype P] in
lemma flatMap_length_le {A Z : Type*} (f : A → List Z) (l : List A) {a : A} (ha : a∈l) :
    (f a).length≤(l.flatMap f).length := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl|ha
    · simp only [List.flatMap_cons,List.length_append]
      omega
    · have h := ih ha
      simp only [List.flatMap_cons,List.length_append]
      omega

lemma length_le_total_of_mem (p : P) (b : B) (hb : b∈paths p) :
    chainLength Γ mark h2 b≤∑p,((paths p).flatMap w).length := by
  rw [←word_length]
  exact (flatMap_length_le w _ hb).trans
    (Finset.single_le_sum (f:=fun p => ((paths p).flatMap w).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ p))

lemma chain_length_le (hu : Used Γ mark h2 paths) (b : B) :
    chainLength Γ mark h2 b≤∑p,((paths p).flatMap w).length := by
  obtain ⟨p,a,ha,he⟩ := representative_used Γ mark h2 paths hu (representative Γ mark h2 b)
  have h := length_le_total_of_mem Γ mark h2 paths p a ha
  rw [oriented_length Γ mark h2 a,he,←oriented_length Γ mark h2 b] at h
  exact h

lemma rep_card_le : Fintype.card R≤Fintype.card B := Fintype.card_subtype_le _

end TorsionFreeZeroDivisors.ChainUsage

namespace TorsionFreeZeroDivisors.SourcePattern
open scoped Classical BigOperators
open PortSubdivision MarkedChainBound DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open ActualComplexity CoreStripping ImageComplexity GirthAsymptotics TypedGraphs

/-- The uniformly bounded number of marked darts is derived, not required of an
original pattern. Extra marks are just the prescribed path endpoints. -/
theorem marked_bound (B K : ℕ) : ∃ R : ℕ,0<R ∧
    ∀ {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
      (Γ : PortGraph V D) (M : Finset V) (_hM : M.card≤2*K)
      (paths : P → List D) (_hp : ∀ p,paths p≠[])
      (_ : Fintype.card P≤K) (_ : Function.Surjective Γ.origin)
      (_ : ∀ p,(paths p).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))
      (_ : ∀ d,∃ p,d∈paths p ∨ Γ.reverse d∈paths p)
      (L : ℝ) (_ : 0<L) (_ : (∑ p,(paths p).length:ℕ)≤(B:ℝ)*L)
      (_ : ∀ a (c : Γ.subdivision.Walk a a),c.IsCycle →
        L≤WeightedCycles.weight (WeightedPortMoore.edgeWeight (fun _ : D => (1:ℝ))) c),
      Fintype.card {d : D // turn Γ.origin (marks Γ M) (marks_degree_two Γ M) d=d}≤R ∧
        Fintype.card (Mark (marks Γ M))≤R := by
  obtain ⟨R,hR⟩ := bounded_image_branches (B:ℝ) (Nat.cast_nonneg _) (2*K)
  refine ⟨R+6*K+1,by omega,?_⟩
  intro V D P _ _ _ Γ M hM paths hp hP hv hc hi L hL hH hg
  have hleaf := leaf_bound Γ paths hp hc hi
  have hdc := dart_count Γ paths hi
  have hdc' : (Fintype.card D:ℝ)≤2*(B:ℝ)*L := by
    have hdc' : (Fintype.card D:ℝ)≤2*(∑ p,(paths p).length:ℕ) := by exact_mod_cast hdc
    nlinarith
  have hleaf' : (Finset.univ.filter (fun v => degree Γ Finset.univ v=1)).card≤2*K :=
    hleaf.trans (Nat.mul_le_mul_left _ hP)
  have hb := hR Γ L hL hdc' hg hleaf'
  have hd := marked_dart_bound Γ M
  have hseed : Fintype.card {d : D //
      turn Γ.origin (marks Γ M) (marks_degree_two Γ M) d=d}≤R+6*K+1 := by
    rw [chain_dart_card]
    omega
  exact ⟨hseed,(marked_vertices_le Γ _ _ hv).trans hseed⟩

abbrev Seeds {V D : Type} [Fintype D] (Γ : PortGraph V D) (M : Finset V) :=
  {d : D // turn Γ.origin (marks Γ M) (marks_degree_two Γ M) d=d}

def R (B K : ℕ) : ℕ := (marked_bound B K).choose
lemma R_pos (B K : ℕ) : 0<R B K := (marked_bound B K).choose_spec.1
def T (B K : ℕ) : ℕ := R B K*(B+K)

/-- The actual suppressed form of source paths. No bound on the resulting
skeleton, chain lengths, multiplicities or number of traversals is assumed. -/
structure Data (B K I rep : ℕ) where
  V : Type
  D : Type
  P : Type
  E : Type
  [fV : Fintype V]
  [fD : Fintype D]
  [fP : Fintype P]
  [fE : Fintype E]
  graph : PortGraph V D
  vertices : Finset V
  vertices_bound : vertices.card≤2*K
  no_isolated : Function.Surjective graph.origin
  side : V → Bool
  side_edge : ∀ d,side (graph.origin (graph.reverse d))=side (graph.origin d)
  paths : P → List (Seeds graph vertices)
  nonempty : ∀ p,paths p≠[]
  root : Option P
  path_bound : Fintype.card P≤K
  comparison_bound : Fintype.card E≤I
  image : ChainUsage.Used graph (marks graph vertices) (marks_degree_two graph vertices) paths
  path_chain : ∀ p,((paths p).flatMap (word graph (marks graph vertices) (marks_degree_two graph vertices))).IsChain
    (WeightedMoore.PortWalk.step graph.origin graph.reverse)
  cyclic_chain : ∀ p,StageRoot.cyclic root p=true →
    ∀ᵉ (x∈((paths p).flatMap (word graph (marks graph vertices) (marks_degree_two graph vertices))).getLast?)
        (y∈((paths p).flatMap (word graph (marks graph vertices) (marks_degree_two graph vertices))).head?),
      WeightedMoore.PortWalk.step graph.origin graph.reverse x y
  girth : ∀ a (c : graph.subdivision.Walk a a),c.IsCycle →
    (L (size rep):ℝ)≤WeightedCycles.weight (WeightedPortMoore.edgeWeight (fun _ : D => (1:ℝ))) c
  length_le : (∑p,((paths p).flatMap (word graph (marks graph vertices) (marks_degree_two graph vertices))).length:ℕ)≤B*L (size rep)
  length_ge : L (size rep)≤(∑p,((paths p).flatMap (word graph (marks graph vertices) (marks_degree_two graph vertices))).length:ℕ)
  comparisons : Comparisons (E:=E) (pathLength (chunks graph (marks graph vertices) (marks_degree_two graph vertices) paths)
    (chunkLength graph (marks graph vertices) (marks_degree_two graph vertices) paths))
  lower : E → ℕ
  upper : E → ℕ
  lower_eq : ∀ e,comparisons.lo e=lower e
  upper_eq : ∀ e,comparisons.hi e=upper e
  lower_le : ∀ e,lower e≤upper e
  upper_le : ∀ e,upper e≤pathLength (chunks graph (marks graph vertices) (marks_degree_two graph vertices) paths)
    (chunkLength graph (marks graph vertices) (marks_degree_two graph vertices) paths) (comparisons.source e)
  reduced : ∀ x e,comparisons.side x=some e →
    originalDart graph (marks graph vertices) (marks_degree_two graph vertices) paths x≠
      originalDart graph (marks graph vertices) (marks_degree_two graph vertices) paths (comparisons.pairing.partner x) ∧
    originalDart graph (marks graph vertices) (marks_degree_two graph vertices) paths x≠graph.reverse
      (originalDart graph (marks graph vertices) (marks_degree_two graph vertices) paths (comparisons.pairing.partner x))
  unpaired_le : ((Finset.univ.filter (fun x => comparisons.pairing.partner x=x)).card:ℝ)≤
    StageFusion.epsilon (1/600) 256*
      (∑p,((paths p).flatMap (word graph (marks graph vertices) (marks_degree_two graph vertices))).length:ℕ)

attribute [instance] Data.fV Data.fD Data.fP Data.fE

namespace Data
variable {B K I rep : ℕ} (a : Data B K I rep)
abbrev mark := marks a.graph a.vertices
abbrev degree_two := marks_degree_two a.graph a.vertices
abbrev words (p : a.P) := (a.paths p).flatMap (word a.graph a.mark a.degree_two)
abbrev totalLength : ℕ := ∑p,(a.words p).length
abbrev lengths : a.P → ℕ := pathLength (chunks a.graph a.mark a.degree_two a.paths)
  (chunkLength a.graph a.mark a.degree_two a.paths)

lemma words_nonempty (p : a.P) : a.words p≠[] := by
  intro he
  obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil (a.paths p) (a.nonempty p)
  have hm : b.val∈a.words p := by
    apply List.mem_flatMap.mpr
    exact ⟨b,hb,start_mem_word a.graph a.mark a.degree_two b⟩
  simp [he] at hm

lemma lengths_le (p : a.P) : a.lengths p≤B*L (size rep) := by
  rw [lengths,pathLength_eq]
  apply le_trans (b:=a.totalLength) _ a.length_le
  exact Finset.single_le_sum (f:=fun p => (a.words p).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)

lemma upper_bound (e : a.E) : a.upper e≤B*L (size rep) :=
  (a.upper_le e).trans (a.lengths_le _)

lemma lower_bound (e : a.E) : a.lower e≤B*L (size rep) :=
  (a.lower_le e).trans (a.upper_bound e)

lemma covered : ∀ d,ChainCoverage.Covered a.graph.reverse (turn a.graph.origin a.mark a.degree_two)
    a.graph.reverse_reverse (turn_involutive a.graph.origin a.mark a.degree_two) d := by
  apply ActualMarkedChains.actual_image_covered a.graph a.mark a.degree_two a.words a.path_chain _ a.image
  intro p d hd
  rw [words,ChainPathTransport.flatMap_head] at hd
  obtain ⟨b,_hb,hbd⟩ := Option.mem_map.mp hd
  subst d
  exact (turn_fixed_iff a.graph.origin a.mark a.degree_two b.val).mp b.property

lemma mark_bounds (hL : 0<L (size rep)) :
    Fintype.card (Seeds a.graph a.vertices)≤R B K ∧ Fintype.card (Mark a.mark)≤R B K := by
  apply (marked_bound B K).choose_spec.2 a.graph a.vertices a.vertices_bound a.words
    a.words_nonempty a.path_bound a.no_isolated a.path_chain a.image (L (size rep))
    (by exact_mod_cast hL) _ a.girth
  exact_mod_cast a.length_le

lemma total_traversals_le (hL : 0<L (size rep)) : ∑p,(a.paths p).length≤T B K := by
  have h := ChainPaths.bounded_chain_traversals a.graph a.mark a.degree_two
    (B:ℝ) (Nat.cast_nonneg _) K (R B K) a.path_bound (a.mark_bounds hL).1
    (L (size rep)) (by exact_mod_cast hL) a.girth a.paths a.path_chain
    (by exact_mod_cast a.length_le)
  have he : (R B K:ℝ)*((B:ℝ)+K)=(T B K:ℝ) := by simp only [T,Nat.cast_mul,Nat.cast_add]
  rw [he,Nat.ceil_natCast] at h
  exact h

lemma traversal_le (hL : 0<L (size rep)) (p : a.P) : (a.paths p).length≤T B K :=
  (Finset.single_le_sum (f:=fun p => (a.paths p).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)).trans (a.total_traversals_le hL)

lemma offset_bounds (e : a.E) :
    -(2*(B*L (size rep):ℕ):ℤ)≤a.comparisons.offset e ∧
      a.comparisons.offset e≤(2*(B*L (size rep):ℕ):ℤ) := by
  have hlo : (0:ℝ)≤a.comparisons.lo e := by rw [a.lower_eq]; positivity
  have hhi : (0:ℝ)≤a.comparisons.hi e := by rw [a.upper_eq]; positivity
  have hlb : a.comparisons.lo e≤(B*L (size rep):ℕ) := by
    rw [a.lower_eq]; exact_mod_cast a.lower_bound e
  have hub : a.comparisons.hi e≤(B*L (size rep):ℕ) := by
    rw [a.upper_eq]; exact_mod_cast a.upper_bound e
  have hlen : (a.lengths (a.comparisons.source (a.comparisons.flip e)):ℝ)≤(B*L (size rep):ℕ) :=
    by exact_mod_cast a.lengths_le _
  have hr := a.comparisons.target_range e
  have he : -2*((B*L (size rep):ℕ):ℝ)≤(a.comparisons.offset e:ℝ) ∧
      (a.comparisons.offset e:ℝ)≤2*((B*L (size rep):ℕ):ℝ) := by
    cases hh : a.comparisons.reverse e <;> simp only [hh,Bool.false_eq_true,↓reduceIte] at hr
    · constructor <;> linarith
    · constructor <;> linarith
  exact_mod_cast he

def bounded (hL : 0<L (size rep)) : BoundedPattern.Data (R B K) K (T B K) I (B*L (size rep)) where
  V := a.V
  D := a.D
  P := a.P
  E := a.E
  graph := a.graph
  mark := a.mark
  degree_two := a.degree_two
  covered := a.covered
  side := a.side
  side_edge := a.side_edge
  paths := a.paths
  nonempty := a.nonempty
  root := a.root
  comparisons := a.comparisons
  lower e := ⟨a.lower e,by have := a.lower_bound e; omega⟩
  upper e := ⟨a.upper e,by have := a.upper_bound e; omega⟩
  offset e := ⟨(a.comparisons.offset e+2*(B*L (size rep):ℕ)).toNat,by
    obtain ⟨hl,hu⟩ := a.offset_bounds e
    omega⟩
  lower_eq := a.lower_eq
  upper_eq := a.upper_eq
  offset_eq e := by
    obtain ⟨hl,hu⟩ := a.offset_bounds e
    dsimp
    omega
  dart_bound := (a.mark_bounds hL).1
  vertex_bound := (a.mark_bounds hL).2
  path_bound := a.path_bound
  comparison_bound := a.comparison_bound
  chain_length_bound d := (ChainUsage.chain_length_le a.graph a.mark a.degree_two a.paths a.image d).trans a.length_le
  traversal_bound := a.traversal_le hL

lemma bounded_good (hL : 0<L (size rep)) :
    (a.bounded hL).Good B (R B K) (T B K) (I*(T B K)^2) rep where
  multiplicity_le c := (ChainUsage.multiplicity_le a.graph a.mark a.degree_two a.paths c).trans
    (a.total_traversals_le hL)
  multiplicity_pos := ChainUsage.multiplicity_pos a.graph a.mark a.degree_two a.paths a.image
  path_chain p := ChainPathTransport.isChain a.graph a.mark a.degree_two (a.paths p) (a.path_chain p)
  cyclic_chain p hp := ChainPathTransport.closing a.graph a.mark a.degree_two (a.paths p) (a.cyclic_chain p hp)
  reduced := a.reduced
  chains_le := (ChainUsage.rep_card_le a.graph a.mark a.degree_two).trans (a.mark_bounds hL).1
  cut_comparisons_le := by
    change Fintype.card a.E*(Fintype.card (RepeatedBlocks.Traversal
      (ChunkComparisons.multiplicity (color a.graph a.mark a.degree_two a.paths))))^2≤_
    rw [ChainUsage.traversal_card]
    exact Nat.mul_le_mul a.comparison_bound (Nat.pow_le_pow_left (a.total_traversals_le hL) 2)
  length_le := by
    change (∑p,(a.words p).length:ℝ)≤_
    exact_mod_cast a.length_le
  length_ge := by
    change _≤(∑p,(a.words p).length:ℝ)
    exact_mod_cast a.length_ge
  unpaired_le := by
    change _≤StageFusion.epsilon (1/600) 256*(∑p,(a.words p).length:ℝ)
    exact_mod_cast a.unpaired_le

end Data
end TorsionFreeZeroDivisors.SourcePattern

namespace TorsionFreeZeroDivisors.BoundedPattern
open scoped Classical Topology
open Filter GirthAsymptotics TypedGraphs ActualPatternEvent

lemma polynomial_exp_tendsto (c B d M : ℕ) (hM : 0<M) :
    Tendsto (fun rep => (c:ℝ)*(B*L (size rep)+1:ℕ)^d*
      Real.exp (-(L (size rep):ℝ)/(4800*M))) atTop (𝓝 0) := by
  have hL : Tendsto (fun rep => (L (size rep):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (L_tendsto.comp size_tendsto)
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d:ℝ)
    (1/(4800*M)) (by positivity)).comp hL
  simp only [Function.comp_def,Real.rpow_natCast] at ht
  have ht' := ht.const_mul ((c:ℝ)*(B+1:ℝ)^d)
  simp only [mul_zero] at ht'
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ ht'
  filter_upwards [hL.eventually (eventually_ge_atTop (1:ℝ))] with rep hr
  have hp : ((B*L (size rep)+1:ℕ):ℝ)^d≤((B+1:ℝ)*(L (size rep):ℝ))^d := by
    gcongr
    push_cast
    nlinarith
  calc
    _ ≤ (c:ℝ)*((B+1:ℝ)*(L (size rep):ℝ))^d*
        Real.exp (-(L (size rep):ℝ)/(4800*M)) := by gcongr
    _ = (c:ℝ)*(B+1:ℝ)^d*((L (size rep):ℝ)^d*
        Real.exp (-(1/(4800*M:ℝ))*(L (size rep):ℝ))) := by
      have he : -(L (size rep):ℝ)/(4800*M)=-(1/(4800*M:ℝ))*(L (size rep):ℝ) := by ring
      rw [he,mul_pow]
      ring

lemma mem_samples (rep : ℕ) (r : Match rep) : r∈samples rep ↔
    (r.1.Contains ∅ ∧ ((3*L (size rep):ℕ):ℕ∞)≤(r.1.graph (PatternEmbeddings.origin (@Types.outgoingA rep))).subdivision.egirth) ∧
    (r.2.Contains ∅ ∧ ((3*L (size rep):ℕ):ℕ∞)≤(r.2.graph (PatternEmbeddings.origin (@Types.outgoingB rep))).subdivision.egirth) := by
  simp only [samples,ConditionedMatchings.Matching.conditioned,Finset.mem_product,
    Finset.mem_filter,Finset.mem_univ,true_and]

lemma samples_eventually_nonempty : ∀ᶠ rep in atTop,(samples rep).Nonempty := by
  filter_upwards [TypedGraphs.eventual_nonempty] with rep hr
  obtain ⟨a,ha⟩ := hr.1
  obtain ⟨b,hb⟩ := hr.2
  simp only [ConditionedMatchings.Matching.conditioned, Finset.mem_filter,
    Finset.mem_univ, true_and] at ha hb
  refine ⟨(a,b),(mem_samples rep (a,b)).mpr ?_⟩
  exact ⟨ha,hb⟩

end TorsionFreeZeroDivisors.BoundedPattern

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.RawDecomposition
open scoped Classical BigOperators
open PortSubdivision MarkedChainBound DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open ActualComplexity CoreStripping ImageComplexity GirthAsymptotics TypedGraphs
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (raw : P → List D) (hp : ∀ p,raw p≠[])
    (hc : ∀ p,(raw p).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))

abbrev marks := ActualComplexity.endpoints Γ raw hp
abbrev mark := MarkedChainBound.marks Γ (marks Γ raw hp)
abbrev degree_two := marks_degree_two Γ (marks Γ raw hp)
abbrev Seeds := SourcePattern.Seeds Γ (marks Γ raw hp)

include hc in
omit [Fintype V] in
lemma decomposition (p : P) : ∃ ds : List (Seeds Γ raw hp),
    ds.flatMap (word Γ (mark Γ raw hp) (degree_two Γ raw hp))=raw p := by
  obtain ⟨ds,hd,_⟩ := ChainPathTransport.decomposes Γ (mark Γ raw hp) (degree_two Γ raw hp)
    (raw p) (hc p) (fun d hd => Or.inr (start_mem Γ raw hp p hd))
    (fun d hd => Or.inr (finish_mem Γ raw hp p hd))
  exact ⟨ds,hd⟩

def paths (p : P) : List (Seeds Γ raw hp) := (decomposition Γ raw hp hc p).choose
omit [Fintype V] in
lemma expands (p : P) : (paths Γ raw hp hc p).flatMap (word Γ (mark Γ raw hp) (degree_two Γ raw hp))=raw p :=
  (decomposition Γ raw hp hc p).choose_spec
omit [Fintype V] in
lemma nonempty (p : P) : paths Γ raw hp hc p≠[] := by
  intro he
  have hx := expands Γ raw hp hc p
  rw [he,List.flatMap_nil] at hx
  exact hp p hx.symm

abbrev lengths := pathLength (chunks Γ (mark Γ raw hp) (degree_two Γ raw hp) (paths Γ raw hp hc))
  (chunkLength Γ (mark Γ raw hp) (degree_two Γ raw hp) (paths Γ raw hp hc))
omit [Fintype V] in
lemma length_eq (p : P) : lengths Γ raw hp hc p=(raw p).length := by
  rw [lengths,pathLength_eq,expands]
omit [Fintype V] in
lemma lengths_eq : lengths Γ raw hp hc=(fun p => (raw p).length) := funext (length_eq Γ raw hp hc)

omit [Fintype D] [Fintype P] in
lemma dart_get (x : Position (fun p => (raw p).length)) :
    (raw x.1)[x.2.val.toNat]?=some (dart raw x) := List.getElem?_eq_getElem _

def position : Position (lengths Γ raw hp hc) ≃ Position (fun p => (raw p).length) :=
  ComparisonGeometry.position (Equiv.refl P) (length_eq Γ raw hp hc)
omit [Fintype V] in
lemma dart_eq (x : Position (lengths Γ raw hp hc)) :
    originalDart Γ (mark Γ raw hp) (degree_two Γ raw hp) (paths Γ raw hp hc) x=
      dart raw (position Γ raw hp hc x) := by
  apply Option.some.inj
  rw [←originalDart_get,expands,←dart_get]
  rfl

omit [Fintype V] in
lemma source_eq (root : Option P) :
    StageRoot.source Γ (mark Γ raw hp) (degree_two Γ raw hp) (paths Γ raw hp hc)
      (nonempty Γ raw hp hc) root = root.map (fun p => Γ.origin ((raw p).head (hp p))) := by
  cases root with
  | none => rfl
  | some p =>
    change some (Γ.origin ((paths Γ raw hp hc p).head (nonempty Γ raw hp hc p)).val)=_
    have he := ChainPathTransport.flatMap_head Γ (mark Γ raw hp) (degree_two Γ raw hp) (paths Γ raw hp hc p)
    rw [expands,List.head?_eq_some_head (hp p),
      List.head?_eq_some_head (nonempty Γ raw hp hc p),Option.map_some] at he
    exact congrArg (fun d => some (Γ.origin d)) (Option.some.inj he).symm

end TorsionFreeZeroDivisors.RawDecomposition

namespace TorsionFreeZeroDivisors.ComparisonGeometry

section
open scoped Classical
open ComparedBlocks ChunkComparisons
variable {P E : Type} {l l' : P → ℕ}

def cast (h : l=l') (c : Comparisons (E:=E) l) : Comparisons (E:=E) l' := h ▸ c

variable [Fintype P]
lemma Iso.unpaired {c : Comparisons (E:=E) l} {c' : Comparisons (E:=E) l'} (f : Iso c c') :
    (Finset.univ.filter (fun x => c.pairing.partner x=x)).card=
    (Finset.univ.filter (fun x => c'.pairing.partner x=x)).card := by
  rw [←Fintype.card_subtype,←Fintype.card_subtype]
  apply Fintype.card_congr
  exact (position f.path f.length_eq).subtypeEquiv (fun x => by
    rw [←f.partner_eq,(position f.path f.length_eq).injective.eq_iff])
end
open scoped Classical
open ComparedBlocks ChunkComparisons
variable {P E : Type} {l l' : P → ℕ}
def castBackIso (h : l'=l) (c : Comparisons (E:=E) l) : Iso (cast h.symm c) c where
  path := Equiv.refl P
  comparison := Equiv.refl E
  length_eq p := congrFun h p
  flip_eq := by cases h; exact fun _ => rfl
  source_eq := by cases h; exact fun _ => rfl
  lo_eq := by cases h; exact fun _ => rfl
  hi_eq := by cases h; exact fun _ => rfl
  reverse_eq := by cases h; exact fun _ => rfl
  offset_eq := by cases h; exact fun _ => rfl
end TorsionFreeZeroDivisors.ComparisonGeometry

namespace TorsionFreeZeroDivisors.RawSourcePattern

section
open scoped Classical BigOperators
open PortSubdivision MarkedChainBound DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open ActualComplexity CoreStripping ImageComplexity GirthAsymptotics TypedGraphs ActualPatternEvent

/-- The data of a literal bounded family of immersed graph paths. The finite
image graph is arbitrary; only the source's bounds on path and comparison
counts, total length and proportion of unpaired letters are stated here. -/
structure Data (B K I rep : ℕ) where
  V : Type
  D : Type
  P : Type
  E : Type
  [fV : Fintype V]
  [fD : Fintype D]
  [fP : Fintype P]
  [fE : Fintype E]
  graph : PortGraph V D
  no_isolated : Function.Surjective graph.origin
  side : V → Bool
  side_edge : ∀ d,side (graph.origin (graph.reverse d))=side (graph.origin d)
  paths : P → List D
  nonempty : ∀ p,paths p≠[]
  root : Option P
  path_bound : Fintype.card P≤K
  comparison_bound : Fintype.card E≤I
  image : ∀ d,∃ p,d∈paths p ∨ graph.reverse d∈paths p
  path_chain : ∀ p,(paths p).IsChain (WeightedMoore.PortWalk.step graph.origin graph.reverse)
  cyclic_chain : ∀ p,StageRoot.cyclic root p=true →
    ∀ᵉ (x∈(paths p).getLast?) (y∈(paths p).head?),
      WeightedMoore.PortWalk.step graph.origin graph.reverse x y
  girth : ∀ a (c : graph.subdivision.Walk a a),c.IsCycle →
    (L (size rep):ℝ)≤WeightedCycles.weight (WeightedPortMoore.edgeWeight (fun _ : D => (1:ℝ))) c
  length_le : (∑p,(paths p).length:ℕ)≤B*L (size rep)
  length_ge : L (size rep)≤(∑p,(paths p).length:ℕ)
  comparisons : Comparisons (E:=E) (fun p => (paths p).length)
  lower : E → ℕ
  upper : E → ℕ
  lower_eq : ∀ e,comparisons.lo e=lower e
  upper_eq : ∀ e,comparisons.hi e=upper e
  lower_le : ∀ e,lower e≤upper e
  upper_le : ∀ e,upper e≤(paths (comparisons.source e)).length
  reduced : ∀ x e,comparisons.side x=some e →
    RawDecomposition.dart paths x≠RawDecomposition.dart paths (comparisons.pairing.partner x) ∧
    RawDecomposition.dart paths x≠graph.reverse (RawDecomposition.dart paths (comparisons.pairing.partner x))
  unpaired_le : ((Finset.univ.filter (fun x => comparisons.pairing.partner x=x)).card:ℝ)≤
    StageFusion.epsilon (1/600) 256*(∑p,(paths p).length:ℕ)
attribute [instance] Data.fV Data.fD Data.fP Data.fE

namespace Data
variable {B K I rep : ℕ} (a : Data B K I rep)
abbrev vertices := ActualComplexity.endpoints a.graph a.paths a.nonempty
abbrev mark := MarkedChainBound.marks a.graph a.vertices
abbrev degree_two := marks_degree_two a.graph a.vertices
abbrev decomposed := RawDecomposition.paths a.graph a.paths a.nonempty a.path_chain
abbrev decomposed_nonempty := RawDecomposition.nonempty a.graph a.paths a.nonempty a.path_chain
abbrev lengths_eq := RawDecomposition.lengths_eq a.graph a.paths a.nonempty a.path_chain
abbrev comparison := ComparisonGeometry.cast a.lengths_eq.symm a.comparisons
abbrev iso := ComparisonGeometry.castBackIso a.lengths_eq a.comparisons
abbrev position := RawDecomposition.position a.graph a.paths a.nonempty a.path_chain

lemma expands (p : a.P) : (a.decomposed p).flatMap (word a.graph a.mark a.degree_two)=a.paths p :=
  RawDecomposition.expands a.graph a.paths a.nonempty a.path_chain p
lemma length_eq (p : a.P) : pathLength (chunks a.graph a.mark a.degree_two a.decomposed)
    (chunkLength a.graph a.mark a.degree_two a.decomposed) p=(a.paths p).length :=
  RawDecomposition.length_eq a.graph a.paths a.nonempty a.path_chain p
lemma dart_eq (x : Position (pathLength (chunks a.graph a.mark a.degree_two a.decomposed)
    (chunkLength a.graph a.mark a.degree_two a.decomposed))) :
    originalDart a.graph a.mark a.degree_two a.decomposed x=RawDecomposition.dart a.paths (a.position x) :=
  RawDecomposition.dart_eq a.graph a.paths a.nonempty a.path_chain x
lemma position_iso : a.position=ComparisonGeometry.position a.iso.path a.iso.length_eq := rfl

/-- All suppression data is constructed from the literal paths, with no bounds
on a suppressed skeleton included among the raw data. -/
def suppressed : SourcePattern.Data B K I rep where
  V := a.V
  D := a.D
  P := a.P
  E := a.E
  graph := a.graph
  vertices := a.vertices
  vertices_bound := (ActualComplexity.endpoints_card a.graph a.paths a.nonempty).trans
    (Nat.mul_le_mul_left 2 a.path_bound)
  no_isolated := a.no_isolated
  side := a.side
  side_edge := a.side_edge
  paths := a.decomposed
  nonempty := a.decomposed_nonempty
  root := a.root
  path_bound := a.path_bound
  comparison_bound := a.comparison_bound
  image := by
    intro d
    simpa only [expands] using a.image d
  path_chain := by simpa only [expands] using a.path_chain
  cyclic_chain := by simpa only [expands] using a.cyclic_chain
  girth := a.girth
  length_le := by simpa only [expands] using a.length_le
  length_ge := by simpa only [expands] using a.length_ge
  comparisons := a.comparison
  lower := a.lower
  upper := a.upper
  lower_eq e := (a.iso.lo_eq e).trans (a.lower_eq e)
  upper_eq e := (a.iso.hi_eq e).trans (a.upper_eq e)
  lower_le := a.lower_le
  upper_le e := by
    rw [a.length_eq]
    have hs : a.comparison.source e=a.comparisons.source e := a.iso.source_eq e
    rw [hs]
    exact a.upper_le e
  reduced := by
    intro x e he
    have hh := a.reduced (a.position x) e ((a.iso.side_some x e).mpr he)
    rw [a.dart_eq,a.dart_eq,position_iso,a.iso.partner_eq]
    exact hh
  unpaired_le := by
    rw [a.iso.unpaired]
    simpa only [expands] using a.unpaired_le

/-- The event reads the literal original path label, and pins the actual initial
vertex of the exceptional interval on its prescribed side. -/
def event (x : Types.VertexA rep) (y : Types.VertexB rep) (r : Match rep) : Prop :=
  ∃ label : a.D → Types.Letter,
    (∀ d,label (a.graph.reverse d)=Types.inverse (label d)) ∧
    (∀ d e,a.graph.origin d=a.graph.origin e → label d=label e → d=e) ∧
    (∀ p e,a.comparisons.side p=some e → label (RawDecomposition.dart a.paths p)=
      if a.comparisons.reverse e then Types.inverse (label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p)))
      else label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p))) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph a.graph a.side a.side_edge true)
      (fun d => label d.val) (@Types.outgoingA rep)
      (RootPins.pin (SidePins.root a.side (a.root.map fun p => a.graph.origin ((a.paths p).head (a.nonempty p))) true) x)
      Types.inverse r.1) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph a.graph a.side a.side_edge false)
      (fun d => label d.val) (@Types.outgoingB rep)
      (RootPins.pin (SidePins.root a.side (a.root.map fun p => a.graph.origin ((a.paths p).head (a.nonempty p))) false) y)
      Types.inverse r.2)

lemma suppressed_event (x : Types.VertexA rep) (y : Types.VertexB rep) (r : Match rep)
    (h : a.event x y r) :
    OriginalPattern.Realized a.graph a.mark a.degree_two a.side a.side_edge a.decomposed
      a.decomposed_nonempty a.root rep x y a.comparison r := by
  rcases h with ⟨label,hl,hn,hc,ha,hb⟩
  refine ⟨label,hl,hn,?_,?_,?_⟩
  · intro p e he
    have hh := hc (a.position p) e ((a.iso.side_some p e).mpr he)
    rw [a.dart_eq,a.dart_eq,position_iso,a.iso.partner_eq,a.iso.reverse_eq]
    exact hh
  · simpa only [sourcePinA,RawDecomposition.source_eq] using ha
  · simpa only [sourcePinB,RawDecomposition.source_eq] using hb

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

variable {label : D → T} {bar : T → T}

end TorsionFreeZeroDivisors.DiameterCounting

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypedDiameter
open Filter ConditionedMatchings MatchingDiameter
open GirthAsymptotics TypedGraphs TorsionFreeZeroDivisors.Types
open scoped Topology Classical BigOperators

theorem diameterA_tendsto :
    Tendsto (fun rep : ℕ => (diameterBadA rep).card/((ΩA rep).card:ℝ)) atTop (𝓝 0) :=
  diameter_tendsto.1



theorem diameterB_tendsto :
    Tendsto (fun rep : ℕ => (diameterBadB rep).card/((ΩB rep).card:ℝ)) atTop (𝓝 0) :=
  diameter_tendsto.2



end TorsionFreeZeroDivisors.TypedDiameter
namespace TorsionFreeZeroDivisors.FiniteJointAvoidance
open scoped Classical
lemma exists_outside {A B : Type} (s : Finset A) (t : Finset B) (a : Finset A) (b : Finset B)
    (P : A×B → Prop) (hs : s.Nonempty) (ht : t.Nonempty)
    (hp : (((s×ˢt).filter P).card:ℝ)/(s.card*t.card:ℕ)<1/3)
    (ha : (a.card:ℝ)/s.card<1/3) (hb : (b.card:ℝ)/t.card<1/3) :
    ∃ r∈s×ˢt,r.1∉a ∧ r.2∉b ∧ ¬P r := by
  by_contra hn
  push Not at hn
  have hsub : s×ˢt ⊆ ((s×ˢt).filter P) ∪ ((a×ˢt) ∪ (s×ˢb)) := by
    intro r hr
    by_cases hp : P r
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr,hp⟩)
    apply Finset.mem_union_right
    have hh := hn r hr
    have hm := Finset.mem_product.mp hr
    by_cases he : r.1∈a
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨he,hm.2⟩)
    · have hf : r.2∈b := by by_contra hb; exact hp (hh he hb)
      exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hm.1,hf⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hc' := Finset.card_union_le (a×ˢt) (s×ˢb)
  rw [Finset.card_product] at hc
  simp only [Finset.card_product] at hc'
  have hc'' : s.card*t.card≤((s×ˢt).filter P).card+a.card*t.card+s.card*b.card := by omega
  have hsr : (0:ℝ)<s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have htr : (0:ℝ)<t.card := by exact_mod_cast Finset.card_pos.mpr ht
  have hpr := (div_lt_iff₀ (mul_pos hsr htr)).mp (by simpa only [Nat.cast_mul] using hp)
  have har := mul_lt_mul_of_pos_right ((div_lt_iff₀ hsr).mp ha) htr
  have hbr := mul_lt_mul_of_pos_left ((div_lt_iff₀ htr).mp hb) hsr
  have hcr : (s.card:ℝ)*t.card≤((s×ˢt).filter P).card+a.card*t.card+s.card*b.card := by exact_mod_cast hc''
  nlinarith
end TorsionFreeZeroDivisors.FiniteJointAvoidance

namespace TorsionFreeZeroDivisors.MatchingAlias
open scoped Classical
end TorsionFreeZeroDivisors.MatchingAlias

namespace TorsionFreeZeroDivisors.GraphSample
open scoped Classical
open GirthAsymptotics TypedGraphs ActualPatternEvent Filter

lemma samples_eq (rep : ℕ) : samples rep = TypedDiameter.ΩA rep ×ˢ TypedDiameter.ΩB rep := by
  apply Finset.ext
  intro r
  rw [BoundedPattern.mem_samples]
  erw [Finset.mem_product]
  simp only [TypedDiameter.ΩA,TypedDiameter.ΩB,
    ConditionedMatchings.Matching.conditioned,Finset.mem_filter,Finset.mem_univ,true_and]
  rfl

lemma diameters_of_not_bad (rep : ℕ) (r : Match rep) (hr : r∈samples rep)
    (ha : r.1∉TypedDiameter.diameterBadA rep) (hb : r.2∉TypedDiameter.diameterBadB rep) :
    Diameters rep r := by
  have hm : r.1∈TypedDiameter.ΩA rep ∧ r.2∈TypedDiameter.ΩB rep := by
    rw [samples_eq] at hr
    exact Finset.mem_product.mp hr
  constructor
  · intro u v huv
    by_contra h
    exact ha (Finset.mem_filter.mpr ⟨hm.1,u,v,huv,Nat.lt_of_not_ge h⟩)
  · intro u v huv
    by_contra h
    exact hb (Finset.mem_filter.mpr ⟨hm.2,u,v,huv,Nat.lt_of_not_ge h⟩)

/-- The diameter event and the entire bounded-pattern avoidance event occur
simultaneously in the literal conditional product sample. -/
theorem bounded_with_diameter (R K T I B Q M J : ℕ)
    (hR : 0<R) (hK : 0<K) (hI : 0<I) (hM : 0<M) :
    ∀ᶠ rep in atTop,∀ (x : Types.VertexA rep) (y : Types.VertexB rep),
      ∃ r∈samples rep,Diameters rep r ∧ ∀ a : BoundedPattern.Data R K T I (B*L (size rep)),
        a.Good B Q M J rep → ¬a.event rep x y r := by
  have hp := (BoundedPattern.polynomial_exp_tendsto (PatternTotalCoding.coefficient R K T I)
    B (R+3*I) M hM).eventually_lt_const (by norm_num : (0:ℝ)<1/3)
  have ha := TypedDiameter.diameterA_tendsto.eventually_lt_const (by norm_num : (0:ℝ)<1/3)
  have hb := TypedDiameter.diameterB_tendsto.eventually_lt_const (by norm_num : (0:ℝ)<1/3)
  filter_upwards [hp,ha,hb,BoundedPattern.samples_eventually_nonempty,
    PatternUniform.eventually_ready B M Q J hM] with rep hp ha hb hs hu
  intro x y
  have hprob := (BoundedPattern.probability_union R K T I (B*L (size rep)) B Q M J rep
    hR hK hI hM hs hu x y).trans_lt hp
  rw [samples_eq] at hs hprob
  have hn := Finset.nonempty_product.mp hs
  have hprob' :
      (((TypedDiameter.ΩA rep ×ˢ TypedDiameter.ΩB rep).filter
        (fun r => ∃ a : BoundedPattern.Data R K T I (B*L (size rep)),a.Good B Q M J rep ∧ a.event rep x y r)).card:ℝ) /
        ((TypedDiameter.ΩA rep).card*(TypedDiameter.ΩB rep).card:ℕ)<1/3 :=
    Eq.mp (congrArg (fun n : ℕ =>
      (((TypedDiameter.ΩA rep ×ˢ TypedDiameter.ΩB rep).filter
        (fun r => ∃ a : BoundedPattern.Data R K T I (B*L (size rep)),a.Good B Q M J rep ∧ a.event rep x y r)).card:ℝ) /
        (n:ℝ)<1/3) (Finset.card_product (TypedDiameter.ΩA rep) (TypedDiameter.ΩB rep))) hprob
  obtain ⟨r,hr,hra,hrb,hrp⟩ := FiniteJointAvoidance.exists_outside
    (TypedDiameter.ΩA rep) (TypedDiameter.ΩB rep)
    (TypedDiameter.diameterBadA rep) (TypedDiameter.diameterBadB rep)
    (fun r => ∃ a : BoundedPattern.Data R K T I (B*L (size rep)),a.Good B Q M J rep ∧ a.event rep x y r)
    hn.1 hn.2 hprob' ha hb
  have hr' : r∈samples rep := by
    rw [samples_eq]
    exact hr
  refine ⟨r,hr',diameters_of_not_bad rep r hr' hra hrb,?_⟩
  exact fun a hg he => hrp ⟨a,hg,he⟩

/-- Source entropy proposition for arbitrary literal immersed path systems,
with the independent short-closure diameter event included. -/
theorem raw_with_diameter (B K I : ℕ) (hK : 0<K) (hI : 0<I) :
    ∀ᶠ rep in atTop,∀ (x : Types.VertexA rep) (y : Types.VertexB rep),
      ∃ r∈samples rep,Diameters rep r ∧ ∀ a : RawSourcePattern.Data B K I rep,¬a.event x y r := by
  have hT : 0<SourcePattern.T B K := Nat.mul_pos (SourcePattern.R_pos B K) (by omega)
  filter_upwards [bounded_with_diameter (SourcePattern.R B K) K (SourcePattern.T B K)
    I B (SourcePattern.R B K) (SourcePattern.T B K) (I*(SourcePattern.T B K)^2)
    (SourcePattern.R_pos B K) hK hI hT,
    (L_tendsto.comp size_tendsto).eventually (eventually_ge_atTop 1)] with rep hr hL
  change 1≤L (size rep) at hL
  intro x y
  obtain ⟨r,hs,hd,ha⟩ := hr x y
  refine ⟨r,hs,hd,fun a he => ?_⟩
  exact ha (a.suppressed.bounded (by omega)) (a.suppressed.bounded_good (by omega))
    (a.suppressed_event x y r he)

end TorsionFreeZeroDivisors.GraphSample

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SupportedImage
open scoped Classical BigOperators
open PortSubdivision WeightedPortMoore WeightedCycles CoreStripping
variable {V D : Type} (Γ : PortGraph V D) (Q : Finset D) (hQ : Symmetric Γ Q)

/-- Discard isolated ambient vertices as well as unused darts. -/
def vertices : Finset V := Q.image Γ.origin

def graph : PortGraph (vertices Γ Q) Q where
  origin d := ⟨Γ.origin d,Finset.mem_image.mpr ⟨d,d.property,rfl⟩⟩
  reverse d := ⟨Γ.reverse d,hQ d d.property⟩
  reverse_reverse d := Subtype.ext (Γ.reverse_reverse d)
  reverse_ne d h := Γ.reverse_ne d (congrArg Subtype.val h)

lemma no_isolated : Function.Surjective (graph Γ Q hQ).origin := by
  intro v
  obtain ⟨d,hd,he⟩ := Finset.mem_image.mp v.property
  exact ⟨⟨d,hd⟩,Subtype.ext he⟩

/-- Literal inclusion into the actual source graph subdivision. -/
def inclusion : (graph Γ Q hQ).subdivision →g Γ.subdivision where
  toFun := Sum.map Subtype.val Subtype.val
  map_rel' := by
    intro a b h
    rcases a with a|a <;> rcases b with b|b
    · exact h
    · exact congrArg Subtype.val h
    · exact congrArg Subtype.val h
    · exact congrArg Subtype.val h
lemma inclusion_injective : Function.Injective (inclusion Γ Q hQ) :=
  Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩
lemma inclusion_weight {a b : (vertices Γ Q) ⊕ Q}
    (p : (graph Γ Q hQ).subdivision.Walk a b) :
    weight (edgeWeight (fun _ : D => (1:ℝ))) (p.map (inclusion Γ Q hQ)) =
      weight (edgeWeight (fun _ : Q => (1:ℝ))) p := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.map_cons,weight_cons,weight_cons,ih]
    congr 1
    cases a <;> cases b <;> rfl

lemma girth (L : ℝ)
    (hL : ∀ a (p : Γ.subdivision.Walk a a),p.IsCycle →
      L≤weight (edgeWeight (fun _ : D => (1:ℝ))) p) :
    ∀ a (p : (graph Γ Q hQ).subdivision.Walk a a),p.IsCycle →
      L≤weight (edgeWeight (fun _ : Q => (1:ℝ))) p := by
  intro a p hp
  have hm := hp.map (inclusion_injective Γ Q hQ)
  simpa only [inclusion_weight] using hL _ (p.map (inclusion Γ Q hQ)) hm

variable {P : Type} (paths : P → List D) (hpaths : ∀ p d,d∈paths p → d∈Q)
def path (p : P) : List Q := (paths p).attach.map (fun d => ⟨d.val,hpaths p d.val d.property⟩)
lemma path_val (p : P) : (path Q paths hpaths p).map Subtype.val=paths p := by
  simp only [path,List.map_map,Function.comp_def]
  simpa only [List.map_id,id_eq] using (List.attach_map_val (f:=id) (l:=paths p))
lemma length (p : P) : (path Q paths hpaths p).length=(paths p).length := by
  simp [path]
lemma nonempty (p : P) (hp : paths p≠[]) : path Q paths hpaths p≠[] := by
  intro hn
  apply hp
  rw [←path_val Q paths hpaths p,hn]
  rfl
lemma chain (p : P) (hp : (paths p).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse)) :
    (path Q paths hpaths p).IsChain (WeightedMoore.PortWalk.step (graph Γ Q hQ).origin (graph Γ Q hQ).reverse) := by
  have hh : ((path Q paths hpaths p).map Subtype.val).IsChain
      (WeightedMoore.PortWalk.step Γ.origin Γ.reverse) := by rw [path_val]; exact hp
  rw [List.isChain_map] at hh
  apply hh.imp
  intro a b hab
  exact ⟨Subtype.ext hab.1,fun h => hab.2 (congrArg Subtype.val h)⟩
lemma mem_path (p : P) (d : Q) : d∈path Q paths hpaths p ↔ d.val∈paths p := by
  rw [←path_val Q paths hpaths p,List.mem_map]
  constructor
  · intro hd
    exact ⟨d,hd,rfl⟩
  · rintro ⟨e,he,hed⟩
    exact (Subtype.ext hed : e=d) ▸ he
lemma head_value (p : P) (hp : paths p≠[]) :
    ((path Q paths hpaths p).head (nonempty Q paths hpaths p hp)).val=(paths p).head hp := by
  have hh := congrArg List.head? (path_val Q paths hpaths p)
  rw [List.head?_map,List.head?_eq_some_head (nonempty Q paths hpaths p hp),
    List.head?_eq_some_head hp] at hh
  exact Option.some.inj hh
lemma cyclic (p : P)
    (hp : ∀ᵉ (x∈(paths p).getLast?) (y∈(paths p).head?),
      WeightedMoore.PortWalk.step Γ.origin Γ.reverse x y) :
    ∀ᵉ (x∈(path Q paths hpaths p).getLast?) (y∈(path Q paths hpaths p).head?),
      WeightedMoore.PortWalk.step (graph Γ Q hQ).origin (graph Γ Q hQ).reverse x y := by
  intro x hx y hy
  have hxv : x.val∈(paths p).getLast? := by
    rw [←path_val Q paths hpaths p,List.getLast?_map]
    change ((path Q paths hpaths p).getLast?).map Subtype.val=some x.val
    rw [show (path Q paths hpaths p).getLast?=some x from hx]
    rfl
  have hyv : y.val∈(paths p).head? := by
    rw [←path_val Q paths hpaths p,List.head?_map]
    change ((path Q paths hpaths p).head?).map Subtype.val=some y.val
    rw [show (path Q paths hpaths p).head?=some y from hy]
    rfl
  have hh := hp x hxv y hyv
  exact ⟨Subtype.ext hh.1,fun he => hh.2 (congrArg Subtype.val he)⟩
lemma covered (hc : ∀ d∈Q,∃ p,d∈paths p ∨ Γ.reverse d∈paths p) :
    ∀ d : Q,∃ p,d∈path Q paths hpaths p ∨ (graph Γ Q hQ).reverse d∈path Q paths hpaths p := by
  intro d
  obtain ⟨p,hp⟩ := hc d d.property
  refine ⟨p,?_⟩
  simpa only [mem_path, graph] using hp

/-- The symmetric set of precisely the darts used by the actual paths. -/
def used [Fintype P] (paths : P → List D) : Finset D :=
  Finset.univ.biUnion fun p => (paths p).toFinset ∪ (paths p).toFinset.image Γ.reverse
lemma mem_used [Fintype P] (paths : P → List D) (d : D) :
    d∈used Γ paths ↔ ∃ p,d∈paths p ∨ Γ.reverse d∈paths p := by
  simp only [used,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_union,List.mem_toFinset,Finset.mem_image]
  apply exists_congr
  intro p
  constructor
  · rintro (h|⟨e,he,hed⟩)
    · exact Or.inl h
    · right
      have heq : e=Γ.reverse d := by simpa using congrArg Γ.reverse hed
      exact heq ▸ he
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr ⟨Γ.reverse d,h,Γ.reverse_reverse d⟩
lemma used_symmetric [Fintype P] (paths : P → List D) : Symmetric Γ (used Γ paths) := by
  intro d hd
  obtain ⟨p,hp⟩ := (mem_used Γ paths d).mp hd
  apply (mem_used Γ paths (Γ.reverse d)).mpr
  refine ⟨p,?_⟩
  simpa only [PortGraph.reverse_reverse_apply] using hp.symm
lemma path_in_used [Fintype P] (paths : P → List D) (p : P) (d : D) (hd : d∈paths p) :
    d∈used Γ paths := (mem_used Γ paths d).mpr ⟨p,Or.inl hd⟩

end TorsionFreeZeroDivisors.SupportedImage

namespace TorsionFreeZeroDivisors.RootPins
open scoped Classical
lemma pin_map {V W T : Type*} (f : V ↪ W) (r : Option V) (t : T) (v : V) :
    pin (r.map f) t (f v)=pin r t v := by
  cases r with
  | none => simp [pin]
  | some w => simp [pin,f.injective.eq_iff]
end TorsionFreeZeroDivisors.RootPins

namespace TorsionFreeZeroDivisors.SupportedImage
open scoped Classical
open PortSubdivision
variable {V D : Type} (Γ : PortGraph V D) (Q : Finset D) (hQ : CoreStripping.Symmetric Γ Q)
    (side : V → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d)) (b : Bool)
def sideVertex : SideRestriction.Vertex (fun v : vertices Γ Q => side v.val) b ↪ SideRestriction.Vertex side b :=
  ⟨fun v => ⟨v.val.val,v.property⟩,fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun x => x.val) h))⟩
def sideDart : SideRestriction.Dart (graph Γ Q hQ) (fun v => side v.val) b ↪ SideRestriction.Dart Γ side b :=
  ⟨fun d => ⟨d.val.val,d.property⟩,fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun x => x.val) h))⟩
lemma side_root (r : Option (vertices Γ Q)) :
    (SidePins.root (fun v : vertices Γ Q => side v.val) r b).map (sideVertex Γ Q side b)=
      SidePins.root side (r.map Subtype.val) b := by
  cases r with
  | none => rfl
  | some v =>
    by_cases hv : side v.val=b
    · simp only [SidePins.root,Option.map_some,Option.bind_some,hv,dif_pos]
      rfl
    · simp [SidePins.root,hv]

variable [Fintype V] [Fintype D] {T TV : Type} [Fintype T] [Fintype TV]
    (label : D → T) (outgoing : TV → Finset T) (bar : T → T)
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) bar)
    (root : Option (vertices Γ Q)) (target : TV)
/-- Actual embeddings restrict to the used image, with the exact side/root pin. -/
def embedding
    (e : RealizationTransport.Embedding (SideRestriction.graph Γ side hs b) (fun d => label d.val)
      outgoing (RootPins.pin (SidePins.root side (root.map Subtype.val) b) target) bar r) :
    RealizationTransport.Embedding
      (SideRestriction.graph (graph Γ Q hQ) (fun v => side v.val) (fun d => hs d.val) b)
      (fun d => label d.val.val) outgoing
      (RootPins.pin (SidePins.root (fun v : vertices Γ Q => side v.val) root b) target) bar r :=
  RealizationTransport.restrict e _ (sideVertex Γ Q side b) (sideDart Γ Q hQ side b)
    (fun _ => rfl) (fun _ => rfl) _ (by
      intro v y hy
      rw [←side_root Γ Q side b root,RootPins.pin_map]
      exact hy)
end TorsionFreeZeroDivisors.SupportedImage
namespace TorsionFreeZeroDivisors.AmbientPattern
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks ComparisonGeometry GirthAsymptotics TypedGraphs ActualPatternEvent
/-- A path system in an ambient finite graph. The graph need not be the union
of the paths; taking its literal supported image constructs the raw data. -/
structure Data (B K I rep : ℕ) where
  V : Type
  D : Type
  P : Type
  E : Type
  [fV : Fintype V]
  [fD : Fintype D]
  [fP : Fintype P]
  [fE : Fintype E]
  graph : PortGraph V D
  side : V → Bool
  side_edge : ∀ d,side (graph.origin (graph.reverse d))=side (graph.origin d)
  paths : P → List D
  nonempty : ∀ p,paths p≠[]
  root : Option P
  path_bound : Fintype.card P≤K
  comparison_bound : Fintype.card E≤I
  path_chain : ∀ p,(paths p).IsChain (WeightedMoore.PortWalk.step graph.origin graph.reverse)
  cyclic_chain : ∀ p,StageRoot.cyclic root p=true →
    ∀ᵉ (x∈(paths p).getLast?) (y∈(paths p).head?),
      WeightedMoore.PortWalk.step graph.origin graph.reverse x y
  girth : ∀ a (c : graph.subdivision.Walk a a),c.IsCycle →
    (L (size rep):ℝ)≤WeightedCycles.weight (WeightedPortMoore.edgeWeight (fun _ : D => (1:ℝ))) c
  length_le : (∑p,(paths p).length:ℕ)≤B*L (size rep)
  length_ge : L (size rep)≤(∑p,(paths p).length:ℕ)
  comparisons : Comparisons (E:=E) (fun p => (paths p).length)
  lower : E → ℕ
  upper : E → ℕ
  lower_eq : ∀ e,comparisons.lo e=lower e
  upper_eq : ∀ e,comparisons.hi e=upper e
  lower_le : ∀ e,lower e≤upper e
  upper_le : ∀ e,upper e≤(paths (comparisons.source e)).length
  reduced : ∀ x e,comparisons.side x=some e →
    RawDecomposition.dart paths x≠RawDecomposition.dart paths (comparisons.pairing.partner x) ∧
    RawDecomposition.dart paths x≠graph.reverse (RawDecomposition.dart paths (comparisons.pairing.partner x))
  unpaired_le : ((Finset.univ.filter (fun x => comparisons.pairing.partner x=x)).card:ℝ)≤
    StageFusion.epsilon (1/600) 256*(∑p,(paths p).length:ℕ)
attribute [instance] Data.fV Data.fD Data.fP Data.fE

namespace Data
variable {B K I rep : ℕ} (a : Data B K I rep)
abbrev used := SupportedImage.used a.graph a.paths
abbrev symmetric := SupportedImage.used_symmetric a.graph a.paths
abbrev supportedGraph := SupportedImage.graph a.graph a.used a.symmetric
abbrev vertices := SupportedImage.vertices a.graph a.used
abbrev pathUsed := SupportedImage.path_in_used a.graph a.paths
abbrev supportedPaths := SupportedImage.path a.used a.paths a.pathUsed
lemma lengths_eq : (fun p => (a.supportedPaths p).length)=(fun p => (a.paths p).length) :=
  funext (SupportedImage.length a.used a.paths a.pathUsed)
abbrev comparison := ComparisonGeometry.cast a.lengths_eq.symm a.comparisons
abbrev iso := ComparisonGeometry.castBackIso a.lengths_eq a.comparisons
abbrev position : Position (fun p => (a.supportedPaths p).length) ≃ Position (fun p => (a.paths p).length) :=
  ComparisonGeometry.position a.iso.path a.iso.length_eq
lemma dart_eq (x : Position (fun p => (a.supportedPaths p).length)) :
    (RawDecomposition.dart a.supportedPaths x).val=RawDecomposition.dart a.paths (a.position x) := by
  apply Option.some.inj
  rw [←Option.map_some (f:=Subtype.val),←RawDecomposition.dart_get,←List.getElem?_map,
    SupportedImage.path_val,←RawDecomposition.dart_get]
  rfl

/-- Restrict to actual used darts and their incident vertices. Every original
length, comparison and counting hypothesis is transported verbatim. -/
def supported : RawSourcePattern.Data B K I rep where
  V := a.vertices
  D := a.used
  P := a.P
  E := a.E
  graph := a.supportedGraph
  no_isolated := SupportedImage.no_isolated a.graph a.used a.symmetric
  side := fun v => a.side v.val
  side_edge d := a.side_edge d.val
  paths := a.supportedPaths
  nonempty p := SupportedImage.nonempty a.used a.paths a.pathUsed p (a.nonempty p)
  root := a.root
  path_bound := a.path_bound
  comparison_bound := a.comparison_bound
  image := SupportedImage.covered a.graph a.used a.symmetric a.paths a.pathUsed
    (fun d hd => (SupportedImage.mem_used a.graph a.paths d).mp hd)
  path_chain p := SupportedImage.chain a.graph a.used a.symmetric a.paths a.pathUsed p (a.path_chain p)
  cyclic_chain p hp := SupportedImage.cyclic a.graph a.used a.symmetric a.paths a.pathUsed p (a.cyclic_chain p hp)
  girth := SupportedImage.girth a.graph a.used a.symmetric (L (size rep)) a.girth
  length_le := by simpa only [SupportedImage.length] using a.length_le
  length_ge := by simpa only [SupportedImage.length] using a.length_ge
  comparisons := a.comparison
  lower := a.lower
  upper := a.upper
  lower_eq e := (a.iso.lo_eq e).trans (a.lower_eq e)
  upper_eq e := (a.iso.hi_eq e).trans (a.upper_eq e)
  lower_le := a.lower_le
  upper_le e := by
    rw [SupportedImage.length]
    have hs : a.comparison.source e=a.comparisons.source e := a.iso.source_eq e
    rw [hs]
    exact a.upper_le e
  reduced := by
    intro x e he
    have hh := a.reduced (a.position x) e ((a.iso.side_some x e).mpr he)
    constructor
    · intro h
      apply hh.1
      have hv := congrArg Subtype.val h
      rw [a.dart_eq,a.dart_eq,a.iso.partner_eq] at hv
      exact hv
    · intro h
      apply hh.2
      have hv := congrArg Subtype.val h
      change (RawDecomposition.dart a.supportedPaths x).val=a.graph.reverse
        (RawDecomposition.dart a.supportedPaths (a.comparison.pairing.partner x)).val at hv
      rw [a.dart_eq,a.dart_eq,a.iso.partner_eq] at hv
      exact hv
  unpaired_le := by
    rw [a.iso.unpaired]
    simpa only [SupportedImage.length] using a.unpaired_le
abbrev supportedRoot : Option a.vertices := a.root.map fun p =>
  a.supportedGraph.origin ((a.supportedPaths p).head (a.supported.nonempty p))
lemma supported_root : a.supportedRoot.map Subtype.val=
    a.root.map (fun p => a.graph.origin ((a.paths p).head (a.nonempty p))) := by
  cases h : a.root with
  | none => simp only [supportedRoot,h,Option.map_none]
  | some p =>
    simp only [supportedRoot,h,Option.map_some]
    change some (a.graph.origin (((a.supportedPaths p).head (a.supported.nonempty p)).val))=_
    rw [SupportedImage.head_value]

def event (x : Types.VertexA rep) (y : Types.VertexB rep) (r : Match rep) : Prop :=
  ∃ label : a.D → Types.Letter,
    (∀ d,label (a.graph.reverse d)=Types.inverse (label d)) ∧
    (∀ d e,a.graph.origin d=a.graph.origin e → label d=label e → d=e) ∧
    (∀ p e,a.comparisons.side p=some e → label (RawDecomposition.dart a.paths p)=
      if a.comparisons.reverse e then Types.inverse (label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p)))
      else label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p))) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph a.graph a.side a.side_edge true)
      (fun d => label d.val) (@Types.outgoingA rep)
      (RootPins.pin (SidePins.root a.side (a.root.map fun p => a.graph.origin ((a.paths p).head (a.nonempty p))) true) x)
      Types.inverse r.1) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph a.graph a.side a.side_edge false)
      (fun d => label d.val) (@Types.outgoingB rep)
      (RootPins.pin (SidePins.root a.side (a.root.map fun p => a.graph.origin ((a.paths p).head (a.nonempty p))) false) y)
      Types.inverse r.2)

lemma comparing (label : a.D → Types.Letter)
    (hc : ∀ p e,a.comparisons.side p=some e → label (RawDecomposition.dart a.paths p)=
      if a.comparisons.reverse e then Types.inverse (label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p)))
      else label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p))) :
    ∀ (p : Position (fun p => (a.supportedPaths p).length)) (e : a.E),a.comparison.side p=some e →
      label (RawDecomposition.dart a.supportedPaths p).val=
      if a.comparison.reverse e then Types.inverse
        (label (RawDecomposition.dart a.supportedPaths (a.comparison.pairing.partner p)).val)
      else label (RawDecomposition.dart a.supportedPaths (a.comparison.pairing.partner p)).val := by
  intro p e he
  have hh := hc (a.position p) e ((a.iso.side_some p e).mpr he)
  have hr : a.comparison.reverse e=a.comparisons.reverse e := a.iso.reverse_eq e
  have hp : a.position (a.comparison.pairing.partner p)=a.comparisons.pairing.partner (a.position p) :=
    a.iso.partner_eq p
  simp only [a.dart_eq]
  rw [hr,hp]
  exact hh

/-- Restrict the literal realization, including its exact root and labels,
to the supported raw source pattern. -/
lemma supported_event (x : Types.VertexA rep) (y : Types.VertexB rep) (r : Match rep)
    (h : a.event x y r) : a.supported.event x y r := by
  rcases h with ⟨label,hl,hn,hc,ha,hb⟩
  refine ⟨(fun d => label d.val),?_,?_,?_,?_,?_⟩
  · exact fun d => hl d.val
  · intro d e ho he
    exact Subtype.ext (hn d.val e.val (congrArg Subtype.val ho) he)
  · exact a.comparing label hc
  · refine ⟨SupportedImage.embedding a.graph a.used a.symmetric a.side a.side_edge true label
      (@Types.outgoingA rep) Types.inverse r.1 a.supportedRoot x ?_⟩
    simpa only [a.supported_root] using ha.some
  · refine ⟨SupportedImage.embedding a.graph a.used a.symmetric a.side a.side_edge false label
      (@Types.outgoingB rep) Types.inverse r.2 a.supportedRoot y ?_⟩
    simpa only [a.supported_root] using hb.some

end Data

/-- The fixed-sample bounded pattern conclusion applies to every original
ambient path system, not only to a presupposed image or suppression. -/
theorem with_diameter (B K I : ℕ) (hK : 0<K) (hI : 0<I) :
    ∀ᶠ rep in Filter.atTop,∀ (x : Types.VertexA rep) (y : Types.VertexB rep),
      ∃ r∈samples rep,GraphSample.Diameters rep r ∧ ∀ a : Data B K I rep,¬a.event x y r := by
  filter_upwards [GraphSample.raw_with_diameter B K I hK hI] with rep hr
  intro x y
  obtain ⟨r,hr,hd,ha⟩ := hr x y
  exact ⟨r,hr,hd,fun a he => ha a.supported (a.supported_event x y r he)⟩
end TorsionFreeZeroDivisors.AmbientPattern

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedGirth
open scoped Classical BigOperators
open PortSubdivision WeightedPortMoore WeightedCycles
variable {V D : Type} (Γ : PortGraph V D)

def middle : Sym2 (V ⊕ D) → Bool :=
  Sym2.lift ⟨fun a b => match a,b with
    | .inr _,.inr _ => true
    | _,_ => false,by intro a b; cases a <;> cases b <;> rfl⟩
def bundle : Sym2 (V ⊕ D) → Finset (Sym2 (V ⊕ D)) :=
  Sym2.lift ⟨fun a b => match a,b with
    | .inr d,.inr e => {s(a,b),s(Sum.inl (Γ.origin d),a),s(Sum.inl (Γ.origin e),b)}
    | _,_ => {s(a,b)},by
      intro a b
      cases a <;> cases b
      all_goals simp only [Sym2.eq_swap]
      exact congrArg (fun t : Finset (Sym2 (V⊕D)) => insert _ t) (Finset.pair_comm _ _)⟩
lemma bundle_card (e : Sym2 (V ⊕ D)) : (bundle Γ e).card≤3 := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    cases a with
    | inl v => cases b <;> simp [bundle]
    | inr d =>
      cases b with
      | inl v => simp [bundle]
      | inr f =>
        change ({_,_,_} : Finset (Sym2 (V⊕D))).card ≤ 3
        have h₁ := Finset.card_insert_le s(Sum.inr d,Sum.inr f)
          ({s(Sum.inl (Γ.origin d),Sum.inr d),s(Sum.inl (Γ.origin f),Sum.inr f)} : Finset (Sym2 (V⊕D)))
        have h₂ := Finset.card_insert_le s(Sum.inl (Γ.origin d),Sum.inr d)
          ({s(Sum.inl (Γ.origin f),Sum.inr f)} : Finset (Sym2 (V⊕D)))
        simp only [Finset.card_singleton] at h₂
        dsimp only at *
        omega
lemma self_mem_bundle (e : Sym2 (V ⊕ D)) : e∈bundle Γ e := by
  induction e using Sym2.inductionOn with
  | _ a b => cases a <;> cases b <;> simp [bundle]
lemma weight_eq_indicator (e : Sym2 (V ⊕ D)) :
    edgeWeight (fun _ : D => (1:ℝ)) e=if middle e then 1 else 0 := by
  induction e using Sym2.inductionOn with
  | _ a b => cases a <;> cases b <;> norm_num [edgeWeight,middle]

lemma edges_covered {a : V⊕D} (p : Γ.subdivision.Walk a a) (hp : p.IsCycle) :
    p.edges.toFinset⊆(p.edges.toFinset.filter (fun e => middle e)).biUnion (bundle Γ) := by
  intro e he
  have hep : e∈p.edges := List.mem_toFinset.mp he
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hadj := p.adj_of_mem_edges hep
    cases x with
    | inl v =>
      cases y with
      | inl w => exact False.elim hadj
      | inr d =>
        change Γ.origin d=v at hadj
        subst v
        have hd : Sum.inr d∈p.support := p.snd_mem_support_of_mem_edges hep
        have hm := Γ.cycle_middle_at_port d (p.rotate (.inr d) hd) (hp.rotate hd)
        have hm' : s(Sum.inr d,Sum.inr (Γ.reverse d))∈p.edges := (p.rotate_edges _ hd).mem_iff.mp hm
        apply Finset.mem_biUnion.mpr
        refine ⟨s(Sum.inr d,Sum.inr (Γ.reverse d)),Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm',rfl⟩,?_⟩
        simp [bundle]
    | inr d =>
      cases y with
      | inl v =>
        change Γ.origin d=v at hadj
        subst v
        have hd : Sum.inr d∈p.support := p.fst_mem_support_of_mem_edges hep
        have hm := Γ.cycle_middle_at_port d (p.rotate (.inr d) hd) (hp.rotate hd)
        have hm' : s(Sum.inr d,Sum.inr (Γ.reverse d))∈p.edges := (p.rotate_edges _ hd).mem_iff.mp hm
        apply Finset.mem_biUnion.mpr
        refine ⟨s(Sum.inr d,Sum.inr (Γ.reverse d)),Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm',rfl⟩,?_⟩
        simp [bundle,Sym2.eq_swap]
      | inr f =>
        exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_filter.mpr ⟨he,rfl⟩,self_mem_bundle Γ _⟩

/-- In a genuine subdivision cycle every middle edge supports at most two
spokes. Thus girth measured in three-edge subdivisions implies the literal
unit macro-edge weighted girth used by the pattern theorem. -/
lemma length_le_three_weight {a : V⊕D} (p : Γ.subdivision.Walk a a) (hp : p.IsCycle) :
    (p.length:ℝ)≤3*weight (edgeWeight (fun _ : D => (1:ℝ))) p := by
  have hn := hp.isTrail.edges_nodup
  have hc : p.edges.toFinset.card≤3*(p.edges.toFinset.filter (fun e => middle e)).card := calc
    _≤((p.edges.toFinset.filter (fun e => middle e)).biUnion (bundle Γ)).card := Finset.card_le_card (edges_covered Γ p hp)
    _≤∑e∈p.edges.toFinset.filter (fun e => middle e),(bundle Γ e).card := Finset.card_biUnion_le
    _≤∑_e∈p.edges.toFinset.filter (fun e => middle e),3 := Finset.sum_le_sum (fun e _ => bundle_card Γ e)
    _=3*(p.edges.toFinset.filter (fun e => middle e)).card := by simp [Nat.mul_comm]
  have hw : weight (edgeWeight (fun _ : D => (1:ℝ))) p=
      (p.edges.toFinset.filter (fun e => middle e)).card := by
    rw [weight,←List.sum_toFinset _ hn]
    simp only [weight_eq_indicator,←Finset.sum_filter]
    simp
  rw [hw]
  have hl : p.edges.toFinset.card=p.length := by rw [List.toFinset_card_of_nodup hn,SimpleGraph.Walk.length_edges]
  rw [hl] at hc
  exact_mod_cast hc
lemma weighted_girth (L : ℕ) (hg : (3*L:ℕ)≤Γ.subdivision.egirth) :
    ∀ a (p : Γ.subdivision.Walk a a),p.IsCycle → (L:ℝ)≤weight (edgeWeight (fun _ : D => (1:ℝ))) p := by
  intro a p hp
  have hl : 3*L≤p.length := by exact_mod_cast SimpleGraph.le_egirth.mp hg a p hp
  have hl' : (3:ℝ)*L≤p.length := by exact_mod_cast hl
  have hw := length_le_three_weight Γ p hp
  linarith
end TorsionFreeZeroDivisors.WeightedGirth
namespace TorsionFreeZeroDivisors.SumGirth
open SimpleGraph
variable {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
def inlWalk {a b : V} : (G⊕g H).Walk (.inl a) (.inl b) → G.Walk a b
  | .nil => .nil
  | .cons (v:=.inl c) h p => .cons h (inlWalk p)
  | .cons (v:=.inr _) h _ => by cases h
lemma map_inlWalk {a b : V} (p : (G⊕g H).Walk (.inl a) (.inl b)) :
    (inlWalk G H p).map Embedding.sumInl.toHom=p := by
  fun_induction inlWalk G H p
  · rfl
  · rename_i a b c h p ih
    change SimpleGraph.Walk.cons _ ((inlWalk G H p).map Embedding.sumInl.toHom) = _
    rw [ih]
    rfl
  · contradiction
lemma inlWalk_length {a b : V} (p : (G⊕g H).Walk (.inl a) (.inl b)) :
    (inlWalk G H p).length=p.length := by
  calc
    _ = ((inlWalk G H p).map Embedding.sumInl.toHom).length := (SimpleGraph.Walk.length_map _ _).symm
    _ = p.length := congrArg SimpleGraph.Walk.length (map_inlWalk G H p)
lemma inlWalk_cycle {a : V} (p : (G⊕g H).Walk (.inl a) (.inl a)) (hp : p.IsCycle) :
    (inlWalk G H p).IsCycle := by
  rw [←map_inlWalk G H p] at hp
  exact hp.of_map
lemma le_egirth (n : ℕ∞) (hG : n≤G.egirth) (hH : n≤H.egirth) :
    n≤(G⊕g H).egirth := by
  apply SimpleGraph.le_egirth.mpr
  intro a p hp
  cases a with
  | inl a =>
    have h := SimpleGraph.le_egirth.mp hG a (inlWalk G H p) (inlWalk_cycle G H p hp)
    simpa only [inlWalk_length] using h
  | inr b =>
    let q : (H⊕g G).Walk (.inl b) (.inl b) := p.map Iso.sumComm.toHom
    have hq : q.IsCycle := hp.map Iso.sumComm.injective
    have h := SimpleGraph.le_egirth.mp hH b (inlWalk H G q) (inlWalk_cycle H G q hq)
    have hl : (inlWalk H G q).length=p.length := (inlWalk_length H G q).trans (p.length_map Iso.sumComm.toHom)
    rw [hl] at h
    exact h
end TorsionFreeZeroDivisors.SumGirth
namespace TorsionFreeZeroDivisors.SumPort

section
open PortSubdivision SimpleGraph
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
def subdivisionIso : (graph A B).subdivision ≃g A.subdivision⊕g B.subdivision where
  toEquiv := Equiv.sumSumSumComm VA VB DA DB
  map_rel_iff' := by
    intro a b
    rcases a with (a|a)|(a|a) <;> rcases b with (b|b)|(b|b) <;>
      simp [graph,PortGraph.subdivision,Equiv.sumSumSumComm]
lemma girth (n : ℕ∞) (hA : n≤A.subdivision.egirth) (hB : n≤B.subdivision.egirth) :
    n≤(graph A B).subdivision.egirth := by
  rw [(subdivisionIso A B).egirth_eq]
  exact SumGirth.le_egirth _ _ _ hA hB

def side : VA⊕VB → Bool | .inl _ => true | .inr _ => false
lemma side_edge (d : DA⊕DB) : side ((graph A B).origin ((graph A B).reverse d))=side ((graph A B).origin d) := by
  cases d <;> rfl

def leftV (v : SideRestriction.Vertex (@side VA VB) true) : VA :=
  match v with
  | ⟨.inl a,_⟩ => a
  | ⟨.inr _,h⟩ => by cases h
def rightV (v : SideRestriction.Vertex (@side VA VB) false) : VB :=
  match v with
  | ⟨.inr b,_⟩ => b
  | ⟨.inl _,h⟩ => by cases h
lemma leftV_injective : Function.Injective (@leftV VA VB) := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  cases a <;> cases b
  · exact Subtype.ext (congrArg Sum.inl h)
  · cases hb
  · cases ha
  · cases ha
lemma rightV_injective : Function.Injective (@rightV VA VB) := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  cases a <;> cases b
  · cases ha
  · cases ha
  · cases hb
  · exact Subtype.ext (congrArg Sum.inr h)
end
open PortSubdivision
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
def leftD (d : SideRestriction.Dart (graph A B) side true) : DA :=
  match d with
  | ⟨.inl a,_⟩ => a
  | ⟨.inr _,h⟩ => by cases h
def rightD (d : SideRestriction.Dart (graph A B) side false) : DB :=
  match d with
  | ⟨.inr b,_⟩ => b
  | ⟨.inl _,h⟩ => by cases h
lemma leftD_injective : Function.Injective (leftD A B) := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  cases a <;> cases b
  · exact Subtype.ext (congrArg Sum.inl h)
  · cases hb
  · cases ha
  · cases ha
lemma rightD_injective : Function.Injective (rightD A B) := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  cases a <;> cases b
  · cases ha
  · cases ha
  · cases hb
  · exact Subtype.ext (congrArg Sum.inr h)
lemma root_value {V : Type*} (s : V → Bool) (r : Option V) (b : Bool)
    (v : SideRestriction.Vertex s b) (h : SidePins.root s r b=some v) : r=some v.val := by
  cases r with
  | none => cases h
  | some w =>
    dsimp only [SidePins.root,Option.bind_some] at h
    split_ifs at h with hw
    have hv : w=v.val := congrArg Subtype.val (Option.some.inj h)
    rw [hv]
end TorsionFreeZeroDivisors.SumPort
namespace TorsionFreeZeroDivisors.SampleGraph

section
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings ActualPatternEvent TypedGraphs GirthAsymptotics
variable (rep : ℕ) (r : Match rep)
lemma label_reverse (d : DA rep⊕DB rep) : label rep ((graph rep r).reverse d)=Types.inverse (label rep d) := by
  cases d with
  | inl d => exact r.1.label_reverse d
  | inr d => exact r.2.label_reverse d
lemma immersed (d e : DA rep⊕DB rep)
    (ho : (graph rep r).origin d=(graph rep r).origin e) (hl : label rep d=label rep e) : d=e := by
  cases d with
  | inl d =>
    cases e with
    | inl e => exact congrArg Sum.inl (Subtype.ext (Prod.ext (Sum.inl.inj ho) hl))
    | inr e => cases ho
  | inr d =>
    cases e with
    | inl e => cases ho
    | inr e => exact congrArg Sum.inr (Subtype.ext (Prod.ext (Sum.inr.inj ho) hl))
lemma girth (hr : r∈samples rep) : (3*L (size rep):ℕ)≤(graph rep r).subdivision.egirth := by
  have hm := Finset.mem_product.mp hr
  have hA := (Finset.mem_filter.mp hm.1).2.2
  have hB := (Finset.mem_filter.mp hm.2).2.2
  exact SumPort.girth _ _ _ hA hB
lemma weighted_girth (hr : r∈samples rep) :
    ∀ a (p : (graph rep r).subdivision.Walk a a),p.IsCycle →
      (L (size rep):ℝ)≤WeightedCycles.weight (WeightedPortMoore.edgeWeight (fun _ : DA rep⊕DB rep => (1:ℝ))) p :=
  WeightedGirth.weighted_girth _ _ (girth rep r hr)

def embeddingA (root : Option (VA rep⊕VB rep)) (x : VA rep)
    (hr : ∀ z,root=some (.inl z) → z=x) :
    RealizationTransport.Embedding
      (SideRestriction.graph (graph rep r) SumPort.side (SumPort.side_edge _ _) true)
      (fun d => label rep d.val) (@Types.outgoingA rep)
      (RootPins.pin (SidePins.root SumPort.side root true) x) Types.inverse r.1 where
  vertex := ⟨SumPort.leftV,SumPort.leftV_injective⟩
  port := ⟨SumPort.leftD _ _,SumPort.leftD_injective _ _⟩
  origin_eq := by rintro ⟨d,hd⟩; cases d with | inl d => rfl | inr d => cases hd
  label_eq := by rintro ⟨d,hd⟩; cases d with | inl d => rfl | inr d => cases hd
  reverse_eq := by rintro ⟨d,hd⟩; cases d with | inl d => rfl | inr d => cases hd
  pin_eq := by
    apply RootPins.respects
    rintro ⟨v,hv⟩ h
    cases v with
    | inl v => exact hr v (SumPort.root_value SumPort.side root true _ h)
    | inr v => cases hv

def embeddingB (root : Option (VA rep⊕VB rep)) (y : VB rep)
    (hr : ∀ z,root=some (.inr z) → z=y) :
    RealizationTransport.Embedding
      (SideRestriction.graph (graph rep r) SumPort.side (SumPort.side_edge _ _) false)
      (fun d => label rep d.val) (@Types.outgoingB rep)
      (RootPins.pin (SidePins.root SumPort.side root false) y) Types.inverse r.2 where
  vertex := ⟨SumPort.rightV,SumPort.rightV_injective⟩
  port := ⟨SumPort.rightD _ _,SumPort.rightD_injective _ _⟩
  origin_eq := by rintro ⟨d,hd⟩; cases d with | inl d => cases hd | inr d => rfl
  label_eq := by rintro ⟨d,hd⟩; cases d with | inl d => cases hd | inr d => rfl
  reverse_eq := by rintro ⟨d,hd⟩; cases d with | inl d => cases hd | inr d => rfl
  pin_eq := by
    apply RootPins.respects
    rintro ⟨v,hv⟩ h
    cases v with
    | inl v => cases hv
    | inr v => exact hr v (SumPort.root_value SumPort.side root false _ h)
end
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks ComparisonGeometry GirthAsymptotics TypedGraphs ActualPatternEvent
attribute [instance] BoundedSystem.fP BoundedSystem.fE

end TorsionFreeZeroDivisors.SampleGraph

end

end OAI
end

section
namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks ComparisonGeometry GirthAsymptotics TypedGraphs ActualPatternEvent
attribute [instance] BoundedSystem.fP BoundedSystem.fE

namespace BoundedSystem
variable {Bnd K I rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
    (s : BoundedSystem Bnd K I rep r x y)
def data (hr : r∈samples rep) : AmbientPattern.Data Bnd K I rep where
  V := VA rep⊕VB rep
  D := DA rep⊕DB rep
  P := s.P
  E := s.E
  graph := graph rep r
  side := SumPort.side
  side_edge := SumPort.side_edge _ _
  paths := s.paths
  nonempty := s.nonempty
  root := s.root
  path_bound := s.path_bound
  comparison_bound := s.comparison_bound
  path_chain := s.path_chain
  cyclic_chain := s.cyclic_chain
  girth := weighted_girth rep r hr
  length_le := s.length_le
  length_ge := s.length_ge
  comparisons := s.comparisons
  lower := s.lower
  upper := s.upper
  lower_eq := s.lower_eq
  upper_eq := s.upper_eq
  lower_le := s.lower_le
  upper_le := s.upper_le
  reduced := s.reduced
  unpaired_le := s.unpaired_le
lemma event (hr : r∈samples rep) : (s.data hr).event x y r :=
  ⟨label rep,label_reverse rep r,immersed rep r,s.compatible,
    ⟨embeddingA rep r _ x s.rootA⟩,⟨embeddingB rep r _ y s.rootB⟩⟩
end BoundedSystem

/-- A literal finite typed graph on both sides, simultaneously with diameter,
large girth, and exclusion of every bounded nearly-paired rooted path system.
This is an actual-word theorem, not a condition on encoded surrogate patterns. -/
theorem exists_avoiding_dev (Bnd K I : ℕ) (hK : 0<K) (hI : 0<I) :
    ∀ᶠ rep in Filter.atTop,∀ (x : VA rep) (y : VB rep),
      ∃ r∈samples rep,GraphSample.Diameters rep r ∧
        IsEmpty (BoundedSystem Bnd K I rep r x y) := by
  filter_upwards [AmbientPattern.with_diameter Bnd K I hK hI] with rep hrep
  intro x y
  obtain ⟨r,hr,hd,ha⟩ := hrep x y
  refine ⟨r,hr,hd,⟨?_⟩⟩
  intro s
  exact ha (s.data hr) (s.event hr)
end TorsionFreeZeroDivisors.SampleGraph
namespace TorsionFreeZeroDivisors.ShortClosure

section
open scoped Classical BigOperators
open PortSubdivision WeightedMoore
variable {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)
    (allowed : D → Prop) (z : V)

end
open scoped Classical BigOperators
open PortSubdivision WeightedMoore
variable {V D : Type} (Γ : PortGraph V D)

namespace ReducedPath
variable {Γ} {a b c : V} {p q : List D}
end ReducedPath

variable [Fintype V] [Fintype D]

end TorsionFreeZeroDivisors.ShortClosure

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
open OAI.TorsionFreeZeroDivisors OAI.TorsionFreeZeroDivisors.SampleGraph ActualPatternEvent in
theorem solution (Bnd K I : ℕ) (hK : 0<K) (hI : 0<I) :
    ∀ᶠ rep in Filter.atTop,∀ (x : VA rep) (y : VB rep),
      ∃ r∈samples rep,GraphSample.Diameters rep r ∧
        IsEmpty (BoundedSystem Bnd K I rep r x y) :=
  OAI.TorsionFreeZeroDivisors.SampleGraph.exists_avoiding_dev Bnd K I hK hI
