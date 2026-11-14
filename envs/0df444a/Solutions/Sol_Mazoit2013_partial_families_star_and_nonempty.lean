-- Prove2me | solution 1 for Mazoit2013.partial_families_star_and_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T23:15:49.147206+00:00
-- url     : https://prove2.me/submissions/f4018d70-e29d-473e-bffe-c13f2624e485

import Definitions.Def_Mazoit2013_PartialDecompositions
import Mathlib.Tactic.Push
open RobertsonSeymour1986.GM5 StableMSR.Recovery.Havens
namespace StarAux
variable {V : Type} [DecidableEq V]
lemma mem_of_walk_closed {G : SimpleGraph V} {C D : Finset V}
    (hclosed : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ D → y ∈ C)
    {u v : V} (p : G.Walk u v) (hu : u ∈ C)
    (hp : ∀ z ∈ p.support, z ∈ D) : v ∈ C := by
  induction p with
  | nil => exact hu
  | @cons u v w huv p ih =>
    apply ih (hclosed u hu v huv (hp v (by simp)))
    intro z hz
    exact hp z (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hz)

lemma flap_contains_touching {G : SimpleGraph V} {W C D : Finset V}
    (hC : IsFlap G W C) (hD : ConnectedSet G D)
    (havoid : Disjoint W D) (htouch : Touch G C D) : D ⊆ C := by
  obtain ⟨u, huD, huC⟩ : ∃ u, u ∈ D ∧ u ∈ C := by
    rcases htouch with ⟨u, huC, huD⟩ | ⟨x, hx, y, hy, hxy⟩
    · exact ⟨u, huD, huC⟩
    · exact ⟨y, hy, hC.closed x hx y hxy (fun hyW =>
        Finset.disjoint_left.mp havoid hyW hy)⟩
  intro v hv
  obtain ⟨p, hp⟩ := hD.2 u huD v hv
  exact mem_of_walk_closed (fun x hx y hxy hy =>
    hC.closed x hx y hxy (fun hyW => Finset.disjoint_left.mp havoid hyW hy)) p huC hp
noncomputable def componentWithin (G : SimpleGraph V) (U : Finset V) (u : V) : Finset V :=
  by classical exact U.filter (fun v => ∃ p : G.Walk u v, ∀ z ∈ p.support, z ∈ U)

lemma mem_componentWithin {G : SimpleGraph V} {U : Finset V} {u v : V} :
    v ∈ componentWithin G U u ↔ v ∈ U ∧ ∃ p : G.Walk u v, ∀ z ∈ p.support, z ∈ U := by
  classical
  simp only [componentWithin, Finset.mem_filter]

lemma componentWithin_subset (G : SimpleGraph V) (U : Finset V) (u : V) :
    componentWithin G U u ⊆ U := by
  intro v hv
  exact (mem_componentWithin.mp hv).1

lemma self_mem_componentWithin {G : SimpleGraph V} {U : Finset V} {u : V} (hu : u ∈ U) :
    u ∈ componentWithin G U u := by
  refine mem_componentWithin.mpr ⟨hu, .nil, ?_⟩
  simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using fun z (hz : z = u) => hz ▸ hu

lemma support_subset_componentWithin {G : SimpleGraph V} {U : Finset V}
    {u v : V} (p : G.Walk u v) (hp : ∀ z ∈ p.support, z ∈ U) :
    ∀ z ∈ p.support, z ∈ componentWithin G U u := by
  intro z hz
  refine mem_componentWithin.mpr ⟨hp z hz, p.takeUntil z hz, ?_⟩
  intro w hw
  exact hp w (p.support_takeUntil_subset_support hz hw)

lemma componentWithin_connected {G : SimpleGraph V} {U : Finset V} {u : V} (hu : u ∈ U) :
    ConnectedSet G (componentWithin G U u) := by
  refine ⟨⟨u, self_mem_componentWithin hu⟩, ?_⟩
  intro x hx y hy
  obtain ⟨_, p, hp⟩ := mem_componentWithin.mp hx
  obtain ⟨_, q, hq⟩ := mem_componentWithin.mp hy
  refine ⟨p.reverse.append q, ?_⟩
  intro z hz
  rcases (SimpleGraph.Walk.mem_support_append_iff p.reverse q).mp hz with hz | hz
  · apply support_subset_componentWithin p hp z
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
  · exact support_subset_componentWithin q hq z hz

lemma componentWithin_closed {G : SimpleGraph V} {U : Finset V} {u x y : V}
    (hx : x ∈ componentWithin G U u) (hxy : G.Adj x y) (hy : y ∈ U) :
    y ∈ componentWithin G U u := by
  obtain ⟨_, p, hp⟩ := mem_componentWithin.mp hx
  refine mem_componentWithin.mpr ⟨hy, p.concat hxy, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_concat] at hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hp z hz
  · simpa only [List.mem_singleton] using (show z = y from List.mem_singleton.mp hz) ▸ hy
end StarAux
open StarAux
namespace StableMSR.Recovery.PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]
lemma component_exists (G : SimpleGraph V) (S : Finset V) {v : V} (hv : v ∉ S) :
    ∃ C ∈ components G S, v ∈ C := by
  refine ⟨componentWithin G Sᶜ v, mem_components.mpr ⟨componentWithin_connected (Finset.mem_compl.mpr hv), ?_, ?_⟩,
    self_mem_componentWithin (Finset.mem_compl.mpr hv)⟩
  · exact Finset.disjoint_left.mpr (fun x hx hC =>
      (Finset.mem_compl.mp (componentWithin_subset G Sᶜ v hC)) hx)
  · intro x hx y hxy hy
    exact componentWithin_closed hx hxy (Finset.mem_compl.mpr hy)
lemma components_eq_of_mem {G : SimpleGraph V} {S C D : Finset V}
    (hC : C ∈ components G S) (hD : D ∈ components G S)
    {v : V} (hvC : v ∈ C) (hvD : v ∈ D) : C = D := by
  have c := mem_components.mp hC
  have d := mem_components.mp hD
  exact Finset.Subset.antisymm
    (flap_contains_touching d c.connected c.avoids (.inl ⟨v,hvD,hvC⟩))
    (flap_contains_touching c d.connected d.avoids (.inl ⟨v,hvC,hvD⟩))
lemma star_decomposition (G : SimpleGraph V) (S : Finset V) :
    IsTreeDecomposition G (SimpleGraph.starGraph (none : Option ↥(components G S))) (starBag G S) := by
  classical
  refine ⟨SimpleGraph.isTree_starGraph _, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ S
    · exact ⟨none,hv⟩
    · obtain ⟨C,hC,hvC⟩ := component_exists G S hv
      exact ⟨some ⟨C,hC⟩,Finset.mem_union_right S hvC⟩
  · intro x y hxy
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · exact ⟨none,hx,hy⟩
      · obtain ⟨C,hC,hyC⟩ := component_exists G S hy
        exact ⟨some ⟨C,hC⟩,Finset.mem_union_left _ hx,Finset.mem_union_right _ hyC⟩
    · obtain ⟨C,hC,hxC⟩ := component_exists G S hx
      refine ⟨some ⟨C,hC⟩,Finset.mem_union_right _ hxC,?_⟩
      by_cases hy : y ∈ S
      · exact Finset.mem_union_left _ hy
      · exact Finset.mem_union_right _ ((mem_components.mp hC).closed x hxC y hxy hy)
  · intro s t u p hp ht v hv
    obtain ⟨hvs,hvu⟩ := Finset.mem_inter.mp hv
    by_cases hvS : v ∈ S
    · cases t with
      | none => exact hvS
      | some C => exact Finset.mem_union_left _ hvS
    · have heq : s = u := by
        cases s with
        | none => exact False.elim (hvS hvs)
        | some C =>
          cases u with
          | none => exact False.elim (hvS hvu)
          | some D =>
            congr 1
            apply Subtype.ext
            exact components_eq_of_mem C.property D.property
              ((Finset.mem_union.mp hvs).resolve_left hvS)
              ((Finset.mem_union.mp hvu).resolve_left hvS)
      subst u
      have hpath : (⟨p,hp⟩ : (SimpleGraph.starGraph (none : Option ↥(components G S))).Path s s) =
          ⟨.nil, by simp⟩ :=
        (SimpleGraph.isTree_starGraph _).isAcyclic.subsingleton_path s s |>.elim _ _
      have hpnil : p = .nil := congrArg Subtype.val hpath
      subst p
      have hts : t = s := by simpa using ht
      subst t
      exact hvs
/-- Large bags are leaves whose unique neighbor is small. -/
lemma flap_nonempty {T : Type} {G : SimpleGraph V} {b : ℕ} {tree : SimpleGraph T}
    {bags : T → Finset V} (h : IsPartial G b tree bags) {C : Finset V}
    (hC : C ∈ flaps b tree bags) : C.Nonempty := by
  obtain ⟨t,u,hbig,htu,rfl⟩ := mem_flaps.mp hC
  obtain ⟨v,_,hv,hunique⟩ := h.2.2 t hbig
  have huv := hunique u htu
  subst u
  apply Finset.sdiff_nonempty.mpr
  intro hsub
  have := Finset.card_le_card hsub
  omega
lemma flaps_nonempty {T : Type} [Fintype T] {G : SimpleGraph V} {w : ℕ}
    {tree : SimpleGraph T} {bags : T → Finset V}
    (h : IsPartial G (w+1) tree bags) (hwidth : ¬ TreewidthLE G w) :
    (flaps (w+1) tree bags).Nonempty := by
  classical
  by_contra hn
  apply hwidth
  refine ⟨T,inferInstance,tree,bags,h.1,?_⟩
  intro t
  by_contra ht
  have hbig : w+1 < (bags t).card := Nat.lt_of_not_ge ht
  obtain ⟨u,htu,_⟩ := h.2.2 t hbig
  exact hn ⟨bags t \ bags u,mem_flaps.mpr ⟨t,u,hbig,htu,rfl⟩⟩
lemma star_partial (G : SimpleGraph V) (S : Finset V) (b : ℕ) (hS : S.card ≤ b) :
    IsPartial G b (SimpleGraph.starGraph (none : Option ↥(components G S))) (starBag G S) := by
  refine ⟨star_decomposition G S,⟨none,hS⟩,?_⟩
  intro t ht
  cases t with
  | none => exact False.elim (Nat.not_lt_of_ge hS ht)
  | some C =>
    refine ⟨none,?_,hS,?_⟩
    · simp [SimpleGraph.starGraph_adj]
    · intro v hv
      exact (SimpleGraph.starGraph_adj.mp hv).2.resolve_left (by simp)
lemma star_flap_characterization (G : SimpleGraph V) (S : Finset V) (b : ℕ)
    (hS : S.card ≤ b) (C : Finset V) :
    C ∈ flaps b (SimpleGraph.starGraph (none : Option ↥(components G S))) (starBag G S) ↔
      IsFlap G S C ∧ b < (S ∪ C).card := by
  classical
  constructor
  · intro hC
    obtain ⟨t,u,hbig,htu,hC⟩ := mem_flaps.mp hC
    cases t with
    | none => exact False.elim (Nat.not_lt_of_ge hS hbig)
    | some D =>
      have hu : u = none := by exact (SimpleGraph.starGraph_adj.mp htu).2.resolve_left (by simp)
      subst u
      have hD := mem_components.mp D.property
      have heq : (S ∪ D.val) \ S = D.val := by
        ext x
        simp only [Finset.mem_sdiff,Finset.mem_union]
        constructor
        · rintro ⟨hx,hn⟩; exact hx.resolve_left hn
        · intro hx
          exact ⟨Or.inr hx,fun hs => Finset.disjoint_left.mp hD.avoids hs hx⟩
      change C = (S ∪ D.val) \ S at hC
      rw [heq] at hC
      subst C
      exact ⟨hD,hbig⟩
  · rintro ⟨hC,hbig⟩
    refine mem_flaps.mpr ⟨some ⟨C,mem_components.mpr hC⟩,none,hbig,by simp [SimpleGraph.starGraph_adj],?_⟩
    change C = (S ∪ C) \ S
    ext x
    simp only [Finset.mem_sdiff,Finset.mem_union]
    constructor
    · intro hx
      exact ⟨Or.inr hx,fun hs => Finset.disjoint_left.mp hC.avoids hs hx⟩
    · rintro ⟨hx,hn⟩; exact hx.resolve_left hn
/-- A family realized by an actual finite partial tree decomposition. -/
lemma partialFamilies_nonempty_members (G : SimpleGraph V) (w : ℕ)
    (hwidth : ¬ TreewidthLE G w) : ∀ d ∈ partialFamilies G (w+1), d.Nonempty := by
  intro d hd
  obtain ⟨T,ht,tree,bags,h,rfl⟩ := mem_partialFamilies.mp hd
  exact flaps_nonempty h hwidth
/-- Every small deletion set has a realized star family of connected flaps avoiding it. -/
theorem partialFamilies_star (G : SimpleGraph V) (w : ℕ) (S : Finset V)
    (hS : S.card < w+2) :
    ∃ d ∈ partialFamilies G (w+1), ∀ C ∈ d, ConnectedSet G C ∧ Disjoint S C := by
  classical
  have hs : S.card ≤ w+1 := by omega
  refine ⟨flaps (w+1) (SimpleGraph.starGraph (none : Option ↥(components G S))) (starBag G S),?_,?_⟩
  · exact mem_partialFamilies.mpr ⟨Option ↥(components G S),inferInstance,_,_,star_partial G S _ hs,rfl⟩
  · intro C hC
    have hc := ((star_flap_characterization G S _ hs C).mp hC).1
    exact ⟨hc.connected,hc.avoids⟩
end StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.PartialDecompositions
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : ℕ) (hwidth : ¬ TreewidthLE G w) :
    (∀ d ∈ partialFamilies G (w+1), d.Nonempty) ∧
    (∀ S : Finset V, S.card < w+2 → ∃ d ∈ partialFamilies G (w+1),
      ∀ C ∈ d, ConnectedSet G C ∧ Disjoint S C) :=
  ⟨partialFamilies_nonempty_members G w hwidth,partialFamilies_star G w⟩
