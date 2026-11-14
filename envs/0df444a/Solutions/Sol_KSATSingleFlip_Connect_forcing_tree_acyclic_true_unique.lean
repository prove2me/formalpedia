-- Prove2me | solution 1 for KSATSingleFlip.Connect.forcing_tree_acyclic_true_unique
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:05:21.877194+00:00
-- url     : https://prove2.me/submissions/82cf462a-a67c-416c-be41-b0531e7861c6

import Definitions.Def_KSATSingleFlip_Connect_FactorGraph

open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

variable {n : ℕ} {Φ : GFormula (Fin n)} {σ : Fin n → Bool}

def auditTreeVertices (T : ForcingTree Φ σ) : Set (Fin n ⊕ Fin Φ.length) :=
  {v | match v with | Sum.inl u => u ∈ T.vars | Sum.inr _ => True}

def auditTreeGraph (T : ForcingTree Φ σ) : SimpleGraph (auditTreeVertices T) :=
  (factorGraph Φ).induce (auditTreeVertices T)

def auditVar (T : ForcingTree Φ σ) (u : Fin n) (hu : u ∈ T.vars) : auditTreeVertices T :=
  ⟨Sum.inl u, hu⟩

def auditClause (T : ForcingTree Φ σ) (c : Fin Φ.length) : auditTreeVertices T :=
  ⟨Sum.inr c, trivial⟩

theorem audit_tree_adj (T : ForcingTree Φ σ) (u : Fin n) (hu : u ∈ T.vars)
    (c : Fin Φ.length) (hc : u ∈ vbl (Φ.get c)) :
    (auditTreeGraph T).Adj (auditVar T u hu) (auditClause T c) := by
  have hs : (Φ.get c u).isSome := by simpa [vbl] using hc
  change (factorGraph Φ).Adj (Sum.inl u) (Sum.inr c)
  simp only [factorGraph, SimpleGraph.fromRel_adj]
  refine ⟨by simp, Or.inl ⟨u, c, rfl, rfl, hs⟩⟩

theorem audit_tree_parent_scope (T : ForcingTree Φ σ) (c : Fin Φ.length) (hc : c ∈ T.cls) :
    T.parent c ∈ vbl (Φ.get c) := by
  have hm : T.parent c ∈ satSet σ (Φ.get c) := by rw [T.forces c hc]; simp
  have hval : Φ.get c (T.parent c) = some (σ (T.parent c)) := (Finset.mem_filter.mp hm).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [hval]
  rfl

/-- Removing any clause not used by the tree leaves all tree variables connected. -/
theorem audit_tree_reachable_avoiding (T : ForcingTree Φ σ) (c : Fin Φ.length) (hc : c ∉ T.cls) :
    ∀ u (hu : u ∈ T.vars), ((auditTreeGraph T).deleteIncidenceSet (auditClause T c)).Reachable
      (auditVar T T.root T.root_mem) (auditVar T u hu) := by
  have h : ∀ d : ℕ, ∀ u (hu : u ∈ T.vars), T.depth u = d →
      ((auditTreeGraph T).deleteIncidenceSet (auditClause T c)).Reachable
      (auditVar T T.root T.root_mem) (auditVar T u hu) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro u hu hdepth
      by_cases hroot : u = T.root
      · subst u
        exact SimpleGraph.Reachable.refl _
      · obtain ⟨e, ⟨he, hechild⟩, _⟩ := T.unique_parent u hu hroot
        have hp := T.parent_mem e he
        have hdep := T.depth_child e he
        rw [hechild, hdepth] at hdep
        have hlt : T.depth (T.parent e) < d := by omega
        have hr := ih (T.depth (T.parent e)) hlt (T.parent e) hp rfl
        have hne : e ≠ c := fun h => hc (h ▸ he)
        have h1 : ((auditTreeGraph T).deleteIncidenceSet (auditClause T c)).Adj
            (auditVar T (T.parent e) hp) (auditClause T e) := by
          rw [SimpleGraph.deleteIncidenceSet_adj]
          refine ⟨audit_tree_adj T _ hp e (audit_tree_parent_scope T e he), ?_, ?_⟩
          · intro hh
            have hh' := congrArg Subtype.val hh
            cases hh'
          · intro hh
            apply hne
            exact Sum.inr.inj (congrArg Subtype.val hh)
        have h2 : ((auditTreeGraph T).deleteIncidenceSet (auditClause T c)).Adj
            (auditClause T e) (auditVar T u hu) := by
          rw [SimpleGraph.deleteIncidenceSet_adj]
          refine ⟨?_, ?_, ?_⟩
          · apply SimpleGraph.Adj.symm
            apply audit_tree_adj
            rw [← hechild]
            exact T.child_vbl e he
          · intro hh
            apply hne
            exact Sum.inr.inj (congrArg Subtype.val hh)
          · intro hh
            have hh' := congrArg Subtype.val hh
            cases hh'
        exact (hr.trans h1.reachable).trans h2.reachable
  intro u hu
  exact h (T.depth u) u hu rfl



/-- In a forest, distinct neighbors of w become disconnected on deleting w. -/
theorem audit_acyclic_delete_vertex {V : Type} (G : SimpleGraph V) (hG : G.IsAcyclic)
    (u v w : V) (huw : G.Adj u w) (hvw : G.Adj v w)
    (huv : (G.deleteIncidenceSet w).Reachable u v) : u = v := by
  classical
  by_contra hne
  have hbridge : G.IsBridge s(u, w) := (SimpleGraph.isAcyclic_iff_forall_isBridge.mp hG) huw
  have hno := SimpleGraph.isBridge_iff.mp hbridge
  have hle : G.deleteIncidenceSet w ≤ G.deleteEdges {s(u, w)} := by
    intro x y hxy
    rw [SimpleGraph.deleteIncidenceSet_adj] at hxy
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hxy.1, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or, not_and]
    exact ⟨fun _ hy => hxy.2.2 hy, fun hx _ => hxy.2.1 hx⟩
  have hreach : (G.deleteEdges {s(u, w)}).Reachable u v := huv.mono hle
  have hvw' : (G.deleteEdges {s(u, w)}).Adj v w := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hvw, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or, not_and]
    exact ⟨fun hvu _ => hne hvu.symm, fun hvwe _ => hvw.ne hvwe⟩
  exact hno (hreach.trans hvw'.reachable)


end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

theorem solution {n : ℕ} (Φ : GFormula (Fin n)) (σ : Fin n → Bool)
    (T : ForcingTree Φ σ)
    (hacyclic : ((factorGraph Φ).induce {v | match v with
      | Sum.inl u => u ∈ T.vars
      | Sum.inr _ => True}).IsAcyclic) :
    ∀ c : Fin Φ.length, ∀ u ∈ T.vars, ∀ v ∈ T.vars,
      Φ.get c u = some (σ u) → Φ.get c v = some (σ v) → u = v := by
  intro c u hu v hv hut hvt
  by_cases hc : c ∈ T.cls
  · have hforced := T.forces c hc
    have h1 : u ∈ satSet σ (Φ.get c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hut⟩
    have h2 : v ∈ satSet σ (Φ.get c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvt⟩
    rw [hforced] at h1 h2
    exact (Finset.mem_singleton.mp h1).trans (Finset.mem_singleton.mp h2).symm
  · have hsu : u ∈ vbl (Φ.get c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hut]; rfl⟩
    have hsv : v ∈ vbl (Φ.get c) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hvt]; rfl⟩
    have huc := audit_tree_adj T u hu c hsu
    have hvc := audit_tree_adj T v hv c hsv
    have hr1 := audit_tree_reachable_avoiding T c hc u hu
    have hr2 := audit_tree_reachable_avoiding T c hc v hv
    have hr := hr1.symm.trans hr2
    have hg : (auditTreeGraph T).IsAcyclic := hacyclic
    have heq := audit_acyclic_delete_vertex (auditTreeGraph T) hg
      (auditVar T u hu) (auditVar T v hv) (auditClause T c) huc hvc hr
    exact Sum.inl.inj (congrArg Subtype.val heq)


#print axioms solution
