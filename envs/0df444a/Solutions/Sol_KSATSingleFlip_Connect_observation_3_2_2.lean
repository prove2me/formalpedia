-- Prove2me | solution 2 for KSATSingleFlip.Connect.observation_3_2
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:06:01.358194+00:00
-- url     : https://prove2.me/submissions/2fb8cb7e-498d-4f3c-808e-54ca74f1feb5

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



theorem audit_tree_acyclic_true_unique {n : ℕ} (Φ : GFormula (Fin n)) (σ : Fin n → Bool)
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



/-- Every finite set of variables admits a bottom-up depth ordering. -/
theorem audit_depth_order {V : Type} [DecidableEq V]
    (s : Finset V) (depth : V → ℕ) :
    ∃ order : List V, order.Nodup ∧ order.toFinset = s ∧
      order.Pairwise (fun u v => depth v ≤ depth u) := by
  let rel : V → V → Bool := fun u v => decide (depth v ≤ depth u)
  let order := s.toList.mergeSort rel
  have hp : order.Perm s.toList := List.mergeSort_perm _ _
  refine ⟨order, hp.nodup_iff.mpr s.nodup_toList, ?_, ?_⟩
  · ext x
    simpa using hp.mem_iff (a := x)
  · have hs := List.pairwise_mergeSort (le := rel) (by
      intro a b c hab hbc
      dsimp [rel] at *
      simp only [decide_eq_true_eq] at *
      omega) (by
      intro a b
      dsimp [rel]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total _ _) s.toList
    simpa [order, rel] using hs



/-- In a bottom-up order, a deeper listed vertex appears in every prefix
which contains its shallower ancestor. -/
theorem audit_depth_prefix {V : Type} [DecidableEq V] (depth : V → ℕ)
    (order : List V) (ho : order.Pairwise (fun u v => depth v ≤ depth u))
    (parent child : V) (hc : child ∈ order) (hdepth : depth parent < depth child)
    (i : ℕ) (hp : parent ∈ order.take i) : child ∈ order.take i := by
  by_contra hnot
  have hchild : child ∈ order.drop i := by
    have h : child ∈ order.take i ++ order.drop i := by simpa using hc
    exact (List.mem_append.mp h).resolve_left hnot
  have hpair : (order.take i ++ order.drop i).Pairwise (fun u v => depth v ≤ depth u) := by
    simpa using ho
  have hle := hpair.rel_of_mem_append hp hchild
  omega

/-- Every state in a flip scan is the fold over some prefix. -/
theorem audit_scan_state_prefix {n : ℕ} (order : List (Fin n)) (σ z : Fin n → Bool)
    (hz : z ∈ order.scanl (fun x u => flip x u) σ) :
    ∃ i ≤ order.length, z = (order.take i).foldl (fun x u => flip x u) σ := by
  obtain ⟨i, hi, hz⟩ := List.mem_iff_getElem.mp hz
  refine ⟨i, ?_, ?_⟩
  · simpa using hi
  · simpa [List.getElem_scanl hi] using hz.symm



theorem audit_scan_hamming_flip {n : ℕ} (z : Fin n → Bool) (u : Fin n) :
    hamming z (flip z u) = 1 := by
  have hs : disagree z (flip z u) = {u} := by
    ext v
    by_cases hv : v = u
    · subst v
      have : z u ≠ flip z u u := by
        simp only [flip, Function.update_self]
        cases h : z u <;> simp
      simpa [disagree] using this
    · simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      rw [show flip z u v = z v from Function.update_of_ne hv _ _]
      simp [hv]
  simp [hamming, hs]

theorem audit_scan_flip_chain {n : ℕ} (order : List (Fin n)) (σ : Fin n → Bool) :
    (order.scanl (fun z u => flip z u) σ).IsChain (fun a b => hamming a b = 1) := by
  induction order generalizing σ with
  | nil => simp
  | cons v rest ih =>
    cases rest with
    | nil => simpa using audit_scan_hamming_flip σ v
    | cons w rest =>
      simp only [List.scanl_cons]
      apply List.isChain_cons_cons.mpr
      refine ⟨audit_scan_hamming_flip σ v, ?_⟩
      simpa only [List.scanl_cons] using ih (flip σ v)

/-- If all intermediate states satisfy the formula, the scan is a satisfying
single-flip path of exactly the number of listed flips. -/
theorem audit_scan_flip_path {n : ℕ} (Φ : GFormula (Fin n))
    (σ : Fin n → Bool) (order : List (Fin n))
    (hs : ∀ z ∈ order.scanl (fun z u => flip z u) σ, FSat z Φ) :
    IsSatPath Φ (order.scanl (fun z u => flip z u) σ) σ
      (order.foldl (fun z u => flip z u) σ) ∧
    pathLength (order.scanl (fun z u => flip z u) σ) = order.length := by
  constructor
  · unfold IsSatPath IsPathIn
    refine ⟨List.head?_scanl, List.getLast?_scanl, ?_, audit_scan_flip_chain order σ⟩
    intro z hz
    simpa [sols] using hs z hz
  · simp [pathLength]

/-- A no-duplicate scan flips precisely the listed coordinates. -/
theorem audit_fold_flips_at {n : ℕ} (order : List (Fin n)) (hn : order.Nodup)
    (σ : Fin n → Bool) (u : Fin n) :
    order.foldl (fun z v => flip z v) σ u = if u ∈ order then !σ u else σ u := by
  induction order generalizing σ with
  | nil => simp
  | cons v rest ih =>
    have hv : v ∉ rest := (List.nodup_cons.mp hn).1
    have hr : rest.Nodup := (List.nodup_cons.mp hn).2
    rw [List.foldl_cons, ih hr]
    by_cases huv : u = v
    · subst u
      simp [hv, flip]
    · have hf : flip σ v u = σ u := Function.update_of_ne huv _ _
      simp [huv, Ne.symm huv, hf]

theorem audit_fold_flips_disagree {n : ℕ} (order : List (Fin n)) (hn : order.Nodup)
    (σ : Fin n → Bool) :
    disagree σ (order.foldl (fun z v => flip z v) σ) = order.toFinset := by
  ext u
  simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
  rw [audit_fold_flips_at order hn]
  by_cases hu : u ∈ order <;> cases h : σ u <;> simp [hu, h]



/-- Clause preservation requires only that no clause have two originally true
literals in the tree. Acyclicity is one way to obtain that condition. -/
theorem audit_tree_flip_of_true_unique {n : ℕ} (Φ : GFormula (Fin n)) (σ : Fin n → Bool)
    (T : ForcingTree Φ σ) (hσ : σ ∈ sols Φ) (hT : T.CompleteIn Finset.univ)
    (hsep : ∀ c : Fin Φ.length, ∀ u ∈ T.vars, ∀ v ∈ T.vars,
      Φ.get c u = some (σ u) → Φ.get c v = some (σ v) → u = v)
    (order : List (Fin n)) (hn : order.Nodup) (hv : order.toFinset = T.vars)
    (ho : order.Pairwise (fun u v => T.depth v ≤ T.depth u)) :
    ∀ z ∈ order.scanl (fun z u => flip z u) σ, FSat z Φ := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := audit_scan_state_prefix order σ z hz
  let pre := order.take i
  have hpre : pre.Nodup := hn.take
  have heq (u : Fin n) : pre.foldl (fun z u => flip z u) σ u =
      if u ∈ pre then !σ u else σ u := audit_fold_flips_at pre hpre σ u
  have hin (u : Fin n) (hu : u ∈ pre) : u ∈ T.vars := by
    rw [← hv, List.mem_toFinset]
    exact List.mem_of_mem_take hu
  intro C hC
  obtain ⟨c, rfl⟩ := List.mem_iff_get.mp hC
  have hσsat : ClauseSat σ (Φ.get c) := (by simpa [sols] using hσ : FSat σ Φ) _ (Φ.get_mem c)
  by_cases hs : ∃ u, Φ.get c u = some (σ u) ∧ u ∉ pre
  · obtain ⟨u, hu, hnot⟩ := hs
    exact ⟨u, by rw [heq, if_neg hnot]; exact hu⟩
  · obtain ⟨v, hvtrue⟩ := hσsat
    have hvpre : v ∈ pre := by
      by_contra hnot
      exact hs ⟨v, hvtrue, hnot⟩
    have hvT : v ∈ T.vars := hin v hvpre
    have hforced : Forces σ (Φ.get c) v := by
      unfold Forces
      ext u
      simp only [satSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hut
        have hupre : u ∈ pre := by
          by_contra hnot
          exact hs ⟨u, hut, hnot⟩
        exact hsep c u (hin u hupre) v hvT hut hvtrue
      · rintro rfl
        exact hvtrue
    have hcT := (hT.2 v hvT c (Finset.mem_univ c) hforced)
    have hchild : T.child c ∈ T.vars := T.child_mem c hcT.1
    have hcpre : T.child c ∈ pre := by
      apply audit_depth_prefix T.depth order ho v (T.child c)
      · rw [← hv, List.mem_toFinset] at hchild
        exact hchild
      · have hh := T.depth_child c hcT.1
        rw [hcT.2] at hh
        omega
      · exact hvpre
    have hcne : T.child c ≠ v := by
      intro he
      have hh := T.depth_child c hcT.1
      rw [hcT.2, he] at hh
      omega
    have hcfalse : Φ.get c (T.child c) = some (!(σ (T.child c))) := by
      have hsome : (Φ.get c (T.child c)).isSome := by
        simpa [vbl] using T.child_vbl c hcT.1
      have hntrue : Φ.get c (T.child c) ≠ some (σ (T.child c)) := by
        intro he
        have hm : T.child c ∈ satSet σ (Φ.get c) := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
        rw [hforced] at hm
        exact hcne (Finset.mem_singleton.mp hm)
      cases hsC : Φ.get c (T.child c) with
      | none => simp [hsC] at hsome
      | some b => cases hsc : σ (T.child c) <;> cases b <;> simp_all
    refine ⟨T.child c, ?_⟩
    rw [heq, if_pos hcpre]
    exact hcfalse


end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

theorem solution {n : ℕ} (Φ : GFormula (Fin n)) (σ : Fin n → Bool)
    (T : ForcingTree Φ σ) (hσ : σ ∈ sols Φ) (hT : T.CompleteIn Finset.univ)
    (hacyclic : ((factorGraph Φ).induce {v | match v with
      | Sum.inl u => u ∈ T.vars
      | Sum.inr _ => True}).IsAcyclic) :
    (∃ order : List (Fin n), order.Nodup ∧ order.toFinset = T.vars ∧
      order.Pairwise (fun u v => T.depth v ≤ T.depth u)) ∧
    ∀ order : List (Fin n), order.Nodup → order.toFinset = T.vars →
      order.Pairwise (fun u v => T.depth v ≤ T.depth u) →
      ∃ τ : Fin n → Bool,
        IsSatPath Φ (order.scanl (fun z u => KSATSingleFlip.Connect.flip z u) σ) σ τ ∧
        pathLength (order.scanl (fun z u => KSATSingleFlip.Connect.flip z u) σ) = T.vars.card ∧
        disagree σ τ = T.vars := by
  constructor
  · exact audit_depth_order T.vars T.depth
  · intro order hn hv ho
    have hsat := audit_tree_flip_of_true_unique Φ σ T hσ hT
      (audit_tree_acyclic_true_unique Φ σ T hacyclic) order hn hv ho
    have hpath := audit_scan_flip_path Φ σ order hsat
    refine ⟨order.foldl (fun z u => KSATSingleFlip.Connect.flip z u) σ, hpath.1, ?_, ?_⟩
    · rw [hpath.2, ← List.toFinset_card_of_nodup hn, hv]
    · rw [audit_fold_flips_disagree order hn, hv]

#print axioms solution
