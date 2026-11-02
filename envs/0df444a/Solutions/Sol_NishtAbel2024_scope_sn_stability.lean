-- Prove2me | solution 1 for NishtAbel2024.scope_sn_stability
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:57:44.085771+00:00
-- url     : https://prove2.me/submissions/10be9607-d407-41f7-a5f4-76497039f9b1

import Mathlib
import Definitions.Def_NishtAbel2024_Syntax
import Definitions.Def_NishtAbel2024_Semantics
import Definitions.Def_NishtAbel2024_ScopeAux
namespace NishtAbel2024

/-- A closed earlier declaration cannot reference any new block name. -/
theorem scope_global_no_block_ref {sig : GlobalSig} {block : MutualBlock}
    (h : scopeBlockExtension sig block) (decl : FunDecl) (hdecl : decl ∈ sig)
    (f : FunName) (href : f ∈ scopeClausesRefs decl.clauses) : f ∉ scopeNames block := by
  intro hblock
  exact h.2.2.1 f hblock (h.1.2 decl hdecl f href)

/-- Adding a fresh block cannot make a reference to an existing global name
select a declaration from that block. -/
theorem scope_existing_name_resolves_globally {sig : GlobalSig} {block : MutualBlock}
    (h : scopeBlockExtension sig block) (f : FunName) (hf : f ∈ scopeNames sig)
    (decl : FunDecl) (hdecl : decl ∈ sig ++ block) (hname : decl.name = f) : decl ∈ sig := by
  rcases List.mem_append.mp hdecl with hglobal | hblock
  · exact hglobal
  · have hnew : decl.name ∈ scopeNames block := by
      exact List.mem_map.mpr ⟨decl, hblock, rfl⟩
    exact False.elim (h.2.2.1 decl.name hnew (hname ▸ hf))

/-- For an existing global name the full set of matching declarations is
unchanged by an admissible block extension. -/
theorem scope_existing_name_matches_iff {sig : GlobalSig} {block : MutualBlock}
    (h : scopeBlockExtension sig block) (f : FunName) (hf : f ∈ scopeNames sig)
    (decl : FunDecl) :
    (decl ∈ sig ++ block ∧ decl.name = f) ↔ (decl ∈ sig ∧ decl.name = f) := by
  constructor
  · intro ⟨hdecl, hname⟩
    exact ⟨scope_existing_name_resolves_globally h f hf decl hdecl hname, hname⟩
  · intro ⟨hdecl, hname⟩
    exact ⟨List.mem_append_left _ hdecl, hname⟩

/-- Every syntactic function reference in an earlier declaration continues
to resolve only to earlier declarations. -/
theorem scope_global_body_resolution_stable {sig : GlobalSig} {block : MutualBlock}
    (h : scopeBlockExtension sig block) (owner : FunDecl) (howner : owner ∈ sig)
    (f : FunName) (href : f ∈ scopeClausesRefs owner.clauses)
    (decl : FunDecl) (hdecl : decl ∈ sig ++ block) (hname : decl.name = f) : decl ∈ sig := by
  exact scope_existing_name_resolves_globally h f (h.1.2 owner howner f href) decl hdecl hname

/-- A reference in the head remains present under any application spine. -/
theorem scope_ref_in_appSpine {t : Term} {f : FunName}
    (hf : f ∈ scopeTermRefs t) (es : List Elim) :
    f ∈ scopeTermRefs (Term.appSpine t es) := by
  induction es generalizing t with
  | nil => exact hf
  | cons e es ih =>
    change f ∈ scopeTermRefs (Term.appSpine (.app t e) es)
    apply ih
    exact List.mem_append_left _ hf


end NishtAbel2024


-- SignatureSubstitution

namespace NishtAbel2024

/-- Every syntactic function reference in t belongs to the allowed names. -/
def ScopeAllowed (names : List FunName) (t : Term) : Prop :=
  ∀ f ∈ scopeTermRefs t, f ∈ names

/-- Every term supplied by a substitution obeys the same restriction. -/
def ScopeSubst (names : List FunName) (σ : TermSubst) : Prop :=
  ∀ p ∈ σ, ScopeAllowed names p.2

mutual

theorem scope_substTerms (names : List FunName) (t : Term) (σ : TermSubst)
    (ht : ScopeAllowed names t) (hσ : ScopeSubst names σ) :
    ScopeAllowed names (t.substTerms σ) := by
  cases t with
  | var x =>
    cases hfind : σ.find? (fun p => p.1 == x) with
    | none => simp [ScopeAllowed, Term.substTerms, hfind, scopeTermRefs]
    | some p =>
      have hp : p ∈ σ := List.mem_of_find?_eq_some hfind
      cases p with
      | mk k v =>
        simpa [Term.substTerms, hfind] using hσ (k, v) hp
  | funRef f as => exact ht
  | app r e =>
    intro f hf
    simp only [Term.substTerms, scopeTermRefs, List.mem_append] at hf
    rcases hf with hf | hf
    · exact scope_substTerms names r σ (fun g hg => ht g (List.mem_append_left _ hg)) hσ f hf
    · exact scope_substElim names e σ (fun g hg => ht g (List.mem_append_right _ hg)) hσ f hf
  | unit => exact ht
  | pair a b =>
    intro f hf
    simp only [Term.substTerms, scopeTermRefs, List.mem_append] at hf
    rcases hf with hf | hf
    · exact scope_substTerms names a σ (fun g hg => ht g (List.mem_append_left _ hg)) hσ f hf
    · exact scope_substTerms names b σ (fun g hg => ht g (List.mem_append_right _ hg)) hσ f hf
  | cons c a t => exact scope_substTerms names t σ ht hσ
  | pack G t => exact scope_substTerms names t σ ht hσ
  | lamClauses ds => exact scope_substClauses names ds σ ht hσ
  | ascr t A => exact scope_substTerms names t σ ht hσ

theorem scope_substElim (names : List FunName) (e : Elim) (σ : TermSubst)
    (he : ∀ f ∈ scopeElimRefs e, f ∈ names) (hσ : ScopeSubst names σ) :
    ∀ f ∈ scopeElimRefs (e.substTerms σ), f ∈ names := by
  cases e with
  | term t => exact scope_substTerms names t σ he hσ
  | tyArg G => simp [Elim.substTerms, scopeElimRefs]
  | proj d a => simp [Elim.substTerms, scopeElimRefs]

theorem scope_substClause (names : List FunName) (d : Clause) (σ : TermSubst)
    (hd : ∀ f ∈ scopeClauseRefs d, f ∈ names) (hσ : ScopeSubst names σ) :
    ∀ f ∈ scopeClauseRefs (d.substTerms σ), f ∈ names := by
  cases d with
  | mk qs t =>
    apply scope_substTerms names t _ hd
    intro p hp
    exact hσ p (List.mem_filter.mp hp).1

theorem scope_substClauses (names : List FunName) (ds : List Clause) (σ : TermSubst)
    (hd : ∀ f ∈ scopeClausesRefs ds, f ∈ names) (hσ : ScopeSubst names σ) :
    ∀ f ∈ scopeClausesRefs (substTermsClauses σ ds), f ∈ names := by
  cases ds with
  | nil => simp [substTermsClauses, scopeClausesRefs]
  | cons d ds =>
    intro f hf
    simp only [substTermsClauses, scopeClausesRefs, List.mem_append] at hf
    rcases hf with hf | hf
    · exact scope_substClause names d σ (fun g hg => hd g (List.mem_append_left _ hg)) hσ f hf
    · exact scope_substClauses names ds σ (fun g hg => hd g (List.mem_append_right _ hg)) hσ f hf

end

end NishtAbel2024

-- SignatureTypeSubst

namespace NishtAbel2024

/-! Size and type substitutions change annotations but cannot introduce or
remove syntactic function references. These lemmas are purely structural;
they do not establish capture avoidance or semantic substitution soundness. -/

mutual

theorem scope_refs_subst_sizes_term (σ : SizeSubst) (t : Term) :
    scopeTermRefs (t.substSizes σ) = scopeTermRefs t := by
  cases t with
  | var x => rfl
  | funRef f as => rfl
  | app r e =>
    simp only [Term.substSizes, scopeTermRefs]
    rw [scope_refs_subst_sizes_term σ r, scope_refs_subst_sizes_elim σ e]
  | unit => rfl
  | pair a b =>
    simp only [Term.substSizes, scopeTermRefs]
    rw [scope_refs_subst_sizes_term σ a, scope_refs_subst_sizes_term σ b]
  | cons c a t =>
    simp only [Term.substSizes, scopeTermRefs]
    exact scope_refs_subst_sizes_term σ t
  | pack A t =>
    simp only [Term.substSizes, scopeTermRefs]
    exact scope_refs_subst_sizes_term σ t
  | lamClauses ds =>
    simp only [Term.substSizes, scopeTermRefs]
    exact scope_refs_subst_sizes_clauses σ ds
  | ascr t A =>
    simp only [Term.substSizes, scopeTermRefs]
    exact scope_refs_subst_sizes_term σ t
termination_by sizeOf t

theorem scope_refs_subst_sizes_elim (σ : SizeSubst) (e : Elim) :
    scopeElimRefs (e.substSizes σ) = scopeElimRefs e := by
  cases e with
  | term t =>
    simp only [Elim.substSizes, scopeElimRefs]
    exact scope_refs_subst_sizes_term σ t
  | tyArg A => rfl
  | proj d a => rfl
termination_by sizeOf e

theorem scope_refs_subst_sizes_clause (σ : SizeSubst) (d : Clause) :
    scopeClauseRefs (d.substSizes σ) = scopeClauseRefs d := by
  cases d with
  | mk qs t =>
    simp only [Clause.substSizes, scopeClauseRefs]
    exact scope_refs_subst_sizes_term _ t
termination_by sizeOf d

theorem scope_refs_subst_sizes_clauses (σ : SizeSubst) (ds : List Clause) :
    scopeClausesRefs (substSizesClauses σ ds) = scopeClausesRefs ds := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    simp only [substSizesClauses, scopeClausesRefs]
    rw [scope_refs_subst_sizes_clause σ d, scope_refs_subst_sizes_clauses σ ds]
termination_by sizeOf ds

end

mutual

theorem scope_refs_subst_types_term (τ : TySubst) (t : Term) :
    scopeTermRefs (t.substTypes τ) = scopeTermRefs t := by
  cases t with
  | var x => rfl
  | funRef f as => rfl
  | app r e =>
    simp only [Term.substTypes, scopeTermRefs]
    rw [scope_refs_subst_types_term τ r, scope_refs_subst_types_elim τ e]
  | unit => rfl
  | pair a b =>
    simp only [Term.substTypes, scopeTermRefs]
    rw [scope_refs_subst_types_term τ a, scope_refs_subst_types_term τ b]
  | cons c a t =>
    simp only [Term.substTypes, scopeTermRefs]
    exact scope_refs_subst_types_term τ t
  | pack A t =>
    simp only [Term.substTypes, scopeTermRefs]
    exact scope_refs_subst_types_term τ t
  | lamClauses ds =>
    simp only [Term.substTypes, scopeTermRefs]
    exact scope_refs_subst_types_clauses τ ds
  | ascr t A =>
    simp only [Term.substTypes, scopeTermRefs]
    exact scope_refs_subst_types_term τ t
termination_by sizeOf t

theorem scope_refs_subst_types_elim (τ : TySubst) (e : Elim) :
    scopeElimRefs (e.substTypes τ) = scopeElimRefs e := by
  cases e with
  | term t =>
    simp only [Elim.substTypes, scopeElimRefs]
    exact scope_refs_subst_types_term τ t
  | tyArg A => rfl
  | proj d a => rfl
termination_by sizeOf e

theorem scope_refs_subst_types_clause (τ : TySubst) (d : Clause) :
    scopeClauseRefs (d.substTypes τ) = scopeClauseRefs d := by
  cases d with
  | mk qs t =>
    simp only [Clause.substTypes, scopeClauseRefs]
    exact scope_refs_subst_types_term _ t
termination_by sizeOf d

theorem scope_refs_subst_types_clauses (τ : TySubst) (ds : List Clause) :
    scopeClausesRefs (substTypesClauses τ ds) = scopeClausesRefs ds := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    simp only [substTypesClauses, scopeClausesRefs]
    rw [scope_refs_subst_types_clause τ d, scope_refs_subst_types_clauses τ ds]
termination_by sizeOf ds

end

end NishtAbel2024

-- SignatureMatchScope

namespace NishtAbel2024

/-- Every term in a substitution mentions only names in `names`. -/
def scopeMatchedSubst (names : List FunName) (σ : TermSubst) : Prop :=
  ∀ p ∈ σ, ∀ f ∈ scopeTermRefs p.2, f ∈ names

/-- Matching a scoped term binds only subterms whose function references are
also scoped. The permissive `.unit` match binds no terms. -/
theorem scope_matchPat (names : List FunName) {t : Term} {p : Pat}
    {τ : TySubst} {σ : TermSubst} (h : MatchPat t p τ σ) :
    (∀ f ∈ scopeTermRefs t, f ∈ names) → scopeMatchedSubst names σ := by
  induction h with
  | unit t => simp [scopeMatchedSubst]
  | var t x =>
    intro ht p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact ht
  | pair h₁ h₂ ih₁ ih₂ =>
    intro ht p hp
    rcases List.mem_append.mp hp with hp | hp
    · apply ih₁ ?_ p hp
      intro f hf
      exact ht f (List.mem_append_left _ hf)
    · apply ih₂ ?_ p hp
      intro f hf
      exact ht f (List.mem_append_right _ hf)
  | cons h ih =>
    intro ht
    exact ih ht
  | tyPack h ih =>
    intro ht
    exact ih ht

/-- Matching a scoped elimination produces a scoped term substitution. -/
theorem scope_matchCopat (names : List FunName) {e : Elim} {q : Copat}
    {τ : TySubst} {σ : TermSubst} (h : MatchCopat e q τ σ) :
    (∀ f ∈ scopeElimRefs e, f ∈ names) → scopeMatchedSubst names σ := by
  cases h with
  | pat h => exact scope_matchPat names h
  | tyVar G X => simp [scopeMatchedSubst]
  | proj d ma => simp [scopeMatchedSubst]

/-- Matching a list of scoped eliminations produces a scoped term substitution. -/
theorem scope_matchSpine (names : List FunName) {es : List Elim} {qs : PatSpine}
    {τ : TySubst} {σ : TermSubst} (h : MatchSpine es qs τ σ) :
    (∀ e ∈ es, ∀ f ∈ scopeElimRefs e, f ∈ names) → scopeMatchedSubst names σ := by
  induction h with
  | nil => simp [scopeMatchedSubst]
  | cons h₁ h₂ ih =>
    intro hs p hp
    rcases List.mem_append.mp hp with hp | hp
    · apply scope_matchCopat names h₁ ?_ p hp
      intro f hf
      exact hs _ (by simp) f hf
    · apply ih ?_ p hp
      intro e he f hf
      exact hs e (by simp [he]) f hf

/-- Any reference in an elimination belonging to a spine also occurs in the
whole applied term. -/
theorem scope_ref_elim_in_appSpine (t : Term) (es : List Elim)
    (e : Elim) (f : FunName) (he : e ∈ es) (hf : f ∈ scopeElimRefs e) :
    f ∈ scopeTermRefs (Term.appSpine t es) := by
  induction es generalizing t with
  | nil => simp at he
  | cons e₀ es ih =>
    simp only [List.mem_cons] at he
    change f ∈ scopeTermRefs (Term.appSpine (.app t e₀) es)
    rcases he with rfl | he
    · apply scope_ref_in_appSpine
      simp [scopeTermRefs, hf]
    · exact ih (.app t e₀) he

/-- A matching spine is scoped whenever its complete source application is scoped. -/
theorem scope_matchSpine_of_appSpine (names : List FunName) (t : Term)
    {es : List Elim} {qs : PatSpine} {τ : TySubst} {σ : TermSubst}
    (h : MatchSpine es qs τ σ)
    (ht : ∀ f ∈ scopeTermRefs (Term.appSpine t es), f ∈ names) :
    scopeMatchedSubst names σ := by
  apply scope_matchSpine names h
  intro e he f hf
  exact ht f (scope_ref_elim_in_appSpine t es e f he hf)

/-- Weak-head redexes may retain an unconsumed suffix of eliminations. -/
theorem scope_matchSpine_of_appSpine_append (names : List FunName) (t : Term)
    {es rest : List Elim} {qs : PatSpine} {τ : TySubst} {σ : TermSubst}
    (h : MatchSpine es qs τ σ)
    (ht : ∀ f ∈ scopeTermRefs (Term.appSpine t (es ++ rest)), f ∈ names) :
    scopeMatchedSubst names σ := by
  apply scope_matchSpine names h
  intro e he f hf
  exact ht f (scope_ref_elim_in_appSpine t (es ++ rest) e f (List.mem_append_left _ he) hf)

end NishtAbel2024

-- SignatureSpineScope

namespace NishtAbel2024

/-- Function references of an application spine are precisely those of its
head, followed by those of each elimination in order. -/
theorem scope_refs_appSpine (t : Term) (es : List Elim) :
    scopeTermRefs (Term.appSpine t es) = scopeTermRefs t ++ es.flatMap scopeElimRefs := by
  induction es generalizing t with
  | nil => simp [Term.appSpine]
  | cons e es ih =>
    change scopeTermRefs (Term.appSpine (.app t e) es) =
      scopeTermRefs t ++ (e :: es).flatMap scopeElimRefs
    rw [ih]
    simp [scopeTermRefs, List.append_assoc]

/-- Building an application spine from scoped parts preserves scope. -/
theorem scope_appSpine (names : List FunName) (t : Term) (es : List Elim)
    (ht : ∀ f ∈ scopeTermRefs t, f ∈ names)
    (hes : ∀ e ∈ es, ∀ f ∈ scopeElimRefs e, f ∈ names) :
    ∀ f ∈ scopeTermRefs (Term.appSpine t es), f ∈ names := by
  intro f hf
  rw [scope_refs_appSpine] at hf
  rcases List.mem_append.mp hf with h | h
  · exact ht f h
  · obtain ⟨e, he, hf⟩ := List.mem_flatMap.mp h
    exact hes e he f hf

end NishtAbel2024

-- SignatureWeakHeadScope

namespace NishtAbel2024

/-- References in a selected clause are included among references in the
whole clause list. -/
private theorem scope_clause_ref_in_clauses (ds : List Clause) (d : Clause)
    (hd : d ∈ ds) (f : FunName) (hf : f ∈ scopeClauseRefs d) :
    f ∈ scopeClausesRefs ds := by
  induction ds with
  | nil => simp at hd
  | cons d₀ ds ih =>
    simp only [List.mem_cons] at hd
    simp only [scopeClausesRefs, List.mem_append]
    rcases hd with rfl | hd
    · exact Or.inl hf
    · exact Or.inr (ih hd)

/-- The unconsumed suffix of a scoped application spine is scoped. -/
private theorem scope_spine_suffix (names : List FunName) (head : Term)
    (es rest : List Elim)
    (ht : ScopeAllowed names (Term.appSpine head (es ++ rest))) :
    ∀ e ∈ rest, ∀ f ∈ scopeElimRefs e, f ∈ names := by
  intro e he f hf
  exact ht f (scope_ref_elim_in_appSpine head (es ++ rest) e f
    (List.mem_append_right es he) hf)

/-- A weak-head step preserves the old-signature scope under a closed, fresh
block extension. This is a syntactic property only. -/
theorem scope_whd_preserves {sig : GlobalSig} {block : MutualBlock} {t u : Term}
    (hscope : scopeBlockExtension sig block)
    (ht : ScopeAllowed (scopeNames sig) t) (hstep : WhdStep sig block t u) :
    ScopeAllowed (scopeNames sig) u := by
  cases hstep with
  | ascr t A es =>
    apply scope_appSpine
    · intro f hf
      apply ht f
      apply scope_ref_in_appSpine
      exact hf
    · intro e he f hf
      exact ht f (scope_ref_elim_in_appSpine (.ascr t A) es e f he hf)
  | @lamClause Ds qs body es rest τ σ hclause hmatch =>
    have hbody : ScopeAllowed (scopeNames sig) body := by
      intro f hf
      apply ht f
      apply scope_ref_in_appSpine
      apply scope_clause_ref_in_clauses Ds (.mk qs body) hclause f
      exact hf
    have hσ : ScopeSubst (scopeNames sig) σ :=
      scope_matchSpine_of_appSpine_append (scopeNames sig) (.lamClauses Ds) hmatch ht
    have htyped : ScopeAllowed (scopeNames sig) (body.substTypes τ) := by
      intro f hf
      apply hbody f
      simpa only [scope_refs_subst_types_term] using hf
    apply scope_appSpine
    · exact scope_substTerms _ _ _ htyped hσ
    · exact scope_spine_suffix _ (.lamClauses Ds) es rest ht
  | @funClause decl as qs body es rest τ σ hdecl hclause hmatch =>
    have hname : decl.name ∈ scopeNames sig := by
      apply ht decl.name
      apply scope_ref_in_appSpine
      simp [scopeTermRefs]
    have hglobal : decl ∈ sig :=
      scope_existing_name_resolves_globally hscope decl.name hname decl hdecl rfl
    have hbody : ScopeAllowed (scopeNames sig) body := by
      intro f hf
      apply hscope.1.2 decl hglobal f
      apply scope_clause_ref_in_clauses decl.clauses (.mk qs body) hclause f
      exact hf
    have hσ : ScopeSubst (scopeNames sig) σ :=
      scope_matchSpine_of_appSpine_append (scopeNames sig) (.funRef decl.name as) hmatch ht
    have htyped : ScopeAllowed (scopeNames sig)
        ((body.substSizes (decl.sizeParams.dom.zip as)).substTypes τ) := by
      intro f hf
      apply hbody f
      simpa only [scope_refs_subst_types_term, scope_refs_subst_sizes_term] using hf
    apply scope_appSpine
    · exact scope_substTerms _ _ _ htyped hσ
    · exact scope_spine_suffix _ (.funRef decl.name as) es rest ht

end NishtAbel2024

-- SignatureReductionScope

namespace NishtAbel2024

mutual

/-- Lift weak-head scope preservation to reductions at any term position. -/
theorem scope_red_preserves_of_whd (names : List FunName) (sig : GlobalSig) (block : MutualBlock)
    (hwhd : ∀ t u, ScopeAllowed names t → WhdStep sig block t u → ScopeAllowed names u)
    {t u : Term} (ht : ScopeAllowed names t) (hstep : RedStep sig block t u) :
    ScopeAllowed names u := by
  cases hstep with
  | whd h => exact hwhd _ _ ht h
  | pairLeft h =>
    intro f hf
    simp only [scopeTermRefs, List.mem_append] at hf
    rcases hf with hf | hf
    · exact scope_red_preserves_of_whd names sig block hwhd
        (fun g hg => ht g (List.mem_append_left _ hg)) h f hf
    · exact ht f (List.mem_append_right _ hf)
  | pairRight h =>
    intro f hf
    simp only [scopeTermRefs, List.mem_append] at hf
    rcases hf with hf | hf
    · exact ht f (List.mem_append_left _ hf)
    · exact scope_red_preserves_of_whd names sig block hwhd
        (fun g hg => ht g (List.mem_append_right _ hg)) h f hf
  | @cons c ma t t' h =>
    change ScopeAllowed names t at ht
    change ScopeAllowed names t'
    exact scope_red_preserves_of_whd names sig block hwhd ht h
  | @pack G t t' h =>
    change ScopeAllowed names t at ht
    change ScopeAllowed names t'
    exact scope_red_preserves_of_whd names sig block hwhd ht h
  | appFun h =>
    intro f hf
    simp only [scopeTermRefs, List.mem_append] at hf
    rcases hf with hf | hf
    · exact scope_red_preserves_of_whd names sig block hwhd
        (fun g hg => ht g (List.mem_append_left _ hg)) h f hf
    · exact ht f (List.mem_append_right _ hf)
  | appArg h =>
    intro f hf
    simp only [scopeTermRefs, scopeElimRefs, List.mem_append] at hf
    rcases hf with hf | hf
    · exact ht f (List.mem_append_left _ hf)
    · exact scope_red_preserves_of_whd names sig block hwhd
        (fun g hg => ht g (List.mem_append_right _ hg)) h f hf
  | @ascr t t' A h =>
    change ScopeAllowed names t at ht
    change ScopeAllowed names t'
    exact scope_red_preserves_of_whd names sig block hwhd ht h
  | lamClauses h => exact scope_clauses_preserves_of_whd names sig block hwhd ht h

theorem scope_clause_preserves_of_whd (names : List FunName) (sig : GlobalSig) (block : MutualBlock)
    (hwhd : ∀ t u, ScopeAllowed names t → WhdStep sig block t u → ScopeAllowed names u)
    {d d' : Clause} (hd : ∀ f ∈ scopeClauseRefs d, f ∈ names)
    (hstep : ClauseRedStep sig block d d') : ∀ f ∈ scopeClauseRefs d', f ∈ names := by
  cases hstep with
  | body h => exact scope_red_preserves_of_whd names sig block hwhd hd h

theorem scope_clauses_preserves_of_whd (names : List FunName) (sig : GlobalSig) (block : MutualBlock)
    (hwhd : ∀ t u, ScopeAllowed names t → WhdStep sig block t u → ScopeAllowed names u)
    {ds ds' : List Clause} (hd : ∀ f ∈ scopeClausesRefs ds, f ∈ names)
    (hstep : ClausesRedStep sig block ds ds') : ∀ f ∈ scopeClausesRefs ds', f ∈ names := by
  cases hstep with
  | head h =>
    intro f hf
    simp only [scopeClausesRefs, List.mem_append] at hf
    rcases hf with hf | hf
    · exact scope_clause_preserves_of_whd names sig block hwhd
        (fun g hg => hd g (List.mem_append_left _ hg)) h f hf
    · exact hd f (List.mem_append_right _ hf)
  | tail h =>
    intro f hf
    simp only [scopeClausesRefs, List.mem_append] at hf
    rcases hf with hf | hf
    · exact hd f (List.mem_append_left _ hf)
    · exact scope_clauses_preserves_of_whd names sig block hwhd
        (fun g hg => hd g (List.mem_append_right _ hg)) h f hf

end

/-- The old-signature reference invariant is preserved by each full step of
reduction under a scoped extension. -/
theorem scope_red_preserves {sig : GlobalSig} {block : MutualBlock}
    (hscope : scopeBlockExtension sig block) {t u : Term}
    (ht : ScopeAllowed (scopeNames sig) t) (hstep : RedStep sig block t u) :
    ScopeAllowed (scopeNames sig) u := by
  exact scope_red_preserves_of_whd (scopeNames sig) sig block
    (fun _ _ => scope_whd_preserves hscope) ht hstep

end NishtAbel2024

-- SignatureReduction

namespace NishtAbel2024

/-- A weak-head step on a term whose function references all resolve in the
old signature is unchanged by a scoped block extension. This is a one-step
lookup property; it does not assert substitution or semantic stability. -/
theorem scope_whd_step_old {sig : GlobalSig} {block : MutualBlock}
    (hscope : scopeBlockExtension sig block) {t u : Term}
    (hrefs : ∀ f ∈ scopeTermRefs t, f ∈ scopeNames sig)
    (hstep : WhdStep sig block t u) : WhdStep sig [] t u := by
  cases hstep with
  | ascr t A es => exact WhdStep.ascr t A es
  | lamClause hclause hmatch => exact WhdStep.lamClause hclause hmatch
  | @funClause decl as qs body es es' τ σ hdecl hclause hmatch =>
    have hname : decl.name ∈ scopeNames sig := by
      apply hrefs
      apply scope_ref_in_appSpine
      simp [scopeTermRefs]
    have hglobal : decl ∈ sig :=
      scope_existing_name_resolves_globally hscope decl.name hname decl hdecl rfl
    apply WhdStep.funClause (decl := decl) ?_ hclause hmatch
    simpa using hglobal

mutual

/-- Backward preservation for a full reduction step on a term whose calls are
all resolved by the earlier signature. -/
theorem scope_red_step_old {sig : GlobalSig} {block : MutualBlock}
    (hscope : scopeBlockExtension sig block) {t u : Term}
    (hrefs : ∀ f ∈ scopeTermRefs t, f ∈ scopeNames sig)
    (hstep : RedStep sig block t u) : RedStep sig [] t u := by
  cases hstep with
  | whd h => exact RedStep.whd (scope_whd_step_old hscope hrefs h)
  | pairLeft h =>
    apply RedStep.pairLeft
    apply scope_red_step_old hscope ?_ h
    intro f hf
    exact hrefs f (List.mem_append_left _ hf)
  | pairRight h =>
    apply RedStep.pairRight
    apply scope_red_step_old hscope ?_ h
    intro f hf
    exact hrefs f (List.mem_append_right _ hf)
  | cons h => exact RedStep.cons (scope_red_step_old hscope hrefs h)
  | pack h => exact RedStep.pack (scope_red_step_old hscope hrefs h)
  | appFun h =>
    apply RedStep.appFun
    apply scope_red_step_old hscope ?_ h
    intro f hf
    exact hrefs f (List.mem_append_left _ hf)
  | appArg h =>
    apply RedStep.appArg
    apply scope_red_step_old hscope ?_ h
    intro f hf
    exact hrefs f (List.mem_append_right _ hf)
  | ascr h => exact RedStep.ascr (scope_red_step_old hscope hrefs h)
  | lamClauses h => exact RedStep.lamClauses (scope_clauses_step_old hscope hrefs h)

theorem scope_clause_step_old {sig : GlobalSig} {block : MutualBlock}
    (hscope : scopeBlockExtension sig block) {d d' : Clause}
    (hrefs : ∀ f ∈ scopeClauseRefs d, f ∈ scopeNames sig)
    (hstep : ClauseRedStep sig block d d') : ClauseRedStep sig [] d d' := by
  cases hstep with
  | body h => exact ClauseRedStep.body (scope_red_step_old hscope hrefs h)

theorem scope_clauses_step_old {sig : GlobalSig} {block : MutualBlock}
    (hscope : scopeBlockExtension sig block) {ds ds' : List Clause}
    (hrefs : ∀ f ∈ scopeClausesRefs ds, f ∈ scopeNames sig)
    (hstep : ClausesRedStep sig block ds ds') : ClausesRedStep sig [] ds ds' := by
  cases hstep with
  | head h =>
    apply ClausesRedStep.head
    apply scope_clause_step_old hscope ?_ h
    intro f hf
    exact hrefs f (List.mem_append_left _ hf)
  | tail h =>
    apply ClausesRedStep.tail
    apply scope_clauses_step_old hscope ?_ h
    intro f hf
    exact hrefs f (List.mem_append_right _ hf)

end

end NishtAbel2024

-- SignatureSNTransfer

namespace NishtAbel2024

/-- Strong normalization transfers to a disjoint block extension when the
reduction steps also preserve the old signature's scope. The preservation
premise is an explicit remaining obligation, not a consequence claimed here. -/
theorem scope_sn_transfer {sig : GlobalSig} {block : MutualBlock}
    (hscope : scopeBlockExtension sig block)
    (hpres : ∀ {t u : Term},
      (∀ f ∈ scopeTermRefs t, f ∈ scopeNames sig) →
      RedStep sig block t u →
      ∀ f ∈ scopeTermRefs u, f ∈ scopeNames sig)
    {t : Term} (ht : ∀ f ∈ scopeTermRefs t, f ∈ scopeNames sig)
    (hsn : SN sig [] t) : SN sig block t := by
  have transfer : ∀ t, SN sig [] t →
      (∀ f ∈ scopeTermRefs t, f ∈ scopeNames sig) → SN sig block t := by
    intro t h
    induction h with
    | intro t old ih =>
      intro hscopeT
      constructor
      intro u hstep
      exact ih u (scope_red_step_old hscope hscopeT hstep) (hpres hscopeT hstep)
  exact transfer t hsn ht

end NishtAbel2024

-- SignatureReductionExtend

namespace NishtAbel2024

/-- Existing weak-head steps remain available after adding a block. -/
theorem scope_whd_step_extend {sig : GlobalSig} {block : MutualBlock} {t u : Term}
    (h : WhdStep sig [] t u) : WhdStep sig block t u := by
  cases h with
  | ascr t A es => exact WhdStep.ascr t A es
  | lamClause hclause hmatch => exact WhdStep.lamClause hclause hmatch
  | @funClause decl as qs body es es' τ σ hdecl hclause hmatch =>
    apply WhdStep.funClause (decl := decl) ?_ hclause hmatch
    exact List.mem_append_left _ (by simpa using hdecl)

mutual

theorem scope_red_step_extend {sig : GlobalSig} {block : MutualBlock} {t u : Term}
    (h : RedStep sig [] t u) : RedStep sig block t u := by
  cases h with
  | whd h => exact .whd (scope_whd_step_extend h)
  | pairLeft h => exact .pairLeft (scope_red_step_extend h)
  | pairRight h => exact .pairRight (scope_red_step_extend h)
  | cons h => exact .cons (scope_red_step_extend h)
  | pack h => exact .pack (scope_red_step_extend h)
  | appFun h => exact .appFun (scope_red_step_extend h)
  | appArg h => exact .appArg (scope_red_step_extend h)
  | ascr h => exact .ascr (scope_red_step_extend h)
  | lamClauses h => exact .lamClauses (scope_clauses_step_extend h)

theorem scope_clause_step_extend {sig : GlobalSig} {block : MutualBlock} {d d' : Clause}
    (h : ClauseRedStep sig [] d d') : ClauseRedStep sig block d d' := by
  cases h with
  | body h => exact .body (scope_red_step_extend h)

theorem scope_clauses_step_extend {sig : GlobalSig} {block : MutualBlock}
    {ds ds' : List Clause} (h : ClausesRedStep sig [] ds ds') :
    ClausesRedStep sig block ds ds' := by
  cases h with
  | head h => exact .head (scope_clause_step_extend h)
  | tail h => exact .tail (scope_clauses_step_extend h)

end

/-- Normalization in the extension always implies normalization in the
original signature, even for terms that refer to the new block. -/
theorem scope_sn_of_extension {sig : GlobalSig} {block : MutualBlock} {t : Term}
    (h : SN sig block t) : SN sig [] t := by
  induction h with
  | intro t hacc ih =>
    constructor
    intro u hstep
    exact ih u (scope_red_step_extend hstep)

/-- Conditional two-way normalization stability for old-scoped terms. -/
theorem scope_sn_extension_iff {sig : GlobalSig} {block : MutualBlock}
    (hscope : scopeBlockExtension sig block)
    (hpres : ∀ {t u : Term},
      (∀ f ∈ scopeTermRefs t, f ∈ scopeNames sig) →
      RedStep sig block t u →
      ∀ f ∈ scopeTermRefs u, f ∈ scopeNames sig)
    {t : Term} (ht : ∀ f ∈ scopeTermRefs t, f ∈ scopeNames sig) :
    SN sig block t ↔ SN sig [] t :=
  ⟨scope_sn_of_extension, scope_sn_transfer hscope hpres ht⟩

end NishtAbel2024
open NishtAbel2024

/-- Auxiliary normalization stability for an old-scoped term. -/
theorem solution {sig : GlobalSig} {block : MutualBlock}
    (hscope : scopeBlockExtension sig block) {t : Term}
    (ht : ∀ f ∈ scopeTermRefs t, f ∈ scopeNames sig) :
    SN sig block t ↔ SN sig [] t := by
  exact scope_sn_extension_iff hscope (fun hrefs hstep => scope_red_preserves hscope hrefs hstep) ht
