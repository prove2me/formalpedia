-- Prove2me | solution 1 for NishtAbel2024.theorem_15
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:46:43.632306+00:00
-- url     : https://prove2.me/submissions/9195b5f7-de63-4b2b-bba7-b74cad323453

import Definitions.Def_NishtAbel2024_Inference

namespace NishtAbel2024.Theorem15FutureReferenceAudit

/-- The old function 1 references a future function 0, which is absent from
its old signature. The newly accepted function 0 calls old function 1. -/
def oldDecl : FunDecl := ⟨1, [], .unitTy, [.mk [] (.funRef 0 [])]⟩
def newDecl : FunDecl := ⟨0, [], .unitTy, [.mk [] (.funRef 1 [])]⟩
def oldSig : GlobalSig := [oldDecl]
def newBlock : MutualBlock := [newDecl]
def noGraphs : InvGraphFamily := ⟨fun _ => 0, fun _ _ => []⟩

theorem noGraphs_sct : SCTValid noGraphs := by
  constructor
  · constructor
    · exact ⟨[], by simp [noGraphs]⟩
    · simp [noGraphs]
  · have noClosure : ∀ f g G, InvGraphClosure noGraphs f g G → False := by
      intro f g G h
      induction h with
      | base hm => simp [noGraphs] at hm
      | comp _ _ ih _ => exact ih
    intro f G h _
    exact (noClosure f f G h).elim

/-- The body refers to old function 1, which inference permits from `sig ++ Ξ`.
The old function's reference to 0 is not inspected by local call checking. -/
theorem body_check :
    CheckTerm oldSig newBlock [] [] KindingCtx.empty .unitTy (.funRef 1 []) [] [] [] (.funRef 1 []) := by
  apply CheckTerm.sub (A := .unitTy) (C₁ := []) (C₂ := [])
  · have h : InferTerm oldSig newBlock [] [] KindingCtx.empty (.funRef oldDecl.name [])
        (oldDecl.ty.substSizes (oldDecl.sizeParams.dom.zip [])) [] [] [] (.funRef oldDecl.name []) := by
      apply InferTerm.funCall (decl := oldDecl) (flexVars := []) (as := [])
      all_goals simp [oldSig, newBlock, oldDecl, FlexVars.dom, SizeCtx.dom]
    simpa [oldDecl, TypeExpr.substSizes, TypeExpr.unitTy] using h
  · constructor <;> intro i π hlookup hocc <;> simp [FlexVars.lookupSizePol, FlexVars.lookupPol, SizeExp.var, SizeMin.single] at hlookup
  · exact CompareTypes.atom _ _ _ _

theorem body_calls_conform :
    LocalCallsConform newBlock noGraphs 0 [] [] (.funRef 1 []) := by
  simp [LocalCallsConform, newBlock, newDecl]

theorem clause_run :
    Nonempty (Algorithm2ClauseRun oldSig newBlock noGraphs 0 [] .unitTy []
      (.funRef 1 []) (.mk [] (.funRef 1 []))) := by
  apply Nonempty.intro
  refine ⟨.unitTy, [], [], [], [], [], [], [], .funRef 1 [], ?_, ?_, ?_, ?_, ?_⟩
  · exact InferSpine.nil _ _
  · constructor
    · exact KindingCtxExtWf.nil _
    · simp
  · exact SizeCtxWf.nil
  · simpa [KindingCtx.empty, KindingCtx.extSizes, KindingCtx.append] using body_check
  · constructor
    · rfl
    · simpa [Term.applyFlex] using body_calls_conform

theorem algorithm_accepts : Algorithm2Accepts oldSig newBlock newBlock := by
  refine ⟨noGraphs, noGraphs_sct, ?_, ?_⟩
  · simp [newBlock, newDecl, noGraphs]
  · constructor
    · refine ⟨rfl, ?_, ?_, SizeCtxWf.nil, ?_, ?_⟩
      · exact EncodeType.unit _ _
      · simp [newDecl, SignatureFixpointHygiene, NegFixpointPolClean, TypeExpr.allMuBranchLists,
          TypeExpr.allNuFieldLists, TypeExpr.unitTy, SizeOccursIn, TypeExpr.allSizeVars]
      · exact KindCheck.sub (KindInfer.unit _) (SubKind.star _)
      · constructor
        · exact ⟨[], .funRef 1 [], rfl, clause_run⟩
        · constructor
    · constructor

/-- An absent future name has no weak-head reduction in the old signature,
even under further eliminations. -/
def termHead : Term → Term
  | .app r _ => termHead r
  | t => t

theorem termHead_spine (r : Term) (es : List Elim) :
    termHead (Term.appSpine r es) = termHead r := by
  induction es generalizing r with
  | nil => rfl
  | cons e es ih =>
    change termHead (Term.appSpine (.app r e) es) = termHead r
    rw [ih]
    rfl

theorem future_no_whd (t u : Term) (h : WhdStep oldSig [] t u)
    (as : List SizeExp) (hh : termHead t = .funRef 0 as) : False := by
  cases h with
  | ascr t A es => simp [termHead_spine, termHead] at hh
  | lamClause hd => simp [termHead_spine, termHead] at hh
  | funClause hd hc =>
    simp only [oldSig, List.append_nil, List.mem_singleton] at hd
    subst hd
    simp [termHead_spine, termHead, oldDecl] at hh

theorem future_no_red (u : Term) : ¬ RedStep oldSig [] (.funRef 0 []) u := by
  intro h
  cases h with
  | whd hw => exact future_no_whd _ _ hw [] rfl

theorem future_sn : SN oldSig [] (.funRef 0 []) := by
  apply Acc.intro
  intro u hu
  exact (future_no_red u hu).elim

theorem future_neutral : IsNeutral oldSig [] (.funRef 0 []) := by
  constructor
  · simp [IsIntro]
  · right
    intro es u hw
    exact future_no_whd _ _ hw [] (by simp [termHead_spine, termHead])

/-- A nonempty application spine always produces an application node. -/
theorem spine_cons_app (r : Term) (e : Elim) (es : List Elim) :
    ∃ f e', Term.appSpine r (e :: es) = .app f e' := by
  induction es generalizing r e with
  | nil => exact ⟨r, e, rfl⟩
  | cons e' es ih =>
    change ∃ f z, Term.appSpine (.app r e) (e' :: es) = .app f z
    exact ih (.app r e) e'

theorem spine_eq_funRef_nil (r : Term) (es : List Elim) (f : FunName)
    (as : List SizeExp) (h : Term.appSpine r es = .funRef f as) : es = [] := by
  cases es with
  | nil => rfl
  | cons e es =>
    obtain ⟨g, e', he⟩ := spine_cons_app r e es
    rw [he] at h
    cases h

theorem spine_eq_lam_nil (r : Term) (es : List Elim) (Ds : List Clause)
    (h : Term.appSpine r es = .lamClauses Ds) : es = [] := by
  cases es with
  | nil => rfl
  | cons e es =>
    obtain ⟨g, e', he⟩ := spine_cons_app r e es
    rw [he] at h
    cases h

end NishtAbel2024.Theorem15FutureReferenceAudit

namespace NishtAbel2024.Theorem15FutureReferenceAudit

/-- Any old-signature weak-head step from a direct call to the old function
reduces it to the absent future function. -/
theorem old_fun_whd_target (t u : Term) (h : WhdStep oldSig [] t u)
    (as : List SizeExp) (ht : t = .funRef 1 as) : u = .funRef 0 [] := by
  cases h with
  | ascr r A es =>
    have he := spine_eq_funRef_nil _ _ _ _ ht
    subst es
    cases ht
  | @lamClause Ds qs body es es' τ σ hd hm =>
    have he := spine_eq_funRef_nil _ _ _ _ ht
    simp only [List.append_eq_nil_iff] at he
    rcases he with ⟨rfl, rfl⟩
    cases ht
  | @funClause decl sizes qs body es es' τ σ hd hc hm =>
    have he := spine_eq_funRef_nil _ _ _ _ ht
    simp only [List.append_eq_nil_iff] at he
    rcases he with ⟨rfl, rfl⟩
    simp only [oldSig, List.append_nil, List.mem_singleton] at hd
    subst decl
    simp only [oldDecl, List.mem_singleton, Clause.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩
    cases hm
    rfl

theorem old_fun_red_target (as : List SizeExp) (u : Term)
    (h : RedStep oldSig [] (.funRef 1 as) u) : u = .funRef 0 [] := by
  cases h with
  | whd h => exact old_fun_whd_target _ _ h as rfl

theorem old_fun_sn (as : List SizeExp) : SN oldSig [] (.funRef 1 as) := by
  apply Acc.intro
  intro u hu
  rw [old_fun_red_target as u hu]
  exact future_sn

theorem old_fun_neutral (as : List SizeExp) : IsNeutral oldSig [] (.funRef 1 as) := by
  constructor
  · simp [IsIntro]
  · left
    refine ⟨.funRef 0 [], ?_⟩
    have h := WhdStep.funClause (sig := oldSig) (Ξ := [])
      (decl := oldDecl) (as := as) (qs := []) (t := .funRef 0 [])
      (es := []) (es' := []) (τ := []) (σ := []) (by simp [oldSig])
      (by simp [oldDecl]) MatchSpine.nil
    simpa [oldDecl, Term.appSpine, Term.substSizes, Term.substTypes, Term.substTerms] using h

theorem old_lam_whd_target (t u : Term) (h : WhdStep oldSig [] t u)
    (ht : t = .lamClauses oldDecl.clauses) : u = .funRef 0 [] := by
  cases h with
  | ascr r A es =>
    have he := spine_eq_lam_nil _ _ _ ht
    subst es
    cases ht
  | @lamClause Ds qs body es es' τ σ hd hm =>
    have he := spine_eq_lam_nil _ _ _ ht
    simp only [List.append_eq_nil_iff] at he
    rcases he with ⟨rfl, rfl⟩
    cases ht
    simp only [oldDecl, List.mem_singleton, Clause.mk.injEq] at hd
    rcases hd with ⟨rfl, rfl⟩
    cases hm
    rfl
  | @funClause decl sizes qs body es es' τ σ hd hc hm =>
    have he := spine_eq_lam_nil _ _ _ ht
    simp only [List.append_eq_nil_iff] at he
    rcases he with ⟨rfl, rfl⟩
    cases ht

theorem old_clauses_no_red (ds : List Clause) :
    ¬ ClausesRedStep oldSig [] oldDecl.clauses ds := by
  change ¬ ClausesRedStep oldSig [] [.mk [] (.funRef 0 [])] ds
  intro h
  cases h with
  | head hc =>
    cases hc with
    | body h => exact future_no_red _ h
  | tail h => cases h

theorem old_lam_sn : SN oldSig [] (.lamClauses oldDecl.clauses) := by
  apply Acc.intro
  intro u hu
  cases hu with
  | whd h =>
    rw [old_lam_whd_target _ _ h rfl]
    exact future_sn
  | lamClauses h => exact (old_clauses_no_red _ h).elim

/-- The old signature is semantically valid in the empty-block world because
its sole function reduces to a neutral reference that is absent there. -/
theorem old_sig_valid : SemSigValid oldSig := by
  intro decl hdecl
  simp only [oldSig, List.mem_singleton] at hdecl
  subst decl
  constructor
  · exact old_lam_sn
  · intro as ρ hvalid
    change SN oldSig [] (.funRef 1 as) ∧ _
    constructor
    · exact old_fun_sn as
    · intro C hC hcontains
      apply hC.neutral_closed
      · exact old_fun_neutral as
      · intro t ht
        rw [old_fun_red_target as t ht]
        apply hC.neutral_closed
        · exact future_neutral
        · intro u hu
          exact (future_no_red u hu).elim

end NishtAbel2024.Theorem15FutureReferenceAudit

namespace NishtAbel2024.Theorem15FutureReferenceAudit

/-- The newly added function 0 calls old function 1. -/
theorem step_new_to_old :
    RedStep (oldSig ++ newBlock) [] (.funRef 0 []) (.funRef 1 []) := by
  apply RedStep.whd
  have h := WhdStep.funClause (sig := oldSig ++ newBlock) (Ξ := [])
    (decl := newDecl) (as := []) (qs := []) (t := .funRef 1 [])
    (es := []) (es' := []) (τ := []) (σ := []) (by simp [oldSig, newBlock])
    (by simp [newDecl]) MatchSpine.nil
  simpa [newDecl, Term.appSpine, Term.substSizes, Term.substTypes, Term.substTerms] using h

/-- The old function 1 calls the newly defined function 0. -/
theorem step_old_to_new :
    RedStep (oldSig ++ newBlock) [] (.funRef 1 []) (.funRef 0 []) := by
  apply RedStep.whd
  have h := WhdStep.funClause (sig := oldSig ++ newBlock) (Ξ := [])
    (decl := oldDecl) (as := []) (qs := []) (t := .funRef 0 [])
    (es := []) (es' := []) (τ := []) (σ := []) (by simp [oldSig, newBlock])
    (by simp [oldDecl]) MatchSpine.nil
  simpa [oldDecl, Term.appSpine, Term.substSizes, Term.substTypes, Term.substTerms] using h

theorem new_not_sn : ¬ SN (oldSig ++ newBlock) [] (.funRef 0 []) := by
  intro h
  have noCycle : ∀ t, SN (oldSig ++ newBlock) [] t →
      (t = .funRef 0 [] ∨ t = .funRef 1 []) → False := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro heq
      rcases heq with rfl | rfl
      · exact ih _ step_new_to_old (Or.inr rfl)
      · exact ih _ step_old_to_new (Or.inl rfl)
  exact noCycle _ h (Or.inl rfl)

theorem block_not_semantic : ¬ SemMutualBlockValid oldSig newBlock := by
  intro h
  have hdecl := h newDecl (by simp [newBlock])
  have hmem := hdecl.2 [] (fun _ => SizeOrd.zero) (by
    simp [ValidSizeTuple, newDecl, ValidSizeVal, SizeCtx.dom])
  have hsn : SN (oldSig ++ newBlock) [] (.funRef 0 []) := by
    exact hmem.1
  exact new_not_sn hsn

/-- Conditional refutation of the exact original theorem shape. The remaining
premise is semantic validity of the old signature, being proved separately. -/
theorem theorem15_false_if_old_valid (hvalid : SemSigValid oldSig) :
    ¬ (∀ (sig : GlobalSig) (Ξ Ξannot : MutualBlock),
      SemSigValid sig → Algorithm2Accepts sig Ξ Ξannot →
      MutualBlockTyping sig Ξannot ∧ SemMutualBlockValid sig Ξannot) := by
  intro h
  exact block_not_semantic (h oldSig newBlock newBlock hvalid algorithm_accepts).2

end NishtAbel2024.Theorem15FutureReferenceAudit

open NishtAbel2024
open NishtAbel2024.Theorem15FutureReferenceAudit

/-- Negation of the exact original Theorem 15 type, witnessed by a valid old
signature containing a forward reference and an accepted block closing a cycle. -/
theorem solution : ¬ (∀ (sig : GlobalSig) (Ξ Ξannot : MutualBlock)
    (hsig : SemSigValid sig) (hacc : Algorithm2Accepts sig Ξ Ξannot),
    MutualBlockTyping sig Ξannot ∧ SemMutualBlockValid sig Ξannot) :=
  theorem15_false_if_old_valid old_sig_valid

