-- Prove2me | solution 1 for NishtAbel2024.theorems_2_and_3
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-02T23:32:26.363959+00:00
-- url     : https://prove2.me/submissions/33af96b2-4760-46a4-b568-514c51eb7ee9

import Definitions.Def_NishtAbel2024_Semantics

namespace NishtAbel2024

def auditBenign : FunDecl := ⟨0, [], .unitTy, []⟩
def auditLoop : FunDecl := ⟨0, [], .unitTy, [.mk [] (.funRef 0 [])]⟩
def auditSig : GlobalSig := [auditBenign]
def auditBlock : MutualBlock := [auditLoop]

def auditHead : Term → Term
  | .app r _ => auditHead r
  | t => t

theorem auditHead_spine (r : Term) (es : List Elim) :
    auditHead (Term.appSpine r es) = auditHead r := by
  induction es generalizing r with
  | nil => rfl
  | cons e es ih =>
    change auditHead (Term.appSpine (.app r e) es) = auditHead r
    rw [ih]
    rfl

theorem audit_global_no_whd (t t' : Term) (h : WhdStep auditSig [] t t')
    (as : List SizeExp) (hh : auditHead t = .funRef 0 as) : False := by
  cases h with
  | ascr t A es => simp [auditHead_spine, auditHead] at hh
  | lamClause hd => simp [auditHead_spine, auditHead] at hh
  | funClause hd hc =>
    simp [auditSig] at hd
    cases hd
    simp [auditBenign] at hc

theorem audit_global_no_reduction (as : List SizeExp) (t : Term) :
    ¬ RedStep auditSig [] (.funRef 0 as) t := by
  intro h
  cases h with
  | whd h => exact audit_global_no_whd _ _ h as rfl

theorem audit_global_neutral (as : List SizeExp) : IsNeutral auditSig [] (.funRef 0 as) := by
  constructor
  · simp [IsIntro]
  · right
    intro es t h
    exact audit_global_no_whd _ _ h as (by simp [auditHead_spine, auditHead])

theorem audit_empty_lam_no_whd (t t' : Term) (h : WhdStep auditSig [] t t')
    (hh : auditHead t = .lamClauses []) : False := by
  cases h with
  | ascr t A es => simp [auditHead_spine, auditHead] at hh
  | lamClause hd =>
    simp [auditHead_spine, auditHead] at hh
    cases hh
    simp at hd
  | funClause hd hc => simp [auditHead_spine, auditHead] at hh

theorem audit_global_valid : SemSigValid auditSig := by
  intro decl hdecl
  simp only [auditSig, List.mem_singleton] at hdecl
  subst decl
  constructor
  · apply Acc.intro
    intro y hy
    cases hy with
    | whd h => exact (audit_empty_lam_no_whd _ _ h rfl).elim
    | lamClauses h => cases h
  · intro as ρ hvalid
    change SN auditSig [] (.funRef 0 as) ∧ _
    constructor
    · apply Acc.intro
      intro y hy
      exact (audit_global_no_reduction as y hy).elim
    · intro C hC hcontains
      apply hC.neutral_closed
      · exact audit_global_neutral as
      · intro t ht
        exact (audit_global_no_reduction as t ht).elim

theorem audit_loop_step :
    RedStep auditSig auditBlock (.funRef 0 []) (.funRef 0 []) := by
  apply RedStep.whd
  have h := WhdStep.funClause (sig := auditSig) (Ξ := auditBlock)
    (decl := auditLoop) (as := []) (qs := []) (t := .funRef 0 [])
    (es := []) (es' := []) (τ := []) (σ := []) (by simp [auditSig, auditBlock])
    (by simp [auditLoop]) MatchSpine.nil
  simpa [auditLoop, Term.appSpine, Term.substSizes, Term.substTypes, Term.substTerms] using h

theorem audit_loop_not_sn : ¬ SN auditSig auditBlock (.funRef 0 []) := by
  intro h
  have noLoop : ∀ t, SN auditSig auditBlock t → t = .funRef 0 [] → False := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro heq
      subst t
      exact ih _ audit_loop_step rfl
  exact noLoop _ h rfl

theorem audit_loop_not_semantic (ρ : SizeVal) :
    Term.funRef 0 [] ∉ evalType auditSig auditBlock ρ TypeExpr.unitTy := by
  intro h
  apply audit_loop_not_sn
  exact h.1

def auditGraphs : InvGraphFamily := ⟨fun _ => 0, fun _ _ => []⟩
def auditEnv : TypingEnv := ⟨auditSig, auditBlock, auditGraphs, 0, []⟩

theorem audit_sct : SCTValid auditGraphs := by
  constructor
  · constructor
    · exact ⟨[], by simp [auditGraphs]⟩
    · simp [auditGraphs]
  · have noClosure : ∀ f g G, InvGraphClosure auditGraphs f g G → False := by
      intro f g G h
      induction h with
      | base hm => simp [auditGraphs] at hm
      | comp _ _ ih _ => exact ih
    intro f G h _
    exact (noClosure f f G h).elim

theorem audit_guarded (ρ : SizeVal) :
    SemBlockGuardedValid auditSig auditBlock auditGraphs 0 [] ρ := by
  simp [SemBlockGuardedValid, auditGraphs]

theorem audit_infer : ExprInfer auditEnv KindingCtx.empty [] (.funRef 0 []) TypeExpr.unitTy := by
  have h : ExprInfer auditEnv KindingCtx.empty [] (.funRef auditBenign.name [])
      (auditBenign.ty.substSizes (auditBenign.sizeParams.dom.zip [])) := by
    apply ExprInfer.globalFun (decl := auditBenign)
    · simp [auditEnv, auditSig]
    · exact SizeSubstWf.nil
  simpa [auditBenign, TypeExpr.substSizes, TypeExpr.unitTy] using h

theorem audit_not_semexpr :
    ¬ SemExprTyping auditSig auditBlock KindingCtx.empty [] (.funRef 0 []) TypeExpr.unitTy := by
  intro h
  have hs := h (fun _ => SizeOrd.zero) (by simp [evalKindingCtx, ValidSizeVal, KindingCtx.empty]) []
    (by simp [evalTermCtx])
  apply audit_loop_not_semantic (fun _ => SizeOrd.zero)
  simpa [Term.substTerms] using hs

theorem audit_conditional_counterexample
    (valid : SemSigValid auditSig) :
    ¬ (∀ (Ω : TypingEnv) (Δ : KindingCtx) (Γ : TermCtx) (C : TypeExpr),
      SemSigValid Ω.sig → SizeCtxWf Δ.sizes → TermCtxWf Δ Γ → KindCheck Δ C .star →
      SCTValid Ω.graphs →
      (∀ ρ ∈ evalKindingCtx Δ, SemBlockGuardedValid Ω.sig Ω.block Ω.graphs Ω.caller Ω.callerSizes ρ) →
      (∀ r : Term, ExprInfer Ω Δ Γ r C → SemExprTyping Ω.sig Ω.block Δ Γ r C) ∧
      (∀ r : Term, ExprCheck Ω Δ Γ r C → SemExprTyping Ω.sig Ω.block Δ Γ r C) ∧
      (∀ Ds : List Clause, (∀ D ∈ Ds, ClauseCheck Ω Δ Γ D C) → SemClausesTyping Ω.sig Ω.block Δ Γ Ds C)) := by
  intro h
  apply audit_not_semexpr
  apply (h auditEnv KindingCtx.empty [] TypeExpr.unitTy valid SizeCtxWf.nil
    TermCtxWf.nil (KindCheck.sub (KindInfer.unit _) (SubKind.star _)) audit_sct ?_).1
    (.funRef 0 []) audit_infer
  intro ρ hρ
  exact audit_guarded ρ

theorem audit_theorem3_false :
    ¬ (∀ (Ω : TypingEnv) (Δ : KindingCtx) (Γ : TermCtx) (C : TypeExpr),
      SemSigValid Ω.sig → SizeCtxWf Δ.sizes → TermCtxWf Δ Γ → KindCheck Δ C .star →
      SCTValid Ω.graphs →
      (∀ ρ ∈ evalKindingCtx Δ, SemBlockGuardedValid Ω.sig Ω.block Ω.graphs Ω.caller Ω.callerSizes ρ) →
      (∀ r : Term, ExprInfer Ω Δ Γ r C → SemExprTyping Ω.sig Ω.block Δ Γ r C) ∧
      (∀ r : Term, ExprCheck Ω Δ Γ r C → SemExprTyping Ω.sig Ω.block Δ Γ r C) ∧
      (∀ Ds : List Clause, (∀ D ∈ Ds, ClauseCheck Ω Δ Γ D C) → SemClausesTyping Ω.sig Ω.block Δ Γ Ds C)) :=
  audit_conditional_counterexample audit_global_valid

end NishtAbel2024

open NishtAbel2024

theorem solution : ¬ ((∀ (Ψ : SizeCtx) (ρ ρ' : SizeVal),
      SizeCtxWf Ψ →
      SizeValLe Ψ ρ ρ' →
      (∀ a : SizeExp, SizeWf Ψ a → SizeOrd.le (evalSizeExp ρ a) (evalSizeExp ρ' a)) ∧
      (∀ a b : SizeExp, SizeLe Ψ a b → SizeOrd.le (evalSizeExp ρ a) (evalSizeExp ρ' b)) ∧
      (∀ a b : SizeExp, SizeLt Ψ a b → SizeOrd.lt (evalSizeExp ρ a) (evalSizeExp ρ' b))) ∧
    (∀ (Ω : TypingEnv) (Δ : KindingCtx) (Γ : TermCtx) (C : TypeExpr),
      SemSigValid Ω.sig →
      SizeCtxWf Δ.sizes →
      TermCtxWf Δ Γ →
      KindCheck Δ C .star →
      SCTValid Ω.graphs →
      (∀ ρ ∈ evalKindingCtx Δ,
        SemBlockGuardedValid Ω.sig Ω.block Ω.graphs Ω.caller Ω.callerSizes ρ) →
      (∀ r : Term, ExprInfer Ω Δ Γ r C → SemExprTyping Ω.sig Ω.block Δ Γ r C) ∧
      (∀ r : Term, ExprCheck Ω Δ Γ r C → SemExprTyping Ω.sig Ω.block Δ Γ r C) ∧
      (∀ Ds : List Clause,
        (∀ D ∈ Ds, ClauseCheck Ω Δ Γ D C) →
        SemClausesTyping Ω.sig Ω.block Δ Γ Ds C))) := by
  intro h
  exact audit_theorem3_false h.2
