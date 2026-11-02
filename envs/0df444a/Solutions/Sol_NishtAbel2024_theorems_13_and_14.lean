-- Prove2me | solution 1 for NishtAbel2024.theorems_13_and_14
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:33:59.749001+00:00
-- url     : https://prove2.me/submissions/2d3a98aa-2e6e-4f98-9bc3-07dadd583b31

import Definitions.Def_NishtAbel2024_Inference

namespace NishtAbel2024.Theorem13BadGlobal

def badSize : SizeDecl := ⟨0, .pos, .var 0 0⟩

def oldDecl : FunDecl := ⟨1, [badSize], .unitTy, []⟩

def annotatedDecl : FunDecl := ⟨0, [], .unitTy, [.mk [] (.funRef 1 [.infty])]⟩

def oldSig : GlobalSig := [oldDecl]

def annotatedBlock : MutualBlock := [annotatedDecl]

def noGraphs : InvGraphFamily := ⟨fun _ => 0, fun _ _ => []⟩

theorem no_fixpol_unit (Δ : KindingCtx) (fk : FixKind) (i : SizeVar) (π : Polarity) :
    ¬ SizeOccursFixPol Δ fk i π .unitTy := by
  intro h
  cases h

theorem body_check :
    CheckTerm oldSig annotatedBlock [] [] KindingCtx.empty .unitTy (.funRef 1 [])
      [(0, .pos)] [] [] (.funRef 1 [.var 0 0]) := by
  apply CheckTerm.sub (A := .unitTy) (C₁ := []) (C₂ := [])
  · have h : InferTerm oldSig annotatedBlock [] [] KindingCtx.empty (.funRef oldDecl.name [])
        (oldDecl.ty.substSizes (oldDecl.sizeParams.dom.zip [.var 0 0])) [(0, .pos)] [] []
        (.funRef oldDecl.name [.var 0 0]) := by
      apply InferTerm.funCall (decl := oldDecl) (flexVars := [(0, .pos)]) (as := [.var 0 0])
      all_goals simp [oldSig, annotatedBlock, oldDecl, badSize, FlexVars.dom, SizeCtx.dom,
        KindingCtx.empty, TypeExpr.unitTy]
      all_goals exact no_fixpol_unit _ _ _ _
    simpa [oldDecl, TypeExpr.substSizes, TypeExpr.unitTy] using h
  · constructor <;> intro i π hlookup hocc <;> rcases hocc with h | h | h | h <;>
      exact (no_fixpol_unit _ _ _ _ h).elim
  · exact CompareTypes.atom _ _ _ _

theorem body_calls_conform :
    LocalCallsConform annotatedBlock noGraphs 0 [] [] (.funRef 1 [.infty]) := by
  simp [LocalCallsConform, annotatedBlock, annotatedDecl]

theorem no_inf_below_meet (Ψ : SizeCtx) {a b : SizeExp} (h : SizeLt Ψ a b) :
    (∃ n, a = .inf n) → ∀ m, b ≠ .meet m := by
  induction h with
  | inf_lt_inf h => intro _ m hm; cases hm
  | var_lt_var h hb => intro ha; obtain ⟨n, hn⟩ := ha; cases hn
  | var_lt_inf hb => intro ha; obtain ⟨n, hn⟩ := ha; cases hn
  | var_lt_inf_add hb => intro ha; obtain ⟨n, hn⟩ := ha; cases hn
  | var_bound_step hb h ih => intro ha; obtain ⟨n, hn⟩ := ha; cases hn
  | meet_lt_left hw hm h ih => intro ha; obtain ⟨n, hn⟩ := ha; cases hn
  | @lt_meet_right a b h ih =>
    intro ha m hm
    cases hm
    have hh := ih b.head (by simp [SizeMin.toList]) ha (SizeMin.single b.head.var b.head.shift)
    exact hh rfl

theorem no_infty_lt_var : ¬ SizeLt [] .infty (.var 0 0) := by
  intro h
  exact no_inf_below_meet [] h ⟨0, rfl⟩ (SizeMin.single 0 0) rfl

theorem no_infty_lt_self_bound : ¬ SizeLt [] .infty (.var 0 0) := no_infty_lt_var

theorem no_valid_instantiation : ¬ SizeSubstWf [] [.infty] oldDecl.sizeParams := by
  have noSingleton : ∀ (as : List SizeExp) (ctx : SizeCtx),
      SizeSubstWf [] as ctx → as = [.infty] → ctx = [badSize] → False := by
    intro as ctx h
    cases h with
    | nil =>
      intro heq _
      cases heq
    | @snoc as ctx a d hpre hlt =>
      intro has hctx
      have haslen : as.length = 0 := by
        have hlen := congrArg List.length has
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      have hctxlen : ctx.length = 0 := by
        have hlen := congrArg List.length hctx
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      have has0 := List.eq_nil_of_length_eq_zero haslen
      have hctx0 := List.eq_nil_of_length_eq_zero hctxlen
      subst as
      subst ctx
      simp only [List.nil_append, List.cons.injEq, and_true] at has hctx
      subst a
      subst d
      apply no_infty_lt_self_bound
      simpa [badSize, SizeExp.subst, SizeCtx.dom, SizeExp.var, SizeMin.single, SizeExp.meetExp] using hlt
  intro h
  apply noSingleton [.infty] [badSize] h rfl rfl

theorem no_annotated_call_infer (𝒢 : InvGraphFamily) (A : TypeExpr) :
    ¬ ExprInfer ⟨oldSig, annotatedBlock, 𝒢, 0, []⟩ KindingCtx.empty []
      (.funRef 1 [.infty]) A := by
  intro h
  generalize hr : (Term.funRef 1 [.infty]) = r at h
  cases h with
  | globalFun hmem hsub =>
    simp only [oldSig, List.mem_singleton] at hmem
    subst_vars
    cases hr
    exact no_valid_instantiation hsub
  | localFun hmem hsub hg hcon =>
    simp only [annotatedBlock, List.mem_singleton] at hmem
    subst_vars
    cases hr
  | _ => cases hr

theorem no_annotated_call_check (𝒢 : InvGraphFamily) (A : TypeExpr) :
    ¬ ExprCheck ⟨oldSig, annotatedBlock, 𝒢, 0, []⟩ KindingCtx.empty []
      (.funRef 1 [.infty]) A := by
  intro h
  cases h with
  | sub hinf _ => exact no_annotated_call_infer 𝒢 _ hinf

def FrozenTarget : Prop :=
(∀ (sig : GlobalSig) (Ξ : MutualBlock) (𝒢 : InvGraphFamily) (f : FunName)
       (Δ₀ : KindingCtx) (Ψ₁ Ψ₂ : SizeCtx) (A A₀ C : TypeExpr)
       (qs qs' : PatSpine) (Γ : TermCtx) (Δ : List TyDecl)
       (t t' : Term) (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar)
       (φ : FlexSubst),
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ C Γ Δ Ψ₂ qs' →
      CheckTerm sig Ξ ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) C t Φ Cs T t' →
      CoherentSubst (Ψ₁ ++ Ψ₂) Cs φ →
      LocalCallsConform Ξ 𝒢 f Ψ₁ (Ψ₁ ++ Ψ₂) (t'.applyFlex φ) →
      ExprCheck ⟨sig, Ξ, 𝒢, f, Ψ₁⟩ ((Δ₀.extSizes Ψ₁).extDecls Δ) Γ (t'.applyFlex φ) C) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (Δ₀ : KindingCtx)
       (Ψ₁ Ψ₂ : SizeCtx) (A A₀ A'' : TypeExpr) (qs qs' : PatSpine)
       (Γ : TermCtx) (Δ : List TyDecl) (t t' : Term)
       (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar),
      SizeCtxWf (Ψ₁ ++ Ψ₂) →
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      SignatureFixpointHygiene (Δ₀.extSizes Ψ₁) A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ A'' Γ Δ Ψ₂ qs' →
      CheckTerm sig Ξ ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) A'' t Φ Cs T t' →
      CoherentSubst (Ψ₁ ++ Ψ₂) Cs (solveConstraintGraph (Ψ₁ ++ Ψ₂) Cs T)) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (𝒢 : InvGraphFamily) (f : FunName)
       (Δ₀ : KindingCtx) (Ψ₁ Ψ₂ : SizeCtx) (A A₀ C : TypeExpr)
       (qs qs' : PatSpine) (Γ : TermCtx) (Δ : List TyDecl)
       (t t' : Term) (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar),
      let φstar := solveConstraintGraph (Ψ₁ ++ Ψ₂) Cs T
      SizeCtxWf (Ψ₁ ++ Ψ₂) →
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      SignatureFixpointHygiene (Δ₀.extSizes Ψ₁) A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ C Γ Δ Ψ₂ qs' →
      CheckTerm sig Ξ ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) C t Φ Cs T t' →
      LocalCallsConform Ξ 𝒢 f Ψ₁ (Ψ₁ ++ Ψ₂) (t'.applyFlex φstar) →
      ExprCheck ⟨sig, Ξ, 𝒢, f, Ψ₁⟩ ((Δ₀.extSizes Ψ₁).extDecls Δ) Γ (t'.applyFlex φstar) C)

theorem empty_solver_coherent : CoherentSubst [] [] (solveConstraintGraph [] [] []) := by
  simp [CoherentSubst, ValidFlexSubst, solveConstraintGraph, SizeCtx.dom,
    SizeWf, SizeExp.infty, SizeExp.vars, lubSizes]

theorem empty_solver_call :
    (Term.funRef 1 [.var 0 0]).applyFlex (solveConstraintGraph [] [] []) =
      .funRef 1 [.infty] := by
  rfl

theorem frozen_target_false : ¬ FrozenTarget := by
  intro h
  have ht := h.1 oldSig annotatedBlock noGraphs 0 KindingCtx.empty [] []
    .unitTy .unitTy .unitTy [] [] [] [] (.funRef 1 []) (.funRef 1 [.var 0 0])
    [(0, .pos)] [] [] (solveConstraintGraph [] [] [])
    (EncodeType.unit _ _) (InferSpine.nil _ _) (by simpa [KindingCtx.empty,
      KindingCtx.extSizes, KindingCtx.append] using body_check) empty_solver_coherent
    (by simp only [List.nil_append]; rw [empty_solver_call]; exact body_calls_conform)
  apply no_annotated_call_check noGraphs .unitTy
  simpa [empty_solver_call, KindingCtx.empty, KindingCtx.extSizes,
    KindingCtx.extDecls] using ht

end NishtAbel2024.Theorem13BadGlobal

open NishtAbel2024

theorem solution : ¬ (
(∀ (sig : GlobalSig) (Ξ : MutualBlock) (𝒢 : InvGraphFamily) (f : FunName)
       (Δ₀ : KindingCtx) (Ψ₁ Ψ₂ : SizeCtx) (A A₀ C : TypeExpr)
       (qs qs' : PatSpine) (Γ : TermCtx) (Δ : List TyDecl)
       (t t' : Term) (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar)
       (φ : FlexSubst),
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ C Γ Δ Ψ₂ qs' →
      CheckTerm sig Ξ ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) C t Φ Cs T t' →
      CoherentSubst (Ψ₁ ++ Ψ₂) Cs φ →
      LocalCallsConform Ξ 𝒢 f Ψ₁ (Ψ₁ ++ Ψ₂) (t'.applyFlex φ) →
      ExprCheck ⟨sig, Ξ, 𝒢, f, Ψ₁⟩ ((Δ₀.extSizes Ψ₁).extDecls Δ) Γ (t'.applyFlex φ) C) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (Δ₀ : KindingCtx)
       (Ψ₁ Ψ₂ : SizeCtx) (A A₀ A'' : TypeExpr) (qs qs' : PatSpine)
       (Γ : TermCtx) (Δ : List TyDecl) (t t' : Term)
       (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar),
      SizeCtxWf (Ψ₁ ++ Ψ₂) →
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      SignatureFixpointHygiene (Δ₀.extSizes Ψ₁) A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ A'' Γ Δ Ψ₂ qs' →
      CheckTerm sig Ξ ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) A'' t Φ Cs T t' →
      CoherentSubst (Ψ₁ ++ Ψ₂) Cs (solveConstraintGraph (Ψ₁ ++ Ψ₂) Cs T)) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (𝒢 : InvGraphFamily) (f : FunName)
       (Δ₀ : KindingCtx) (Ψ₁ Ψ₂ : SizeCtx) (A A₀ C : TypeExpr)
       (qs qs' : PatSpine) (Γ : TermCtx) (Δ : List TyDecl)
       (t t' : Term) (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar),
      let φstar := solveConstraintGraph (Ψ₁ ++ Ψ₂) Cs T
      SizeCtxWf (Ψ₁ ++ Ψ₂) →
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      SignatureFixpointHygiene (Δ₀.extSizes Ψ₁) A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ C Γ Δ Ψ₂ qs' →
      CheckTerm sig Ξ ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) C t Φ Cs T t' →
      LocalCallsConform Ξ 𝒢 f Ψ₁ (Ψ₁ ++ Ψ₂) (t'.applyFlex φstar) →
      ExprCheck ⟨sig, Ξ, 𝒢, f, Ψ₁⟩ ((Δ₀.extSizes Ψ₁).extDecls Δ) Γ (t'.applyFlex φstar) C)
) :=
  NishtAbel2024.Theorem13BadGlobal.frozen_target_false

#print axioms solution
