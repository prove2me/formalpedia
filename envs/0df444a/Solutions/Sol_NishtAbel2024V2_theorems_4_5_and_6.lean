-- Prove2me | solution 1 for NishtAbel2024V2.theorems_4_5_and_6
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T14:42:21.406165+00:00
-- url     : https://prove2.me/submissions/48095235-a3d5-4b9f-bde6-8c929976c9ff

import Definitions.Def_NishtAbel2024V2_Syntax
import Definitions.Def_NishtAbel2024V2_Semantics
import Definitions.Def_NishtAbel2024V2_Inference

namespace NishtAbel2024V2.CaptureCounterexample

open NishtAbel2024V2

abbrev tyV (X : TyVar) : TypeExpr := .atom (.var X)

/-- `λY. Y → Y`. -/
abbrev Fid : TypeExpr := .lam 0 .star (.arrTy (tyV 0) (tyV 0))

/-- `G = ∀Y. Y → Y`. -/
abbrev G : TypeExpr := .allTy .star Fid

abbrev GG : TypeExpr := .arrTy G G

/-- `y Z x` -/
abbrev innerBody : Term := .app (.app (.var 1) (.tyArg (tyV 5))) (.term (.var 0))

/-- `λ{Z x → y Z x}` -/
abbrev innerLam : Term := .lamClauses [.mk [.tyVar 5, .pat (.var 0)] innerBody]

/-- `λ{y → λ{Z x → y Z x}}` -/
abbrev outerLam : Term := .lamClauses [.mk [.pat (.var 1)] innerLam]

/-- `N = (outerLam : G → G) x` -/
abbrev N : Term := .app (.ascr outerLam GG) (.term (.var 0))

/-- `N G N` -/
abbrev body : Term := .app (.app N (.tyArg G)) (.term N)

abbrev clause : Clause := .mk [.pat (.var 0)] body

abbrev decl : FunDecl := { name := 0, sizeParams := [], ty := GG, clauses := [clause] }

abbrev block : MutualBlock := [decl]

abbrev noGraphs : InvGraphFamily := ⟨fun _ => 0, fun _ _ => []⟩

/-- `δ = λ{Z x → x Z x}`, the result of variable capture under `Clause.substTerms`. -/
abbrev delta : Term :=
  .lamClauses [.mk [.tyVar 5, .pat (.var 0)] (.app (.app (.var 0) (.tyArg (tyV 5))) (.term (.var 0)))]

/-- `δ G δ`, which reduces to itself. -/
abbrev loopTerm : Term := .app (.app delta (.tyArg G)) (.term delta)

theorem fid_body_kind (Δ : KindingCtx) :
    KindCheck (Δ.extType 0 .mixed .star) (.arrTy (tyV 0) (tyV 0)) .star := by
  have hmem : ∀ π : Polarity, TyDecl.mk 0 (Polarity.invComp π .mixed) .star ∈
      ((Δ.extType 0 .mixed .star).invScalePol π).types := by
    intro π
    simp [KindingCtx.invScalePol, KindingCtx.extType]
  refine KindCheck.sub (κ := .star) ?_ (SubKind.star _)
  refine KindInfer.app (π := .pos) (κ := .star) ?_ ?_
  · refine KindInfer.app (π := .neg) (κ := .star) (KindInfer.arr _) ?_
    exact KindCheck.sub (KindInfer.var (π := .mixed) (hmem .neg) rfl) (SubKind.star _)
  · exact KindCheck.sub (KindInfer.var (π := .mixed) (hmem .pos) rfl) (SubKind.star _)

theorem fid_kind (Δ : KindingCtx) : KindCheck Δ Fid (.arr .mixed .star .star) :=
  KindCheck.lam rfl (KindWf.star _) (KindWf.star _) (fid_body_kind Δ)

theorem G_kind (Δ : KindingCtx) : KindCheck Δ G .star :=
  KindCheck.sub
    (KindInfer.app (π := .pos) (κ := .arr .mixed .star .star)
      (KindInfer.all (KindWf.star _)) (fid_kind _))
    (SubKind.star _)

theorem GG_kind (Δ : KindingCtx) : KindCheck Δ GG .star :=
  KindCheck.sub
    (KindInfer.app (π := .pos) (κ := .star)
      (KindInfer.app (π := .neg) (κ := .star) (KindInfer.arr _) (G_kind _)) (G_kind _))
    (SubKind.star _)

theorem var0_mem (Δ : KindingCtx) (π π' : Polarity) :
    TyDecl.mk 0 (Polarity.invComp π' .mixed) .star ∈
      ((Δ.extType 0 .mixed (Kind.ofSKind .star)).invScalePol π').types := by
  simp [KindingCtx.invScalePol, KindingCtx.extType, Kind.ofSKind]

theorem invComp_mixed_le (π : Polarity) : Polarity.le (Polarity.invComp π .mixed) .pos = true := by
  cases π <;> rfl

theorem G_sub (Δ : KindingCtx) : SubType Δ G G := by
  unfold SubType
  refine SubTypeInfer.app (π₁ := .pos) (κ₁ := .arr .mixed .star .star) (by decide) ?_ ?_
  · exact SubTypeInfer.atom (by decide) (KindInfer.all (KindWf.star _))
  · refine SubTypeCheck.arr (X := 0) (KindWf.star _) ?_
    show SubTypeCheck _ _ (.arrTy (tyV 0) (tyV 0)) (.arrTy (tyV 0) (tyV 0)) _
    refine SubTypeCheck.star ?_
    refine SubTypeInfer.app (π₁ := .pos) (κ₁ := .star) (by decide) ?_ ?_
    · refine SubTypeInfer.app (π₁ := .neg) (κ₁ := .star) (by decide) ?_ ?_
      · exact SubTypeInfer.atom (by decide) (KindInfer.arr _)
      · exact SubTypeCheck.star (SubTypeInfer.atom (by decide)
          (KindInfer.var (var0_mem _ .pos .neg) (invComp_mixed_le _)))
    · exact SubTypeCheck.star (SubTypeInfer.atom (by decide)
        (KindInfer.var (var0_mem _ .pos .pos) (invComp_mixed_le _)))

abbrev Ω : TypingEnv := ⟨[], block, noGraphs, 0, []⟩

theorem var5_mem (Δ : KindingCtx) :
    TyDecl.mk 5 .pos .star ∈ (Δ.extDecls [⟨5, .pos, .star⟩]).types := by
  simp [KindingCtx.extDecls, KindingCtx.extType]

theorem var5_sub (Δ : KindingCtx) : SubType (Δ.extDecls [⟨5, .pos, .star⟩]) (tyV 5) (tyV 5) :=
  SubTypeInfer.atom (by decide) (KindInfer.var (var5_mem _) rfl)

theorem inner_clause_check (Δ : KindingCtx) (Γ : TermCtx) (hy : (1, G) ∈ Γ) :
    ClauseCheck Ω Δ Γ (.mk [.tyVar 5, .pat (.var 0)] innerBody) G := by
  have hsp : SpineTyping Δ [⟨5, .pos, .star⟩] [(0, tyV 5)] G [.tyVar 5, .pat (.var 0)] (tyV 5) := by
    refine SpineTyping.tyVar (κ := .star) (F := Fid) ?_
    show SpineTyping _ _ _ (.arrTy (tyV 5) (tyV 5)) _ _
    exact SpineTyping.pat (Δ₁ := []) (Δ₂ := []) (Γ₁ := [(0, tyV 5)]) (Γ₂ := [])
      (PatTyping.var _ 0 _) (SpineTyping.nil _ _)
  have hcons : KindingCtxConsistentExt Δ [⟨5, .pos, .star⟩] :=
    ⟨KindingCtxExtWf.cons (KindWf.star _) (KindingCtxExtWf.nil _), by simp⟩
  refine ClauseCheck.mk hsp hcons ?_
  have hx : ((0 : TermVar), tyV 5) ∈ Γ ++ [(0, tyV 5)] := by simp
  have hy' : ((1 : TermVar), G) ∈ Γ ++ [(0, tyV 5)] := by simp [hy]
  have happ : ExprInfer Ω (Δ.extDecls [⟨5, .pos, .star⟩]) (Γ ++ [(0, tyV 5)])
      (.app (.var 1) (.tyArg (tyV 5))) (.arrTy (tyV 5) (tyV 5)) :=
    ExprInfer.appTy (κ := .star) (F := Fid) (ExprInfer.var hy')
      (KindCheck.sub (KindInfer.var (var5_mem _) rfl) (SubKind.star _))
  exact ExprCheck.sub (A := tyV 5)
    (ExprInfer.appTerm happ (ExprCheck.sub (ExprInfer.var hx) (var5_sub _))) (var5_sub _)

theorem outer_lam_check (Δ : KindingCtx) (Γ : TermCtx) :
    ExprCheck Ω Δ Γ outerLam GG := by
  refine ExprCheck.lamClauses ?_
  intro D hD
  simp only [List.mem_singleton] at hD
  subst hD
  have hsp : SpineTyping Δ [] [(1, G)] GG [.pat (.var 1)] G :=
    SpineTyping.pat (Δ₁ := []) (Δ₂ := []) (Γ₁ := [(1, G)]) (Γ₂ := [])
      (PatTyping.var _ 1 _) (SpineTyping.nil _ _)
  refine ClauseCheck.mk hsp ⟨KindingCtxExtWf.nil _, by simp⟩ ?_
  refine ExprCheck.lamClauses ?_
  intro D hD
  simp only [List.mem_singleton] at hD
  subst hD
  exact inner_clause_check _ _ (by simp)

theorem N_infer (Δ : KindingCtx) (Γ : TermCtx) (hx : (0, G) ∈ Γ) : ExprInfer Ω Δ Γ N G :=
  ExprInfer.appTerm (A := G) (B := G)
    (ExprInfer.ascr (GG_kind _) (outer_lam_check _ _))
    (ExprCheck.sub (ExprInfer.var hx) (G_sub _))

theorem body_check (Δ : KindingCtx) (Γ : TermCtx) (hx : (0, G) ∈ Γ) : ExprCheck Ω Δ Γ body G := by
  have hNG : ExprInfer Ω Δ Γ (.app N (.tyArg G)) (.arrTy G G) :=
    ExprInfer.appTy (κ := .star) (F := Fid) (N_infer _ _ hx) (G_kind _)
  exact ExprCheck.sub (A := G)
    (ExprInfer.appTerm hNG (ExprCheck.sub (N_infer _ _ hx) (G_sub _))) (G_sub _)

theorem clause_check (Δ : KindingCtx) : ClauseCheck Ω Δ [] clause GG := by
  have hsp : SpineTyping Δ [] [(0, G)] GG [.pat (.var 0)] G :=
    SpineTyping.pat (Δ₁ := []) (Δ₂ := []) (Γ₁ := [(0, G)]) (Γ₂ := [])
      (PatTyping.var _ 0 _) (SpineTyping.nil _ _)
  exact ClauseCheck.mk hsp ⟨KindingCtxExtWf.nil _, by simp⟩ (body_check _ _ (by simp))

theorem noGraphs_sct : SCTValid noGraphs := by
  constructor
  · constructor
    · exact ⟨[], by simp⟩
    · simp
  · have noClosure : ∀ f g G, InvGraphClosure noGraphs f g G → False := by
      intro f g G h
      induction h with
      | base hm => simp at hm
      | comp _ _ ih _ => exact ih
    intro f G h _
    exact (noClosure f f G h).elim

theorem scope_ok : scopeBlockExtension [] block := by
  simp [scopeBlockExtension, scopeSignatureClosed, scopeNames, scopeDeclClosed,
    scopeClausesRefs, scopeClauseRefs, scopeTermRefs, scopeElimRefs]

theorem semsig_ok : SemSigValidIn [] block := by
  intro d hd
  simp at hd

theorem block_typing : MutualBlockTyping [] block := by
  refine ⟨noGraphs, noGraphs_sct, ?_, ?_⟩
  · intro d hd
    simp only [List.mem_singleton] at hd
    subst hd
    rfl
  · intro d hd
    simp only [List.mem_singleton] at hd
    subst hd
    refine ⟨SizeCtxWf.nil, GG_kind _, ?_⟩
    intro D hD
    simp only [List.mem_singleton] at hD
    subst hD
    exact clause_check _

theorem acc_irrefl {α : Type} {r : α → α → Prop} {a : α} (h : Acc r a) : ¬ r a a := by
  induction h with
  | intro x _ ih => exact fun hxx => ih x hxx hxx

theorem step_ascr (sig : GlobalSig) (Ξ : MutualBlock) :
    RedStep sig Ξ N (.app outerLam (.term (.var 0))) :=
  RedStep.whd (WhdStep.ascr outerLam GG [.term (.var 0)])

theorem step_capture (sig : GlobalSig) (Ξ : MutualBlock) :
    RedStep sig Ξ (.app outerLam (.term (.var 0))) delta :=
  RedStep.whd (WhdStep.lamClause (Ds := [.mk [.pat (.var 1)] innerLam]) (qs := [.pat (.var 1)])
    (t := innerLam) (es := [.term (.var 0)]) (es' := []) (by simp)
    (MatchSpine.cons (MatchCopat.pat (MatchPat.var _ _)) MatchSpine.nil))

theorem step_loop (sig : GlobalSig) (Ξ : MutualBlock) :
    RedStep sig Ξ loopTerm loopTerm :=
  RedStep.whd (WhdStep.lamClause
    (Ds := [.mk [.tyVar 5, .pat (.var 0)] (.app (.app (.var 0) (.tyArg (tyV 5))) (.term (.var 0)))])
    (qs := [.tyVar 5, .pat (.var 0)])
    (t := .app (.app (.var 0) (.tyArg (tyV 5))) (.term (.var 0)))
    (es := [.tyArg G, .term delta]) (es' := []) (by simp)
    (MatchSpine.cons (MatchCopat.tyVar G 5)
      (MatchSpine.cons (MatchCopat.pat (MatchPat.var _ _)) MatchSpine.nil)))

theorem under_clause {sig : GlobalSig} {Ξ : MutualBlock} {t t' : Term} (h : RedStep sig Ξ t t') :
    RedStep sig Ξ (.lamClauses [.mk [.pat (.var 0)] t]) (.lamClauses [.mk [.pat (.var 0)] t']) :=
  RedStep.lamClauses (ClausesRedStep.head (ClauseRedStep.body h))

theorem not_sn (sig : GlobalSig) (Ξ : MutualBlock) : ¬ SN sig Ξ (.lamClauses [clause]) := by
  intro h
  unfold SN at h
  have h1 := h.inv (under_clause (RedStep.appFun (RedStep.appFun (step_ascr sig Ξ))))
  have h2 := h1.inv (under_clause (RedStep.appFun (RedStep.appFun (step_capture sig Ξ))))
  have h3 := h2.inv (under_clause (RedStep.appArg (step_ascr sig Ξ)))
  have h4 := h3.inv (under_clause (RedStep.appArg (step_capture sig Ξ)))
  exact acc_irrefl h4 (under_clause (step_loop sig Ξ))

theorem not_valid : ¬ SemMutualBlockValid [] block := by
  intro h
  exact not_sn ([] ++ block) [] (h decl (by simp)).1

end NishtAbel2024V2.CaptureCounterexample

open NishtAbel2024V2 in
theorem solution :
    ¬ ((∀ (sig : GlobalSig) (Ξ : MutualBlock), scopeBlockExtension sig Ξ → SemSigValidIn sig Ξ → MutualBlockTyping sig Ξ → SemMutualBlockValid sig Ξ) ∧ (∀ blocks : List MutualBlock, scopeOrderedBlocks blocks → SigBlocksTyping blocks → SemSigValid blocks.flatten) ∧ (∀ P : Program, ScopedProgramTyping P → SemProgramValid P) ∧ (∀ (sig : GlobalSig) (Ξcop : List CopFunDecl), CopMutualBlockTyping sig Ξcop → MutualBlockTyping sig (eraseMeasures Ξcop))) := by
  intro claimed
  exact NishtAbel2024V2.CaptureCounterexample.not_valid
    (claimed.1 [] NishtAbel2024V2.CaptureCounterexample.block
      NishtAbel2024V2.CaptureCounterexample.scope_ok
      NishtAbel2024V2.CaptureCounterexample.semsig_ok
      NishtAbel2024V2.CaptureCounterexample.block_typing)

#print axioms solution
