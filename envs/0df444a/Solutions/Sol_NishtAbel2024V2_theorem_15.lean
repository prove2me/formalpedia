-- Prove2me | solution 1 for NishtAbel2024V2.theorem_15
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-05T20:48:36.254227+00:00
-- url     : https://prove2.me/submissions/dc6bf346-21ce-43b6-95fc-f3825da58594

import Definitions.Def_NishtAbel2024V2_Syntax
import Definitions.Def_NishtAbel2024V2_Semantics
import Definitions.Def_NishtAbel2024V2_Inference

/-!
# A counterexample to `NishtAbel2024V2.theorem_15`

Term substitution in the V2 semantics (`Clause.substTerms`) drops bound names from the
substitution but never renames binders, so substituting an open term under a clause binder
can capture.  `SemMutualBlockValid` asks for strong normalization of `λ D⃗` under full
reduction, which reduces inside clause bodies, where the substituted terms are open.

The block below has one function `f : G → G` with `G = ∀Y. Y → Y` and the single clause

  `f x = N G N`  where  `N = ((λ{y → λ{Z x → y Z x}}) : G → G) x`.

Postchecked Algorithm 2 accepts it: every type is size-free, so no constraints, solver
steps or call graphs arise.  Under the binder `x`, `N` reduces to `δ = λ{Z x → x Z x}`
(the inner `x` captures the outer one), and `δ G δ` reduces to itself.
-/

namespace NishtAbel2024V2.Theorem15Capture

open NishtAbel2024V2

/-! ## The block -/

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

/-- `δ = λ{Z x → x Z x}`, the result of capture. -/
abbrev delta : Term :=
  .lamClauses [.mk [.tyVar 5, .pat (.var 0)] (.app (.app (.var 0) (.tyArg (tyV 5))) (.term (.var 0)))]

/-- `δ G δ`, which reduces to itself. -/
abbrev loopTerm : Term := .app (.app delta (.tyArg G)) (.term delta)

theorem dnil (l : List Nat) : List.Disjoint (SizeCtx.dom []) l := by
  simp [SizeCtx.dom]

/-! ## Kinding of `G` -/

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

theorem G_fwkind (Δ : KindingCtx) : FwKindCheck Δ G .star := by
  have hmem : ∀ (Δ' : KindingCtx) (π : Polarity), TyDecl.mk 0 (Polarity.invComp π .mixed)
      (Kind.ofSKind .star) ∈ ((Δ'.extType 0 .mixed (Kind.ofSKind .star)).invScalePol π).types := by
    intro Δ' π
    simp [KindingCtx.invScalePol, KindingCtx.extType, Kind.ofSKind]
  refine FwKindCheck.infer (FwKindInfer.app (π := .pos) (ι := .arr .mixed .star .star)
    (FwKindInfer.all (ι := .star)) ?_)
  refine FwKindCheck.lam (π := .mixed) (FwKindCheck.infer ?_)
  refine FwKindInfer.app (π := .pos) (ι := .star) ?_ ?_
  · exact FwKindInfer.app (π := .neg) (ι := .star) (FwKindInfer.arr _)
      (FwKindCheck.infer (FwKindInfer.var (π := .mixed) (hmem _ .neg) rfl))
  · exact FwKindCheck.infer (FwKindInfer.var (π := .mixed) (hmem _ .pos) rfl)

/-! ## Encoding of `G` and `G → G` (no fixpoints, so no size variables) -/

theorem fid_body_encode (πstar π : Polarity) (Δ : KindingCtx) :
    EncodeType πstar π (Δ.extType 0 .mixed (Kind.ofSKind .star))
      (.arrTy (tyV 0) (tyV 0)) [] (.arrTy (tyV 0) (tyV 0)) := by
  have hmem : ∀ π' : Polarity, TyDecl.mk 0 (Polarity.invComp π' .mixed) (Kind.ofSKind .star) ∈
      ((Δ.extType 0 .mixed (Kind.ofSKind .star)).invScalePol π').types := by
    intro π'
    simp [KindingCtx.invScalePol, KindingCtx.extType, Kind.ofSKind]
  have hmem0 : TyDecl.mk 0 .mixed (Kind.ofSKind .star) ∈
      (Δ.extType 0 .mixed (Kind.ofSKind .star)).types := by
    simp [KindingCtx.extType, Kind.ofSKind]
  have hkv : ∀ (Δ' : KindingCtx) (π' : Polarity),
      TyDecl.mk 0 (Polarity.invComp π' .mixed) .star ∈ Δ'.types →
      KindCheck Δ' (tyV 0) .star := by
    intro Δ' π' h
    have hle : Polarity.le (Polarity.invComp π' .mixed) .pos = true := by
      cases π' <;> rfl
    exact KindCheck.sub (KindInfer.var h hle) (SubKind.star _)
  have hinner : EncodeType πstar π (Δ.extType 0 .mixed (Kind.ofSKind .star))
      (.app (.atom .arr) (tyV 0)) ([] ++ []) (.app (.atom .arr) (tyV 0)) := by
    refine EncodeType.app (π' := .neg) (ι := .star) (ι' := .arr .pos .star .star)
      (FwKindInfer.arr _) (KindInfer.arr _) ?_ (EncodeType.arr _ _) ?_ (dnil _) (dnil _) (dnil _)
    · apply hkv _ .neg
      simpa [KindingCtx.extSizes, KindingCtx.invScalePol, KindingCtx.extType, Kind.ofSKind]
        using hmem .neg
    · exact EncodeType.var (π' := Polarity.invComp .neg .mixed) (ι := .star) (hmem .neg) rfl
  refine EncodeType.app (π' := .pos) (ι := .star) (ι' := .star) (Ψ₁ := []) (Ψ₂ := [])
    ?_ ?_ ?_ hinner ?_ (dnil _) (dnil _) (dnil _)
  · exact FwKindInfer.app (π := .neg) (ι := .star) (FwKindInfer.arr _)
      (FwKindCheck.infer (FwKindInfer.var (π := Polarity.invComp .neg .mixed) (hmem .neg) rfl))
  · refine KindInfer.app (π := .neg) (κ := .star) (KindInfer.arr _) ?_
    apply hkv _ .neg
    simpa [KindingCtx.extSizes, KindingCtx.invScalePol, KindingCtx.extType, Kind.ofSKind]
      using hmem .neg
  · apply hkv _ .pos
    simpa [KindingCtx.extSizes, KindingCtx.invScalePol, KindingCtx.extType, Kind.ofSKind]
      using hmem .pos
  · exact EncodeType.var (π' := Polarity.invComp .pos .mixed) (ι := .star) (hmem .pos) rfl

theorem G_encode (πstar π : Polarity) (Δ : KindingCtx) : EncodeType πstar π Δ G [] G := by
  refine EncodeType.app (π' := .pos) (ι := .arr .mixed .star .star) (ι' := .star)
    (Ψ₁ := []) (Ψ₂ := []) (FwKindInfer.all (ι := .star)) (KindInfer.all (KindWf.star _))
    (fid_kind _) (EncodeType.all π Δ .star) ?_ (dnil _) (dnil _) (dnil _)
  exact EncodeType.lam (Ψ := []) (by simp [SizeCtx.dom]) (fid_body_encode _ _ _)

theorem GG_encode (πstar π : Polarity) (Δ : KindingCtx) : EncodeType πstar π Δ GG [] GG := by
  have hleft : EncodeType πstar π Δ (.app (.atom .arr) G) ([] ++ []) (.app (.atom .arr) G) :=
    EncodeType.app (π' := .neg) (ι := .star) (ι' := .arr .pos .star .star)
      (FwKindInfer.arr _) (KindInfer.arr _) (G_kind _) (EncodeType.arr _ _) (G_encode _ _ _)
      (dnil _) (dnil _) (dnil _)
  exact EncodeType.app (π' := .pos) (ι := .star) (ι' := .star) (Ψ₁ := []) (Ψ₂ := [])
    (FwKindInfer.app (π := .neg) (ι := .star) (FwKindInfer.arr _) (G_fwkind _))
    (KindInfer.app (π := .neg) (κ := .star) (KindInfer.arr _) (G_kind _))
    (G_kind _) hleft (G_encode _ _ _) (dnil _) (dnil _) (dnil _)


/-! ## Subtyping and comparison of `G` with itself -/

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

theorem G_cmp (Δ : KindingCtx) (hs : Δ.sizes = []) (ht : Δ.types = []) :
    CompareTypes [] Δ .star .pos G G [] := by
  have hmem7 : ∀ π : Polarity, TyDecl.mk 7 (Polarity.invComp π .mixed) .star ∈
      (((Δ.invScalePol .pos).extType 7 .mixed (Kind.ofSKind .star)).invScalePol π).types := by
    intro π
    simp [KindingCtx.invScalePol, KindingCtx.extType, Kind.ofSKind]
  have hbody : CompareTypes [] ((Δ.invScalePol .pos).extType 7 .mixed (Kind.ofSKind .star)) .star
      (Polarity.comp .pos .pos) (.arrTy (tyV 7) (tyV 7)) (.arrTy (tyV 7) (tyV 7)) ([] ++ []) := by
    refine CompareTypes.app (π₁ := .pos) (ι₁ := .star) (ι₂ := .star) ?_ ?_ (CompareTypes.atom _ _ _ _)
    · exact KindInfer.app (π := .neg) (κ := .star) (KindInfer.arr _)
        (KindCheck.sub (KindInfer.var (hmem7 .neg) (invComp_mixed_le _)) (SubKind.star _))
    · exact CompareTypes.app (π₁ := .neg) (ι₁ := .star) (ι₂ := .arr .pos .star .star)
        (C₁ := []) (C₂ := []) (KindInfer.arr _) (CompareTypes.atom _ _ _ _) (CompareTypes.atom _ _ _ _)
  have hfresh : CompareFresh 7 (Δ.invScalePol .pos) [] Fid Fid := by
    simp [CompareFresh, comparisonTypeNames, FlexVars.dom, KindingCtx.invScalePol,
      SizeCtx.invScalePol, SizeCtx.dom, hs, ht, TypeExpr.arrTy]
  have hlam : CompareTypes [] (Δ.invScalePol .pos) (.arr .mixed .star .star) (Polarity.comp .pos .pos)
      Fid Fid [] :=
    CompareTypes.lam (X := 7) hfresh ⟨.arr .mixed .star .star, rfl, fid_kind _⟩
      ⟨.arr .mixed .star .star, rfl, fid_kind _⟩ hbody
  exact CompareTypes.app (π₁ := .pos) (ι₁ := .arr .mixed .star .star) (ι₂ := .star)
    (C₁ := []) (C₂ := []) (KindInfer.all (KindWf.star _)) (CompareTypes.atom _ _ _ _) hlam

theorem hyg (Δ : KindingCtx) (A C : TypeExpr) : FlexPolHygiene [] Δ A C := by
  constructor <;> intro i π h <;>
    simp [FlexVars.lookupSizePol, FlexVars.lookupPol, SizeExp.var, SizeMin.single] at h

/-! ## Declarative typing of the clause body (the postcheck) -/

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

/-! ## Algorithm 2 inference on the clause body -/

theorem inner_clause_infer (Φ : FlexVars) (hΦ : Φ = []) (Δ : KindingCtx) (Γ : TermCtx)
    (hy : (1, G) ∈ Γ) :
    CheckClauseInfer [] block Φ Γ Δ G (.mk [.tyVar 5, .pat (.var 0)] innerBody)
      [] [] [] (.mk [.tyVar 5, .pat (.var 0)] innerBody) := by
  subst hΦ
  have hmem5 : ∀ Δ' : KindingCtx, TyDecl.mk 5 .pos .star ∈ (Δ'.extType 5 .pos (Kind.ofSKind .star)).types := by
    intro Δ'
    simp [KindingCtx.extType, Kind.ofSKind]
  have hsp : InferSpine Δ [.tyVar 5, .pat (.var 0)] G (tyV 5) [(0, tyV 5)] [⟨5, .pos, .star⟩] []
      [.tyVar 5, .pat (.var 0)] := by
    refine InferSpine.tyApp (ι := .star) (F := Fid) (KindWf.star _) ?_
    show InferSpine _ _ (.arrTy (tyV 5) (tyV 5)) _ _ _ _ _
    exact InferSpine.pat (Γ₁ := [(0, tyV 5)]) (Γ₂ := []) (Δ₁ := []) (Δ₂ := []) (Ψ₁ := []) (Ψ₂ := [])
      (InferPat.var _ 0 (KindCheck.sub (KindInfer.var (hmem5 _) rfl) (SubKind.star _)))
      (InferSpine.nil _ _) (dnil _) (dnil _)
  refine CheckClauseInfer.mk (Ψ := []) (Ψ' := []) hsp rfl ?_
  have hmemD : TyDecl.mk 5 .pos (Kind.ofSKind .star) ∈
      (Δ.append ⟨[], [⟨5, .pos, .star⟩]⟩).types := by
    simp [KindingCtx.append, Kind.ofSKind]
  have hx : ((0 : TermVar), tyV 5) ∈ Γ ++ [(0, tyV 5)] := by simp
  have hy' : ((1 : TermVar), G) ∈ Γ ++ [(0, tyV 5)] := by simp [hy]
  have happ : InferTerm [] block ([].map (fun d : SizeDecl => (d.var, d.pol)) ++ [])
      (Γ ++ [(0, tyV 5)]) (Δ.append ⟨[], [⟨5, .pos, .star⟩]⟩)
      (.app (.var 1) (.tyArg (tyV 5))) (.arrTy (tyV 5) (tyV 5)) [] [] []
      (.app (.var 1) (.tyArg (tyV 5))) :=
    InferTerm.appTy (Ψ := []) (ι := .star) (F := Fid)
      (EncodeType.var (π' := .pos) (ι := .star) hmemD rfl) (dnil _) (InferTerm.var hy')
  have harg : CheckTerm [] block [] (Γ ++ [(0, tyV 5)]) (Δ.append ⟨[], [⟨5, .pos, .star⟩]⟩)
      (tyV 5) (.var 0) [] [] [] (.var 0) :=
    CheckTerm.sub (C₁ := []) (C₂ := []) (InferTerm.var hx) (hyg _ _ _) (CompareTypes.atom _ _ _ _)
  exact CheckTerm.sub (A := tyV 5) (C₁ := []) (C₂ := [])
    (InferTerm.appTerm (C₁ := []) (C₂ := []) (T₁ := []) (T₂ := []) happ harg)
    (hyg _ _ _) (CompareTypes.atom _ _ _ _)

theorem outer_lam_infer (Δ : KindingCtx) (Γ : TermCtx) :
    CheckTerm [] block [] Γ Δ GG outerLam [] [] [] outerLam := by
  refine CheckTerm.lamClauses ?_
  refine CheckClausesInfer.cons (Φ₁ := []) (C₁ := []) (C₂ := []) (T₁ := []) (T₂ := [])
    ?_ (CheckClausesInfer.nil _ _ _ _)
  have hsp : InferSpine Δ [.pat (.var 1)] GG G [(1, G)] [] [] [.pat (.var 1)] :=
    InferSpine.pat (Γ₁ := [(1, G)]) (Γ₂ := []) (Δ₁ := []) (Δ₂ := []) (Ψ₁ := []) (Ψ₂ := [])
      (InferPat.var _ 1 (G_kind _)) (InferSpine.nil _ _) (dnil _) (dnil _)
  refine CheckClauseInfer.mk (Ψ := []) (Ψ' := []) hsp rfl ?_
  refine CheckTerm.lamClauses ?_
  refine CheckClausesInfer.cons (Φ₁ := []) (C₁ := []) (C₂ := []) (T₁ := []) (T₂ := [])
    ?_ (CheckClausesInfer.nil _ _ _ _)
  exact inner_clause_infer _ rfl _ _ (by simp)

theorem N_infer_alg (Δ : KindingCtx) (Γ : TermCtx) (hx : (0, G) ∈ Γ)
    (hs : Δ.sizes = []) (ht : Δ.types = []) :
    InferTerm [] block [] Γ Δ N G [] [] [] N :=
  InferTerm.appTerm (A := G) (B := G) (Φ₁ := []) (C₁ := []) (C₂ := []) (T₁ := []) (T₂ := [])
    (InferTerm.ascr (Ψ := []) (GG_encode _ _ _) (dnil _) (outer_lam_infer _ _))
    (CheckTerm.sub (C₁ := []) (C₂ := []) (InferTerm.var hx) (hyg _ _ _) (G_cmp _ hs ht))

theorem body_infer (Δ : KindingCtx) (Γ : TermCtx) (hx : (0, G) ∈ Γ)
    (hs : Δ.sizes = []) (ht : Δ.types = []) :
    CheckTerm [] block [] Γ Δ G body [] [] [] body := by
  have hNG : InferTerm [] block [] Γ Δ (.app N (.tyArg G)) (.arrTy G G) [] [] [] (.app N (.tyArg G)) :=
    InferTerm.appTy (Ψ := []) (ι := .star) (F := Fid) (G_encode _ _ _) (dnil _)
      (N_infer_alg _ _ hx hs ht)
  exact CheckTerm.sub (A := G) (C₁ := []) (C₂ := [])
    (InferTerm.appTerm (Φ₁ := []) (C₁ := []) (C₂ := []) (T₁ := []) (T₂ := []) hNG
      (CheckTerm.sub (C₁ := []) (C₂ := []) (N_infer_alg _ _ hx hs ht) (hyg _ _ _) (G_cmp _ hs ht)))
    (hyg _ _ _) (G_cmp _ hs ht)

/-! ## Postchecked Algorithm 2 accepts the block -/

theorem body_applyFlex (φ : FlexSubst) : body.applyFlex φ = body := by
  rfl

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

theorem sig_hygiene : SignatureFixpointHygiene (KindingCtx.empty.extSizes []) GG := by
  have h0 : GG.allSizeVars = [] := rfl
  have h1 : GG.allMuBranchLists = [] := rfl
  have h2 : GG.allNuFieldLists = [] := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simp [SizeOccursIn, h0] at hi
  · intro S hS
    simp [h1] at hS
  · intro R hR
    simp [h2] at hR

def run : PostcheckedAlgorithm2ClauseRun [] block noGraphs 0 [] GG [.pat (.var 0)] body clause where
  C' := G
  Γ := [(0, G)]
  Δ' := []
  Ψ₂ := []
  qs' := [.pat (.var 0)]
  Φ := []
  Cs := []
  T := []
  t' := body
  inferSpine :=
    InferSpine.pat (Γ₁ := [(0, G)]) (Γ₂ := []) (Δ₁ := []) (Δ₂ := []) (Ψ₁ := []) (Ψ₂ := [])
      (InferPat.var _ 0 (G_kind _)) (InferSpine.nil _ _) (dnil _) (dnil _)
  consistentExt := ⟨KindingCtxExtWf.nil _, by simp⟩
  clauseSizesWf := SizeCtxWf.nil
  checkBody := body_infer _ _ (by simp) rfl rfl
  callsConform := by
    refine ⟨by rw [body_applyFlex], ?_⟩
    rw [body_applyFlex]
    simp [LocalCallsConform, LocalCallsConformElim, LocalCallsConformClauses]
  postcheckedBody := by
    show ExprCheck _ _ _ (body.applyFlex _) _
    rw [body_applyFlex]
    exact body_check _ _ (by simp)

theorem accepts : PostcheckedAlgorithm2Accepts [] block block := by
  refine ⟨noGraphs, noGraphs_sct, by simp, ?_⟩
  refine List.Forall₂.cons ⟨rfl, GG_encode _ _ _, sig_hygiene, SizeCtxWf.nil, GG_kind _, ?_⟩
    List.Forall₂.nil
  exact List.Forall₂.cons ⟨[.pat (.var 0)], body, rfl, ⟨run⟩⟩ List.Forall₂.nil

theorem scope_ok : scopeBlockExtension [] block := by
  simp [scopeBlockExtension, scopeSignatureClosed, scopeNames, scopeDeclClosed,
    scopeClausesRefs, scopeClauseRefs, scopeTermRefs, scopeElimRefs]

theorem semsig_ok : SemSigValidIn [] block := by
  intro d hd
  simp at hd

/-! ## The clause abstraction is not strongly normalizing -/

theorem acc_irrefl {α : Type} {r : α → α → Prop} {a : α} (h : Acc r a) : ¬ r a a := by
  induction h with
  | intro x _ ih => exact fun hxx => ih x hxx hxx

/-- `(outerLam : G → G) x` steps to `outerLam x`. -/
theorem step_ascr : RedStep block [] N (.app outerLam (.term (.var 0))) :=
  RedStep.whd (WhdStep.ascr outerLam GG [.term (.var 0)])

/-- `outerLam x` steps to `δ`: the substitution `y ↦ x` passes under the binder `x` of the
inner clause and captures. -/
theorem step_capture : RedStep block [] (.app outerLam (.term (.var 0))) delta :=
  RedStep.whd (WhdStep.lamClause (Ds := [.mk [.pat (.var 1)] innerLam]) (qs := [.pat (.var 1)])
    (t := innerLam) (es := [.term (.var 0)]) (es' := []) (by simp)
    (MatchSpine.cons (MatchCopat.pat (MatchPat.var _ _)) MatchSpine.nil))

/-- `δ G δ` steps to itself. -/
theorem step_loop : RedStep block [] loopTerm loopTerm :=
  RedStep.whd (WhdStep.lamClause
    (Ds := [.mk [.tyVar 5, .pat (.var 0)] (.app (.app (.var 0) (.tyArg (tyV 5))) (.term (.var 0)))])
    (qs := [.tyVar 5, .pat (.var 0)])
    (t := .app (.app (.var 0) (.tyArg (tyV 5))) (.term (.var 0)))
    (es := [.tyArg G, .term delta]) (es' := []) (by simp)
    (MatchSpine.cons (MatchCopat.tyVar G 5)
      (MatchSpine.cons (MatchCopat.pat (MatchPat.var _ _)) MatchSpine.nil)))

theorem under_clause {t t' : Term} (h : RedStep block [] t t') :
    RedStep block [] (.lamClauses [.mk [.pat (.var 0)] t]) (.lamClauses [.mk [.pat (.var 0)] t']) :=
  RedStep.lamClauses (ClausesRedStep.head (ClauseRedStep.body h))

theorem not_sn : ¬ SN block [] (.lamClauses [clause]) := by
  intro h
  unfold SN at h
  have h1 := h.inv (under_clause (RedStep.appFun (RedStep.appFun step_ascr)))
  have h2 := h1.inv (under_clause (RedStep.appFun (RedStep.appFun step_capture)))
  have h3 := h2.inv (under_clause (RedStep.appArg step_ascr))
  have h4 := h3.inv (under_clause (RedStep.appArg step_capture))
  exact acc_irrefl h4 (under_clause step_loop)

theorem not_valid : ¬ SemMutualBlockValid [] block := by
  intro h
  exact not_sn (h decl (by simp)).1

/-- The exact `NishtAbel2024V2.theorem_15` statement, universally quantified, is false. -/
theorem theorem_15_false :
    ¬ (∀ (sig : GlobalSig) (Ξ Ξannot : MutualBlock)
        (_hscope : scopeBlockExtension sig Ξannot)
        (_hsig : SemSigValidIn sig Ξannot)
        (_hacc : PostcheckedAlgorithm2Accepts sig Ξ Ξannot),
        MutualBlockTyping sig Ξannot ∧ SemMutualBlockValid sig Ξannot) := by
  intro h
  exact not_valid (h [] block block scope_ok semsig_ok accepts).2

end NishtAbel2024V2.Theorem15Capture

open NishtAbel2024V2

theorem solution : ¬ (∀ (sig : GlobalSig) (Ξ Ξannot : MutualBlock)
    (hscope : scopeBlockExtension sig Ξannot)
    (hsig : SemSigValidIn sig Ξannot)
    (hacc : PostcheckedAlgorithm2Accepts sig Ξ Ξannot),
    MutualBlockTyping sig Ξannot ∧ SemMutualBlockValid sig Ξannot) :=
  NishtAbel2024V2.Theorem15Capture.theorem_15_false

#print axioms solution
