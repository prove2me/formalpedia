-- Prove2me | solution 1 for NishtAbel2024.theorems_7_8_9_and_lemmas_3_4_5
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:47:30.845348+00:00
-- url     : https://prove2.me/submissions/cc630262-14b8-44ff-8ad5-2a36e3725105

import Definitions.Def_NishtAbel2024_Inference

set_option autoImplicit false

namespace NishtAbel2024

theorem lemma3_branch_vars {i : SizeVar} {S : List (Nat × TypeExpr)} {c : Nat} {F : TypeExpr}
    (hm : (c, F) ∈ S) (hi : i ∈ F.allSizeVars) : i ∈ allSizeVarsBranches S := by
  induction S with
  | nil => simp at hm
  | cons head rest ih =>
    rcases head with ⟨name, body⟩
    simp only [List.mem_cons] at hm
    simp only [allSizeVarsBranches, List.mem_append]
    rcases hm with h | h
    · cases h
      exact Or.inl hi
    · exact Or.inr (ih h)

theorem lemma3_occurs_mem {Δ : KindingCtx} {fk : FixKind} {i : SizeVar}
    {π : Polarity} {A : TypeExpr} (h : SizeOccursFixPol Δ fk i π A) :
    i ∈ A.allSizeVars := by
  induction h with
  | mu_top => simp [TypeExpr.allSizeVars, SizeExp.vars, SizeExp.var, SizeMin.vars,
      SizeMin.single, SizeMin.toList]
  | nu_top => simp [TypeExpr.allSizeVars, SizeExp.vars, SizeExp.var, SizeMin.vars,
      SizeMin.single, SizeMin.toList]
  | mu_branch hm ho ih => simp [TypeExpr.allSizeVars, lemma3_branch_vars hm ih]
  | nu_field hm ho ih => simp [TypeExpr.allSizeVars, lemma3_branch_vars hm ih]
  | lam ho ih => simpa [TypeExpr.allSizeVars] using ih
  | app_left hk ho ih => simp [TypeExpr.allSizeVars, ih]
  | app_right hk ho ih => simp [TypeExpr.allSizeVars, ih]

end NishtAbel2024

namespace NishtAbel2024

def Lemma3NoOccurs (fk : FixKind) (i : SizeVar) (A : TypeExpr) : Prop :=
  ∀ (Δ : KindingCtx) (π : Polarity), ¬ SizeOccursFixPol Δ fk i π A

theorem lemma3_no_of_absent {fk : FixKind} {i : SizeVar} {A : TypeExpr}
    (h : i ∉ A.allSizeVars) : Lemma3NoOccurs fk i A := by
  intro Δ π ho
  exact h (lemma3_occurs_mem ho)

theorem lemma3_no_app {fk : FixKind} {i : SizeVar} {F G : TypeExpr}
    (hf : Lemma3NoOccurs fk i F) (hg : Lemma3NoOccurs fk i G) :
    Lemma3NoOccurs fk i (.app F G) := by
  intro Δ π ho
  cases ho with
  | app_left hk ho => exact hf _ _ ho
  | app_right hk ho => exact hg _ _ ho

theorem lemma3_no_lam {fk : FixKind} {i : SizeVar} {X : TyVar} {ι : SKind} {F : TypeExpr}
    (hf : Lemma3NoOccurs fk i F) : Lemma3NoOccurs fk i (.lam X ι F) := by
  intro Δ π ho
  cases ho with | lam ho => exact hf _ _ ho

theorem lemma3_no_mu_other {i : SizeVar} {a : SizeExp} {S : List (Nat × TypeExpr)}
    (hs : ∀ p ∈ S, Lemma3NoOccurs .nu i p.2) : Lemma3NoOccurs .nu i (.mu a S) := by
  intro Δ π ho
  cases ho with | mu_branch hm ho => exact hs _ hm _ _ ho

theorem lemma3_no_nu_other {i : SizeVar} {a : SizeExp} {S : List (Nat × TypeExpr)}
    (hs : ∀ p ∈ S, Lemma3NoOccurs .mu i p.2) : Lemma3NoOccurs .mu i (.nu a S) := by
  intro Δ π ho
  cases ho with | nu_field hm ho => exact hs _ hm _ _ ho

theorem lemma3_no_mu_same {i : SizeVar} {a : SizeExp} {S : List (Nat × TypeExpr)}
    (ha : ∀ n, a ≠ .var i n) (hs : ∀ p ∈ S, Lemma3NoOccurs .mu i p.2) :
    Lemma3NoOccurs .mu i (.mu a S) := by
  intro Δ π ho
  cases ho with
  | mu_top => exact ha _ rfl
  | mu_branch hm ho => exact hs _ hm _ _ ho

theorem lemma3_no_nu_same {i : SizeVar} {a : SizeExp} {S : List (Nat × TypeExpr)}
    (ha : ∀ n, a ≠ .var i n) (hs : ∀ p ∈ S, Lemma3NoOccurs .nu i p.2) :
    Lemma3NoOccurs .nu i (.nu a S) := by
  intro Δ π ho
  cases ho with
  | nu_top => exact ha _ rfl
  | nu_field hm ho => exact hs _ hm _ _ ho

theorem lemma3_sizeVar_ne {i j : SizeVar} (h : i ≠ j) (n : Nat) :
    SizeExp.var j 0 ≠ .var i n := by
  intro heq
  have hx : j = i := congrArg (fun a : SizeExp =>
    match a with | .inf _ => 0 | .meet m => m.head.var) heq
  exact h hx.symm

end NishtAbel2024


namespace NishtAbel2024.Lemma45DuplicateMuAudit

def sizes : SizeCtx := [⟨1, .mixed, .infty⟩]
def world : KindingCtx := KindingCtx.empty.extSizes sizes
def M : TypeExpr := .mu (.var 1 0) []
def residual : TypeExpr := TypeExpr.arrTy M .unitTy
def initial : TypeExpr := TypeExpr.arrTy M residual
def env : TermCtx := [(0, M)]

theorem no_nu_M : Lemma3NoOccurs .nu 1 M := by
  unfold M
  apply lemma3_no_mu_other
  simp

theorem no_nu_initial : Lemma3NoOccurs .nu 1 initial := by
  unfold initial residual TypeExpr.arrTy
  apply lemma3_no_app
  · apply lemma3_no_app
    · apply lemma3_no_of_absent; simp [TypeExpr.allSizeVars]
    · exact no_nu_M
  · apply lemma3_no_app
    · apply lemma3_no_app
      · apply lemma3_no_of_absent; simp [TypeExpr.allSizeVars]
      · exact no_nu_M
    · apply lemma3_no_of_absent; simp [TypeExpr.unitTy, TypeExpr.allSizeVars]

theorem kind_M (Δ : KindingCtx)
    (h : SizeWf Δ.sizes (.var 1 0)) : KindCheck Δ M .star := by
  unfold M
  exact KindCheck.sub (KindInfer.mu h (by simp)) (SubKind.star _)

theorem wf_size_world : SizeWf world.sizes (.var 1 0) := by
  intro sv hsv
  simp [SizeMin.single, SizeMin.toList] at hsv
  subst sv
  exact ⟨.infty, .mixed, by simp [world, sizes, KindingCtx.empty, KindingCtx.extSizes], rfl⟩

theorem wf_size_neg_world : SizeWf (world.invScalePol .neg).sizes (.var 1 0) := by
  intro sv hsv
  simp [SizeMin.single, SizeMin.toList] at hsv
  subst sv
  exact ⟨.infty, .mixed, by simp [world, sizes, KindingCtx.empty, KindingCtx.extSizes,
    KindingCtx.invScalePol, SizeCtx.invScalePol, Polarity.invComp, Polarity.comp], rfl⟩

theorem mu_neg_initial : SizeOccursFixPol world .mu 1 .neg initial := by
  unfold initial TypeExpr.arrTy
  apply SizeOccursFixPol.app_left (π' := .pos) (κ := .star) (κ' := .star)
  · exact KindInfer.app (KindInfer.arr _) (kind_M _ wf_size_neg_world)
  · apply SizeOccursFixPol.app_right (π := .pos) (π' := .neg)
      (κ := .star) (κ' := .arr .pos .star .star)
    · exact KindInfer.arr _
    · exact SizeOccursFixPol.mu_top

theorem initial_hygiene : SignatureFixpointHygiene world initial := by
  constructor
  · intro i hi
    have heq : i = 1 := by
      simpa [SizeOccursIn, initial, residual, M, TypeExpr.arrTy, TypeExpr.unitTy,
        TypeExpr.allSizeVars, allSizeVarsBranches, SizeExp.vars, SizeMin.vars,
        SizeMin.single, SizeMin.toList, SizeExp.var] using hi
    subst i
    exact Or.inl ⟨mu_neg_initial, no_nu_initial world .pos⟩
  constructor
  · intro S hS c Sc j hlookup _ _
    have : S = [] := by
      simpa [initial, residual, M, TypeExpr.arrTy, TypeExpr.unitTy,
        TypeExpr.allMuBranchLists, allMuBranchListsInBranches] using hS
    subst S
    simp [TypeExpr.lookupCons] at hlookup
  · intro R hR
    simp [initial, residual, M, TypeExpr.arrTy, TypeExpr.unitTy,
      TypeExpr.allNuFieldLists, allNuFieldListsInBranches] at hR

theorem spine : InferSpine world [.pat (.var 0)] initial residual env [] [] [.pat (.var 0)] := by
  unfold initial env
  apply InferSpine.pat (Γ₁ := [(0, M)]) (Γ₂ := []) (Δ₁ := []) (Δ₂ := [])
    (Ψ₁ := []) (Ψ₂ := [])
  · exact InferPat.var _ _ (kind_M _ wf_size_world)
  · exact InferSpine.nil _ _
  · simp [SizeCtx.dom, List.Disjoint]
  · simp [SizeCtx.dom, List.Disjoint]

theorem c1 : ∃ p ∈ env, SizeOccursFixPol world .mu 1 .pos p.2 := by
  exact ⟨(0, M), by simp [env], SizeOccursFixPol.mu_top⟩

theorem c2 : SizeOccursFixPol world .mu 1 .neg residual := by
  unfold residual TypeExpr.arrTy
  apply SizeOccursFixPol.app_left (π' := .pos) (κ := .star) (κ' := .star)
  · exact KindInfer.app (KindInfer.arr _) (kind_M _ wf_size_neg_world)
  · apply SizeOccursFixPol.app_right (π := .pos) (π' := .neg)
      (κ := .star) (κ' := .arr .pos .star .star)
    · exact KindInfer.arr _
    · exact SizeOccursFixPol.mu_top

theorem not_class : ¬ SpineRigidVarClass world env residual 1 := by
  intro h
  rcases h with h | h | h | h
  · exact h.2.1 c2
  · exact h.1 c1
  · exact h.1 c1
  · exact h.1 c1

theorem original_lemma5_false :
    ¬ (∀ (Δ₀ : KindingCtx) (Ψ₁ Ψ₂ : SizeCtx) (qs qs' : PatSpine)
       (A₀ A'' : TypeExpr) (Γ : TermCtx) (Δ : List TyDecl),
      SignatureFixpointHygiene (Δ₀.extSizes Ψ₁) A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ A'' Γ Δ Ψ₂ qs' →
      ∀ i ∈ (Ψ₁ ++ Ψ₂).dom,
        SpineRigidVarClass ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) Γ A'' i) := by
  intro h
  apply not_class
  exact h KindingCtx.empty sizes [] [.pat (.var 0)] [.pat (.var 0)]
    initial residual env [] initial_hygiene spine 1 (by simp [sizes, SizeCtx.dom])


end NishtAbel2024.Lemma45DuplicateMuAudit

open NishtAbel2024

theorem solution : ¬ (
(∀ (πstar π : Polarity) (Δ : KindingCtx) (A A' : TypeExpr) (Ψ : SizeCtx),
      SizeCtxWf Δ.sizes →
      FwKindCheck Δ A .star →
      EncodeType πstar π Δ A Ψ A' →
      KindCheck Δ (TypeExpr.forallSizes Ψ A') .star) ∧
    (∀ (Δ : KindingCtx) (A A' : TypeExpr) (Ψ : SizeCtx),
      EncodeType .neg .pos Δ A Ψ A' →
      ∀ i ∈ Ψ.dom,
        (SizeOccursFixPol (Δ.extSizes Ψ) .mu i .neg A' ∧
          ¬ SizeOccursFixPol (Δ.extSizes Ψ) .nu i .pos A') ∨
        (SizeOccursFixPol (Δ.extSizes Ψ) .nu i .pos A' ∧
          ¬ SizeOccursFixPol (Δ.extSizes Ψ) .mu i .neg A')) ∧
    (∀ (Δ₀ : KindingCtx) (p p' : Pat) (A : TypeExpr)
       (Γ : TermCtx) (Δ : List TyDecl) (Ψ : SizeCtx),
      InferPat Δ₀ p A Γ Δ Ψ p' →
      PatTyping Δ₀ Δ Γ p' A) ∧
    (∀ (Δ₀ : KindingCtx) (qs qs' : PatSpine) (A C : TypeExpr)
       (Γ : TermCtx) (Δ : List TyDecl) (Ψ : SizeCtx),
      InferSpine Δ₀ qs A C Γ Δ Ψ qs' →
      SpineTyping Δ₀ Δ Γ A qs' C) ∧
    (∀ (Δ₀ : KindingCtx) (p p' : Pat) (A₀ : TypeExpr)
       (Γ : TermCtx) (Δ : List TyDecl) (Ψ : SizeCtx),
      PositiveFixpointHygiene Δ₀ A₀ →
      InferPat Δ₀ p A₀ Γ Δ Ψ p' →
      ∀ i ∈ Ψ.dom, PatRigidVarClass (Δ₀.append ⟨Ψ, Δ⟩) Γ i) ∧
    (∀ (Δ₀ : KindingCtx) (Ψ₁ Ψ₂ : SizeCtx) (qs qs' : PatSpine)
       (A₀ A'' : TypeExpr) (Γ : TermCtx) (Δ : List TyDecl),
      SignatureFixpointHygiene (Δ₀.extSizes Ψ₁) A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ A'' Γ Δ Ψ₂ qs' →
      ∀ i ∈ (Ψ₁ ++ Ψ₂).dom,
        SpineRigidVarClass ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) Γ A'' i)
) := by
  intro h
  exact Lemma45DuplicateMuAudit.original_lemma5_false h.2.2.2.2.2
