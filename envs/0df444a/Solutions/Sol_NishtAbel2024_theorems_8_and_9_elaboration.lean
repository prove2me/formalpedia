-- Prove2me | solution 1 for NishtAbel2024.theorems_8_and_9_elaboration
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:18:40.22216+00:00
-- url     : https://prove2.me/submissions/3465ecb0-fc00-4bc7-942b-e68b06269f41

import Definitions.Def_NishtAbel2024_Inference

namespace NishtAbel2024

mutual

theorem spine_subst_self (X : TyVar) (F : TypeExpr) :
    TypeExpr.substTyVar X (.atom (.var X)) F = F := by
  cases F with
  | atom K =>
    cases K with
    | var Y =>
      simp only [TypeExpr.substTyVar]
      split <;> simp_all
    | size a => rfl
    | unit => rfl
    | prod => rfl
    | arr => rfl
    | all κ => rfl
    | ex κ => rfl
  | lam Y ι F =>
    simp only [TypeExpr.substTyVar]
    split
    · rfl
    · rw [spine_subst_self X F]
  | app F G =>
    simp only [TypeExpr.substTyVar]
    rw [spine_subst_self X F, spine_subst_self X G]
  | mu a S =>
    simp only [TypeExpr.substTyVar]
    rw [spine_subst_branches_self X S]
  | nu a R =>
    simp only [TypeExpr.substTyVar]
    rw [spine_subst_branches_self X R]
termination_by sizeOf F

theorem spine_subst_branches_self (X : TyVar) (S : List (Nat × TypeExpr)) :
    TypeExpr.substTyVarBranches X (.atom (.var X)) S = S := by
  cases S with
  | nil => rfl
  | cons p rest =>
    rcases p with ⟨name, body⟩
    simp only [TypeExpr.substTyVarBranches]
    rw [spine_subst_self X body, spine_subst_branches_self X rest]
termination_by sizeOf S

end

theorem spine_normApp_self (X : TyVar) (ι : SKind) (B : TypeExpr) :
    (TypeExpr.lam X ι B).normApp (.atom (.var X)) = B := by
  exact spine_subst_self X B

theorem inferPat_elaborates {Δ₀ : KindingCtx} {p p' : Pat} {A : TypeExpr}
    {Γ : TermCtx} {Δ : List TyDecl} {Ψ : SizeCtx}
    (h : InferPat Δ₀ p A Γ Δ Ψ p') : PatTyping Δ₀ Δ Γ p' A := by
  induction h with
  | var Δ₀ x h => exact PatTyping.var Δ₀ x _
  | unit Δ₀ => exact PatTyping.unit Δ₀
  | pair h₁ h₂ hd ha ih₁ ih₂ => exact PatTyping.pair ih₁ ih₂
  | cons j hlookup hf₁ hf₂ hf₃ hf₄ h ih =>
    apply PatTyping.cons j hlookup
    apply PatTyping.tyPack
    simpa [TypeExpr.existsSizeLt, spine_normApp_self] using ih
  | tyPack hw h ih => exact PatTyping.tyPack ih

theorem inferSpine_elaborates {Δ₀ : KindingCtx} {qs qs' : PatSpine} {A C : TypeExpr}
    {Γ : TermCtx} {Δ : List TyDecl} {Ψ : SizeCtx}
    (h : InferSpine Δ₀ qs A C Γ Δ Ψ qs') : SpineTyping Δ₀ Δ Γ A qs' C := by
  induction h with
  | nil Δ₀ A => exact SpineTyping.nil Δ₀ A
  | pat hp hs hd ha ih => exact SpineTyping.pat (inferPat_elaborates hp) ih
  | proj j hlookup hf₁ hf₂ hf₃ hf₄ h ih =>
    apply SpineTyping.proj j hlookup
    apply SpineTyping.tyVar
    simpa [TypeExpr.forallSizeLt, spine_normApp_self] using ih
  | tyApp hw h ih => exact SpineTyping.tyVar ih

end NishtAbel2024

open NishtAbel2024

theorem solution :
    (∀ (Δ₀ : KindingCtx) (p p' : Pat) (A : TypeExpr)
      (Γ : TermCtx) (Δ : List TyDecl) (Ψ : SizeCtx),
      InferPat Δ₀ p A Γ Δ Ψ p' → PatTyping Δ₀ Δ Γ p' A) ∧
    (∀ (Δ₀ : KindingCtx) (qs qs' : PatSpine) (A C : TypeExpr)
      (Γ : TermCtx) (Δ : List TyDecl) (Ψ : SizeCtx),
      InferSpine Δ₀ qs A C Γ Δ Ψ qs' → SpineTyping Δ₀ Δ Γ A qs' C) := by
  exact ⟨fun _ _ _ _ _ _ _ h => inferPat_elaborates h,
         fun _ _ _ _ _ _ _ _ h => inferSpine_elaborates h⟩


#print axioms solution
