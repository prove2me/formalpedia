-- Prove2me | solution 1 for NishtAbel2024.theorems_10_11_and_12
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-02T23:33:40.229893+00:00
-- url     : https://prove2.me/submissions/66d9f635-be98-4efa-83f1-846d677c4882

import Definitions.Def_NishtAbel2024_Inference

namespace NishtAbel2024

def auditPhi : FlexVars := [(0, .pos)]
def auditR : List (ProjName × TypeExpr) := [(0, .mu (.var 0 0) [])]
def auditType : TypeExpr := .nu (.var 0 0) auditR
def auditGamma : TermCtx := [(0, auditType)]
def auditResult : TypeExpr := (TypeExpr.mu (.var 0 0) []).normApp (.nu (.var 1 0) auditR)
def auditT : List SizeVar := if 1 ∈ auditResult.allSizeVars then [] else [1]
def auditConstraint : SizeConstraint := ⟨.var 1 0, .lt, .var 0 0⟩

theorem auditRigid : RigidVarHypotheses .pos [0] auditPhi auditGamma KindingCtx.empty TypeExpr.unitTy := by
  refine ⟨Or.inl rfl, ?_⟩
  dsimp only
  intro i hi
  simp only [List.mem_singleton] at hi
  subst i
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · intro p hp
    simp only [auditGamma, List.mem_singleton] at hp
    subst p
    left
    change SizeOccursFixPol KindingCtx.empty .mu 0 .pos (.nu (.var 0 0) auditR)
    apply SizeOccursFixPol.nu_field (d := 0) (Rd := .mu (.var 0 0) [])
    · simp [auditR]
    · exact SizeOccursFixPol.mu_top
  · right
    simp [SizeOccursIn, TypeExpr.unitTy, TypeExpr.allSizeVars]

theorem auditInfer :
    InferTerm [] [] auditPhi auditGamma KindingCtx.empty
      (.app (.var 0) (.proj 0 none)) auditResult ((1, .neg) :: auditPhi)
      [auditConstraint] auditT (.app (.var 0) (.proj 0 (some (.var 1 0)))) := by
  change InferTerm [] [] auditPhi auditGamma KindingCtx.empty
      (.app (.var 0) (.proj 0 none)) auditResult ((1, .neg) :: auditPhi)
      (⟨.var 1 0, .lt, .var 0 0⟩ :: []) auditT (.app (.var 0) (.proj 0 (some (.var 1 0))))
  refine InferTerm.proj (T := []) 1 ?_ ?_ ?_ ?_ ?_
  · exact InferTerm.var (by simp [auditGamma, auditType])
  · rfl
  · simp [auditPhi, FlexVars.dom]
  · simp [KindingCtx.empty, SizeCtx.dom]
  · rfl

theorem auditForbidden :
    ∃ i ∈ ([0] : List SizeVar), ∃ j ∈ (FlexVars.dom ((1, .neg) :: auditPhi)), j ∉ ([0] : List SizeVar) ∧
      ∃ c ∈ ([auditConstraint] : List SizeConstraint), c.lhs = .var j 0 ∧ c.rhs = .var i 0 := by
  refine ⟨0, by simp, 1, ?_, by simp, auditConstraint, by simp, rfl, rfl⟩
  simp [FlexVars.dom]

theorem audit_theorem11_false :
    ¬ (∀ (sig : GlobalSig) (Ξ : MutualBlock) (π : Polarity) (X : List SizeVar)
       (Φ₀ Φ : FlexVars) (Γ : TermCtx) (Δ : KindingCtx) (A C : TypeExpr)
       (t t' : Term) (Cs : List SizeConstraint) (T : List SizeVar),
      RigidVarHypotheses π X Φ₀ Γ Δ A →
      ((InferTerm sig Ξ Φ₀ Γ Δ t C Φ Cs T t' →
          (∀ i ∈ X, ∀ j ∈ Φ.dom, j ∉ X →
            ∀ c ∈ Cs, ¬ (c.lhs = .var j 0 ∧ c.rhs = .var i 0)) ∧
          (∀ i ∈ X,
            SizeOccursFixPol Δ (if π == .pos then .mu else .nu) i π C ∨ ¬ SizeOccursIn i C)) ∧
       (CheckTerm sig Ξ Φ₀ Γ Δ A t Φ Cs T t' →
          ∀ i ∈ X, ∀ j ∈ Φ.dom, j ∉ X →
            ∀ c ∈ Cs, ¬ (c.lhs = .var j 0 ∧ c.rhs = .var i 0)))) := by
  intro h
  have hbad := ((h [] [] .pos [0] auditPhi ((1, .neg) :: auditPhi) auditGamma KindingCtx.empty
    .unitTy auditResult (.app (.var 0) (.proj 0 none))
    (.app (.var 0) (.proj 0 (some (.var 1 0)))) [auditConstraint] auditT auditRigid).1 auditInfer).1
  obtain ⟨i, hi, j, hj, hjx, c, hc, hl, hr⟩ := auditForbidden
  exact hbad i hi j hj hjx c hc ⟨hl, hr⟩

end NishtAbel2024

open NishtAbel2024

theorem solution : ¬ ((∀ (Φ : FlexVars) (Δ : KindingCtx) (ι : SKind) (π π' π'' : Polarity)
       (A C : TypeExpr) (Cs : List SizeConstraint) (i : SizeVar),
      FlexPolHygiene Φ Δ A C →
      Φ.lookupPol i = some π' →
      (π' = .pos ∨ π' = .neg) →
      (π'' = .pos ∨ π'' = .neg) →
      ¬ SizeOccursIn i A →
      (∀ fk π₀, SizeOccursFixPol Δ fk i π₀ C →
        π₀ = π'' ∧ ((fk = .mu ∧ π' = .pos) ∨ (fk = .nu ∧ π' = .neg))) →
      CompareTypes Φ Δ ι π A C Cs →
      ∀ c ∈ Cs, c.mentions i = true →
        ∃ a : SizeExp,
          c ∈ SizeConstraint.ofPol (Polarity.comp (Polarity.comp π π') π'') a (.var i 0)) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (π : Polarity) (X : List SizeVar)
       (Φ₀ Φ : FlexVars) (Γ : TermCtx) (Δ : KindingCtx) (A C : TypeExpr)
       (t t' : Term) (Cs : List SizeConstraint) (T : List SizeVar),
      RigidVarHypotheses π X Φ₀ Γ Δ A →
      ((InferTerm sig Ξ Φ₀ Γ Δ t C Φ Cs T t' →
          (∀ i ∈ X, ∀ j ∈ Φ.dom, j ∉ X →
            ∀ c ∈ Cs, ¬ (c.lhs = .var j 0 ∧ c.rhs = .var i 0)) ∧
          (∀ i ∈ X,
            SizeOccursFixPol Δ (if π == .pos then .mu else .nu) i π C ∨ ¬ SizeOccursIn i C)) ∧
       (CheckTerm sig Ξ Φ₀ Γ Δ A t Φ Cs T t' →
          ∀ i ∈ X, ∀ j ∈ Φ.dom, j ∉ X →
            ∀ c ∈ Cs, ¬ (c.lhs = .var j 0 ∧ c.rhs = .var i 0)))) ∧
    (∀ (sig : GlobalSig) (Ξ : MutualBlock) (Δ₀ : KindingCtx)
       (Ψ₁ Ψ₂ : SizeCtx) (A A₀ A'' : TypeExpr) (qs qs' : PatSpine)
       (Γ : TermCtx) (Δ : List TyDecl) (t t' : Term)
       (Φ : FlexVars) (Cs : List SizeConstraint) (T : List SizeVar),
      EncodeType .neg .pos Δ₀ A Ψ₁ A₀ →
      SignatureFixpointHygiene (Δ₀.extSizes Ψ₁) A₀ →
      InferSpine (Δ₀.extSizes Ψ₁) qs A₀ A'' Γ Δ Ψ₂ qs' →
      CheckTerm sig Ξ ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
        Γ ((Δ₀.extSizes Ψ₁).append ⟨Ψ₂, Δ⟩) A'' t Φ Cs T t' →
      ∀ k ∈ Φ.dom, k ∉ (Ψ₁ ++ Ψ₂).dom →
        ∀ j ∈ (Ψ₁ ++ Ψ₂).dom,
          ∀ c ∈ Cs, ¬ (c.lhs = .var k 0 ∧ c.rhs = .var j 0))) := by
  intro h
  exact audit_theorem11_false h.2.1
