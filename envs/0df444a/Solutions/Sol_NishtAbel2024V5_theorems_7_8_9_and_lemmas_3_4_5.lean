-- Prove2me | solution 1 for NishtAbel2024V5.theorems_7_8_9_and_lemmas_3_4_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T04:30:25.85443+00:00
-- url     : https://prove2.me/submissions/56f369b3-e34a-4442-8a37-115414cf1669

import Definitions.Def_NishtAbel2024V5_Syntax
import Definitions.Def_NishtAbel2024V5_Semantics
import Definitions.Def_NishtAbel2024V5_Inference
import Definitions.Def_NishtAbel2024V5_InfAlgorithm

open NishtAbel2024V5

theorem solution :
    (∀ {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx} {A A' : Ty} {Ψ : SizeCtx}
       {κ : Kind},
      EKinding Δ Δb A κ →
      Encode πs ok π Δ Δb A Ψ A' →
      SizeCtxWf Ψ ∧ Kinding Ψ Δ Δb 0 A' κ) ∧
    (∀ {ok : Nat → Prop} {Δ : KCtx} {Δb : BCtx} {A A' : Ty} {Ψ : SizeCtx},
      Encode .neg ok .pos Δ Δb A Ψ A' →
      ∀ i ∈ Ψ.dom,
        (SizeOcc .mu i Δ Δb .neg A' ∧ paramPol A' i = .pos ∧
          (∀ Δ' Δb' q, ¬ SizeOcc .nu i Δ' Δb' q A')) ∨
        (SizeOcc .nu i Δ Δb .pos A' ∧ paramPol A' i = .neg ∧
          (∀ Δ' Δb' q, ¬ SizeOcc .mu i Δ' Δb' q A'))) ∧
    (∀ {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx} {Θ' : TyCtx},
      InferPat Ψ Θ p A Γ Ψ' Θ' →
      PatTy Ψ Θ p A Γ Ψ' Θ') ∧
    (∀ {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
       {Θ' : TyCtx} {C : Ty},
      InferSpine Ψ Θ qs A Γ Ψ' Θ' C →
      SpineTy Ψ Θ qs A Γ Ψ' Θ' C) ∧
    (∀ {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx} {Θ' : TyCtx},
      InferPat Ψ Θ p A Γ Ψ' Θ' →
      (∀ q ∈ Ψ', RigidName q.1) ∧
      (∀ {fk : FixKind} {i : Nat} {Δ : KCtx} {Δb : BCtx} {π : Pol} {xB : Nat × Ty},
        xB ∈ Γ → SizeOcc fk i Δ Δb π xB.2 → A.indexes fk i = true ∨ (fk = .mu ∧ i ∈ Ψ'.dom)) ∧
      (∀ j ∈ Ψ'.dom, A.indexes .nu j = false →
        ∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .nu j Δ Δb π xB.2)) ∧
    (∀ {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx}
       {Θ' : TyCtx} {C : Ty},
      InferSpine Ψ Θ qs A Γ Ψ' Θ' C →
      (∀ i ∈ Ψ'.dom, RigidName i) ∧
      (∀ {fk : FixKind} {i : Nat} {Δ : KCtx} {Δb : BCtx} {π : Pol},
        ((∃ xB ∈ Γ, SizeOcc fk i Δ Δb π xB.2) ∨ SizeOcc fk i Δ Δb π C) →
        A.indexes fk i = true ∨ i ∈ Ψ'.dom) ∧
      (∀ {ok : Nat → Prop} {Δ₀ : KCtx} {Δb₀ : BCtx} {A₀ : Ty},
        Encode .neg ok .pos Δ₀ Δb₀ A₀ Ψ A →
        NamesDisjoint Ψ.dom Ψ'.dom →
        ∀ i ∈ Ψ.dom,
          (paramPol A i = .pos ∧
            (∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .nu i Δ Δb π xB.2) ∧
            (∀ Δ Δb π, ¬ SizeOcc .nu i Δ Δb π C)) ∨
          (paramPol A i = .neg ∧
            (∀ xB ∈ Γ, ∀ Δ Δb π, ¬ SizeOcc .mu i Δ Δb π xB.2) ∧
            (∀ Δ Δb π, ¬ SizeOcc .mu i Δ Δb π C)))) :=
  ⟨theorem_7, lemma_3, inferPat_sound, inferSpine_sound, lemma_4, lemma_5⟩
