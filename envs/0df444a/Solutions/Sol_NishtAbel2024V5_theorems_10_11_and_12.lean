-- Prove2me | solution 1 for NishtAbel2024V5.theorems_10_11_and_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T04:30:26.473661+00:00
-- url     : https://prove2.me/submissions/098fe31b-5d9a-4856-a016-c603318b111e

import Definitions.Def_NishtAbel2024V5_Syntax
import Definitions.Def_NishtAbel2024V5_Semantics
import Definitions.Def_NishtAbel2024V5_Inference
import Definitions.Def_NishtAbel2024V5_InfAlgorithm

open NishtAbel2024V5

theorem solution :
    (∀ {Ψ : SizeCtx} {Δ : KCtx} {A B : Ty} {κ : Kind} {C : List SConstr},
      Compare Ψ Δ A B κ C →
      ∀ c ∈ C,
        c.ctx = Ψ ∧ c.strict = false ∧ c.up = true ∧
        ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars, A.indexes .mu i = true ∨ B.indexes .mu i = true) ∨
         (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars, A.indexes .nu i = true ∨ B.indexes .nu i = true))) ∧
    (∀ {Ω : InfEnv},
      (∀ {Ψ Θ Γ r A Φ C T K},
        InferTm Ω Ψ Θ Γ r A Φ C T K →
        ∀ c ∈ C,
          (∃ j π, FlexName j ∧ ⟨j, π, c.ctx⟩ ∈ Φ ∧ (π = .pos ∨ π = .neg) ∧
            c.lhs = .var j 0 ∧ c.strict = true ∧ c.up = true) ∨
          (∃ k, FlexName k ∧ c.lhs = .var k 0 ∧ c.strict = true ∧ c.up = false) ∨
          (∃ A₁ B₁ : Ty, c.strict = false ∧ c.up = true ∧
            ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .mu i = true ∨ B₁.indexes .mu i = true) ∨
             (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .nu i = true ∨ B₁.indexes .nu i = true)))) ∧
      (∀ {Ψ Θ Γ A t Φ C T K},
        CheckTm Ω Ψ Θ Γ A t Φ C T K →
        ∀ c ∈ C,
          (∃ j π, FlexName j ∧ ⟨j, π, c.ctx⟩ ∈ Φ ∧ (π = .pos ∨ π = .neg) ∧
            c.lhs = .var j 0 ∧ c.strict = true ∧ c.up = true) ∨
          (∃ k, FlexName k ∧ c.lhs = .var k 0 ∧ c.strict = true ∧ c.up = false) ∨
          (∃ A₁ B₁ : Ty, c.strict = false ∧ c.up = true ∧
            ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .mu i = true ∨ B₁.indexes .mu i = true) ∨
             (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .nu i = true ∨ B₁.indexes .nu i = true)))) ∧
      (∀ {Ψ Θ Γ A cl Φ C T K},
        CheckClause Ω Ψ Θ Γ A cl Φ C T K →
        ∀ c ∈ C,
          (∃ j π, FlexName j ∧ ⟨j, π, c.ctx⟩ ∈ Φ ∧ (π = .pos ∨ π = .neg) ∧
            c.lhs = .var j 0 ∧ c.strict = true ∧ c.up = true) ∨
          (∃ k, FlexName k ∧ c.lhs = .var k 0 ∧ c.strict = true ∧ c.up = false) ∨
          (∃ A₁ B₁ : Ty, c.strict = false ∧ c.up = true ∧
            ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .mu i = true ∨ B₁.indexes .mu i = true) ∨
             (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
                A₁.indexes .nu i = true ∨ B₁.indexes .nu i = true))))) := by
  refine ⟨theorem_10, fun {Ω} => ?_⟩
  obtain ⟨hI, hC, hCl⟩ := theorems_11_and_12 (Ω := Ω)
  have unpack : ∀ {Φ : List FlexVar} {c : SConstr}, InfConstrOrigin Φ c →
      (∃ j π, FlexName j ∧ ⟨j, π, c.ctx⟩ ∈ Φ ∧ (π = .pos ∨ π = .neg) ∧
        c.lhs = .var j 0 ∧ c.strict = true ∧ c.up = true) ∨
      (∃ k, FlexName k ∧ c.lhs = .var k 0 ∧ c.strict = true ∧ c.up = false) ∨
      (∃ A₁ B₁ : Ty, c.strict = false ∧ c.up = true ∧
        ((∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
            A₁.indexes .mu i = true ∨ B₁.indexes .mu i = true) ∨
         (∀ i ∈ c.lhs.fvars ++ c.rhs.fvars,
            A₁.indexes .nu i = true ∨ B₁.indexes .nu i = true))) := by
    intro Φ c h
    rcases h with h1 | h2 | ⟨A₁, B₁, _, hstr, hup, hvars⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨A₁, B₁, hstr, hup, hvars⟩)
  exact ⟨fun h c hc => unpack (hI h c hc),
    fun h c hc => unpack (hC h c hc),
    fun h c hc => unpack (hCl h c hc)⟩
