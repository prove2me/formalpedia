-- Prove2me | solution 1 for NishtAbel2024V5.theorems_13_and_14
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T04:30:27.174193+00:00
-- url     : https://prove2.me/submissions/f93dac9d-3ca0-48d5-8624-5083fafa77fd

import Definitions.Def_NishtAbel2024V5_Syntax
import Definitions.Def_NishtAbel2024V5_Semantics
import Definitions.Def_NishtAbel2024V5_Inference
import Definitions.Def_NishtAbel2024V5_InfAlgorithm

open NishtAbel2024V5

theorem solution :
    (∀ {Ω : InfEnv} {Ωd : TypingEnv} {φ : FlexSubst}
       {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {A : Ty} {cl : Clause}
       {Φ : List FlexVar} {C : List SConstr} {T : List Nat} {K : List CallRec},
      Ω.sig = Ωd.sig →
      Ω.block = Ωd.block →
      (∀ g ∈ Ω.sig, SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star) →
      (∀ g ∈ Ω.block, SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star) →
      (∀ p ∈ φ, FlexName p.1) →
      CheckClause Ω Ψ Θ Γ A cl Φ C T K →
      Coherent φ C →
      ScopeOK φ Φ →
      (∀ k ∈ K, Ωd.localOK (k.ctx.substBounds φ) k.callee (k.args.map (Size.subst φ))) →
      (∀ p ∈ Γ, KindingC (Ψ.substBounds φ) Θ.toK (p.2.substSize φ) .star) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star →
      ClauseTy Ωd (Ψ.substBounds φ) Θ (Γ.map fun p => (p.1, p.2.substSize φ)) cl
        (A.substSize φ)) ∧
    (∀ (fuel : Nat) (Φ : List FlexVar) (C : List SConstr) (T : List Nat),
      (∀ v ∈ Φ, FlexName v.name) →
      checkScope (solve fuel Φ C T) Φ = true →
      checkCoherent fuel (solve fuel Φ C T) C = true →
      (∀ p ∈ solve fuel Φ C T, FlexName p.1) ∧
        ScopeOK (solve fuel Φ C T) Φ ∧
        Coherent (solve fuel Φ C T) C) ∧
    (∀ {sig Ξ Ξannot : List FunDecl},
      (∀ g ∈ sig, SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star) →
      Algorithm2Accepts sig Ξ Ξannot →
      BlockTy sig Ξannot) :=
  ⟨fun hsig hblk hsigwf hblkwf hφ hcl hcoh hsc hK hΓ hA =>
     (inference_sound hsig.symm hblk.symm hsigwf hblkwf hφ).2.2 hcl hcoh hsc hK
       (fun q hq => by
         obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
         exact hΓ p hp)
       hA,
   theorem_14,
   fun hsigwf hacc => algorithm2_typing hsigwf hacc⟩
