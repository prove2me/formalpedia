-- Prove2me | solution 1 for NishtAbel2024V5.theorems_2_and_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T04:29:43.170741+00:00
-- url     : https://prove2.me/submissions/ded24d07-95bc-4e61-afba-67695c0c10e0

import Definitions.Def_NishtAbel2024V5_Syntax
import Definitions.Def_NishtAbel2024V5_Semantics
import Definitions.Def_NishtAbel2024V5_Inference
import Definitions.Def_NishtAbel2024V5_SemFundamental

open NishtAbel2024V5

theorem solution :
    (∀ (Ψ : SizeCtx) (ρ ρ' : SizeVal),
      ValidVal Ψ ρ →
      ValidVal Ψ ρ' →
      (∀ i ∈ Ψ.dom, ρ i ≤ ρ' i) →
      (∀ a : Size, SizeWf Ψ a → sizeVal ρ SzEnv.zero a ≤ sizeVal ρ' SzEnv.zero a) ∧
      (∀ a b : Size, SizeLe Ψ a b → sizeVal ρ SzEnv.zero a ≤ sizeVal ρ' SzEnv.zero b) ∧
      (∀ a b : Size, SizeLt Ψ a b → sizeVal ρ SzEnv.zero a < sizeVal ρ' SzEnv.zero b)) ∧
    (∀ (W : World) (Ψ : SizeCtx) (ρ : SizeVal),
      (∀ d ∈ W, (Tm.lam d.clauses).Closed) →
      SizeCtxWf Ψ →
      ValidVal Ψ ρ →
      (∀ (F : Ty) (κ : Kind),
        KindingC Ψ [] F κ →
        Good W κ (interp W ρ TEnv.empty F κ.erase SzEnv.zero Env.empty)) ∧
      (∀ (A B : Ty) (κ : Kind),
        SubTy Ψ [] A B κ →
        SemLe W κ (interp W ρ TEnv.empty A κ.erase SzEnv.zero Env.empty)
          (interp W ρ TEnv.empty B κ.erase SzEnv.zero Env.empty))) ∧
    (∀ (W : World) (Ω : TypingEnv) (Ψ : SizeCtx) (ρ : SizeVal),
      (∀ d ∈ W, (Tm.lam d.clauses).Closed) →
      SemValid W Ω.sig →
      (∀ (Ψ' : SizeCtx) (ρ' : SizeVal) (g : FunDecl) (as : List Size),
        g ∈ Ω.block → Ω.localOK Ψ' g.name as → ValidVal Ψ' ρ' →
        ∀ ρg : SizeVal, ValidVal g.sizeParams ρg →
          g.sizeParams.map (fun p => ρg p.1) = as.map (sizeVal ρ' SzEnv.zero) →
          Tm.fn g.name ∈ interpT W ρg TEnv.empty g.ty SzEnv.zero Env.empty) →
      SizeCtxWf Ψ →
      ValidVal Ψ ρ →
      (∀ (t : Tm) (A : Ty),
        ExprTy Ω Ψ [] [] t A →
        KindingC Ψ [] A .star ∧ t ∈ interpT W ρ TEnv.empty A SzEnv.zero Env.empty) ∧
      (∀ (D : List Clause) (A : Ty),
        KindingC Ψ [] A .star →
        (∀ cl ∈ D, ClauseTy Ω Ψ [] [] cl A) →
        Tm.lam D ∈ interpT W ρ TEnv.empty A SzEnv.zero Env.empty)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Ψ ρ ρ' hv hv' hle
    exact ⟨fun _ ha => sizeWf_sound hle SzEnv.zero ha,
      fun _ _ h => sizeLe_sound2 h hv hv' hle,
      fun _ _ h => sizeLt_sound2 h hv hv' hle⟩
  · intro W Ψ ρ hW hΨ hv
    have hθ : TRel W [] TEnv.empty TEnv.empty := fun _ _ _ hX => by simp at hX
    refine ⟨fun F κ hk => (kinding_sound hW hk ρ TEnv.empty TEnv.empty SzEnv.zero
        Env.empty Env.empty hθ (BRel.nil W _ _)).1,
      fun A B κ hsub => (subTy_sound hW hsub ρ TEnv.empty hv hΨ.bounds hθ).2.2⟩
  · intro W Ω Ψ ρ hW hsig hguard hΨ hv
    have E : FundEnv W Ω (fun _ _ => True) :=
      ⟨hW, hsig, fun Ψ' ρ' g as hg hloc hv' _ => hguard Ψ' ρ' g as hg hloc hv',
        fun _ _ _ _ _ _ _ => trivial⟩
    have hθ : TEnvOK W [] TEnv.empty := by intro X π κ hX; simp [TyCtx.toK] at hX
    have hok : CtxOK W (fun _ _ => True) Ψ [] [] ρ TEnv.empty [] :=
      ⟨hv, hΨ.bounds, hθ, by simp [TermCtxWf], SemCtx.nil W ρ TEnv.empty, trivial⟩
    refine ⟨fun t A ht => ?_, fun D A hA hD => ?_⟩
    · have h := fundamental E ht ρ TEnv.empty [] hok
      rwa [Tm.subst_nil] at h
    · have h := (fundamental E (ExprTy.lam hA hD) ρ TEnv.empty [] hok).2
      rwa [Tm.subst_nil] at h
