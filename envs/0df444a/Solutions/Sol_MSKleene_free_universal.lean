-- Prove2me | solution 1 for MSKleene.free_universal
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-08T12:54:40.415285+00:00
-- url     : https://prove2.me/submissions/62357ecb-5a78-4575-a1d9-ef73d7f2151a

import Definitions.Def_MSKleene_Term

open MSKleene

private theorem ofArgs_toArgs {S : Type} {sig : Signature S} {X : SSet S} :
    ∀ {w : List S} (ts : TermVec sig X w), TermVec.ofArgs (TermVec.toArgs ts) = ts
  | [], .nil => rfl
  | _ :: _, .cons t ts => congrArg (TermVec.cons t) (ofArgs_toArgs ts)

private theorem hom_eq_eval_term {S : Type} {sig : Signature S} {X : SSet S}
    (A : Algebra sig) (ρ : SMap X A.carrier) (g : Hom (freeAlgebra sig X) A)
    (hgen : ∀ (s : S) (x : X s), g.toFun s (eta sig X s x) = ρ s x) :
    ∀ {s : S} (t : Term sig X s), g.toFun s t = Term.eval A ρ t :=
  @Term.rec _ _ _
    (motive_1 := fun s t => g.toFun s t = Term.eval A ρ t)
    (motive_2 := fun w ts =>
      Args.map g.toFun (TermVec.toArgs ts) = TermVec.evalArgs A ρ ts)
    (fun x => hgen _ x)
    (fun σ ts ih => by
      calc
        g.toFun _ (Term.app σ ts) =
            g.toFun _ ((freeAlgebra sig X).op σ (TermVec.toArgs ts)) := by
              simp only [freeAlgebra]
              rw [ofArgs_toArgs]
        _ = A.op σ (Args.map g.toFun (TermVec.toArgs ts)) :=
          g.map_op σ (TermVec.toArgs ts)
        _ = A.op σ (TermVec.evalArgs A ρ ts) := congrArg (A.op σ) ih
        _ = Term.eval A ρ (Term.app σ ts) := rfl)
    rfl
    (fun _ _ iht ihv => congrArg₂ Prod.mk iht ihv)

/-- Evaluation is the unique homomorphism extending the assignment on variables. -/
theorem solution {S : Type} (sig : Signature S) (X : SSet S)
    (A : Algebra sig) (ρ : SMap X A.carrier) :
    ∃! g : Hom (freeAlgebra sig X) A,
      ∀ (s : S) (x : X s), g.toFun s (eta sig X s x) = ρ s x := by
  refine ⟨evalHom A ρ, evalHom_eta A ρ, ?_⟩
  intro g hg
  cases g with
  | mk f hf =>
      have hfun : f = (evalHom A ρ).toFun := by
        funext s t
        exact hom_eq_eval_term A ρ ⟨f, hf⟩ hg t
      cases hfun
      rfl
