-- Prove2me | solution 1 for MoritaEquiv.proj_faithful
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-12T20:09:27.986745+00:00
-- url     : https://prove2.me/submissions/25cae79f-8025-4a78-8780-e347c0122df0

import Mathlib
import Definitions.Def_MoritaEquiv_defs
import Theorems.Thm_MoritaEquiv_ElemEmb_map_funMap
import Theorems.Thm_MoritaEquiv_MoritaData_model_ext_newSorts

open CategoryTheory

namespace MoritaEquiv

namespace PF

set_option allowUnsafeReducibility true
attribute [local reducible] MoritaData.sig Ctx.cons

/-- Apply a unary symbol to a value. -/
def ap {L : Sig} (M : Str L) {a b : L.Srt} (f : L.Func 1 ![a] b) (z : M.carrier a) : M.carrier b :=
  M.funMap f (Fin.cons (α := fun j => M.carrier (![a] j)) z finZeroElim)

theorem emb_ext {L : Sig} {M N : Str L} {f g : ElemEmb M N} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

theorem emb_ap {L : Sig} {M N : Str L} (e : ElemEmb M N) {a b : L.Srt} (F : L.Func 1 ![a] b)
    (z : M.carrier a) : e.toFun b (ap M F z) = ap N F (e.toFun a z) := by
  refine (ElemEmb.map_funMap e F _).trans (congrArg _ (funext fun j => ?_))
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨k + 1, hk⟩ => exact absurd hk (by omega)

theorem pf_main {L : Sig} {T : Theory L} (D : MoritaData L T) : D.proj.Faithful := by
  constructor
  intro M N f g h
  have hold : ∀ (s : L.Srt) (x : M.str.carrier (.old s)),
      ElemEmb.toFun f (.old s) x = ElemEmb.toFun g (.old s) x := fun s x =>
    congrFun (congrFun (congrArg
      (fun e : ElemEmb (M.str.reduct D.incl) (N.str.reduct D.incl) => e.toFun) h) s) x
  have key : ∀ s x, ElemEmb.toFun f s x = ElemEmb.toFun g s x := by
    intro s
    cases s with
    | old s => exact hold s
    | prod σ =>
      intro z
      apply ((MoritaData.model_ext_newSorts D N).1 σ).1
      refine Prod.ext ?_ ?_
      · exact (emb_ap f (MoritaData.ExtFunc.fst σ) z).symm.trans
          ((hold _ _).trans (emb_ap g (MoritaData.ExtFunc.fst σ) z))
      · exact (emb_ap f (MoritaData.ExtFunc.snd σ) z).symm.trans
          ((hold _ _).trans (emb_ap g (MoritaData.ExtFunc.snd σ) z))
    | coprod σ =>
      intro z
      obtain ⟨a | b, rfl⟩ := ((MoritaData.model_ext_newSorts D M).2.1 σ).2 z
      · exact (emb_ap f (MoritaData.ExtFunc.inl σ) a).trans
          ((congrArg (ap N.str (MoritaData.ExtFunc.inl σ)) (hold _ a)).trans
            (emb_ap g (MoritaData.ExtFunc.inl σ) a).symm)
      · exact (emb_ap f (MoritaData.ExtFunc.inr σ) b).trans
          ((congrArg (ap N.str (MoritaData.ExtFunc.inr σ)) (hold _ b)).trans
            (emb_ap g (MoritaData.ExtFunc.inr σ) b).symm)
    | sub σ =>
      intro z
      apply ((MoritaData.model_ext_newSorts D N).2.2.1 σ).1
      exact (emb_ap f (MoritaData.ExtFunc.incl σ) z).symm.trans
        ((hold _ _).trans (emb_ap g (MoritaData.ExtFunc.incl σ) z))
    | quot σ =>
      intro z
      obtain ⟨a, rfl⟩ := ((MoritaData.model_ext_newSorts D M).2.2.2 σ).1 z
      exact (emb_ap f (MoritaData.ExtFunc.proj σ) a).trans
        ((congrArg (ap N.str (MoritaData.ExtFunc.proj σ)) (hold _ a)).trans
          (emb_ap g (MoritaData.ExtFunc.proj σ) a).symm)
  exact emb_ext (funext fun s => funext (key s))

end PF

end MoritaEquiv

open MoritaEquiv

theorem solution {L : Sig} {T : Theory L} (D : MoritaData L T) : D.proj.Faithful :=
  PF.pf_main D
