-- Prove2me | solution 1 for MoritaEquiv.ElemEmb.map_funMap
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-12T20:09:25.535125+00:00
-- url     : https://prove2.me/submissions/fd9f7a13-3582-44c5-b3cf-af828cdb4fd1

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Elementary embeddings commute with the interpretations of function symbols. -/
theorem emf_main {L : Sig} {M N : Str L} (h : ElemEmb M N) {m : ℕ} {dom : Fin m → L.Srt}
    {s : L.Srt} (f : L.Func m dom s) (xs : (j : Fin m) → M.carrier (dom j)) :
    h.toFun s (M.funMap f xs) = N.funMap f (fun j => h.toFun (dom j) (xs j)) := by
  have := (h.map_formula (Formula.equal (Term.func f (fun j => Term.var (Γ := Ctx.cons s dom) j.succ))
    (Term.var 0)) (Fin.cons (α := fun i => M.carrier (Ctx.cons s dom i)) (M.funMap f xs) xs)).2 rfl
  exact this.symm

end MoritaEquiv

open MoritaEquiv

theorem solution {L : Sig} {M N : Str L} (h : ElemEmb M N) {m : ℕ} {dom : Fin m → L.Srt}
    {s : L.Srt} (f : L.Func m dom s) (xs : (j : Fin m) → M.carrier (dom j)) :
    h.toFun s (M.funMap f xs) = N.funMap f (fun j => h.toFun (dom j) (xs j)) := by
  exact emf_main h f xs
