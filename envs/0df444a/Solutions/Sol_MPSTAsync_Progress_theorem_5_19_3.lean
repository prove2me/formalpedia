-- Prove2me | solution 1 for MPSTAsync.Progress.theorem_5_19_3
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-28T01:38:05.206717+00:00
-- url     : https://prove2.me/submissions/9749a899-6cfb-44d1-b1e2-601acded7162

import Definitions.Def_MPSTAsync_Progress_Activity

set_option autoImplicit false

namespace MPSTAsync.Progress.PreservationCounterexample

private def emptyEnv : Env := ⟨[], []⟩

/-- A syntactically valid conditional whose free Boolean name is absent from the empty
environment. It occurs in an unused declaration with no value parameters. -/
private def badBody : Proc := .ite (.val (.name 0)) .nil .nil
private def badDecl : Decl := .mk 0 [] [] badBody
private def badDecls : List Decl := [badDecl]
private def start : Proc := .ite (.val .tt) .nil .nil
private def finish : Proc := .defn badDecls .nil

private def HeadExprTyped (Γ : Env) : Proc → Prop
  | .ite e _ _ => ExprTyped Γ e .bool
  | _ => True

private theorem typed_head_expr {subs : Bool} {Γ : Env} {P : Proc}
    {q : List Chan} {Δ : Typing} (h : RTyped subs Γ P q Δ) : HeadExprTyped Γ P := by
  induction h <;> simp_all only [HeadExprTyped]

private theorem bad_body_needs_name {subs : Bool} {Γ : Env} {q : List Chan}
    {Δ : Typing} (h : RTyped subs Γ badBody q Δ) : (0, ValSort.bool) ∈ Γ.names := by
  have he : ExprTyped Γ (.val (.name 0)) .bool := typed_head_expr h
  cases he with
  | NAME _ _ hm => exact hm

private def BadDeclHasName (Γ : Env) : Proc → Prop
  | .defn D _ => badDecl ∈ D → (0, ValSort.bool) ∈ Γ.names
  | _ => True

private theorem typed_bad_decl_has_name {subs : Bool} {Γ : Env} {P : Proc}
    {q : List Chan} {Δ : Typing} (h : RTyped subs Γ P q Δ) : BadDeclHasName Γ P := by
  induction h <;> simp only [BadDeclHasName] at * <;> try trivial
  case DEF Γ D P q Δ signatures hbind hX hparams hdefs hP ihdefs ihP =>
    intro hd
    have hname : 0 ∈ signatures.map Prod.fst := by
      rw [← hbind]
      exact List.mem_map.mpr ⟨badDecl, hd, rfl⟩
    obtain ⟨⟨Y, sig⟩, hsig, hY⟩ := List.mem_map.mp hname
    dsimp at hY
    subst Y
    obtain ⟨_, _, _, sss, hsplit, _⟩ :=
      hparams badDecl hd 0 [] [] badBody rfl sig hsig
    have hbody := hdefs badDecl hd 0 [] [] badBody rfl sig hsig sss hsplit
    simpa [Env.addNames, Env.addPVars] using bad_body_needs_name hbody

private theorem finish_untypable {subs : Bool} {q : List Chan} {Δ : Typing}
    (h : RTyped subs emptyEnv finish q Δ) : False := by
  have hh := typed_bad_decl_has_name h
  have hm := hh (by simp [badDecls])
  simp [emptyEnv] at hm

private theorem empty_env_wf : emptyEnv.WellFormed := by
  simp [emptyEnv, Env.WellFormed]

private theorem start_typed : RTyped true emptyEnv start [] [] := by
  apply RTyped.IF
  · exact ExprTyped.BOOL_T _
  · apply RTyped.INACT
    simp [Typing.EndOnly, Typing.WellFormed]
  · apply RTyped.INACT
    simp [Typing.EndOnly, Typing.WellFormed]

private theorem start_reduces_finish : Reduces start finish := by
  apply Reduces.STR start start .nil finish (Congr.refl _)
  · exact Reduces.IFT _ _ _ (Eval.value .tt)
  · exact Congr.symm _ _ (Congr.defNil badDecls)

end MPSTAsync.Progress.PreservationCounterexample

open MPSTAsync.Progress MPSTAsync.Progress.PreservationCounterexample

theorem solution : ¬ (∀ (Γ : Env), Γ.WellFormed → ∀ (P P' : Proc),
    RTyped true Γ P [] [] → Reduces P P' → RTyped true Γ P' [] []) := by
  intro h
  exact finish_untypable (h emptyEnv empty_env_wf start finish start_typed start_reduces_finish)
