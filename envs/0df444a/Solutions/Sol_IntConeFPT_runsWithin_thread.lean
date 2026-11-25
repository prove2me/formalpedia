-- Prove2me | solution 1 for IntConeFPT.runsWithin_thread
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T11:45:40.671938+00:00
-- url     : https://prove2.me/submissions/ffe44d42-8445-4175-a7c9-98a3a26baabe

import Definitions.Def_IntConeFPT_Machine

open Turing IntConeFPT OnlineCRS.Combine Function
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

namespace IntConeFPT.Thread

private abbrev Key (M : Machine) := M.tm.K ⊕ Unit
private abbrev G (M : Machine) : Key M → Type
  | .inl k => M.tm.Γ k
  | .inr _ => Sym
-- false/false: scan context; true/false: prefix delimiter on return; true/true: restore.
private abbrev Lab (M : Machine) := M.tm.Λ ⊕ Fin 3
private abbrev St (M : Machine) := M.tm.σ × Option Sym
private abbrev Code (M : Machine) := TM2.Stmt (G M) (Lab M) (St M)
private def pack (M : Machine) (s : ∀ k, List (M.tm.Γ k)) (b : List Sym) :
    ∀ k, List (G M k)
  | .inl k => s k
  | .inr _ => b

private lemma upd (M : Machine) (s : ∀ k, List (M.tm.Γ k)) b k (v : List (M.tm.Γ k)) :
    update (pack M s b) (.inl k) v = pack M (update s k v) b := by
  funext i; cases i with
  | inr u => simp [pack]
  | inl i =>
    by_cases h : i=k
    · subst i; simp [pack]
    · simp [pack,update,h]

private lemma tmp (M : Machine) (s : ∀ k, List (M.tm.Γ k)) (b c : List Sym) :
    update (pack M s b) (.inr ()) c = pack M s c := by
  funext i; rcases i with i|⟨⟩ <;> simp [pack]

private def tr (M : Machine) : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ → Code M
  | .push k f q => .push (.inl k) (fun s => f s.1) (tr M q)
  | .peek k f q => .peek (.inl k) (fun s o => (f s.1 o,s.2)) (tr M q)
  | .pop k f q => .pop (.inl k) (fun s o => (f s.1 o,s.2)) (tr M q)
  | .load f q => .load (fun s => (f s.1,s.2)) (tr M q)
  | .branch f q r => .branch (fun s => f s.1) (tr M q) (tr M r)
  | .goto f => .goto (fun s => .inl (f s.1))
  | .halt => .goto (fun _ => .inr 1)

private def loc (M : Machine) : Option M.tm.Λ → Option (Lab M)
  | none => some (.inr 1)
  | some l => some (.inl l)

private def liftCfg (M : Machine) (c : M.tm.Cfg) (b : List Sym) : TM2.Cfg (G M) (Lab M) (St M) :=
  ⟨loc M c.l,(c.var,none),pack M c.stk b⟩

private lemma trStep (M : Machine) (q : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ) (v : M.tm.σ)
    (s : ∀ k, List (M.tm.Γ k)) (b : List Sym) :
    TM2.stepAux (tr M q) (v,none) (pack M s b) = liftCfg M (TM2.stepAux q v s) b := by
  induction q generalizing v s with
  | push k f q ih => simpa only [tr,TM2.stepAux,upd,pack] using ih (v:=v) (s:=update s k (f v :: s k))
  | peek k f q ih => exact ih _ _
  | pop k f q ih => simp only [tr,TM2.stepAux,upd]; exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r ih jh => cases h : f v <;> simp [tr,TM2.stepAux,h,ih,jh]
  | goto f => rfl
  | halt => rfl

private def prog (M : Machine) : Lab M → Code M
  | .inl l => tr M (M.tm.m l)
  | .inr 0 => .pop (.inl M.tm.k₀) (fun s o => (s.1,o.map M.inputAlphabet))
      (.branch (fun s => decide (s.2 = some 0))
        (.pop (.inl M.tm.k₀) (fun s o => (s.1,o.map M.inputAlphabet))
          (.push (.inr ()) (fun s => s.2.getD 0) (.goto (fun _ => .inr 0))))
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inl M.tm.main))))
  | .inr 1 => .push (.inl M.tm.k₁) (fun _ => M.outputAlphabet.symm 1) (.goto (fun _ => .inr 2))
  | .inr 2 => .pop (.inr ()) (fun s o => (s.1,o))
      (.branch (fun s => s.2.isSome)
        (.push (.inl M.tm.k₁) (fun s => M.outputAlphabet.symm (s.2.getD 0))
          (.push (.inl M.tm.k₁) (fun _ => M.outputAlphabet.symm 0) (.goto (fun _ => .inr 2))))
        (.load (fun s => (s.1,none)) .halt))

private abbrev W (M : Machine) : Machine where
  tm := { K := Key M, Γ := G M, k₀ := .inl M.tm.k₀, k₁ := .inl M.tm.k₁,
          Λ := Lab M, main := .inr 0, σ := St M, initialState := (M.tm.initialState,none), m := prog M }
  inputAlphabet := M.inputAlphabet
  outputAlphabet := M.outputAlphabet

private abbrev it (M : Machine) (n : ℕ) (c : M.tm.Cfg) :=
  (flip Option.bind M.tm.step)^[n] (some c)

private lemma nullIt (M : Machine) : ∀ n, (flip Option.bind M.tm.step)^[n] none = none
  | 0 => rfl
  | n+1 => by rw [Function.iterate_succ_apply]; exact nullIt M n

private lemma sim (M : Machine) (b : List Sym) : ∀ n c d, it M n c = some d →
    it (W M) n (liftCfg M c b) = some (liftCfg M d b)
  | 0,c,d,h => by have he : c=d := Option.some.inj h; subst d; rfl
  | n+1,c,d,h => by
    unfold it at h ⊢
    rw [Function.iterate_succ_apply] at h ⊢
    rcases c with ⟨l,v,s⟩
    cases l with
    | none =>
      change (flip Option.bind M.tm.step)^[n] none = some d at h
      rw [nullIt] at h
      contradiction
    | some l =>
      change (flip Option.bind (W M).tm.step)^[n] (some (TM2.stepAux (tr M (M.tm.m l)) (v,none) (pack M s b))) = _
      rw [trStep]; exact sim M b n _ _ h

private abbrev io (M : Machine) (k : M.tm.K) (l : List (M.tm.Γ k)) : ∀ i, List (M.tm.Γ i) :=
  update (fun _ => []) k l

private def frame (c x : List Sym) := c.flatMap (fun s => [0,s]) ++ 1 :: x
private def scan (M : Machine) (w b : List Sym) (v : Option Sym) : (W M).tm.Cfg :=
  ⟨some (.inr 0),(M.tm.initialState,v),pack M (io M M.tm.k₀ (w.map M.inputAlphabet.symm)) b⟩
private def restore (M : Machine) (w b : List Sym) (v : Option Sym) : (W M).tm.Cfg :=
  ⟨some (.inr 2),(M.tm.initialState,v),pack M (io M M.tm.k₁ (w.map M.outputAlphabet.symm)) b⟩

private lemma io_init (M : Machine) (w) : (initList M.tm w).stk = io M M.tm.k₀ w := by
  funext k; by_cases h : k=M.tm.k₀
  · subst k; simp [initList,io]
  · simp [h,initList,io,update]
private lemma io_halt (M : Machine) (w) : (haltList M.tm w).stk = io M M.tm.k₁ w := by
  funext k; by_cases h : k=M.tm.k₁
  · subst k; simp [haltList,io]
  · simp [h,haltList,io,update]

private lemma scan_cons (M : Machine) (w b : List Sym) (s : Sym) v :
    (W M).tm.step (scan M (0::s::w) b v) = some (scan M w (s::b) (some s)) := by
  simp [FinTM2.step,TM2.step,scan,prog,TM2.stepAux,upd,tmp,pack,io,Function.update_idem] <;> rfl

private lemma scan_end (M : Machine) (x b : List Sym) v :
    (W M).tm.step (scan M (1::x) b v) =
      some (liftCfg M (initList M.tm (x.map M.inputAlphabet.symm)) b) := by
  simp [FinTM2.step,TM2.step,scan,prog,TM2.stepAux,liftCfg,loc,upd,io_init,io,Function.update_idem,pack] <;> rfl

private lemma scan_trace (M : Machine) (c x b : List Sym) v :
    it (W M) (c.length+1) (scan M (frame c x) b v) =
      some (liftCfg M (initList M.tm (x.map M.inputAlphabet.symm)) (c.reverse ++ b)) := by
  induction c generalizing b v with
  | nil => exact scan_end M x b v
  | cons s c ih =>
    rw [it,List.length_cons,Function.iterate_succ_apply]
    change (flip Option.bind (W M).tm.step)^[c.length+1] ((W M).tm.step (scan M (0::s::frame c x) b v)) = _
    rw [scan_cons]; simpa only [it,List.reverse_cons,List.append_assoc,List.singleton_append] using ih (s::b) (some s)

private lemma return_step (M : Machine) (z b : List Sym) :
    (W M).tm.step (liftCfg M (haltList M.tm (z.map M.outputAlphabet.symm)) b) =
      some (restore M (1::z) b none) := by
  change some (TM2.stepAux (prog M (.inr 1)) (M.tm.initialState,none) (pack M (haltList M.tm (z.map M.outputAlphabet.symm)).stk b)) = _
  rw [io_halt]
  simp [prog,TM2.stepAux,restore,upd,io,pack] <;> rfl

private lemma restore_cons (M : Machine) (w b : List Sym) s v :
    (W M).tm.step (restore M w (s::b) v) = some (restore M (0::s::w) b (some s)) := by
  simp [FinTM2.step,TM2.step,restore,prog,TM2.stepAux,tmp,upd,pack,io,Function.update_idem] <;> rfl

private lemma restore_nil (M : Machine) (w : List Sym) v :
    (W M).tm.step (restore M w [] v) = some (haltList (W M).tm (w.map M.outputAlphabet.symm)) := by
  simp [FinTM2.step,TM2.step,restore,prog,TM2.stepAux,tmp,pack]
  congr 1
  apply TM2.Cfg.mk.injEq .. |>.mpr
  refine ⟨rfl,rfl,?_⟩
  funext k; rcases k with k|⟨⟩
  · by_cases h : k = M.tm.k₁
    · subst k; simp [pack,io,haltList]
    · simp [pack,io,update,haltList,h]
  · simp [pack,haltList]

private lemma restore_trace (M : Machine) (c w : List Sym) v :
    it (W M) (c.length+1) (restore M w c v) =
      some (haltList (W M).tm ((c.reverse.flatMap (fun s => [0,s]) ++ w).map M.outputAlphabet.symm)) := by
  induction c generalizing w v with
  | nil => exact restore_nil M w v
  | cons s c ih =>
    rw [it,List.length_cons,Function.iterate_succ_apply]
    change (flip Option.bind (W M).tm.step)^[c.length+1] ((W M).tm.step (restore M w (s::c) v)) = _
    rw [restore_cons]
    simpa only [it,List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,List.cons_append,List.nil_append] using ih (0::s::w) (some s)

private lemma start (M : Machine) (w : List Sym) :
    initList (W M).tm (w.map M.inputAlphabet.symm) = scan M w [] none := by
  apply TM2.Cfg.mk.injEq .. |>.mpr
  refine ⟨rfl,rfl,?_⟩
  funext k; rcases k with k|⟨⟩
  · by_cases h : k = M.tm.k₀
    · subst k; simp [scan,pack,io,initList]
    · simp [scan,pack,io,update,initList,h]
  · simp [scan,pack,initList]

end IntConeFPT.Thread
open IntConeFPT.Thread

theorem solution (M : Machine) :
    ∃ W : Machine, ∀ (ctx x y : List Sym) (T : ℝ), RunsWithin M x y T →
      RunsWithin W (ctx.flatMap (fun s => [0,s]) ++ 1::x)
        (ctx.flatMap (fun s => [0,s]) ++ 1::y) (T + 2*ctx.length + 3) := by
  refine ⟨W M,?_⟩
  rintro c x y T ⟨n,hn,⟨h⟩⟩
  have a := scan_trace M c x [] none
  have b := sim M c.reverse h.steps _ _ h.evals_in_steps
  change it (W M) h.steps (liftCfg M (initList M.tm (x.map M.inputAlphabet.symm)) c.reverse) =
    some (liftCfg M (haltList M.tm (y.map M.outputAlphabet.symm)) c.reverse) at b
  have d := restore_trace M c.reverse (1::y) none
  let steps := (c.reverse.length+1) + (1 + (h.steps + (c.length+1)))
  refine ⟨steps,?_,⟨⟨⟨steps,?_⟩,le_rfl⟩⟩⟩
  · dsimp [steps]; push_cast
    have hh : (h.steps:ℝ) ≤ n := Nat.cast_le.mpr h.steps_le_m
    simp only [List.length_reverse]; linarith
  · change it (W M) steps (initList _ ((frame c x).map M.inputAlphabet.symm)) = _
    rw [start,it,show steps = _ from rfl,Function.iterate_add_apply,
      Function.iterate_add_apply (m:=1) (n:=h.steps + (c.length+1)),Function.iterate_add_apply (m:=h.steps) (n:=c.length+1)]
    simp only [it,List.append_nil] at a b
    rw [a,Function.iterate_one]
    refine Eq.trans (congrArg (fun o => (flip Option.bind (W M).tm.step)^[c.reverse.length + 1]
      ((flip Option.bind (W M).tm.step) o)) b) ?_
    change (flip Option.bind (W M).tm.step)^[c.reverse.length + 1]
      ((W M).tm.step (liftCfg M (haltList M.tm (y.map M.outputAlphabet.symm)) c.reverse)) = _
    rw [return_step]
    rw [List.reverse_reverse] at d
    exact d
