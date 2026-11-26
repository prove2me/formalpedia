-- Prove2me | solution 1 for IntConeFPT.lemma_6_prep_writer
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-26T10:17:20.328932+00:00
-- url     : https://prove2.me/submissions/967dacdb-c37b-465c-858c-55094a1cef62

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_RobustToDynamics_encMat
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue

set_option autoImplicit false

open Turing OnlineCRS.Combine IntConeFPT Function
open RobustToDynamics (encMat)

namespace IntConeFPT.Lemma6PrepProof

/-! ### 1. Self-contained multi-register stack TM2 machine model (`StackVM`) -/

namespace StackVM
noncomputable section

abbrev Word := List OnlineCRS.Combine.Sym
abbrev Mem (R : Type) := R → Word

inductive Cmd (R : Type)
  | put (r : R) (w : Word)
  | drop (r : R)
  | pop1 (r : R) (f : R → Sym → Word)
  | drain (r : R) (f : R → Sym → Word)
  | seq (a b : Cmd R)
  | cond (r : R) (p : Option Sym → Bool) (a b : Cmd R)
  | loop (r : R) (p : Option Sym → Bool) (a : Cmd R)

def popped {R : Type} [DecidableEq R] (s : Mem R) (r : R) (f : R → Sym → Word) : Mem R :=
  match s r with
  | [] => s
  | a :: tl => fun j => if j = r then tl else f j a ++ s j

def drained {R : Type} [DecidableEq R] (s : Mem R) (r : R) (f : R → Sym → Word) : Mem R :=
  fun j => if j = r then [] else (s r).reverse.flatMap (f j) ++ s j

inductive Eval {R : Type} [DecidableEq R] : Cmd R → Mem R → Mem R → ℕ → Prop
  | put (s r w) : Eval (.put r w) s (update s r (w ++ s r)) 1
  | drop (s r) : Eval (.drop r) s (update s r (s r).tail) 1
  | pop1 (s r f) : Eval (.pop1 r f) s (popped s r f) 1
  | drain (s r f) : Eval (.drain r f) s (drained s r f) ((s r).length + 1)
  | seq {a b s t u h k} : Eval a s t h → Eval b t u k → Eval (.seq a b) s u (h + k)
  | yes {r p a b s t h} : p (s r).head? = true → Eval a s t h →
      Eval (.cond r p a b) s t (1 + h)
  | no {r p a b s t h} : p (s r).head? = false → Eval b s t h →
      Eval (.cond r p a b) s t (1 + h)
  | stop {r p a s} : p (s r).head? = false → Eval (.loop r p a) s s 1
  | more {r p a s t u h k} : p (s r).head? = true → Eval a s t h →
      Eval (.loop r p a) t u k → Eval (.loop r p a) s u (1 + h + k)
  | mono {a s t h k} : Eval a s t h → h ≤ k → Eval a s t k

def Pos {R : Type} : Cmd R → Type
  | .seq a b => Pos a ⊕ Pos b
  | .cond _ _ a b => Option (Pos a ⊕ Pos b)
  | .loop _ _ a => Option (Pos a)
  | _ => Unit

instance posFin {R : Type} (c : Cmd R) : Fintype (Pos c) := by
  induction c <;> dsimp [Pos] <;> infer_instance

def entry {R : Type} : (c : Cmd R) → Pos c
  | .seq a _ => .inl (entry a)
  | .loop .. | .cond .. => none
  | .put .. | .drop .. | .pop1 .. | .drain .. => ()

inductive Ins (R Q : Type) where
  | put (r : R) (w : Word) (k : Q)
  | drop (r : R) (k : Q)
  | pop1 (r : R) (f : R → Sym → Word) (k : Q)
  | drain (r : R) (f : R → Sym → Word) (k : Q)
  | branch (r : R) (f : Option Sym → Q)
  | halt

def asm {R PC : Type} : (c : Cmd R) → (Pos c → PC) → PC → Pos c → Ins R PC
  | .put r w, _, k, _ => .put r w k
  | .drop r, _, k, _ => .drop r k
  | .pop1 r f, _, k, _ => .pop1 r f k
  | .drain r f, _, k, _ => .drain r f k
  | .seq a b, g, k, .inl j => asm a (g ∘ Sum.inl) (g (.inr (entry b))) j
  | .seq a b, g, k, .inr j => asm b (g ∘ Sum.inr) k j
  | .cond r p a b, g, _, none =>
      .branch r (fun o => if p o then g (some (.inl (entry a))) else g (some (.inr (entry b))))
  | .cond _ _ a _, g, k, some (.inl i) => asm a (fun i => g (some (.inl i))) k i
  | .cond _ _ _ b, g, k, some (.inr i) => asm b (fun i => g (some (.inr i))) k i
  | .loop r p a, g, k, none => .branch r (fun o => if p o then g (some (entry a)) else k)
  | .loop _ _ a, g, _, some i => asm a (g ∘ some) (g none) i

abbrev Code (R PC : Type) := TM2.Stmt (fun _ : R => Sym) PC (Option Sym)

def pushWord {R PC : Type} [DecidableEq R] (k : R) (w : Word) (q : Code R PC) : Code R PC :=
  w.reverse.foldr (fun s q => .push k (fun _ => s) q) q

lemma pushWord_aux {R PC : Type} [DecidableEq R] (k : R) (w : Word) (q : Code R PC) v (s : Mem R) :
    TM2.stepAux (pushWord k w q) v s = TM2.stepAux q v (update s k (w ++ s k)) := by
  have aux (xs : Word) (s : Mem R) :
      TM2.stepAux (xs.foldr (fun a q => TM2.Stmt.push k (fun _ => a) q) q) v s =
        TM2.stepAux q v (update s k (xs.reverse ++ s k)) := by
    induction xs generalizing s with
    | nil => simp
    | cons a xs ih =>
        simp only [List.foldr_cons, TM2.stepAux, ih, update_idem, update_self, List.reverse_cons,
          List.append_assoc, List.singleton_append]
  simpa [pushWord] using aux w.reverse s

def pushAll {R PC : Type} [DecidableEq R] (ks : List R) (f : R → Word) (q : Code R PC) :
    Code R PC :=
  ks.foldr (fun k q => pushWord k (f k) q) q

lemma pushAll_aux {R PC : Type} [DecidableEq R] (ks : List R) (f : R → Word) (q : Code R PC) v
    (s : Mem R) (hn : ks.Nodup) :
    TM2.stepAux (pushAll ks f q) v s =
      TM2.stepAux q v (fun i => if i ∈ ks then f i ++ s i else s i) := by
  induction ks generalizing s with
  | nil => simp [pushAll]
  | cons k ks ih =>
      rw [show pushAll (k :: ks) f q = pushWord k (f k) (pushAll ks f q) from rfl, pushWord_aux,
        ih _ (List.nodup_cons.mp hn).2]
      congr 2; funext i
      by_cases he : i = k
      · subst i; simp [(List.nodup_cons.mp hn).1]
      · simp [he]

def stopAt {R PC : Type} (k : PC) : Code R PC :=
  .load (fun _ => none) (.goto (fun _ => k))

def onSym {R PC : Type} (f : Sym → Code R PC) : Code R PC :=
  .branch (fun v => decide (v = some 0)) (f 0)
    (.branch (fun v => decide (v = some 1)) (f 1)
      (.branch (fun v => decide (v = some 2)) (f 2) (f 3)))

lemma onSym_aux {R PC : Type} [DecidableEq R] (f : Sym → Code R PC) (sym : Sym) (s : Mem R) :
    TM2.stepAux (onSym f) (some sym) s = TM2.stepAux (f sym) (some sym) s := by
  fin_cases sym <;> rfl

noncomputable def code {R PC : Type} [Fintype R] [DecidableEq R]
    (pg : PC → Ins R PC) (i : PC) : Code R PC :=
  match pg i with
  | .halt => .halt
  | .put r w k => pushWord r w (stopAt k)
  | .drop r k => .pop r (fun _ _ => none) (stopAt k)
  | .pop1 r f k =>
      .pop r (fun _ o => o) (.branch (fun v => v.isSome)
        (onSym (fun a => pushAll Finset.univ.toList (fun j => if j = r then [] else f j a)
          (stopAt k)))
        (stopAt k))
  | .drain r f k =>
      .pop r (fun _ o => o) (.branch (fun v => v.isSome)
        (onSym (fun a => pushAll Finset.univ.toList (fun j => if j = r then [] else f j a)
          (stopAt i)))
        (stopAt k))
  | .branch r f => .peek r (fun _ o => o)
      (.branch (fun v => v.isSome) (onSym fun a => stopAt (f (some a))) (stopAt (f none)))

abbrev Cfg (R PC : Type) := TM2.Cfg (fun _ : R => Sym) PC (Option Sym)

def cfg {R PC : Type} (i : PC) (s : Mem R) : Cfg R PC :=
  ⟨some i, none, s⟩

def Reach {α : Type} (f : α → Option α) (n : ℕ) (u v : α) :=
  ∃ k ≤ n, (flip Option.bind f)^[k] (some u) = some v

namespace Reach
variable {α : Type} {f : α → Option α} {a b c : α} {h k : ℕ}
theorem refl : Reach f 0 a a := ⟨0, le_rfl, rfl⟩
theorem one (he : f a = some b) : Reach f 1 a b := ⟨1, le_rfl, he⟩
theorem trans (x : Reach f h a b) (y : Reach f k b c) : Reach f (h + k) a c := by
  obtain ⟨h', hl, he⟩ := x; obtain ⟨k', kl, ke⟩ := y
  exact ⟨k' + h', by omega, by rw [Function.iterate_add_apply, he, ke]⟩
theorem mono (x : Reach f h a b) (hl : h ≤ k) : Reach f k a b := by
  obtain ⟨t, ht, he⟩ := x; exact ⟨t, ht.trans hl, he⟩
end Reach

abbrev step {R PC : Type} [Fintype R] [DecidableEq R] (pg : PC → Ins R PC) :=
  TM2.step (code pg)

private lemma br {R PC : Type} [Fintype R] [DecidableEq R] {pg : PC → Ins R PC} {i r f}
    (he : pg i = .branch r f) (s : Mem R) :
    Reach (step pg) 1 (cfg i s) (cfg (f (s r).head?) s) := by
  apply Reach.one
  cases h : (s r).head? with
  | none => simp [cfg, step, code, he, TM2.step, TM2.stepAux, h, stopAt]
  | some a => simp [cfg, step, code, he, TM2.step, TM2.stepAux, h, onSym_aux, stopAt]

private lemma step_pop1 {R PC : Type} [Fintype R] [DecidableEq R] {pg : PC → Ins R PC} {i r f k}
    (he : pg i = .pop1 r f k) (s : Mem R) :
    Reach (step pg) 1 (cfg i s) (cfg k (popped s r f)) := by
  apply Reach.one
  cases hx : s r with
  | nil =>
      have eq : update s r [] = popped s r f := by
        funext j; by_cases hj : j = r <;> simp [popped, hx, hj]
      simp [cfg, step, code, he, TM2.step, TM2.stepAux, hx, stopAt, eq]
  | cons a tl =>
      simp only [cfg, step, TM2.step, code, he, TM2.stepAux, hx, List.head?_cons,
        List.tail_cons, Option.isSome_some, Bool.cond_true, onSym_aux,
        pushAll_aux _ _ _ _ _ Finset.univ.nodup_toList, Finset.mem_toList, Finset.mem_univ,
        if_true, stopAt, popped]
      congr 3; funext j; by_cases h : j = r <;> simp_all [update]

private lemma bulk {R PC : Type} [Fintype R] [DecidableEq R] {pg : PC → Ins R PC} {i r f k}
    (he : pg i = .drain r f k) (s : Mem R) :
    Reach (step pg) ((s r).length + 1) (cfg i s) (cfg k (drained s r f)) := by
  generalize hx : s r = xs
  induction xs generalizing s with
  | nil =>
      apply Reach.one
      have eq : update s r [] = drained s r f := by
        funext j; simp [drained, hx, update_apply]
      simp [cfg, code, step, he, TM2.step, TM2.stepAux, hx, stopAt, eq]
  | cons a xs ih =>
      let t : Mem R := fun j => if j = r then xs else f j a ++ s j
      have h1 : step pg (cfg i s) = some (cfg i t) := by
        simp only [cfg, step, TM2.step, code, he, TM2.stepAux, hx, List.head?_cons,
          List.tail_cons, Option.isSome_some, Bool.cond_true, onSym_aux,
          pushAll_aux _ _ _ _ _ Finset.univ.nodup_toList, Finset.mem_toList, Finset.mem_univ,
          if_true, stopAt]
        congr 3; funext j; by_cases h : j = r <;> simp_all [t, update]
      have h2 := ih t (by simp [t])
      have eq : drained t r f = drained s r f := by
        funext j; by_cases h : j = r <;>
          simp [drained, t, h, hx, List.flatMap_append, List.append_assoc]
      rw [eq] at h2
      exact ((Reach.one h1).trans h2).mono (by simp; omega)

theorem sound {R PC : Type} [Fintype R] [DecidableEq R] {c : Cmd R} {s t n} (h : Eval c s t n)
    (pg : PC → Ins R PC) (g : Pos c → PC) (k : PC) (sub : ∀ j, pg (g j) = asm c g k j) :
    Reach (step pg) n (cfg (g (entry c)) s) (cfg k t) := by
  induction h generalizing k with
  | put s r w =>
      apply Reach.one
      change some (TM2.stepAux (code pg (g ())) _ _) = _
      have h : pg (g ()) = .put r w k := sub ()
      simp [code, h, pushWord_aux, stopAt, TM2.stepAux, cfg]
  | drop s r =>
      apply Reach.one
      change some (TM2.stepAux (code pg (g ())) _ _) = _
      have h : pg (g ()) = .drop r k := sub ()
      simp [code, h, stopAt, TM2.stepAux, cfg]
  | pop1 _ _ _ => exact step_pop1 (sub ()) _
  | drain _ _ _ => exact bulk (sub ()) _
  | seq _ _ ih jh =>
      exact (ih (g ∘ Sum.inl) _ (fun j => sub (.inl j))).trans
        (jh (g ∘ Sum.inr) k (fun j => sub (.inr j)))
  | @yes r p a b s t n hp _ ih =>
      have branch := br (pg := pg) (i := g none) (r := r)
        (f := fun o => if p o then g (some (.inl (entry a))) else g (some (.inr (entry b))))
        (sub none) s
      simp only [hp, if_true] at branch
      exact branch.trans (ih (fun j => g (some (.inl j))) k (fun j => sub (some (.inl j))))
  | @no r p a b s t n hp _ ih =>
      have branch := br (pg := pg) (i := g none) (r := r)
        (f := fun o => if p o then g (some (.inl (entry a))) else g (some (.inr (entry b))))
        (sub none) s
      simp only [hp, Bool.false_eq_true, if_false] at branch
      exact branch.trans (ih (fun j => g (some (.inr j))) k (fun j => sub (some (.inr j))))
  | @stop r p a s hn =>
      have branch := br (pg := pg) (i := g none) (r := r)
        (f := fun o => if p o then g (some (entry a)) else k) (sub none) s
      simp only [hn, Bool.false_eq_true, if_false] at branch; exact branch
  | @more r p a s t u h j hp _ _ ih jh =>
      have branch := br (pg := pg) (i := g none) (r := r)
        (f := fun o => if p o then g (some (entry a)) else k) (sub none) s
      simp only [hp, if_true] at branch
      exact (branch.trans (ih (g ∘ some) (g none) (fun j => sub (some j)))).trans (jh g k sub)
  | mono _ hl ih => exact (ih g k sub).mono hl

def pgm {R : Type} (c : Cmd R) : Option (Pos c) → Ins R (Option (Pos c))
  | none => .halt
  | some j => asm c some none j

noncomputable abbrev compiled {R : Type} [Fintype R] [DecidableEq R]
    (io : R) (c : Cmd R) : Machine where
  tm :=
    { K := R, k₀ := io, k₁ := io, Γ := fun _ => Sym,
      Λ := Option (Pos c), main := some (entry c), σ := Option Sym,
      initialState := none, m := code (pgm c) }
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _

def singleWord {R : Type} [DecidableEq R] (i : R) (x : Word) : Mem R := update (fun _ => []) i x

theorem compile_run {R : Type} [Fintype R] [DecidableEq R] {io : R} {c : Cmd R} {x y n}
    (h : Eval c (singleWord io x) (singleWord io y) n) :
    RunsWithin (compiled io c) x y ((n + 1 : ℕ) : ℝ) := by
  let W := compiled io c
  have hinit : initList W.tm (x.map W.inputAlphabet.invFun) =
      cfg (PC := Option (Pos c)) (some (entry c)) (singleWord io x) := by
    apply TM2.Cfg.mk.injEq .. |>.mpr
    refine ⟨rfl, rfl, funext fun j => ?_⟩
    by_cases he : j = io
    · subst j; simp [initList, W, compiled, singleWord, Equiv.refl]
    · simp [initList, W, compiled, singleWord, update, he]
  have hstop : W.tm.step (cfg (PC := Option (Pos c)) none (singleWord io y)) =
      some (haltList W.tm (y.map W.outputAlphabet.invFun)) := by
    change some (TM2.stepAux (code (pgm c) none) _ _) = _
    apply congrArg some; apply TM2.Cfg.mk.injEq .. |>.mpr
    refine ⟨rfl, rfl, funext fun j => ?_⟩
    by_cases he : j = io
    · subst j; simp [haltList, W, compiled, code, pgm, TM2.stepAux, singleWord, Equiv.refl]
    · simp [haltList, W, compiled, code, pgm, TM2.stepAux, singleWord, update, he]
  have hrun := sound h (pgm c) some none (fun _ => rfl)
  obtain ⟨k, hk, hr⟩ := hrun.trans (Reach.one hstop)
  exact ⟨n + 1, le_rfl, ⟨⟨⟨k, hinit ▸ hr⟩, hk⟩⟩⟩

theorem runsWithin_of_eval {R : Type} [Fintype R] [DecidableEq R] {io : R} {c : Cmd R} {x y : Word}
    {n : ℕ} {T : ℝ} (h : Eval c (singleWord io x) (singleWord io y) n) (hT : ((n + 1 : ℕ) : ℝ) ≤ T) :
    RunsWithin (compiled io c) x y T := by
  obtain ⟨m, hm, hr⟩ := compile_run h
  exact ⟨m, hm.trans hT, hr⟩

-- Convenience `Eval` frame lemmas
lemma eval_drain1 {R : Type} [DecidableEq R] (src dst : R) (hne : src ≠ dst)
    (f : Sym → Word) (s : Mem R) :
    Eval (.drain src (fun j a => if j = dst then f a else []))
      s (update (update s src []) dst ((s src).reverse.flatMap f ++ s dst)) ((s src).length + 1) := by
  have heq : drained s src (fun j a => if j = dst then f a else []) =
      update (update s src []) dst ((s src).reverse.flatMap f ++ s dst) := by
    funext j
    by_cases hj1 : j = dst
    · subst hj1; simp [drained, hne.symm]
    · by_cases hj2 : j = src
      · subst hj2; simp [drained, hj1]
      · simp [drained, hj1, hj2]
  rw [← heq]
  exact Eval.drain s src _

lemma eval_drain2 {R : Type} [DecidableEq R] (src d1 d2 : R)
    (h1 : src ≠ d1) (h2 : src ≠ d2) (h12 : d1 ≠ d2) (f1 f2 : Sym → Word) (s : Mem R) :
    Eval (.drain src (fun j a => if j = d1 then f1 a else if j = d2 then f2 a else []))
      s (update (update (update s src []) d1 ((s src).reverse.flatMap f1 ++ s d1))
          d2 ((s src).reverse.flatMap f2 ++ s d2))
      ((s src).length + 1) := by
  have heq : drained s src (fun j a => if j = d1 then f1 a else if j = d2 then f2 a else []) =
      update (update (update s src []) d1 ((s src).reverse.flatMap f1 ++ s d1))
        d2 ((s src).reverse.flatMap f2 ++ s d2) := by
    funext j
    by_cases hj2 : j = d2
    · subst hj2; simp [drained, h2.symm, h12.symm]
    · by_cases hj1 : j = d1
      · subst hj1; simp [drained, h1.symm, hj2]
      · by_cases hjs : j = src
        · subst hjs; simp [drained, hj1, hj2]
        · simp [drained, hj1, hj2, hjs]
  rw [← heq]
  exact Eval.drain s src _

lemma eval_drain3 {R : Type} [DecidableEq R] (src d1 d2 d3 : R)
    (hs1 : src ≠ d1) (hs2 : src ≠ d2) (hs3 : src ≠ d3)
    (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (f1 f2 f3 : Sym → Word) (s : Mem R) :
    Eval (.drain src (fun j a =>
        if j = d1 then f1 a else if j = d2 then f2 a else if j = d3 then f3 a else []))
      s (update (update (update (update s src []) d1 ((s src).reverse.flatMap f1 ++ s d1))
          d2 ((s src).reverse.flatMap f2 ++ s d2))
          d3 ((s src).reverse.flatMap f3 ++ s d3))
      ((s src).length + 1) := by
  have heq : drained s src (fun j a =>
        if j = d1 then f1 a else if j = d2 then f2 a else if j = d3 then f3 a else []) =
      update (update (update (update s src []) d1 ((s src).reverse.flatMap f1 ++ s d1))
          d2 ((s src).reverse.flatMap f2 ++ s d2))
          d3 ((s src).reverse.flatMap f3 ++ s d3) := by
    funext j
    by_cases hj3 : j = d3
    · subst hj3; simp [drained, hs3.symm, h13.symm, h23.symm]
    · by_cases hj2 : j = d2
      · subst hj2; simp [drained, hs2.symm, h12.symm, hj3]
      · by_cases hj1 : j = d1
        · subst hj1; simp [drained, hs1.symm, hj2, hj3]
        · by_cases hjs : j = src
          · subst hjs; simp [drained, hj1, hj2, hj3]
          · simp [drained, hj1, hj2, hj3, hjs]
  rw [← heq]
  exact Eval.drain s src _

lemma eval_pop1_1 {R : Type} [DecidableEq R] (src dst : R) (hne : src ≠ dst)
    (f : Sym → Word) (s : Mem R) (a : Sym) (tl : Word) (hs : s src = a :: tl) :
    Eval (.pop1 src (fun j x => if j = dst then f x else []))
      s (update (update s src tl) dst (f a ++ s dst)) 1 := by
  have heq : popped s src (fun j x => if j = dst then f x else []) =
      update (update s src tl) dst (f a ++ s dst) := by
    funext j
    by_cases hj1 : j = dst
    · subst hj1; simp [popped, hs, hne.symm]
    · by_cases hj2 : j = src
      · subst hj2; simp [popped, hs, hj1]
      · simp [popped, hs, hj1, hj2]
  rw [← heq]
  exact Eval.pop1 s src _

lemma eval_pop1_2 {R : Type} [DecidableEq R] (src d1 d2 : R)
    (h1 : src ≠ d1) (h2 : src ≠ d2) (h12 : d1 ≠ d2) (f1 f2 : Sym → Word)
    (s : Mem R) (a : Sym) (tl : Word) (hs : s src = a :: tl) :
    Eval (.pop1 src (fun j x => if j = d1 then f1 x else if j = d2 then f2 x else []))
      s (update (update (update s src tl) d1 (f1 a ++ s d1)) d2 (f2 a ++ s d2)) 1 := by
  have heq : popped s src (fun j x => if j = d1 then f1 x else if j = d2 then f2 x else []) =
      update (update (update s src tl) d1 (f1 a ++ s d1)) d2 (f2 a ++ s d2) := by
    funext j
    by_cases hj2 : j = d2
    · subst hj2; simp [popped, hs, h2.symm, h12.symm]
    · by_cases hj1 : j = d1
      · subst hj1; simp [popped, hs, h1.symm, hj2]
      · by_cases hjs : j = src
        · subst hjs; simp [popped, hs, hj1, hj2]
        · simp [popped, hs, hj1, hj2, hjs]
  rw [← heq]
  exact Eval.pop1 s src _

end
end StackVM

/-! ### 2. Binary encoding, counter decrement, and length lemmas -/

section Encodings

open StackVM

private lemma encNat_zero : encNat 0 = [] := by rfl

private lemma encNat_one : encNat 1 = [1] := by
  simp [encNat, Computability.encodeNat, Computability.encodeNum, Computability.encodePosNum, bit]

private lemma encNat_bit1 (n : ℕ) : encNat (2 * n + 1) = 1 :: encNat n := by
  rw [show 2 * n + 1 = ((n : Num).bit1 : ℕ) by simp [Num.cast_bit1, add_comm]]
  simp only [encNat, Computability.encodeNat, Num.of_to_nat]
  cases hn : (n : Num) with
  | zero => simp [Num.bit1, Computability.encodeNum, Computability.encodePosNum, bit]
  | pos p => simp [Num.bit1, Computability.encodeNum, Computability.encodePosNum, bit]

private lemma encNat_bit0 (n : ℕ) (hn : n ≠ 0) : encNat (2 * n) = 0 :: encNat n := by
  obtain ⟨m, hm⟩ : ∃ m : Num, (m : ℕ) = n := ⟨n, Num.to_of_nat n⟩
  subst n
  rw [← Num.cast_bit0]
  simp only [encNat, Computability.encodeNat, Num.of_to_nat]
  cases m with
  | zero => exact (hn rfl).elim
  | pos _ => rfl

private lemma encNat_ne_nil (n : ℕ) (hn : n ≠ 0) : encNat n ≠ [] := by
  obtain ⟨m, hm⟩ : ∃ m : Num, (m : ℕ) = n := ⟨n, Num.to_of_nat n⟩
  subst n
  simp only [encNat, Computability.encodeNat, Num.of_to_nat, ne_eq, List.map_eq_nil_iff]
  cases m with
  | zero => exact (hn rfl).elim
  | pos p => cases p <;> simp [Computability.encodeNum, Computability.encodePosNum]

private lemma encNat_length_eq_size (n : ℕ) : (encNat n).length = n.size := by
  obtain ⟨m, rfl⟩ : ∃ m : Num, (m : ℕ) = n := ⟨n, Num.to_of_nat n⟩
  simp only [encNat, Computability.encodeNat, Num.of_to_nat, List.length_map]
  cases m with
  | zero => rfl
  | pos p =>
      change (Computability.encodePosNum p).length = Nat.size (p : ℕ)
      rw [← PosNum.natSize_to_nat]
      induction p <;> simp_all [Computability.encodePosNum, PosNum.natSize]

private lemma encNat_length_mono {a b : ℕ} (hab : a ≤ b) :
    (encNat a).length ≤ (encNat b).length := by
  rw [encNat_length_eq_size, encNat_length_eq_size]
  exact Nat.size_le_size hab

private lemma exists_odd_mul_two_pow : ∀ k : ℕ, 1 ≤ k → ∃ e q : ℕ, k = (2 * q + 1) * 2 ^ e
  | 0, hk => by omega
  | k + 1, _ => by
      by_cases hodd : (k + 1) % 2 = 1
      · refine ⟨0, (k + 1) / 2, ?_⟩
        omega
      · have hev : (k + 1) % 2 = 0 := by omega
        have hk2 : 1 ≤ (k + 1) / 2 := by omega
        obtain ⟨e, q, hq⟩ := exists_odd_mul_two_pow ((k + 1) / 2) hk2
        refine ⟨e + 1, q, ?_⟩
        calc k + 1 = 2 * ((k + 1) / 2) := by omega
          _ = 2 * ((2 * q + 1) * 2 ^ e) := by rw [hq]
          _ = (2 * q + 1) * 2 ^ (e + 1) := by rw [pow_succ]; ring
termination_by k => k

private lemma encNat_odd_mul_two_pow (q e : ℕ) :
    encNat ((2 * q + 1) * 2 ^ e) = List.replicate e 0 ++ 1 :: encNat q := by
  induction e with
  | zero => simp [encNat_bit1]
  | succ e ih =>
      rw [show (2 * q + 1) * 2 ^ (e + 1) = 2 * ((2 * q + 1) * 2 ^ e) by rw [pow_succ]; ring,
        encNat_bit0 _ (by positivity), ih, List.replicate_succ, List.cons_append]

private lemma encNat_pred_zero (e : ℕ) : encNat (2 ^ e - 1) = List.replicate e 1 := by
  induction e with
  | zero => simp [encNat_zero]
  | succ e ih =>
      have hpos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
      rw [show 2 ^ (e + 1) - 1 = 2 * (2 ^ e - 1) + 1 by rw [pow_succ']; omega,
        encNat_bit1, ih, List.replicate_succ]

private lemma encNat_pred_pos (q e : ℕ) (hq : q ≠ 0) :
    encNat ((2 * q + 1) * 2 ^ e - 1) = List.replicate e 1 ++ 0 :: encNat q := by
  induction e with
  | zero =>
      simp only [pow_zero, mul_one, Nat.add_sub_cancel, List.replicate_zero, List.nil_append]
      exact encNat_bit0 q hq
  | succ e ih =>
      have hpow : 1 ≤ (2 * q + 1) * 2 ^ e := Nat.succ_le_of_lt (by positivity)
      have hmul2 : (2 * q + 1) * 2 ^ (e + 1) = 2 * ((2 * q + 1) * 2 ^ e) := by rw [pow_succ]; ring
      rw [show (2 * q + 1) * 2 ^ (e + 1) - 1 = 2 * ((2 * q + 1) * 2 ^ e - 1) + 1 by omega,
        encNat_bit1, ih, List.replicate_succ, List.cons_append]

private lemma encNat_mem_zero_or_one {n : ℕ} {s : Sym} (hs : s ∈ encNat n) : s = 0 ∨ s = 1 := by
  simp only [encNat, List.mem_map] at hs
  rcases hs with ⟨b, _, rfl⟩
  cases b <;> decide

private lemma three_not_mem_encNat (k : ℕ) : (3 : Sym) ∉ encNat k := by
  intro hs
  rcases encNat_mem_zero_or_one hs with h | h <;> exact absurd h (by decide)

private lemma three_not_mem_encInt (z : ℤ) : (3 : Sym) ∉ encInt z := by
  simp only [encInt, List.mem_cons]
  rintro (h | hs)
  · revert h; cases decide (z < 0) <;> decide
  · exact three_not_mem_encNat _ hs

private lemma three_not_mem_encRat (q : ℚ) : (3 : Sym) ∉ encRat q := by
  simp only [encRat, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro ((h | h) | h)
  · exact three_not_mem_encInt _ h
  · exact absurd h (by decide)
  · exact three_not_mem_encNat _ h

private lemma mem_tok_ne_three_iff (s : Sym) :
    decide (s = 0 ∨ s = 1 ∨ s = 2) = true ↔ s ≠ 3 := by
  fin_cases s <;> decide

private lemma encRat_intCast (a : ℤ) : encRat (a : ℚ) = encInt a ++ [2, 1] := by
  simp [encRat, Rat.num_intCast, Rat.den_intCast, encNat_one, List.append_assoc]

private lemma encRat_natCast (n : ℕ) : encRat (n : ℚ) = 0 :: encNat n ++ [2, 1] := by
  have h : encInt (n : ℤ) = 0 :: encNat n := by
    simp [encInt, bit, Int.natAbs_natCast]
  simpa [Rat.cast_natCast, h] using encRat_intCast (n : ℤ)

private lemma encVec_intCast {d : ℕ} (z : Fin d → ℤ) :
    encVec (fun i => (z i : ℚ)) =
      (encIntVec z).flatMap (fun s => if s = 3 then [2, 1, 3] else [s]) := by
  have haux : ∀ xs : List (Fin d),
      xs.flatMap (fun i => encRat (z i : ℚ) ++ [3]) =
        (xs.flatMap (fun i => encInt (z i) ++ [3])).flatMap
          (fun s => if s = 3 then [2, 1, 3] else [s]) := fun xs => by
    induction xs with
    | nil => simp
    | cons a tl ih =>
        have htok : (encInt (z a)).flatMap (fun s => if s = 3 then [2, 1, 3] else [s]) =
            encInt (z a) := by
          have hgen : ∀ w : Word, (3 : Sym) ∉ w →
              w.flatMap (fun s => if s = 3 then [2, 1, 3] else [s]) = w := fun w hw => by
            induction w with
            | nil => simp
            | cons x xs ihw =>
                have hx : x ≠ 3 := fun h => hw (h ▸ List.mem_cons_self)
                simp [hx, ihw (fun h => hw (List.mem_cons_of_mem _ h))]
          exact hgen _ (three_not_mem_encInt _)
        rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_append, List.flatMap_append,
          htok, ← ih]
        simp [encRat_intCast, List.append_assoc]
  exact haux (List.finRange d)

private lemma reverse_flatMap {α β : Type} (xs : List α) (f : α → List β) :
    (xs.flatMap f).reverse = xs.reverse.flatMap (fun a => (f a).reverse) := by
  induction xs with
  | nil => simp
  | cons a tl ih => simp [List.flatMap_cons, List.reverse_append, List.flatMap_append, ih]

private lemma reverse_flatMap_frame (w : Word) :
    (w.flatMap (fun s => [(0 : Sym), s])).reverse = w.reverse.flatMap (fun s => [s, (0 : Sym)]) := by
  simpa using reverse_flatMap w (fun s => [(0 : Sym), s])

private lemma reverse_flatMap_int2rat (w : Word) :
    (w.flatMap (fun s => if s = 3 then [(2 : Sym), 1, 3] else [s])).reverse =
      w.reverse.flatMap (fun s => if s = 3 then [(3 : Sym), 1, 2] else [s]) := by
  rw [reverse_flatMap]
  congr 1; funext s
  by_cases hs : s = 3 <;> simp [hs]

private lemma encIntVec_ends_three {d : ℕ} (hd : 1 ≤ d) (z : Fin d → ℤ) :
    ∃ pre : Word, encIntVec z = pre ++ [3] := by
  have aux : ∀ (xs : List (Fin d)) (_ : xs ≠ []),
      ∃ pre : Word, xs.flatMap (fun i => encInt (z i) ++ [3]) = pre ++ [3] := fun xs hne => by
    induction xs with
    | nil => exact absurd rfl hne
    | cons a tl ih =>
        cases tl with
        | nil => exact ⟨encInt (z a), by simp⟩
        | cons b tl2 =>
            obtain ⟨pre, hpre⟩ := ih (by simp)
            exact ⟨encInt (z a) ++ [3] ++ pre, by simp [List.flatMap_cons, hpre, List.append_assoc]⟩
  refine aux (List.finRange d) ?_
  intro h
  have hlen := congrArg List.length h
  simp at hlen
  omega

private lemma encResidue_ends_three {d : ℕ} (hd : 1 ≤ d) (r : Residue d) :
    ∃ pre : Word, encResidue r = pre ++ [3] := by
  have aux : ∀ (xs : List (Fin d)) (_ : xs ≠ []),
      ∃ pre : Word, xs.flatMap (fun i => encNat (r i) ++ [3]) = pre ++ [3] := fun xs hne => by
    induction xs with
    | nil => exact absurd rfl hne
    | cons a tl ih =>
        cases tl with
        | nil => exact ⟨encNat (r a), by simp⟩
        | cons b tl2 =>
            obtain ⟨pre, hpre⟩ := ih (by simp)
            exact ⟨encNat (r a) ++ [3] ++ pre, by simp [List.flatMap_cons, hpre, List.append_assoc]⟩
  refine aux (List.finRange d) ?_
  intro h
  have hlen := congrArg List.length h
  simp at hlen
  omega

-- Length bounds relative to `inp.length`
private lemma encIntVec_ge_dim {d : ℕ} (z : Fin d → ℤ) : d ≤ (encIntVec z).length := by
  have aux : ∀ xs : List (Fin d),
      xs.length ≤ (xs.flatMap fun i => encInt (z i) ++ [3]).length := fun xs => by
    induction xs with
    | nil => simp
    | cons a tl ih =>
        simp only [List.length_cons, List.flatMap_cons, List.length_append]
        have h1 : 1 ≤ (encInt (z a)).length := by simp [encInt]
        omega
  simpa [encIntVec] using aux (List.finRange d)

private lemma encVec_ge_dim {k : ℕ} (w : Fin k → ℚ) : k ≤ (encVec w).length := by
  have aux : ∀ xs : List (Fin k),
      xs.length ≤ (xs.flatMap fun j => encRat (w j) ++ [3]).length := fun xs => by
    induction xs with
    | nil => simp
    | cons a tl ih =>
        simp only [List.length_cons, List.flatMap_cons, List.length_append]
        have h1 : 1 ≤ (encRat (w a)).length := by simp [encRat, encInt]
        omega
  simpa [encVec] using aux (List.finRange k)

end Encodings

/-! ### 3. 16-register machine subroutines -/

section Subroutines

open StackVM

abbrev Reg := Fin 16
abbrev rIO  : Reg := 0
abbrev rRev : Reg := 1
abbrev rD   : Reg := 2
abbrev rK   : Reg := 3
abbrev rCD  : Reg := 4
abbrev rCZ  : Reg := 5
abbrev rCK  : Reg := 6
abbrev rN   : Reg := 7
abbrev rW   : Reg := 8
abbrev rZ   : Reg := 9
abbrev rR   : Reg := 10
abbrev rTR  : Reg := 11
abbrev rTZ  : Reg := 12
abbrev rTN  : Reg := 13
abbrev rTmp : Reg := 14
abbrev rOut : Reg := 15

def isTokSym (o : Option Sym) : Bool :=
  match o with
  | some a => decide (a = 0 ∨ a = 1 ∨ a = 2)
  | none => false

lemma isTokSym_eq_false_nil : isTokSym ([] : Word).head? = false := rfl

lemma isTokSym_eq_false_three (tl : Word) : isTokSym ((3 : Sym) :: tl).head? = false := rfl

lemma isTokSym_eq_true_of_ne_three {a : Sym} (ha : a ≠ 3) (tl : Word) :
    isTokSym (a :: tl).head? = true := by
  simp only [List.head?_cons, isTokSym]
  exact (mem_tok_ne_three_iff a).mpr ha

/-- Read one `3`-free token `tok` followed by `3` from `src`, pushing `3 :: tok.reverse`
onto `dstRev` and `tok.reverse` onto `dstTok`, in `2 * tok.length + 2` steps. -/
def readTok (src dstRev dstTok : Reg) : Cmd Reg :=
  .seq
    (.loop src isTokSym (.pop1 src (fun j a => if j = dstRev then [a] else if j = dstTok then [a] else [])))
    (.pop1 src (fun j a => if j = dstRev then [a] else []))

lemma eval_readTok (src dstRev dstTok : Reg) (h1 : src ≠ dstRev) (h2 : src ≠ dstTok) (h12 : dstRev ≠ dstTok)
    (tok rest : Word) (htok : (3 : Sym) ∉ tok) (s : Mem Reg) (hs : s src = tok ++ 3 :: rest) :
    Eval (readTok src dstRev dstTok) s
      (update (update (update s src rest) dstRev (3 :: tok.reverse ++ s dstRev))
        dstTok (tok.reverse ++ s dstTok))
      (2 * tok.length + 2) := by
  have hloop : ∀ (w accR accT : Word) (s0 : Mem Reg)
      (_ : (3 : Sym) ∉ w)
      (_ : s0 src = w ++ 3 :: rest) (_ : s0 dstRev = accR) (_ : s0 dstTok = accT),
      Eval (.loop src isTokSym (.pop1 src (fun j a => if j = dstRev then [a] else if j = dstTok then [a] else [])))
        s0 (update (update (update s0 src (3 :: rest)) dstRev (w.reverse ++ accR)) dstTok (w.reverse ++ accT))
        (2 * w.length + 1) := by
    intro w
    induction w with
    | nil =>
        intro accR accT s0 _ hs0 hr0 ht0
        simp only [List.nil_append] at hs0
        simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.mul_zero, Nat.zero_add]
        have hmem : update (update (update s0 src (3 :: rest)) dstRev accR) dstTok accT = s0 := by
          funext j
          by_cases hj3 : j = dstTok
          · subst hj3; simp [ht0]
          · by_cases hj2 : j = dstRev
            · subst hj2; simp [hr0, hj3]
            · by_cases hj1 : j = src
              · subst hj1; simp [hs0, hj2, hj3]
              · simp [hj1, hj2, hj3]
        rw [hmem]
        refine Eval.stop ?_
        rw [hs0]; rfl
    | cons a tl ih =>
        intro accR accT s0 hmem hs0 hr0 ht0
        have ha3 : a ≠ 3 := fun h => hmem (h ▸ List.mem_cons_self)
        have htl3 : (3 : Sym) ∉ tl := fun h => hmem (List.mem_cons_of_mem _ h)
        let s1 := update (update (update s0 src (tl ++ 3 :: rest)) dstRev ([a] ++ s0 dstRev))
          dstTok ([a] ++ s0 dstTok)
        have hpop : Eval (.pop1 src (fun j x => if j = dstRev then [x] else if j = dstTok then [x] else []))
            s0 s1 1 :=
          eval_pop1_2 src dstRev dstTok h1 h2 h12 _ _ s0 a (tl ++ 3 :: rest) hs0
        have hih := ih (a :: accR) (a :: accT) s1 htl3
          (by simp [s1, Function.update_apply, h1, h2, h1.symm, h2.symm])
          (by simp [s1, Function.update_apply, h12, h12.symm, hr0])
          (by simp [s1, Function.update_apply, ht0])
        have heq : update (update (update s1 src (3 :: rest)) dstRev (tl.reverse ++ (a :: accR)))
            dstTok (tl.reverse ++ (a :: accT)) =
            update (update (update s0 src (3 :: rest)) dstRev ((a :: tl).reverse ++ accR))
              dstTok ((a :: tl).reverse ++ accT) := by
          funext j
          by_cases hj3 : j = dstTok
          · subst hj3; simp [s1, Function.update_apply]
          · by_cases hj2 : j = dstRev
            · subst hj2; simp [s1, Function.update_apply, hj3]
            · by_cases hj1 : j = src
              · subst hj1; simp [s1, Function.update_apply, hj2, hj3]
              · simp [s1, Function.update_apply, hj1, hj2, hj3]
        rw [heq] at hih
        have hcond : isTokSym (s0 src).head? = true := by
          rw [hs0]; exact isTokSym_eq_true_of_ne_three ha3 _
        refine (Eval.more hcond hpop hih).mono ?_; simp; omega
  have e1 := hloop tok (s dstRev) (s dstTok) s htok hs rfl rfl
  let s1 := update (update (update s src (3 :: rest)) dstRev (tok.reverse ++ s dstRev))
    dstTok (tok.reverse ++ s dstTok)
  have hs1 : s1 src = 3 :: rest := by simp [s1, Function.update_apply, h1, h2, h1.symm, h2.symm]
  have e2 := eval_pop1_1 src dstRev h1 (fun a => [a]) s1 3 rest hs1
  have hmem : update (update s1 src rest) dstRev ([3] ++ s1 dstRev) =
      update (update (update s src rest) dstRev (3 :: tok.reverse ++ s dstRev))
        dstTok (tok.reverse ++ s dstTok) := by
    funext j
    by_cases hj3 : j = dstTok
    · subst hj3; simp [s1, Function.update_apply, h2, h2.symm, h12, h12.symm]
    · by_cases hj2 : j = dstRev
      · subst hj2; simp [s1, Function.update_apply, h1, h1.symm, hj3, h12, h12.symm]
      · by_cases hj1 : j = src
        · subst hj1; simp [s1, Function.update_apply, hj2, hj3]
        · simp [s1, Function.update_apply, hj1, hj2, hj3]
  rw [hmem] at e2
  refine (e1.seq e2).mono ?_; omega

/-- Pop one reversed token `3 :: tok.reverse` from `src` (with `rest = [] ∨ ∃ r', rest = 3 :: r'`),
pushing `tok ++ [3]` onto `dst`, in `2 * tok.length + 2` steps. -/
def popOneToken (src dst : Reg) : Cmd Reg :=
  .seq
    (.pop1 src (fun j a => if j = dst then [a] else []))
    (.loop src isTokSym (.pop1 src (fun j a => if j = dst then [a] else [])))

lemma eval_popOneToken (src dst : Reg) (hne : src ≠ dst)
    (tok rest : Word) (htok : (3 : Sym) ∉ tok)
    (hrest : rest = [] ∨ ∃ r', rest = (3 : Sym) :: r')
    (s : Mem Reg) (hs : s src = 3 :: tok.reverse ++ rest) :
    Eval (popOneToken src dst) s
      (update (update s src rest) dst (tok ++ [3] ++ s dst))
      (2 * tok.length + 2) := by
  have hs' : s src = 3 :: (tok.reverse ++ rest) := hs
  have e1 := eval_pop1_1 src dst hne (fun a => [a]) s 3 (tok.reverse ++ rest) hs'
  let s1 := update (update s src (tok.reverse ++ rest)) dst ([3] ++ s dst)
  have hloop : ∀ (w acc : Word) (s0 : Mem Reg)
      (_ : (3 : Sym) ∉ w)
      (_ : s0 src = w ++ rest) (_ : s0 dst = acc),
      Eval (.loop src isTokSym (.pop1 src (fun j a => if j = dst then [a] else [])))
        s0 (update (update s0 src rest) dst (w.reverse ++ acc))
        (2 * w.length + 1) := by
    intro w
    induction w with
    | nil =>
        intro acc s0 _ hs0 hacc
        simp only [List.nil_append] at hs0
        simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.mul_zero, Nat.zero_add]
        have hmem : update (update s0 src rest) dst acc = s0 := by
          funext j
          by_cases hj2 : j = dst
          · subst hj2; simp [hacc]
          · by_cases hj1 : j = src
            · subst hj1; simp [hs0, hj2]
            · simp [hj1, hj2]
        rw [hmem]
        refine Eval.stop ?_
        rcases hrest with rfl | ⟨r', rfl⟩
        · rw [hs0]; rfl
        · rw [hs0]; rfl
    | cons a tl ih =>
        intro acc s0 hmem hs0 hacc
        have ha3 : a ≠ 3 := fun h => hmem (h ▸ List.mem_cons_self)
        have htl3 : (3 : Sym) ∉ tl := fun h => hmem (List.mem_cons_of_mem _ h)
        let s2 := update (update s0 src (tl ++ rest)) dst ([a] ++ s0 dst)
        have hpop : Eval (.pop1 src (fun j x => if j = dst then [x] else [])) s0 s2 1 :=
          eval_pop1_1 src dst hne (fun x => [x]) s0 a (tl ++ rest) hs0
        have hih := ih (a :: acc) s2 htl3
          (by simp [s2, Function.update_apply, hne, hne.symm])
          (by simp [s2, Function.update_apply, hacc])
        have heq : update (update s2 src rest) dst (tl.reverse ++ a :: acc) =
            update (update s0 src rest) dst ((a :: tl).reverse ++ acc) := by
          funext j
          by_cases hj2 : j = dst
          · subst hj2; simp [s2, Function.update_apply]
          · by_cases hj1 : j = src
            · subst hj1; simp [s2, Function.update_apply, hj2]
            · simp [s2, Function.update_apply, hj1, hj2]
        rw [heq] at hih
        have hcond : isTokSym (s0 src).head? = true := by
          rw [hs0]; exact isTokSym_eq_true_of_ne_three ha3 _
        refine (Eval.more hcond hpop hih).mono ?_; simp; omega
  have hrev3 : (3 : Sym) ∉ tok.reverse := fun h => htok (List.mem_reverse.mp h)
  have e2 := hloop tok.reverse (3 :: s dst) s1 hrev3
    (by simp [s1, Function.update_apply, hne, hne.symm])
    (by simp [s1, Function.update_apply])
  have hmem : update (update s1 src rest) dst (tok.reverse.reverse ++ 3 :: s dst) =
      update (update s src rest) dst (tok ++ [3] ++ s dst) := by
    funext j
    by_cases hj2 : j = dst
    · subst hj2; simp [s1, Function.update_apply]
    · by_cases hj1 : j = src
      · subst hj1; simp [s1, Function.update_apply, hj2]
      · simp [s1, Function.update_apply, hj1, hj2]
  rw [hmem] at e2
  refine (e1.seq e2).mono ?_; simp; omega

def isZeroSym (o : Option Sym) : Bool := decide (o = some 0)
def isSomeSym (o : Option Sym) : Bool := o.isSome

/-- Decrement positive binary counter `ctr` in-place using scratch register `tmp` (`s tmp = []`),
in at most `4 * (encNat (m + 1)).length + 5` steps. -/
def decr (ctr tmp : Reg) : Cmd Reg :=
  .seq (.loop ctr isZeroSym (.seq (.drop ctr) (.put tmp [1])))
    (.seq (.drop ctr)
      (.seq (.cond ctr isSomeSym (.put ctr [0]) (.put ctr []))
        (.drain tmp (fun j a => if j = ctr then [a] else []))))

lemma eval_decr (ctr tmp : Reg) (hne : ctr ≠ tmp) (m : ℕ) (s : Mem Reg)
    (hctr : s ctr = encNat (m + 1)) (htmp : s tmp = []) :
    Eval (decr ctr tmp) s (update s ctr (encNat m)) (4 * (encNat (m + 1)).length + 5) := by
  obtain ⟨e, q, hmq⟩ := exists_odd_mul_two_pow (m + 1) (by omega)
  have hbits : encNat (m + 1) = List.replicate e 0 ++ 1 :: encNat q := by
    rw [hmq, encNat_odd_mul_two_pow]
  have hlen_e : e ≤ (encNat (m + 1)).length := by
    rw [hbits, List.length_append, List.length_replicate, List.length_cons]
    omega
  have hloop : ∀ (k acc : ℕ) (s0 : Mem Reg)
      (_ : s0 ctr = List.replicate k 0 ++ 1 :: encNat q) (_ : s0 tmp = List.replicate acc 1),
      Eval (.loop ctr isZeroSym (.seq (.drop ctr) (.put tmp [1])))
        s0 (update (update s0 ctr (1 :: encNat q)) tmp (List.replicate (k + acc) 1))
        (3 * k + 1) := by
    intro k
    induction k with
    | zero =>
        intro acc s0 h0 ht0
        simp only [List.replicate_zero, List.nil_append, Nat.zero_add, Nat.mul_zero] at h0 ⊢
        have hmem : update (update s0 ctr (1 :: encNat q)) tmp (List.replicate acc 1) = s0 := by
          funext j
          by_cases hj2 : j = tmp
          · subst hj2; simp [ht0]
          · by_cases hj1 : j = ctr
            · subst hj1; simp [h0, hj2]
            · simp [hj1, hj2]
        rw [hmem]
        exact Eval.stop (by rw [h0]; rfl)
    | succ k ih =>
        intro acc s0 h0 ht0
        rw [List.replicate_succ, List.cons_append] at h0
        have e_drop : Eval (.drop ctr) s0 (update s0 ctr (List.replicate k 0 ++ 1 :: encNat q)) 1 := by
          simpa [h0] using Eval.drop s0 ctr
        have e_put : Eval (.put tmp [1]) (update s0 ctr (List.replicate k 0 ++ 1 :: encNat q))
            (update (update s0 ctr (List.replicate k 0 ++ 1 :: encNat q)) tmp (List.replicate (acc + 1) 1)) 1 := by
          have hs1 : update s0 ctr (List.replicate k 0 ++ 1 :: encNat q) tmp = List.replicate acc 1 := by
            simp [Function.update_apply, hne.symm, ht0]
          have hrep : ([1] ++ update s0 ctr (List.replicate k 0 ++ 1 :: encNat q) tmp) =
              List.replicate (acc + 1) 1 := by
            rw [hs1, List.replicate_succ]
            rfl
          rw [← hrep]
          exact Eval.put _ tmp [1]
        let s1 := update (update s0 ctr (List.replicate k 0 ++ 1 :: encNat q)) tmp (List.replicate (acc + 1) 1)
        have hih := ih (acc + 1) s1 (by simp [s1, Function.update_apply, hne, hne.symm])
          (by simp [s1, Function.update_apply])
        have hmem : update (update s1 ctr (1 :: encNat q)) tmp (List.replicate (k + (acc + 1)) 1) =
            update (update s0 ctr (1 :: encNat q)) tmp (List.replicate (k + 1 + acc) 1) := by
          funext j
          by_cases hj2 : j = tmp
          · subst hj2; simp [s1, Function.update_apply, show k + (acc + 1) = k + 1 + acc by omega]
          · by_cases hj1 : j = ctr
            · subst hj1; simp [s1, Function.update_apply, hj2]
            · simp [s1, Function.update_apply, hj1, hj2]
        rw [hmem] at hih
        have hcond : isZeroSym (s0 ctr).head? = true := by rw [h0]; rfl
        refine (Eval.more hcond (e_drop.seq e_put) hih).mono ?_; omega
  have e1 := hloop e 0 s (hctr.trans hbits) (by simp [htmp])
  let s1 := update (update s ctr (1 :: encNat q)) tmp (List.replicate e 1)
  have hs1_ctr : s1 ctr = 1 :: encNat q := by simp [s1, Function.update_apply, hne, hne.symm]
  have e2 : Eval (.drop ctr) s1 (update s1 ctr (encNat q)) 1 := by
    simpa [hs1_ctr] using Eval.drop s1 ctr
  let s2 := update s1 ctr (encNat q)
  have hs2_ctr : s2 ctr = encNat q := by simp [s2]
  have hs2_tmp : s2 tmp = List.replicate e 1 := by simp [s2, s1, Function.update_apply, hne, hne.symm]
  have e3 : Eval (.cond ctr isSomeSym (.put ctr [0]) (.put ctr []))
      s2 (update s2 ctr (if q = 0 then [] else 0 :: encNat q)) 2 := by
    by_cases hq0 : q = 0
    · subst hq0
      have hnone : isSomeSym (s2 ctr).head? = false := by simp [hs2_ctr, encNat_zero, isSomeSym]
      have ep : Eval (.put ctr []) s2 (update s2 ctr ([] ++ s2 ctr)) 1 := Eval.put s2 ctr []
      simpa [hs2_ctr, encNat_zero] using Eval.no hnone ep
    · have hne_nil := encNat_ne_nil q hq0
      cases hqcons : encNat q with
      | nil => exact absurd hqcons hne_nil
      | cons b bs =>
          have hsome : isSomeSym (s2 ctr).head? = true := by simp [hs2_ctr, hqcons, isSomeSym]
          have ep : Eval (.put ctr [0]) s2 (update s2 ctr ([0] ++ s2 ctr)) 1 := Eval.put s2 ctr [0]
          simpa [hs2_ctr, hq0, hqcons] using Eval.yes hsome ep
  let s3 := update s2 ctr (if q = 0 then [] else 0 :: encNat q)
  have hs3_tmp : s3 tmp = List.replicate e 1 := by simp [s3, hs2_tmp, Function.update_apply, hne, hne.symm]
  have hs3_ctr : s3 ctr = (if q = 0 then [] else 0 :: encNat q) := by simp [s3]
  have e4 := eval_drain1 tmp ctr hne.symm (fun a => [a]) s3
  have hlen_tmp : (s3 tmp).length = e := by simp [hs3_tmp]
  have hfinal_mem :
      update (update s3 tmp []) ctr ((s3 tmp).reverse.flatMap (fun a => [a]) ++ s3 ctr) =
        update s ctr (encNat m) := by
    funext j
    by_cases hj1 : j = ctr
    · subst hj1
      have hm_eq : encNat m =
          (List.replicate e 1) ++ (if q = 0 then [] else 0 :: encNat q) := by
        by_cases hq0 : q = 0
        · subst hq0
          have hm' : m = 2 ^ e - 1 := by omega
          rw [hm', encNat_pred_zero e]
          simp
        · have hm' : m = (2 * q + 1) * 2 ^ e - 1 := by omega
          rw [hm', encNat_pred_pos q e hq0]
          simp [hq0]
      simp [hs3_tmp, hs3_ctr, List.flatMap_id', hm_eq, Function.update_apply]
    · by_cases hj2 : j = tmp
      · subst hj2; simp [htmp, Function.update_apply, hj1]
      · simp [s3, s2, s1, Function.update_apply, hj1, hj2]
  rw [hfinal_mem, hlen_tmp] at e4
  unfold decr
  refine (e1.seq (e2.seq (e3.seq e4))).mono ?_; omega

/-- Pop `toks.length` tokens (`toks : List Word` of `3`-free tokens) stored in reverse on `src`,
decrementing counter `ctr = encNat toks.length` down to `[]`, pushing `toks.flatMap (· ++ [3])`
onto `dst`, using scratch `tmp` (`s tmp = []`), in time linear in tokens + counter bits. -/
def popManyTokens (ctr src dst tmp : Reg) : Cmd Reg :=
  .loop ctr isSomeSym (.seq (decr ctr tmp) (popOneToken src dst))

lemma eval_popManyTokens (ctr src dst tmp : Reg)
    (h1 : ctr ≠ src) (h2 : ctr ≠ dst) (h3 : ctr ≠ tmp)
    (h4 : src ≠ dst) (h5 : src ≠ tmp) (h6 : dst ≠ tmp)
    (toks : List Word) (htoks : ∀ tok ∈ toks, (3 : Sym) ∉ tok)
    (rest : Word) (hrest : rest = [] ∨ ∃ r', rest = (3 : Sym) :: r')
    (s : Mem Reg)
    (hctr : s ctr = encNat toks.length)
    (hsrc : s src = (toks.flatMap fun t => t ++ [3]).reverse ++ rest)
    (htmp : s tmp = []) :
    Eval (popManyTokens ctr src dst tmp) s
      (update (update (update s ctr []) src rest) dst ((toks.flatMap fun t => t ++ [3]) ++ s dst))
      (toks.length * (4 * (encNat toks.length).length + 8) +
        2 * (toks.flatMap fun t => t ++ [3]).length + 1) := by
  induction toks using List.reverseRecOn generalizing rest s with
  | nil =>
      simp only [List.length_nil, encNat_zero, List.flatMap_nil, List.reverse_nil, List.nil_append,
        Nat.zero_mul, Nat.mul_zero, Nat.zero_add] at hctr hsrc ⊢
      have hmem : update (update (update s ctr []) src rest) dst (s dst) = s := by
        funext j
        by_cases hj3 : j = dst
        · subst hj3; simp
        · by_cases hj2 : j = src
          · subst hj2; simp [hsrc, hj3]
          · by_cases hj1 : j = ctr
            · subst hj1; simp [hctr, hj2, hj3]
            · simp [hj1, hj2, hj3]
      rw [hmem]
      exact Eval.stop (by simp [hctr, isSomeSym])
  | append_singleton xs tok ih =>
      have htok3 : (3 : Sym) ∉ tok := htoks tok (by simp)
      have hxs3 : ∀ t ∈ xs, (3 : Sym) ∉ t := fun t ht => htoks t (by simp [ht])
      have hm_eq : (xs ++ [tok]).length = xs.length + 1 := by simp
      have e_dec := eval_decr ctr tmp h3 xs.length s (by simpa [hm_eq] using hctr) htmp
      let s1 := update s ctr (encNat xs.length)
      have hs1_src : s1 src = 3 :: tok.reverse ++ ((xs.flatMap fun t => t ++ [3]).reverse ++ rest) := by
        simpa [s1, h1.symm, List.flatMap_append, List.reverse_append, List.append_assoc] using hsrc
      have hrest_xs : (xs.flatMap fun t => t ++ [3]).reverse ++ rest = [] ∨
          ∃ r', (xs.flatMap fun t => t ++ [3]).reverse ++ rest = (3 : Sym) :: r' := by
        cases xs using List.reverseRecOn with
        | nil => simpa using hrest
        | append_singleton ys y =>
            right
            refine ⟨y.reverse ++ (ys.flatMap fun t => t ++ [3]).reverse ++ rest, ?_⟩
            simp [List.flatMap_append, List.reverse_append, List.append_assoc]
      have e_pop := eval_popOneToken src dst h4 tok ((xs.flatMap fun t => t ++ [3]).reverse ++ rest)
        htok3 hrest_xs s1 hs1_src
      let s2 := update (update s1 src ((xs.flatMap fun t => t ++ [3]).reverse ++ rest)) dst
        (tok ++ [3] ++ s1 dst)
      have e_rec := ih hxs3 rest hrest s2
        (by simp [s2, s1, Function.update_apply, h1, h1.symm, h2, h2.symm])
        (by simp [s2, Function.update_apply, h4, h4.symm])
        (by simp [s2, s1, Function.update_apply, h3, h3.symm, h5, h5.symm, h6, h6.symm, htmp])
      have hfinal_mem :
          update (update (update s2 ctr []) src rest) dst ((xs.flatMap fun t => t ++ [3]) ++ s2 dst) =
            update (update (update s ctr []) src rest) dst (((xs ++ [tok]).flatMap fun t => t ++ [3]) ++ s dst) := by
        funext j
        by_cases hj3 : j = dst
        · subst hj3; simp [s2, s1, Function.update_apply, h2.symm, List.flatMap_append, List.append_assoc]
        · by_cases hj2 : j = src
          · subst hj2; simp [s2, s1, Function.update_apply, hj3]
          · by_cases hj1 : j = ctr
            · subst hj1; simp [s2, s1, Function.update_apply, hj2, hj3]
            · simp [s2, s1, Function.update_apply, hj1, hj2, hj3]
      rw [hfinal_mem] at e_rec
      have hne_nil := encNat_ne_nil (xs.length + 1) (by omega)
      have hcond : isSomeSym (s ctr).head? = true := by
        rw [hctr, hm_eq]
        cases hc : encNat (xs.length + 1) with
        | nil => exact absurd hc hne_nil
        | cons b bs => simp [isSomeSym]
      have hmono_len : (encNat xs.length).length ≤ (encNat (xs.length + 1)).length :=
        encNat_length_mono (by omega)
      have hstep_le :
          1 + ((4 * (encNat (xs.length + 1)).length + 5) + (2 * tok.length + 2)) +
              (xs.length * (4 * (encNat xs.length).length + 8) +
                2 * (xs.flatMap fun t => t ++ [3]).length + 1) ≤
            (xs ++ [tok]).length * (4 * (encNat (xs ++ [tok]).length).length + 8) +
              2 * ((xs ++ [tok]).flatMap fun t => t ++ [3]).length + 1 := by
        rw [hm_eq, List.flatMap_append, List.length_append]
        have hlen_tok : (List.flatMap (fun t => t ++ [3]) [tok]).length = tok.length + 1 := by simp
        rw [hlen_tok]
        have hmul : xs.length * (4 * (encNat xs.length).length + 8) ≤
            xs.length * (4 * (encNat (xs.length + 1)).length + 8) :=
          Nat.mul_le_mul_left _ (by omega)
        have hadd : (xs.length + 1) * (4 * (encNat (xs.length + 1)).length + 8) =
            xs.length * (4 * (encNat (xs.length + 1)).length + 8) +
              (4 * (encNat (xs.length + 1)).length + 8) := Nat.succ_mul _ _
        omega
      exact (Eval.more hcond (e_dec.seq e_pop) e_rec).mono hstep_le

end Subroutines

/-! ### 4. The `lemma_6_prep_writer` TM2 machine and correctness proof -/

section PrepMachine

open StackVM

def phase1Cmd : Cmd Reg :=
  .seq (readTok rIO rRev rTmp)
    (.seq (.drain rTmp (fun j a => if j = rD then [a] else if j = rCD then [a] else if j = rCZ then [a] else []))
      (.seq (readTok rIO rRev rTmp)
        (.seq (.drain rTmp (fun j a => if j = rK then [a] else if j = rCK then [a] else []))
          (.drain rIO (fun j a => if j = rRev then [a] else [])))))

def phase2Cmd : Cmd Reg :=
  .seq (popOneToken rRev rN)
    (.seq (popManyTokens rCK rRev rW rTmp)
      (.seq (popManyTokens rCZ rRev rZ rTmp)
        (popManyTokens rCD rRev rR rTmp)))

def phase3aCmd : Cmd Reg :=
  .seq (.drain rD (fun j a => if j = rOut then [a, 0] else []))
    (.seq (.put rOut [3, 0])
      (.seq (.drain rK (fun j a => if j = rOut then [a, 0] else []))
        (.seq (.put rOut [3, 0])
          (.seq (.drain rR (fun j a => if j = rOut then [a, 0] else if j = rTR then [a] else []))
            (.seq (.drain rZ (fun j a => if j = rOut then [a, 0] else if j = rTZ then [a] else []))
              (.seq (.drain rN (fun j a => if j = rOut then [a, 0] else if j = rTN then [a] else []))
                (.put rOut [1])))))))

def phase3bCmd : Cmd Reg :=
  .seq (.drain rRev (fun j a => if j = rTmp then [a] else []))
    (.seq (.drain rTmp (fun j a => if j = rOut then [a] else []))
      (.seq (.drain rTR (fun j a => if j = rR then [a] else []))
        (.seq (.drain rR (fun j a => if j = rOut then [a] else []))
          (.seq (.drain rTZ (fun j a => if j = rZ then [a] else []))
            (.seq (.drain rZ (fun j a => if j = rOut then (if a = 3 then [3, 1, 2] else [a]) else []))
              (.seq (.drain rW (fun j a => if j = rOut then [a] else []))
                (.seq (.drop rTN)
                  (.seq (.drain rTN (fun j a => if j = rN then [a] else []))
                    (.seq (.put rOut [0])
                      (.seq (.drain rN (fun j a => if j = rOut then [a] else []))
                        (.put rOut [3, 1, 2])))))))))))

def prepCmd : Cmd Reg :=
  .seq phase1Cmd
    (.seq phase2Cmd
      (.seq phase3aCmd
        (.seq phase3bCmd (.drain rOut (fun j a => if j = rIO then [a] else [])))))

private def memState
    (io rev d k cd cz ck n w z r tr tz tn tmp out : Word) (j : Reg) : Word :=
  match j.1 with
  | 0 => io
  | 1 => rev
  | 2 => d
  | 3 => k
  | 4 => cd
  | 5 => cz
  | 6 => ck
  | 7 => n
  | 8 => w
  | 9 => z
  | 10 => r
  | 11 => tr
  | 12 => tz
  | 13 => tn
  | 14 => tmp
  | _ => out

private lemma memState_single_in (inp : Word) :
    singleWord rIO inp = memState inp [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] := by
  funext j; fin_cases j <;> rfl

private lemma memState_single_out (out : Word) :
    singleWord rIO out = memState out [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] := by
  funext j; fin_cases j <;> rfl

@[simp] private lemma memState_rIO (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rIO = x0 := rfl
@[simp] private lemma memState_rRev (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rRev = x1 := rfl
@[simp] private lemma memState_rD (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rD = x2 := rfl
@[simp] private lemma memState_rK (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rK = x3 := rfl
@[simp] private lemma memState_rCD (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rCD = x4 := rfl
@[simp] private lemma memState_rCZ (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rCZ = x5 := rfl
@[simp] private lemma memState_rCK (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rCK = x6 := rfl
@[simp] private lemma memState_rN (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rN = x7 := rfl
@[simp] private lemma memState_rW (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rW = x8 := rfl
@[simp] private lemma memState_rZ (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rZ = x9 := rfl
@[simp] private lemma memState_rR (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rR = x10 := rfl
@[simp] private lemma memState_rTR (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rTR = x11 := rfl
@[simp] private lemma memState_rTZ (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rTZ = x12 := rfl
@[simp] private lemma memState_rTN (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rTN = x13 := rfl
@[simp] private lemma memState_rTmp (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rTmp = x14 := rfl
@[simp] private lemma memState_rOut (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) :
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rOut = x15 := rfl

@[simp] private lemma upd_rIO (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rIO y =
    memState y x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rRev (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rRev y =
    memState x0 y x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rD (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rD y =
    memState x0 x1 y x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rK (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rK y =
    memState x0 x1 x2 y x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rCD (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rCD y =
    memState x0 x1 x2 x3 y x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rCZ (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rCZ y =
    memState x0 x1 x2 x3 x4 y x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rCK (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rCK y =
    memState x0 x1 x2 x3 x4 x5 y x7 x8 x9 x10 x11 x12 x13 x14 x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rN (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rN y =
    memState x0 x1 x2 x3 x4 x5 x6 y x8 x9 x10 x11 x12 x13 x14 x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rW (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rW y =
    memState x0 x1 x2 x3 x4 x5 x6 x7 y x9 x10 x11 x12 x13 x14 x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rZ (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rZ y =
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 y x10 x11 x12 x13 x14 x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rR (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rR y =
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y x11 x12 x13 x14 x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rTR (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rTR y =
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y x12 x13 x14 x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rTZ (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rTZ y =
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y x13 x14 x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rTN (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rTN y =
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 y x14 x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rTmp (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rTmp y =
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 y x15 := by funext j; fin_cases j <;> rfl
@[simp] private lemma upd_rOut (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y : Word) :
    update (memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) rOut y =
    memState x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 y := by funext j; fin_cases j <;> rfl

private lemma eval_phase1_abs (dW kW tail2 : Word) (hd : (3 : Sym) ∉ dW) (hk : (3 : Sym) ∉ kW) :
    let inp := dW ++ 3 :: (kW ++ 3 :: tail2)
    Eval phase1Cmd (memState inp [] [] [] [] [] [] [] [] [] [] [] [] [] [] [])
      (memState [] inp.reverse dW kW dW dW kW [] [] [] [] [] [] [] [] [])
      (inp.length + 2 * dW.length + 2 * kW.length + 5) := by
  intro inp
  let tail1 := kW ++ 3 :: tail2
  have hinp1 : inp = dW ++ 3 :: tail1 := rfl
  have e1 := eval_readTok rIO rRev rTmp (by decide) (by decide) (by decide)
    dW tail1 hd (memState inp [] [] [] [] [] [] [] [] [] [] [] [] [] [] []) rfl
  let s1 := memState tail1 (3 :: dW.reverse) [] [] [] [] [] [] [] [] [] [] [] [] dW.reverse []
  have hs1 : update (update (update (memState inp [] [] [] [] [] [] [] [] [] [] [] [] [] [] [])
      rIO tail1) rRev (3 :: dW.reverse)) rTmp dW.reverse = s1 := by
    simp [s1]
  simp only [memState_rRev, memState_rTmp, List.append_nil] at e1
  rw [hs1] at e1
  have e2 := eval_drain3 rTmp rD rCD rCZ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (fun a => [a]) (fun a => [a]) (fun a => [a]) s1
  let s2 := memState tail1 (3 :: dW.reverse) dW [] dW dW [] [] [] [] [] [] [] [] [] []
  have hs2 : update (update (update (update s1 rTmp []) rD ((s1 rTmp).reverse.flatMap (fun a => [a]) ++ s1 rD))
      rCD ((s1 rTmp).reverse.flatMap (fun a => [a]) ++ s1 rCD))
      rCZ ((s1 rTmp).reverse.flatMap (fun a => [a]) ++ s1 rCZ) = s2 := by
    simp [s1, s2, List.flatMap_id']
  have hlen_tmp1 : (s1 rTmp).length = dW.length := by simp [s1]
  rw [hs2, hlen_tmp1] at e2
  have e3 := eval_readTok rIO rRev rTmp (by decide) (by decide) (by decide)
    kW tail2 hk s2 rfl
  let s3 := memState tail2 (3 :: kW.reverse ++ 3 :: dW.reverse) dW [] dW dW [] [] [] [] [] [] [] [] kW.reverse []
  have hs3 : update (update (update s2 rIO tail2) rRev (3 :: kW.reverse ++ s2 rRev))
      rTmp (kW.reverse ++ s2 rTmp) = s3 := by
    simp [s2, s3]
  rw [hs3] at e3
  have e4 := eval_drain2 rTmp rK rCK (by decide) (by decide) (by decide)
    (fun a => [a]) (fun a => [a]) s3
  let s4 := memState tail2 (3 :: kW.reverse ++ 3 :: dW.reverse) dW kW dW dW kW [] [] [] [] [] [] [] [] []
  have hs4 : update (update (update s3 rTmp []) rK ((s3 rTmp).reverse.flatMap (fun a => [a]) ++ s3 rK))
      rCK ((s3 rTmp).reverse.flatMap (fun a => [a]) ++ s3 rCK) = s4 := by
    simp [s3, s4, List.flatMap_id']
  have hlen_tmp2 : (s3 rTmp).length = kW.length := by simp [s3]
  rw [hs4, hlen_tmp2] at e4
  have e5 := eval_drain1 rIO rRev (by decide) (fun a => [a]) s4
  let s5 := memState [] inp.reverse dW kW dW dW kW [] [] [] [] [] [] [] [] []
  have hrev_inp : tail2.reverse ++ 3 :: (kW.reverse ++ 3 :: dW.reverse) = inp.reverse := by
    simp [inp, List.reverse_append, List.append_assoc]
  have hs5 : update (update s4 rIO []) rRev ((s4 rIO).reverse.flatMap (fun a => [a]) ++ s4 rRev) = s5 := by
    simp [s4, s5, hrev_inp]
  have hlen_s4 : (s4 rIO).length = tail2.length := rfl
  have hlen_inp : tail2.length + dW.length + kW.length + 2 = inp.length := by
    simp only [inp, List.length_append, List.length_cons]
    omega
  rw [hs5, hlen_s4] at e5
  refine (e1.seq (e2.seq (e3.seq (e4.seq e5)))).mono ?_; omega

private lemma eval_phase2_abs (d k : ℕ) (nW prefixLoc : Word)
    (hn3 : (3 : Sym) ∉ nW) (hpfx3 : prefixLoc = [] ∨ ∃ p', prefixLoc.reverse = (3 : Sym) :: p')
    (toksW toksZ toksR : List Word)
    (htoksW : ∀ tok ∈ toksW, (3 : Sym) ∉ tok) (hlenW : toksW.length = k)
    (htoksZ : ∀ tok ∈ toksZ, (3 : Sym) ∉ tok) (hlenZ : toksZ.length = d)
    (htoksR : ∀ tok ∈ toksR, (3 : Sym) ∉ tok) (hlenR : toksR.length = d)
    (hnonemptyZ : ∃ p', (toksZ.flatMap fun t => t ++ [3]).reverse = (3 : Sym) :: p')
    (hnonemptyR : ∃ p', (toksR.flatMap fun t => t ++ [3]).reverse = (3 : Sym) :: p') :
    let dW := encNat d
    let kW := encNat k
    let wWord := toksW.flatMap fun t => t ++ [3]
    let zWord := toksZ.flatMap fun t => t ++ [3]
    let rWord := toksR.flatMap fun t => t ++ [3]
    let inp := prefixLoc ++ rWord ++ zWord ++ wWord ++ nW ++ [3]
    Eval phase2Cmd (memState [] inp.reverse dW kW dW dW kW [] [] [] [] [] [] [] [] [])
      (memState [] prefixLoc.reverse dW kW [] [] [] (nW ++ [3]) wWord zWord rWord [] [] [] [] [])
      ((k + 2 * d) * (4 * max kW.length dW.length + 8) +
        2 * (nW.length + wWord.length + zWord.length + rWord.length) + 6) := by
  intro dW kW wWord zWord rWord inp
  let s0 := memState [] inp.reverse dW kW dW dW kW [] [] [] [] [] [] [] [] []
  let restN := (prefixLoc ++ rWord ++ zWord ++ wWord).reverse
  have hrev1 : inp.reverse = 3 :: nW.reverse ++ restN := by
    simp [inp, restN, List.reverse_append, List.append_assoc]
  have hrestN : restN = [] ∨ ∃ r', restN = (3 : Sym) :: r' := by
    obtain ⟨pZ, hpZ⟩ := hnonemptyZ
    cases hw : wWord.reverse with
    | nil =>
        right; refine ⟨pZ ++ (prefixLoc ++ rWord).reverse, ?_⟩
        simp only [restN, List.reverse_append, hw, List.nil_append, List.append_assoc]
        dsimp only [zWord]
        rw [hpZ]
        simp [List.append_assoc]
    | cons b bs =>
        have hwend : wWord ≠ [] := by
          intro he; have := congrArg List.reverse he; rw [hw] at this; simp at this
        have htoks_ne : toksW ≠ [] := by
          intro hk; subst hk; simp [wWord] at hwend
        have hlast_three : ∃ p', wWord.reverse = (3 : Sym) :: p' := by
          induction toksW using List.reverseRecOn with
          | nil => exact absurd rfl htoks_ne
          | append_singleton xs tok _ =>
              refine ⟨tok.reverse ++ (xs.flatMap fun t => t ++ [3]).reverse, ?_⟩
              simp [wWord, List.flatMap_append, List.reverse_append, List.append_assoc]
        obtain ⟨pw, hpw⟩ := hlast_three
        right; refine ⟨pw ++ (prefixLoc ++ rWord ++ zWord).reverse, ?_⟩
        simp [restN, List.reverse_append, hpw, List.append_assoc]
  have e1 := eval_popOneToken rRev rN (by decide) nW restN hn3 hrestN s0 hrev1
  let s1 := memState [] restN dW kW dW dW kW (nW ++ [3]) [] [] [] [] [] [] [] []
  have hs1 : update (update s0 rRev restN) rN (nW ++ [3] ++ s0 rN) = s1 := by
    simp [s0, s1]
  rw [hs1] at e1
  let restW := (prefixLoc ++ rWord ++ zWord).reverse
  have hrevW : s1 rRev = wWord.reverse ++ restW := by
    simp [s1, restN, restW, List.reverse_append, List.append_assoc]
  have hrestW : restW = [] ∨ ∃ r', restW = (3 : Sym) :: r' := by
    obtain ⟨pZ, hpZ⟩ := hnonemptyZ
    right; refine ⟨pZ ++ (prefixLoc ++ rWord).reverse, ?_⟩
    simp only [restW, List.reverse_append, List.append_assoc]
    dsimp only [zWord]
    rw [hpZ]
    simp [List.append_assoc]
  have e2 := eval_popManyTokens rCK rRev rW rTmp (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) toksW htoksW restW hrestW s1
    (by simp [s1, kW, hlenW]) hrevW (by rfl)
  let s2 := memState [] restW dW kW dW dW [] (nW ++ [3]) wWord [] [] [] [] [] [] []
  have hs2 : update (update (update s1 rCK []) rRev restW) rW (wWord ++ s1 rW) = s2 := by
    simp [s1, s2]
  rw [hs2, hlenW] at e2
  let restZ := (prefixLoc ++ rWord).reverse
  have hrevZ : s2 rRev = zWord.reverse ++ restZ := by
    simp [s2, restW, restZ, List.reverse_append, List.append_assoc]
  have hrestZ : restZ = [] ∨ ∃ r', restZ = (3 : Sym) :: r' := by
    obtain ⟨pR, hpR⟩ := hnonemptyR
    right; refine ⟨pR ++ prefixLoc.reverse, ?_⟩
    simp only [restZ, List.reverse_append, List.append_assoc]
    dsimp only [rWord]
    rw [hpR]
    simp
  have e3 := eval_popManyTokens rCZ rRev rZ rTmp (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) toksZ htoksZ restZ hrestZ s2
    (by simp [s2, dW, hlenZ]) hrevZ (by rfl)
  let s3 := memState [] restZ dW kW dW [] [] (nW ++ [3]) wWord zWord [] [] [] [] [] []
  have hs3 : update (update (update s2 rCZ []) rRev restZ) rZ (zWord ++ s2 rZ) = s3 := by
    simp [s2, s3]
  rw [hs3, hlenZ] at e3
  have hrevR : s3 rRev = rWord.reverse ++ prefixLoc.reverse := by
    simp [s3, restZ, List.reverse_append]
  have hrestR : prefixLoc.reverse = [] ∨ ∃ r', prefixLoc.reverse = (3 : Sym) :: r' := by
    rcases hpfx3 with rfl | ⟨p', hp'⟩
    · left; rfl
    · right; exact ⟨p', hp'⟩
  have e4 := eval_popManyTokens rCD rRev rR rTmp (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) toksR htoksR prefixLoc.reverse hrestR s3
    (by simp [s3, dW, hlenR]) hrevR (by rfl)
  let s4 := memState [] prefixLoc.reverse dW kW [] [] [] (nW ++ [3]) wWord zWord rWord [] [] [] [] []
  have hs4 : update (update (update s3 rCD []) rRev prefixLoc.reverse) rR (rWord ++ s3 rR) = s4 := by
    simp [s3, s4]
  rw [hs4, hlenR] at e4
  have hbound : (2 * nW.length + 2) +
      ((k * (4 * kW.length + 8) + 2 * wWord.length + 1) +
        ((d * (4 * dW.length + 8) + 2 * zWord.length + 1) +
          (d * (4 * dW.length + 8) + 2 * rWord.length + 1))) ≤
      (k + 2 * d) * (4 * max kW.length dW.length + 8) +
        2 * (nW.length + wWord.length + zWord.length + rWord.length) + 6 := by
    have hk_le : k * (4 * kW.length + 8) ≤ k * (4 * max kW.length dW.length + 8) :=
      Nat.mul_le_mul_left _ (by omega)
    have hd_le : d * (4 * dW.length + 8) ≤ d * (4 * max kW.length dW.length + 8) :=
      Nat.mul_le_mul_left _ (by omega)
    have hmul : (k + 2 * d) * (4 * max kW.length dW.length + 8) =
        k * (4 * max kW.length dW.length + 8) +
        d * (4 * max kW.length dW.length + 8) +
        d * (4 * max kW.length dW.length + 8) := by ring
    omega
  exact (e1.seq (e2.seq (e3.seq e4))).mono hbound

private lemma eval_phase3a_abs (dW kW nW prefixLoc wWord zWord rWord : Word) :
    let ctx := dW ++ [3] ++ kW ++ [3] ++ rWord ++ zWord ++ nW ++ [3]
    let o8 := 1 :: ctx.reverse.flatMap (fun s => [s, 0])
    Eval phase3aCmd
      (memState [] prefixLoc.reverse dW kW [] [] [] (nW ++ [3]) wWord zWord rWord [] [] [] [] [])
      (memState [] prefixLoc.reverse [] [] [] [] [] [] wWord [] [] rWord.reverse zWord.reverse (3 :: nW.reverse) [] o8)
      (dW.length + kW.length + rWord.length + zWord.length + nW.length + 10) := by
  intro ctx o8
  let s0 := memState [] prefixLoc.reverse dW kW [] [] [] (nW ++ [3]) wWord zWord rWord [] [] [] [] []
  let o1 := dW.reverse.flatMap (fun a => [a, 0])
  have e1 := eval_drain1 rD rOut (by decide) (fun a => [a, 0]) s0
  let s1 := memState [] prefixLoc.reverse [] kW [] [] [] (nW ++ [3]) wWord zWord rWord [] [] [] [] o1
  have hs1 : update (update s0 rD []) rOut ((s0 rD).reverse.flatMap (fun a => [a, 0]) ++ s0 rOut) = s1 := by
    simp [s0, s1, o1]
  have hl1 : (s0 rD).length = dW.length := rfl
  rw [hs1, hl1] at e1
  let o2 := [3, 0] ++ o1
  have e2 := Eval.put s1 rOut [3, 0]
  let s2 := memState [] prefixLoc.reverse [] kW [] [] [] (nW ++ [3]) wWord zWord rWord [] [] [] [] o2
  have hs2 : update s1 rOut ([3, 0] ++ s1 rOut) = s2 := by
    simp [s1, s2, o2]
  rw [hs2] at e2
  let o3 := kW.reverse.flatMap (fun a => [a, 0]) ++ o2
  have e3 := eval_drain1 rK rOut (by decide) (fun a => [a, 0]) s2
  let s3 := memState [] prefixLoc.reverse [] [] [] [] [] (nW ++ [3]) wWord zWord rWord [] [] [] [] o3
  have hs3 : update (update s2 rK []) rOut ((s2 rK).reverse.flatMap (fun a => [a, 0]) ++ s2 rOut) = s3 := by
    simp [s2, s3, o3]
  have hl3 : (s2 rK).length = kW.length := rfl
  rw [hs3, hl3] at e3
  let o4 := [3, 0] ++ o3
  have e4 := Eval.put s3 rOut [3, 0]
  let s4 := memState [] prefixLoc.reverse [] [] [] [] [] (nW ++ [3]) wWord zWord rWord [] [] [] [] o4
  have hs4 : update s3 rOut ([3, 0] ++ s3 rOut) = s4 := by
    simp [s3, s4, o4]
  rw [hs4] at e4
  let o5 := rWord.reverse.flatMap (fun a => [a, 0]) ++ o4
  have e5 := eval_drain2 rR rOut rTR (by decide) (by decide) (by decide) (fun a => [a, 0]) (fun a => [a]) s4
  let s5 := memState [] prefixLoc.reverse [] [] [] [] [] (nW ++ [3]) wWord zWord [] rWord.reverse [] [] [] o5
  have hs5 : update (update (update s4 rR []) rOut ((s4 rR).reverse.flatMap (fun a => [a, 0]) ++ s4 rOut))
      rTR ((s4 rR).reverse.flatMap (fun a => [a]) ++ s4 rTR) = s5 := by
    simp [s4, s5, o5, List.flatMap_id']
  have hl5 : (s4 rR).length = rWord.length := rfl
  rw [hs5, hl5] at e5
  let o6 := zWord.reverse.flatMap (fun a => [a, 0]) ++ o5
  have e6 := eval_drain2 rZ rOut rTZ (by decide) (by decide) (by decide) (fun a => [a, 0]) (fun a => [a]) s5
  let s6 := memState [] prefixLoc.reverse [] [] [] [] [] (nW ++ [3]) wWord [] [] rWord.reverse zWord.reverse [] [] o6
  have hs6 : update (update (update s5 rZ []) rOut ((s5 rZ).reverse.flatMap (fun a => [a, 0]) ++ s5 rOut))
      rTZ ((s5 rZ).reverse.flatMap (fun a => [a]) ++ s5 rTZ) = s6 := by
    simp [s5, s6, o6, List.flatMap_id']
  have hl6 : (s5 rZ).length = zWord.length := rfl
  rw [hs6, hl6] at e6
  let o7 := (nW ++ [3]).reverse.flatMap (fun a => [a, 0]) ++ o6
  have e7 := eval_drain2 rN rOut rTN (by decide) (by decide) (by decide) (fun a => [a, 0]) (fun a => [a]) s6
  have ho7 : o7 = ctx.reverse.flatMap (fun s => [s, 0]) := by
    simp only [o7, o6, o5, o4, o3, o2, o1, ctx, List.reverse_append, List.flatMap_append,
      List.append_assoc]
    rfl
  let s7 := memState [] prefixLoc.reverse [] [] [] [] [] [] wWord [] [] rWord.reverse zWord.reverse (3 :: nW.reverse) [] o7
  have hs7 : update (update (update s6 rN []) rOut ((s6 rN).reverse.flatMap (fun a => [a, 0]) ++ s6 rOut))
      rTN ((s6 rN).reverse.flatMap (fun a => [a]) ++ s6 rTN) = s7 := by
    simp [s6, s7, o7, List.flatMap_id', List.reverse_append]
  have hl7 : (s6 rN).length = nW.length + 1 := by simp [s6]
  rw [hs7, hl7] at e7
  have e8 := Eval.put s7 rOut [1]
  have hs8 : update s7 rOut ([1] ++ s7 rOut) =
      memState [] prefixLoc.reverse [] [] [] [] [] [] wWord [] [] rWord.reverse zWord.reverse (3 :: nW.reverse) [] o8 := by
    simp [s7, o8, ho7]
  rw [hs8] at e8
  refine (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))).mono ?_
  omega

private lemma eval_phase3b_abs (nW prefixLoc wWord zWord rWord zRatW nRatW o8 : Word)
    (hzrat : zRatW = zWord.flatMap (fun s => if s = 3 then [2, 1, 3] else [s]))
    (hnrat : nRatW = 0 :: nW ++ [2, 1]) :
    let inp5 := prefixLoc ++ rWord ++ zRatW ++ wWord ++ nRatW ++ [3]
    Eval phase3bCmd
      (memState [] prefixLoc.reverse [] [] [] [] [] [] wWord [] [] rWord.reverse zWord.reverse (3 :: nW.reverse) [] o8)
      (memState [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] (inp5.reverse ++ o8))
      (2 * prefixLoc.length + 2 * rWord.length + 2 * zWord.length + wWord.length + 2 * nW.length + 15) := by
  intro inp5
  let s8 := memState [] prefixLoc.reverse [] [] [] [] [] [] wWord [] [] rWord.reverse zWord.reverse (3 :: nW.reverse) [] o8
  have e9 := eval_drain1 rRev rTmp (by decide) (fun a => [a]) s8
  let s9 := memState [] [] [] [] [] [] [] [] wWord [] [] rWord.reverse zWord.reverse (3 :: nW.reverse) prefixLoc o8
  have hs9 : update (update s8 rRev []) rTmp ((s8 rRev).reverse.flatMap (fun a => [a]) ++ s8 rTmp) = s9 := by
    simp [s8, s9, List.flatMap_id']
  have hl9 : (s8 rRev).length = prefixLoc.length := by simp [s8]
  rw [hs9, hl9] at e9
  let o10 := prefixLoc.reverse ++ o8
  have e10 := eval_drain1 rTmp rOut (by decide) (fun a => [a]) s9
  let s10 := memState [] [] [] [] [] [] [] [] wWord [] [] rWord.reverse zWord.reverse (3 :: nW.reverse) [] o10
  have hs10 : update (update s9 rTmp []) rOut ((s9 rTmp).reverse.flatMap (fun a => [a]) ++ s9 rOut) = s10 := by
    simp [s9, s10, o10, List.flatMap_id']
  have hl10 : (s9 rTmp).length = prefixLoc.length := rfl
  rw [hs10, hl10] at e10
  have e11 := eval_drain1 rTR rR (by decide) (fun a => [a]) s10
  let s11 := memState [] [] [] [] [] [] [] [] wWord [] rWord [] zWord.reverse (3 :: nW.reverse) [] o10
  have hs11 : update (update s10 rTR []) rR ((s10 rTR).reverse.flatMap (fun a => [a]) ++ s10 rR) = s11 := by
    simp [s10, s11, List.flatMap_id']
  have hl11 : (s10 rTR).length = rWord.length := by simp [s10]
  rw [hs11, hl11] at e11
  let o12 := rWord.reverse ++ o10
  have e12 := eval_drain1 rR rOut (by decide) (fun a => [a]) s11
  let s12 := memState [] [] [] [] [] [] [] [] wWord [] [] [] zWord.reverse (3 :: nW.reverse) [] o12
  have hs12 : update (update s11 rR []) rOut ((s11 rR).reverse.flatMap (fun a => [a]) ++ s11 rOut) = s12 := by
    simp [s11, s12, o12, List.flatMap_id']
  have hl12 : (s11 rR).length = rWord.length := rfl
  rw [hs12, hl12] at e12
  have e13 := eval_drain1 rTZ rZ (by decide) (fun a => [a]) s12
  let s13 := memState [] [] [] [] [] [] [] [] wWord zWord [] [] [] (3 :: nW.reverse) [] o12
  have hs13 : update (update s12 rTZ []) rZ ((s12 rTZ).reverse.flatMap (fun a => [a]) ++ s12 rZ) = s13 := by
    simp [s12, s13, List.flatMap_id']
  have hl13 : (s12 rTZ).length = zWord.length := by simp [s12]
  rw [hs13, hl13] at e13
  let o14 := zRatW.reverse ++ o12
  have e14 := eval_drain1 rZ rOut (by decide) (fun a => if a = 3 then [3, 1, 2] else [a]) s13
  let s14 := memState [] [] [] [] [] [] [] [] wWord [] [] [] [] (3 :: nW.reverse) [] o14
  have hs14 : update (update s13 rZ []) rOut
      ((s13 rZ).reverse.flatMap (fun a => if a = 3 then [3, 1, 2] else [a]) ++ s13 rOut) = s14 := by
    simp [s13, s14, o14, hzrat, reverse_flatMap_int2rat]
  have hl14 : (s13 rZ).length = zWord.length := rfl
  rw [hs14, hl14] at e14
  let o15 := wWord.reverse ++ o14
  have e15 := eval_drain1 rW rOut (by decide) (fun a => [a]) s14
  let s15 := memState [] [] [] [] [] [] [] [] [] [] [] [] [] (3 :: nW.reverse) [] o15
  have hs15 : update (update s14 rW []) rOut ((s14 rW).reverse.flatMap (fun a => [a]) ++ s14 rOut) = s15 := by
    simp [s14, s15, o15, List.flatMap_id']
  have hl15 : (s14 rW).length = wWord.length := rfl
  rw [hs15, hl15] at e15
  have e16 := Eval.drop s15 rTN
  let s16 := memState [] [] [] [] [] [] [] [] [] [] [] [] [] nW.reverse [] o15
  have hs16 : update s15 rTN (s15 rTN).tail = s16 := by
    simp [s15, s16]
  rw [hs16] at e16
  have e17 := eval_drain1 rTN rN (by decide) (fun a => [a]) s16
  let s17 := memState [] [] [] [] [] [] [] nW [] [] [] [] [] [] [] o15
  have hs17 : update (update s16 rTN []) rN ((s16 rTN).reverse.flatMap (fun a => [a]) ++ s16 rN) = s17 := by
    simp [s16, s17, List.flatMap_id']
  have hl17 : (s16 rTN).length = nW.length := by simp [s16]
  rw [hs17, hl17] at e17
  let o18 := 0 :: o15
  have e18 := Eval.put s17 rOut [0]
  let s18 := memState [] [] [] [] [] [] [] nW [] [] [] [] [] [] [] o18
  have hs18 : update s17 rOut ([0] ++ s17 rOut) = s18 := by
    simp [s17, s18, o18]
  rw [hs18] at e18
  let o19 := nW.reverse ++ o18
  have e19 := eval_drain1 rN rOut (by decide) (fun a => [a]) s18
  let s19 := memState [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] o19
  have hs19 : update (update s18 rN []) rOut ((s18 rN).reverse.flatMap (fun a => [a]) ++ s18 rOut) = s19 := by
    simp [s18, s19, o19, List.flatMap_id']
  have hl19 : (s18 rN).length = nW.length := rfl
  rw [hs19, hl19] at e19
  let o20 := [3, 1, 2] ++ o19
  have e20 := Eval.put s19 rOut [3, 1, 2]
  have ho20 : o20 = inp5.reverse ++ o8 := by
    simp only [o20, o19, o18, o15, o14, o12, o10, inp5, hnrat, List.reverse_append, List.reverse_cons,
      List.append_assoc]
    rfl
  have hs20 : update s19 rOut ([3, 1, 2] ++ s19 rOut) =
      memState [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] (inp5.reverse ++ o8) := by
    rw [← ho20]
    simp [s19, o20]
  rw [hs20] at e20
  refine (e9.seq (e10.seq (e11.seq (e12.seq (e13.seq (e14.seq (e15.seq (e16.seq (e17.seq
    (e18.seq (e19.seq e20))))))))))).mono ?_
  omega

private lemma step_bound (L : ℕ) :
    ((12 * L ^ 2 + 80 * L + 80 : ℕ) : ℝ) ≤ ((L : ℝ) + 2) ^ 7 := by
  have h4 : ((L : ℝ) + 2) ^ 7 =
      (L : ℝ) ^ 7 + 14 * (L : ℝ) ^ 6 + 84 * (L : ℝ) ^ 5 + 280 * (L : ℝ) ^ 4 +
        560 * (L : ℝ) ^ 3 + 672 * (L : ℝ) ^ 2 + 448 * (L : ℝ) + 128 := by ring
  have h5 : (0 : ℝ) ≤ (L : ℝ) ^ 7 + 14 * (L : ℝ) ^ 6 + 84 * (L : ℝ) ^ 5 + 280 * (L : ℝ) ^ 4 +
      560 * (L : ℝ) ^ 3 + 660 * (L : ℝ) ^ 2 + 368 * (L : ℝ) + 48 := by positivity
  push_cast
  linarith

end PrepMachine

end IntConeFPT.Lemma6PrepProof

open IntConeFPT.Lemma6PrepProof IntConeFPT.Lemma6PrepProof.StackVM

private lemma eval_prep_abs (d k : ℕ) (nW prefixLoc tail2 zRatW nRatW : Word)
    (hn3 : (3 : Sym) ∉ nW)
    (hpfx3 : prefixLoc = [] ∨ ∃ p', prefixLoc.reverse = (3 : Sym) :: p')
    (toksW toksZ toksR : List Word)
    (htoksW : ∀ tok ∈ toksW, (3 : Sym) ∉ tok) (hlenW : toksW.length = k)
    (htoksZ : ∀ tok ∈ toksZ, (3 : Sym) ∉ tok) (hlenZ : toksZ.length = d)
    (htoksR : ∀ tok ∈ toksR, (3 : Sym) ∉ tok) (hlenR : toksR.length = d)
    (hnonemptyZ : ∃ p', (toksZ.flatMap fun t => t ++ [3]).reverse = (3 : Sym) :: p')
    (hnonemptyR : ∃ p', (toksR.flatMap fun t => t ++ [3]).reverse = (3 : Sym) :: p')
    (hz : zRatW = (toksZ.flatMap fun t => t ++ [3]).flatMap fun s => if s = 3 then [2, 1, 3] else [s])
    (hn : nRatW = 0 :: nW ++ [2, 1])
    (hinp_loc : prefixLoc ++ (toksR.flatMap fun t => t ++ [3]) ++
      (toksZ.flatMap fun t => t ++ [3]) ++ (toksW.flatMap fun t => t ++ [3]) ++ nW ++ [3] =
      encNat d ++ 3 :: (encNat k ++ 3 :: tail2)) :
    let inp := encNat d ++ 3 :: (encNat k ++ 3 :: tail2)
    let rW := toksR.flatMap fun t => t ++ [3]
    let zW := toksZ.flatMap fun t => t ++ [3]
    let wW := toksW.flatMap fun t => t ++ [3]
    let ctx := encNat d ++ [3] ++ encNat k ++ [3] ++ rW ++ zW ++ nW ++ [3]
    let inp5 := prefixLoc ++ rW ++ zRatW ++ wW ++ nRatW ++ [3]
    let frame := fun (x y : List Sym) => x.flatMap (fun s => [(0 : Sym), s]) ++ 1 :: y
    Eval prepCmd (singleWord rIO inp) (singleWord rIO (frame ctx inp5))
      ((inp.length + 2 * (encNat d).length + 2 * (encNat k).length + 5) +
        (((k + 2 * d) * (4 * max (encNat k).length (encNat d).length + 8) +
          2 * (nW.length + wW.length + zW.length + rW.length) + 6) +
          (((encNat d).length + (encNat k).length + rW.length + zW.length + nW.length + 10) +
            ((2 * prefixLoc.length + 2 * rW.length + 2 * zW.length + wW.length + 2 * nW.length + 15) +
              ((frame ctx inp5).length + 1))))) := by
  intro inp rW zW wW ctx inp5 frame
  have ep1 := eval_phase1_abs (encNat d) (encNat k) tail2
    (three_not_mem_encNat _) (three_not_mem_encNat _)
  have ep2 := eval_phase2_abs d k nW prefixLoc hn3 hpfx3 toksW toksZ toksR
    htoksW hlenW htoksZ hlenZ htoksR hlenR hnonemptyZ hnonemptyR
  dsimp only [rW, zW, wW] at ep2
  rw [hinp_loc] at ep2
  have ep3a := eval_phase3a_abs (encNat d) (encNat k) nW prefixLoc wW zW rW
  have hctx_eq : encNat d ++ [3] ++ encNat k ++ [3] ++ rW ++ zW ++ nW ++ [3] = ctx := rfl
  rw [hctx_eq] at ep3a
  have ep3b := eval_phase3b_abs nW prefixLoc wW zW rW zRatW nRatW
    (1 :: ctx.reverse.flatMap (fun s => [s, 0])) hz hn
  have hrev_frame : (prefixLoc ++ rW ++ zRatW ++ wW ++ nRatW ++ [3]).reverse ++
      (1 :: ctx.reverse.flatMap fun s => [s, 0]) = (frame ctx inp5).reverse := by
    have hinp5_eq : prefixLoc ++ rW ++ zRatW ++ wW ++ nRatW ++ [3] = inp5 := rfl
    rw [hinp5_eq]
    conv_rhs => dsimp only [frame]; rw [List.reverse_append, List.reverse_cons, reverse_flatMap_frame, List.append_assoc]
    rfl
  dsimp only at ep3b
  rw [hrev_frame] at ep3b
  have ep4 := eval_drain1 rOut rIO (by decide) (fun a => [a])
    (memState [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] (frame ctx inp5).reverse)
  have hfm : ∀ l : Word, l.flatMap (fun a => [a]) = l := fun l => by
    induction l with
    | nil => rfl
    | cons a tl ih => simp [ih]
  have hfin : update (update
      (memState [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] (frame ctx inp5).reverse) rOut []) rIO
      (((memState [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] (frame ctx inp5).reverse rOut).reverse.flatMap
        (fun a => [a])) ++
        memState [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] (frame ctx inp5).reverse rIO) =
      singleWord rIO (frame ctx inp5) := by
    simp only [memState_single_out, memState_rOut, memState_rIO, upd_rOut, upd_rIO,
      hfm, List.reverse_reverse, List.append_nil]
  have hlen_ep4 :
      (memState [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] (frame ctx inp5).reverse rOut).length + 1 =
      (frame ctx inp5).length + 1 := by
    simp only [memState_rOut, List.length_reverse]
  rw [hfin, hlen_ep4] at ep4
  have eall := ep1.seq (ep2.seq (ep3a.seq (ep3b.seq ep4)))
  rw [← memState_single_in] at eall
  exact eall

theorem solution :
    let frame := fun (x y : List Sym) => x.flatMap (fun s => [(0 : Sym), s]) ++ 1 :: y
    ∃ C : ℕ, ∃ P : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (z : Fin I.d → ℤ) (w : Fin I.k → ℚ) (n : ℕ),
        1 ≤ n →
        let inp := encLocal I t r ++ encIntVec z ++ encVec w ++ encNat n ++ [3]
        let ctx := encNat I.d ++ [3] ++ encNat I.k ++ [3] ++ encResidue r ++ encIntVec z ++ encNat n ++ [3]
        let inp5 := encLocal I t r ++ encVec (fun i => (z i : ℚ)) ++ encVec w ++ encRat (n : ℚ) ++ [3]
        RunsWithin P inp (frame ctx inp5) (((inp.length : ℝ) + 2) ^ C) := by
  intro frame
  refine ⟨7, compiled rIO prepCmd, fun I hI t r z w n _ => ?_⟩
  intro inp ctx inp5
  let tail2 : Word := encNat I.τ ++ [3] ++
    (List.finRange I.τ).flatMap (fun t =>
      encNat (I.m t) ++ [3] ++ encMat (I.Aloc t) ++ encMat (I.Bloc t) ++ encVec (I.bloc t) ++ [3] ++
      encNat (I.deg t) ++ [3] ++ encVec (I.coeff t) ++ [3]) ++
    encNat I.mQ ++ [3] ++ encMat I.QY ++ encMat I.QV ++ encVec I.cQ ++ [3] ++
    encNat I.mA ++ [3] ++
    (List.finRange I.τ).flatMap (fun t => encMat (I.AY t) ++ encMat (I.AV t)) ++
    encMat I.AN ++ encVec I.cA ++ [3] ++ encNat t ++ [3] ++ encResidue r ++
    encIntVec z ++ encVec w ++ encNat n ++ [3]
  have hinp_split : inp = encNat I.d ++ 3 :: (encNat I.k ++ 3 :: tail2) := by
    simp only [inp, encLocal, encInstance, tail2, List.append_assoc, List.cons_append,
      List.nil_append]
  let prefixLoc : Word := encInstance I ++ encNat t ++ [3]
  let toksW := (List.finRange I.k).map fun j => encRat (w j)
  let toksZ := (List.finRange I.d).map fun i => encInt (z i)
  let toksR := (List.finRange I.d).map fun i => encNat (r i)
  have hflatW : (toksW.flatMap fun tok => tok ++ [3]) = encVec w := by
    simp [toksW, encVec, List.flatMap_map]
  have hflatZ : (toksZ.flatMap fun tok => tok ++ [3]) = encIntVec z := by
    simp [toksZ, encIntVec, List.flatMap_map]
  have hflatR : (toksR.flatMap fun tok => tok ++ [3]) = encResidue r := by
    simp [toksR, encResidue, List.flatMap_map]
  have htoksW_mem : ∀ tok ∈ toksW, (3 : Sym) ∉ tok := by
    rintro tok hm; simp only [toksW, List.mem_map] at hm; rcases hm with ⟨j, _, rfl⟩; exact three_not_mem_encRat _
  have htoksZ_mem : ∀ tok ∈ toksZ, (3 : Sym) ∉ tok := by
    rintro tok hm; simp only [toksZ, List.mem_map] at hm; rcases hm with ⟨i, _, rfl⟩; exact three_not_mem_encInt _
  have htoksR_mem : ∀ tok ∈ toksR, (3 : Sym) ∉ tok := by
    rintro tok hm; simp only [toksR, List.mem_map] at hm; rcases hm with ⟨i, _, rfl⟩; exact three_not_mem_encNat _
  have hneZ : ∃ p', (toksZ.flatMap fun tok => tok ++ [3]).reverse = (3 : Sym) :: p' := by
    obtain ⟨pre, hpre⟩ := encIntVec_ends_three hI.one_le_d z
    exact ⟨pre.reverse, by simp [hflatZ, hpre]⟩
  have hneR : ∃ p', (toksR.flatMap fun tok => tok ++ [3]).reverse = (3 : Sym) :: p' := by
    obtain ⟨pre, hpre⟩ := encResidue_ends_three hI.one_le_d r
    exact ⟨pre.reverse, by simp [hflatR, hpre]⟩
  have hinp_loc : prefixLoc ++ (toksR.flatMap fun tok => tok ++ [3]) ++
      (toksZ.flatMap fun tok => tok ++ [3]) ++ (toksW.flatMap fun tok => tok ++ [3]) ++
      encNat n ++ [3] = encNat I.d ++ 3 :: (encNat I.k ++ 3 :: tail2) := by
    rw [← hinp_split, hflatW, hflatZ, hflatR]
    simp [prefixLoc, encLocal, inp, List.append_assoc]
  have eall := eval_prep_abs I.d I.k (encNat n) prefixLoc tail2
    (encVec fun i => (z i : ℚ)) (encRat (n : ℚ)) (three_not_mem_encNat _)
    (Or.inr ⟨(encInstance I ++ encNat t).reverse, by simp [prefixLoc, List.reverse_append]⟩)
    toksW toksZ toksR htoksW_mem (by simp [toksW]) htoksZ_mem (by simp [toksZ])
    htoksR_mem (by simp [toksR]) hneZ hneR
    (by simpa [hflatZ] using encVec_intCast z) (encRat_natCast n) hinp_loc
  simp only [← hinp_split, hflatW, hflatZ, hflatR] at eall
  change Eval prepCmd (singleWord rIO inp) (singleWord rIO (frame ctx inp5)) _ at eall
  -- Bound total steps cleanly in terms of L := inp.length
  have hd_len : (encNat I.d).length ≤ inp.length := by
    rw [hinp_split]; simp only [List.length_append, List.length_cons]; omega
  have hk_len : (encNat I.k).length ≤ inp.length := by
    rw [hinp_split]; simp only [List.length_append, List.length_cons]; omega
  have hinp_loc' : prefixLoc ++ encResidue r ++ encIntVec z ++ encVec w ++ encNat n ++ [3] = inp := by
    simpa [← hinp_split, hflatW, hflatZ, hflatR] using hinp_loc
  have hloc_len : prefixLoc.length ≤ inp.length := by
    rw [← hinp_loc']; simp only [List.length_append, List.length_cons]; omega
  have hr_len : (encResidue r).length ≤ inp.length := by
    rw [← hinp_loc']; simp only [List.length_append, List.length_cons]; omega
  have hz_len : (encIntVec z).length ≤ inp.length := by
    rw [← hinp_loc']; simp only [List.length_append, List.length_cons]; omega
  have hw_len : (encVec w).length ≤ inp.length := by
    rw [← hinp_loc']; simp only [List.length_append, List.length_cons]; omega
  have hn_len : (encNat n).length ≤ inp.length := by
    rw [← hinp_loc']; simp only [List.length_append, List.length_cons]; omega
  have hd_le_L : I.d ≤ inp.length := (encIntVec_ge_dim z).trans hz_len
  have hk_le_L : I.k ≤ inp.length := (encVec_ge_dim w).trans hw_len
  have hctx_len : ctx.length ≤ 5 * inp.length + 3 := by
    simp only [ctx, List.length_append, List.length_cons, List.length_nil]
    omega
  have hinp5_len : inp5.length ≤ 6 * inp.length + 4 := by
    have hzrat_len : (encVec (fun i => (z i : ℚ))).length ≤ 3 * (encIntVec z).length := by
      have aux : ∀ xs : List (Fin I.d),
          (xs.flatMap fun i => encRat (z i : ℚ) ++ [3]).length ≤
            3 * (xs.flatMap fun i => encInt (z i) ++ [3]).length := fun xs => by
        induction xs with
        | nil => simp
        | cons a tl ih =>
            simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
            have h1 : (encRat (z a : ℚ)).length ≤ 3 * (encInt (z a)).length := by
              have hlen : 1 ≤ (encInt (z a)).length := by simp [encInt]
              simp only [encRat_intCast, List.length_append, List.length_cons, List.length_nil]
              omega
            omega
      exact aux (List.finRange I.d)
    have hnrat_len : (encRat (n : ℚ)).length ≤ (encNat n).length + 3 := by
      simp only [encRat_natCast, List.length_cons, List.length_append, List.length_nil]
      omega
    have henc_loc : (encLocal I t r).length ≤ inp.length := by
      simp only [inp, List.length_append, List.length_cons, List.length_nil]
      omega
    simp only [inp5, List.length_append, List.length_cons, List.length_nil]
    omega
  have hframe_len : (frame ctx inp5).length ≤ 16 * inp.length + 11 := by
    have hfl : (frame ctx inp5).length = 2 * ctx.length + 1 + inp5.length := by
      simp [frame, List.length_flatMap]; ring
    omega
  have hloop_bound : (I.k + 2 * I.d) * (4 * max (encNat I.k).length (encNat I.d).length + 8) ≤
      12 * inp.length ^ 2 + 24 * inp.length := by
    have h1 : I.k + 2 * I.d ≤ 3 * inp.length := by omega
    have h2 : 4 * max (encNat I.k).length (encNat I.d).length + 8 ≤ 4 * inp.length + 8 := by omega
    calc (I.k + 2 * I.d) * (4 * max (encNat I.k).length (encNat I.d).length + 8)
      _ ≤ (3 * inp.length) * (4 * inp.length + 8) := Nat.mul_le_mul h1 h2
      _ = 12 * inp.length ^ 2 + 24 * inp.length := by ring
  have htot_steps :
      ((inp.length + 2 * (encNat I.d).length + 2 * (encNat I.k).length + 5) +
        (((I.k + 2 * I.d) * (4 * max (encNat I.k).length (encNat I.d).length + 8) +
          2 * ((encNat n).length + (encVec w).length + (encIntVec z).length + (encResidue r).length) + 6) +
          (((encNat I.d).length + (encNat I.k).length + (encResidue r).length + (encIntVec z).length +
            (encNat n).length + 10) +
            ((2 * prefixLoc.length + 2 * (encResidue r).length + 2 * (encIntVec z).length +
              (encVec w).length + 2 * (encNat n).length + 15) +
              ((frame ctx inp5).length + 1))))) + 1 ≤
      12 * inp.length ^ 2 + 80 * inp.length + 80 := by
    omega
  have htot_real : (((((inp.length + 2 * (encNat I.d).length + 2 * (encNat I.k).length + 5) +
      (((I.k + 2 * I.d) * (4 * max (encNat I.k).length (encNat I.d).length + 8) +
        2 * ((encNat n).length + (encVec w).length + (encIntVec z).length + (encResidue r).length) + 6) +
        (((encNat I.d).length + (encNat I.k).length + (encResidue r).length + (encIntVec z).length +
          (encNat n).length + 10) +
          ((2 * prefixLoc.length + 2 * (encResidue r).length + 2 * (encIntVec z).length +
            (encVec w).length + 2 * (encNat n).length + 15) +
            ((frame ctx inp5).length + 1))))) + 1 : ℕ) : ℝ)) ≤
      ((inp.length : ℝ) + 2) ^ 7 := by
    have h1 : (((((inp.length + 2 * (encNat I.d).length + 2 * (encNat I.k).length + 5) +
        (((I.k + 2 * I.d) * (4 * max (encNat I.k).length (encNat I.d).length + 8) +
          2 * ((encNat n).length + (encVec w).length + (encIntVec z).length + (encResidue r).length) + 6) +
          (((encNat I.d).length + (encNat I.k).length + (encResidue r).length + (encIntVec z).length +
            (encNat n).length + 10) +
            ((2 * prefixLoc.length + 2 * (encResidue r).length + 2 * (encIntVec z).length +
              (encVec w).length + 2 * (encNat n).length + 15) +
              ((frame ctx inp5).length + 1))))) + 1 : ℕ) : ℝ)) ≤
        ((12 * inp.length ^ 2 + 80 * inp.length + 80 : ℕ) : ℝ) := by
      exact_mod_cast htot_steps
    exact h1.trans (step_bound inp.length)
  exact runsWithin_of_eval eall htot_real
