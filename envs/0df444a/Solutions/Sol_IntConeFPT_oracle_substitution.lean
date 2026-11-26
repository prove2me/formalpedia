-- Prove2me | solution 1 for IntConeFPT.oracle_substitution
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-26T14:04:46.960977+00:00
-- url     : https://prove2.me/submissions/74be09e8-3417-4cfa-9e0c-ea7789b15925

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_OracleMachine

/-! Oracle substitution: replace the oracle of an oracle machine by a machine.
The `tr`/`pack`/`Reach` technique is adapted from the Prove2Me submission for
`IntConeFPT.threshold_bisection_machine` (Apache-2.0). -/

open Turing OnlineCRS.Combine Function

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin
  Turing.FinTM2.Γk₀Fin

namespace IntConeFPT.OSub
noncomputable section

inductive Glue | g0 | g1 | g2 | g3
  deriving DecidableEq

instance : Fintype Glue :=
  Fintype.ofList [.g0, .g1, .g2, .g3] (by intro x; cases x <;> simp)

variable (OM : OracleMachine) (P : Machine)

abbrev KW := OM.M.tm.K ⊕ (P.tm.K ⊕ Unit)
abbrev GW : KW OM P → Type
  | .inl k => OM.M.tm.Γ k
  | .inr (.inl k) => P.tm.Γ k
  | .inr (.inr _) => Sym
abbrev LW := OM.M.tm.Λ ⊕ (P.tm.Λ ⊕ Glue)
abbrev SW := (OM.M.tm.σ × P.tm.σ) × Option Sym
abbrev Code := TM2.Stmt (GW OM P) (LW OM P) (SW OM P)
abbrev CW := TM2.Cfg (GW OM P) (LW OM P) (SW OM P)

def pack (sO : ∀ k, List (OM.M.tm.Γ k)) (sP : ∀ k, List (P.tm.Γ k)) (sT : List Sym) :
    ∀ k, List (GW OM P k)
  | .inl k => sO k
  | .inr (.inl k) => sP k
  | .inr (.inr _) => sT

variable {OM P}

lemma updO (sO : ∀ k, List (OM.M.tm.Γ k)) (sP : ∀ k, List (P.tm.Γ k)) (sT : List Sym)
    (k : OM.M.tm.K) (v : List (OM.M.tm.Γ k)) :
    update (pack OM P sO sP sT) (.inl k) v = pack OM P (update sO k v) sP sT := by
  funext i
  rcases i with i | i | i
  · by_cases h : i = k
    · subst i; simp [pack]
    · simp [pack, update, h]
  · simp [pack]
  · simp [pack]

lemma updP (sO : ∀ k, List (OM.M.tm.Γ k)) (sP : ∀ k, List (P.tm.Γ k)) (sT : List Sym)
    (k : P.tm.K) (v : List (P.tm.Γ k)) :
    update (pack OM P sO sP sT) (.inr (.inl k)) v = pack OM P sO (update sP k v) sT := by
  funext i
  rcases i with i | i | i
  · simp [pack]
  · by_cases h : i = k
    · subst i; simp [pack]
    · simp [pack, update, h]
  · simp [pack]

lemma updT (sO : ∀ k, List (OM.M.tm.Γ k)) (sP : ∀ k, List (P.tm.Γ k)) (sT : List Sym)
    (v : List Sym) :
    update (pack OM P sO sP sT) (.inr (.inr ())) v = pack OM P sO sP v := by
  funext i
  rcases i with i | i | i
  · simp [pack]
  · simp [pack]
  · simp [pack]

variable (OM P)

def trO : TM2.Stmt OM.M.tm.Γ OM.M.tm.Λ OM.M.tm.σ → Code OM P
  | .push k f q => .push (.inl k) (fun s => f s.1.1) (trO q)
  | .peek k f q => .peek (.inl k) (fun s o => ((f s.1.1 o, s.1.2), s.2)) (trO q)
  | .pop k f q => .pop (.inl k) (fun s o => ((f s.1.1 o, s.1.2), s.2)) (trO q)
  | .load f q => .load (fun s => ((f s.1.1, s.1.2), s.2)) (trO q)
  | .branch f q r => .branch (fun s => f s.1.1) (trO q) (trO r)
  | .goto f => .goto (fun s => .inl (f s.1.1))
  | .halt => .halt

def trP : TM2.Stmt P.tm.Γ P.tm.Λ P.tm.σ → Code OM P
  | .push k f q => .push (.inr (.inl k)) (fun s => f s.1.2) (trP q)
  | .peek k f q => .peek (.inr (.inl k)) (fun s o => ((s.1.1, f s.1.2 o), s.2)) (trP q)
  | .pop k f q => .pop (.inr (.inl k)) (fun s o => ((s.1.1, f s.1.2 o), s.2)) (trP q)
  | .load f q => .load (fun s => ((s.1.1, f s.1.2), s.2)) (trP q)
  | .branch f q r => .branch (fun s => f s.1.2) (trP q) (trP r)
  | .goto f => .goto (fun s => .inr (.inl (f s.1.2)))
  | .halt => .goto (fun _ => .inr (.inr .g2))

def mv (a b : KW OM P) (f : GW OM P a → Sym) (g : Sym → GW OM P b) (here next : LW OM P) :
    Code OM P :=
  .pop a (fun s o => (s.1, o.map f)) (.branch (fun s => s.2.isSome)
     (.push b (fun s => g (s.2.getD 0)) (.load (fun s => (s.1, none)) (.goto fun _ => here)))
     (.goto fun _ => next))

abbrev tmpK : KW OM P := .inr (.inr ())

def prog : LW OM P → Code OM P
  | .inl l => @ite _ (l = OM.ask) (OM.decEqΛ l OM.ask) (.goto (fun _ => .inr (.inr .g0)))
      (trO OM P (OM.M.tm.m l))
  | .inr (.inl l) => trP OM P (P.tm.m l)
  | .inr (.inr .g0) => mv OM P (.inl OM.qs) (tmpK OM P) OM.qsAlphabet (fun a => a)
      (.inr (.inr .g0)) (.inr (.inr .g1))
  | .inr (.inr .g1) => mv OM P (tmpK OM P) (.inr (.inl P.tm.k₀)) (fun a => a) P.inputAlphabet.symm
      (.inr (.inr .g1)) (.inr (.inl P.tm.main))
  | .inr (.inr .g2) => mv OM P (.inr (.inl P.tm.k₁)) (tmpK OM P) P.outputAlphabet (fun a => a)
      (.inr (.inr .g2)) (.inr (.inr .g3))
  | .inr (.inr .g3) => mv OM P (tmpK OM P) (.inl OM.qs) (fun a => a) OM.qsAlphabet.symm
      (.inr (.inr .g3)) (.inl OM.resume)

def W : Machine where
  tm := { K := KW OM P, k₀ := .inl OM.M.tm.k₀, k₁ := .inl OM.M.tm.k₁, Γ := GW OM P,
          Λ := LW OM P, main := .inl OM.M.tm.main, σ := SW OM P,
          initialState := ((OM.M.tm.initialState, P.tm.initialState), none),
          Γk₀Fin := OM.M.tm.Γk₀Fin, m := prog OM P }
  inputAlphabet := OM.M.inputAlphabet
  outputAlphabet := OM.M.outputAlphabet

def Reach {α : Type} (f : α → Option α) (n : ℕ) (u v : α) :=
  ∃ k ≤ n, (flip Option.bind f)^[k] (some u) = some v
namespace Reach
variable {α : Type} {f : α → Option α} {a b c : α} {h k : ℕ}
theorem refl : Reach f 0 a a := ⟨0,le_rfl,rfl⟩
theorem one (he : f a = some b) : Reach f 1 a b := ⟨1,le_rfl,he⟩
theorem trans (x : Reach f h a b) (y : Reach f k b c) : Reach f (h+k) a c := by
  obtain ⟨h',hl,he⟩ := x; obtain ⟨k',kl,ke⟩ := y
  exact ⟨k'+h',by omega,by rw [Function.iterate_add_apply,he,ke]⟩
theorem mono (x : Reach f h a b) (hl : h ≤ k) : Reach f k a b := by
  obtain ⟨t,ht,he⟩ := x; exact ⟨t,ht.trans hl,he⟩
end Reach

abbrev stepW := TM2.step (prog OM P)

def liftO (c : OCfg OM) (w : P.tm.σ) (o : Option Sym) (sP : ∀ k, List (P.tm.Γ k))
    (sT : List Sym) : CW OM P :=
  ⟨c.l.map Sum.inl, ((c.var, w), o), pack OM P c.stk sP sT⟩

def locP : Option P.tm.Λ → Option (LW OM P)
  | none => some (.inr (.inr .g2))
  | some l => some (.inr (.inl l))

def liftP (u : OM.M.tm.σ) (sO : ∀ k, List (OM.M.tm.Γ k)) (c : P.tm.Cfg) (sT : List Sym) :
    CW OM P :=
  ⟨locP OM P c.l, ((u, c.var), none), pack OM P sO c.stk sT⟩

variable {OM P}

lemma trO_step (q : TM2.Stmt OM.M.tm.Γ OM.M.tm.Λ OM.M.tm.σ) (v : OM.M.tm.σ) (w : P.tm.σ)
    (o : Option Sym) (sO : ∀ k, List (OM.M.tm.Γ k)) (sP : ∀ k, List (P.tm.Γ k)) (sT : List Sym) :
    TM2.stepAux (trO OM P q) ((v, w), o) (pack OM P sO sP sT) =
      liftO OM P (TM2.stepAux q v sO) w o sP sT := by
  induction q generalizing v sO with
  | push k f q ih => simp only [trO, TM2.stepAux, updO]; exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => simp only [trO, TM2.stepAux, updO]; exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r ih jh => cases h : f v <;> simp [trO, TM2.stepAux, h, ih, jh]
  | goto f => rfl
  | halt => rfl

lemma trP_step (q : TM2.Stmt P.tm.Γ P.tm.Λ P.tm.σ) (u : OM.M.tm.σ) (v : P.tm.σ)
    (sO : ∀ k, List (OM.M.tm.Γ k)) (sP : ∀ k, List (P.tm.Γ k)) (sT : List Sym) :
    TM2.stepAux (trP OM P q) ((u, v), none) (pack OM P sO sP sT) =
      liftP OM P u sO (TM2.stepAux q v sP) sT := by
  induction q generalizing v sP with
  | push k f q ih => simp only [trP, TM2.stepAux, updP]; exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => simp only [trP, TM2.stepAux, updP]; exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r ih jh => cases h : f v <;> simp [trP, TM2.stepAux, h, ih, jh]
  | goto f => rfl
  | halt => rfl

lemma mv_run {a b : KW OM P} (hab : a ≠ b) (f : GW OM P a → Sym) (g : Sym → GW OM P b)
    (here next : LW OM P) (hm : prog OM P here = mv OM P a b f g here next)
    (u : OM.M.tm.σ × P.tm.σ) :
    ∀ (xs : List (GW OM P a)) (S : ∀ k, List (GW OM P k)), S a = xs →
      Reach (stepW OM P) (xs.length + 1) ⟨some here, (u, none), S⟩
        ⟨some next, (u, none), update (update S a []) b ((xs.map (g ∘ f)).reverse ++ S b)⟩ := by
  intro xs
  induction xs with
  | nil =>
    intro S hS
    apply Reach.one
    simp [stepW, TM2.step, hm, mv, TM2.stepAux, hS, update_of_ne hab.symm]
  | cons x xs ih =>
    intro S hS
    let S' := update (update S a xs) b (g (f x) :: S b)
    have h1 : stepW OM P ⟨some here, (u, none), S⟩ = some ⟨some here, (u, none), S'⟩ := by
      simp [stepW, TM2.step, hm, mv, TM2.stepAux, hS, S', update_of_ne hab.symm]
    have h2 := ih S' (by simp [S', update_of_ne hab])
    have e : update (update S' a []) b ((xs.map (g ∘ f)).reverse ++ S' b) =
        update (update S a []) b (((x :: xs).map (g ∘ f)).reverse ++ S b) := by
      funext k
      by_cases hb : k = b
      · subst hb; simp [S']
      · by_cases ha : k = a
        · subst ha; simp [S', update_of_ne hab]
        · simp [S', update_of_ne ha, update_of_ne hb]
    rw [e] at h2
    exact ((Reach.one h1).trans h2).mono (by simp; omega)

lemma init_stk (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    (initList tm s).stk = update (fun _ => []) tm.k₀ s := by
  funext k; by_cases h : k = tm.k₀
  · subst k; simp [initList]
  · simp [h, initList, update]

lemma halt_stk (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    (haltList tm s).stk = update (fun _ => []) tm.k₁ s := by
  funext k; by_cases h : k = tm.k₁
  · subst k; simp [haltList]
  · simp [h, haltList, update]

lemma upd_nil {K : Type} [DecidableEq K] {Γ : K → Type} (k : K) :
    update (fun j => ([] : List (Γ j))) k ([] : List (Γ k)) = fun _ => [] := by
  funext j; by_cases h : j = k
  · subst h; simp
  · simp [update_of_ne h]

lemma simP (u : OM.M.tm.σ) (sO : ∀ k, List (OM.M.tm.Γ k)) (sT : List Sym)
    (n : ℕ) (c d : P.tm.Cfg) (hr : (flip Option.bind P.tm.step)^[n] (some c) = some d) :
    Reach (stepW OM P) n (liftP OM P u sO c sT) (liftP OM P u sO d sT) := by
  induction n generalizing c with
  | zero => have he : c = d := Option.some.inj hr; subst c; exact Reach.refl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hr
    rcases c with ⟨l, v, os⟩
    cases l with
    | none =>
      have hh : ∀ n, (flip Option.bind P.tm.step)^[n] none = none := by
        intro n; induction n with
        | zero => rfl
        | succ n ih => rw [Function.iterate_succ_apply]; exact ih
      change (flip Option.bind P.tm.step)^[n] none = some d at hr
      rw [hh] at hr; contradiction
    | some l =>
      let t := TM2.stepAux (P.tm.m l) v os
      have hstep : stepW OM P (liftP OM P u sO ⟨some l, v, os⟩ sT) = some (liftP OM P u sO t sT) :=
        congrArg some (trP_step _ u v sO os sT)
      exact ((Reach.one hstep).trans (ih t hr)).mono (by omega)

lemma call_run (O : List Sym → List Sym) (c : OCfg OM) (hc : c.l = some OM.ask) (n : ℕ)
    (hP : TM2OutputsInTime P.tm (((c.stk OM.qs).map OM.qsAlphabet).map P.inputAlphabet.invFun)
      (some ((O ((c.stk OM.qs).map OM.qsAlphabet)).map P.outputAlphabet.invFun)) n) :
    Reach (stepW OM P)
      (2 * (c.stk OM.qs).length + 2 * (O ((c.stk OM.qs).map OM.qsAlphabet)).length + n + 5)
      (liftO OM P c P.tm.initialState none (fun _ => []) [])
      (liftO OM P ⟨some OM.resume, c.var, update c.stk OM.qs
        ((O ((c.stk OM.qs).map OM.qsAlphabet)).map OM.qsAlphabet.symm)⟩
        P.tm.initialState none (fun _ => []) []) := by
  obtain ⟨l, v, sO⟩ := c
  simp only at hc; subst hc
  simp only at hP ⊢
  set q := (sO OM.qs).map OM.qsAlphabet with hq
  set r := O q with hr
  have h0 : Reach (stepW OM P) 1 (liftO OM P ⟨some OM.ask, v, sO⟩ P.tm.initialState none
      (fun _ => []) [])
      ⟨some (.inr (.inr .g0)), ((v, P.tm.initialState), none), pack OM P sO (fun _ => []) []⟩ := by
    apply Reach.one
    simp [liftO, stepW, TM2.step, prog, TM2.stepAux]
  have h1 := mv_run (OM := OM) (P := P) (a := .inl OM.qs) (b := tmpK OM P) (by simp)
    OM.qsAlphabet (fun a => a) (.inr (.inr .g0)) (.inr (.inr .g1)) rfl (v, P.tm.initialState)
    (sO OM.qs) (pack OM P sO (fun _ => []) []) rfl
  simp only [updO, updT, pack] at h1
  have h2 := mv_run (OM := OM) (P := P) (a := tmpK OM P) (b := .inr (.inl P.tm.k₀)) (by simp)
    (fun a => a) P.inputAlphabet.symm (.inr (.inr .g1)) (.inr (.inl P.tm.main)) rfl
    (v, P.tm.initialState) _ (pack OM P (update sO OM.qs []) (fun _ => [])
      ((List.map ((fun a => a) ∘ OM.qsAlphabet) (sO OM.qs)).reverse ++ [])) rfl
  simp only [updP, updT, pack] at h2
  have e2 : (⟨some (.inr (.inl P.tm.main)), ((v, P.tm.initialState), none),
      pack OM P (update sO OM.qs [])
          (update (fun x => []) P.tm.k₀
            ((List.map (⇑P.inputAlphabet.symm ∘ fun a => a)
                  ((List.map ((fun a => a) ∘ ⇑OM.qsAlphabet) (sO OM.qs)).reverse ++ [])).reverse ++
              []))
          []⟩ : CW OM P) =
      liftP OM P v (update sO OM.qs []) (initList P.tm (q.map P.inputAlphabet.invFun)) [] := by
    simp [liftP, locP, init_stk, hq, List.map_reverse, Function.comp_def] <;> exact ⟨rfl, rfl⟩
  rw [e2] at h2
  have h3 := simP (OM := OM) (P := P) v (update sO OM.qs []) [] _ _ _ hP.evals_in_steps
  have h4 := mv_run (OM := OM) (P := P) (a := .inr (.inl P.tm.k₁)) (b := tmpK OM P) (by simp)
    P.outputAlphabet (fun a => a) (.inr (.inr .g2)) (.inr (.inr .g3)) rfl
    (v, P.tm.initialState) _ (pack OM P (update sO OM.qs [])
      (update (fun _ => []) P.tm.k₁ (r.map P.outputAlphabet.invFun)) []) rfl
  simp only [updP, updT, pack, update_idem, update_self] at h4
  rw [show update (fun _ => []) P.tm.k₁ [] = (fun _ => [] : ∀ k, List (P.tm.Γ k)) from
    upd_nil _] at h4
  have e3 : liftP OM P v (update sO OM.qs []) (haltList P.tm (r.map P.outputAlphabet.invFun)) [] =
      ⟨some (.inr (.inr .g2)), ((v, P.tm.initialState), none), pack OM P (update sO OM.qs [])
      (update (fun _ => []) P.tm.k₁ (r.map P.outputAlphabet.invFun)) []⟩ := by
    simp [liftP, locP, halt_stk] <;> exact ⟨rfl, rfl⟩
  simp only [Option.map_some] at h3
  rw [e3] at h3
  have h5 := mv_run (OM := OM) (P := P) (a := tmpK OM P) (b := .inl OM.qs) (by simp)
    (fun a => a) OM.qsAlphabet.symm (.inr (.inr .g3)) (.inl OM.resume) rfl
    (v, P.tm.initialState) _ (pack OM P (update sO OM.qs []) (fun _ => [])
      ((List.map ((fun a => a) ∘ ⇑P.outputAlphabet) (List.map P.outputAlphabet.invFun r)).reverse
        ++ [])) rfl
  simp only [updO, updT, pack, update_idem] at h5
  have e5 : (⟨some (.inl OM.resume), ((v, P.tm.initialState), none), pack OM P (update sO OM.qs
      ((List.map (⇑OM.qsAlphabet.symm ∘ fun a => a) ((List.map ((fun a => a) ∘ ⇑P.outputAlphabet)
        (List.map P.outputAlphabet.invFun r)).reverse ++ [])).reverse ++ update sO OM.qs [] OM.qs))
      (fun _ => []) []⟩ : CW OM P) =
      liftO OM P ⟨some OM.resume, v, update sO OM.qs (List.map (⇑OM.qsAlphabet.symm) r)⟩
        P.tm.initialState none (fun x => []) [] := by
    simp [liftO, List.map_reverse, Function.comp_def]
  rw [e5] at h5
  refine ((((h0.trans h1).trans h2).trans (h3.mono hP.steps_le_m)).trans (h4.trans h5)).mono ?_
  simp [hq]
  omega

lemma plain_step (c c' : OCfg OM) (hc : c.l ≠ some OM.ask) (h : OM.M.tm.step c = some c') :
    stepW OM P (liftO OM P c P.tm.initialState none (fun _ => []) []) =
      some (liftO OM P c' P.tm.initialState none (fun _ => []) []) := by
  obtain ⟨l, v, sO⟩ := c
  cases l with
  | none => exact absurd h (by simp [FinTM2.step, TM2.step])
  | some l =>
    have hl : l ≠ OM.ask := fun e => hc (by simp [e])
    have h' : TM2.stepAux (OM.M.tm.m l) v sO = c' := Option.some.inj h
    change some (TM2.stepAux (prog OM P (.inl l)) _ _) = _
    simp only [prog, if_neg hl]
    rw [trO_step, h']

lemma pack_nil : pack OM P (fun _ => []) (fun _ => []) [] = fun _ => [] := by
  funext k; rcases k with k | k | k <;> rfl

lemma main_run (O : List Sym → List Sym) (x : List Sym) (steps C : ℕ) (hC : 1 ≤ C)
    (hG : ∀ j < steps, ∀ c : OCfg OM, oRun OM O x j = some c → c.l = some OM.ask →
      ∃ n, 2 * (c.stk OM.qs).length + 2 * (O ((c.stk OM.qs).map OM.qsAlphabet)).length + n + 5
        ≤ C ∧ Nonempty (TM2OutputsInTime P.tm
          (((c.stk OM.qs).map OM.qsAlphabet).map P.inputAlphabet.invFun)
          (some ((O ((c.stk OM.qs).map OM.qsAlphabet)).map P.outputAlphabet.invFun)) n)) :
    ∀ j ≤ steps, ∀ c, oRun OM O x j = some c →
      Reach (stepW OM P) (j * C)
        (liftO OM P (initList OM.M.tm (x.map OM.M.inputAlphabet.symm)) P.tm.initialState none
          (fun _ => []) [])
        (liftO OM P c P.tm.initialState none (fun _ => []) []) := by
  intro j
  induction j with
  | zero =>
    intro _ c hc
    have : c = initList OM.M.tm (x.map OM.M.inputAlphabet.symm) := (Option.some.inj hc).symm
    subst this; simpa using (Reach.refl (f := stepW OM P))
  | succ j ih =>
    intro hj c hc
    have hs : oRun OM O x (j + 1) = (flip bind (oStep OM O)) (oRun OM O x j) := by
      simp only [oRun]; rw [Function.iterate_succ_apply']
    cases hd : oRun OM O x j with
    | none => rw [hs, hd] at hc; exact absurd hc (by simp [flip])
    | some d =>
      have hr := ih (by omega) d hd
      rw [hs, hd] at hc
      change oStep OM O d = some c at hc
      by_cases hl : d.l = some OM.ask
      · obtain ⟨n, hn, ⟨hP⟩⟩ := hG j (by omega) d hd hl
        have hcc : c = ⟨some OM.resume, d.var, update d.stk OM.qs
            ((O ((d.stk OM.qs).map OM.qsAlphabet)).map OM.qsAlphabet.symm)⟩ := by
          simp only [oStep, hl] at hc; exact (Option.some.inj hc).symm
        subst hcc
        exact (hr.trans ((call_run O d hl n hP).mono hn)).mono (by rw [Nat.succ_mul])
      · simp only [oStep, hl] at hc
        exact (hr.trans (Reach.one (plain_step d c hl hc))).mono (by rw [Nat.succ_mul]; omega)

end
end IntConeFPT.OSub

open IntConeFPT IntConeFPT.OSub in
theorem solution (OM : OracleMachine) (P : Machine) :
    ∃ W : Machine, ∀ (O : List Sym → List Sym) (G : List Sym → Prop) (x y : List Sym)
      (t Q R : ℕ) (Tq : ℝ), 0 ≤ Tq →
      ORunsWithin OM O G x y t →
      (∀ q, G q → q.length ≤ Q ∧ (O q).length ≤ R ∧ RunsWithin P q (O q) Tq) →
      RunsWithin W x y (4 * ((t : ℝ) + 1) * (Tq + Q + R + 4)) := by
  refine ⟨W OM P, ?_⟩
  intro O G x y t Q R Tq hTq ⟨steps, hst, hrun, hG⟩ hP
  set N := ⌊Tq⌋₊ with hN
  have key := main_run (OM := OM) (P := P) O x steps (2 * Q + 2 * R + N + 5) (by omega)
    (fun j hj c hc hl => by
      obtain ⟨hQ, hR, m, hm, hm'⟩ := hP _ (hG j hj c hc hl)
      have hmN : m ≤ N := Nat.le_floor hm
      refine ⟨m, ?_, hm'⟩
      simp only [List.length_map] at hQ
      omega) steps le_rfl _ hrun
  have hi : initList (W OM P).tm (x.map (W OM P).inputAlphabet.invFun) =
      liftO OM P (initList OM.M.tm (x.map OM.M.inputAlphabet.symm)) P.tm.initialState none
        (fun _ => []) [] := by
    apply TM2.Cfg.mk.injEq .. |>.mpr
    refine ⟨rfl, rfl, (init_stk (W OM P).tm _).trans ?_⟩
    rw [init_stk, ← updO, pack_nil]
    rfl
  have hf : liftO OM P (haltList OM.M.tm (y.map OM.M.outputAlphabet.symm)) P.tm.initialState none
        (fun _ => []) [] = haltList (W OM P).tm (y.map (W OM P).outputAlphabet.invFun) := by
    apply TM2.Cfg.mk.injEq .. |>.mpr
    refine ⟨rfl, rfl, Eq.trans ?_ (halt_stk (W OM P).tm _).symm⟩
    rw [halt_stk, ← updO, pack_nil]
    rfl
  rw [← hi, hf] at key
  obtain ⟨k, hk, hit⟩ := key
  refine ⟨steps * (2 * Q + 2 * R + N + 5), ?_, ⟨⟨⟨k, hit⟩, hk⟩⟩⟩
  have hs : (steps : ℝ) ≤ t := by exact_mod_cast hst
  have hNq : (N : ℝ) ≤ Tq := Nat.floor_le hTq
  have h0 : (0 : ℝ) ≤ steps := by positivity
  push_cast
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hR0 : (0 : ℝ) ≤ R := by positivity
  calc (steps : ℝ) * (2 * Q + 2 * R + N + 5) ≤ t * (2 * Q + 2 * R + Tq + 5) := by
        apply mul_le_mul hs (by linarith) (by positivity) (by positivity)
    _ ≤ 4 * ((t : ℝ) + 1) * (Tq + Q + R + 4) := by
        have ht : (0 : ℝ) ≤ t := by positivity
        nlinarith [mul_nonneg ht hTq, mul_nonneg ht hQ0, mul_nonneg ht hR0]
