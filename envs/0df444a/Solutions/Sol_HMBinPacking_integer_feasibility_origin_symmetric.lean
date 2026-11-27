-- Prove2me | solution 1 for HMBinPacking.integer_feasibility_origin_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:35:53.39286+00:00
-- url     : https://prove2.me/submissions/ba14285a-3521-4b36-8614-47d47c0ab33b

import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_HMBinPacking_OracleMachine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Definitions.Def_HMBinPacking_Encoding
import Definitions.Def_HMBinPacking_Oracles
import Definitions.Def_HMBinPacking_ILP
import Mathlib.Analysis.Convex.Topology
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Size

set_option autoImplicit false

open Turing

namespace BitStacks

abbrev Mem (K : Type) := K → List Bool

/-- One straight-line, finitely branching stack instruction. Each read sees one bit or EOF. -/
inductive Action (K Λ : Type) where
  | stop (label : Option Λ)
  | peek (k : K) (next : Option Bool → Action K Λ)
  | drop (k : K) (next : Action K Λ)
  | push (k : K) (b : Bool) (next : Action K Λ)

namespace Action
variable {K Λ : Type} [DecidableEq K]

def run : Action K Λ → Mem K → Option Λ × Mem K
  | .stop l, m => (l,m)
  | .peek k f, m => (f (m k).head?).run m
  | .drop k a, m => a.run (Function.update m k (m k).tail)
  | .push k b a, m => a.run (Function.update m k (b::m k))

def compile : Action K Λ → TM2.Stmt (fun _ : K => Bool) Λ (Option Bool)
  | .stop (some l) => .load (fun _ => none) (.goto (fun _ => l))
  | .stop none => .load (fun _ => none) .halt
  | .peek k f => .peek k (fun _ v => v) (.branch Option.isNone (f none).compile
        (.branch (fun v => v.getD false) (f (some true)).compile (f (some false)).compile))
  | .drop k a => .pop k (fun v _ => v) a.compile
  | .push k b a => .push k (fun _ => b) a.compile

theorem correct (a : Action K Λ) (s : Option Bool) (m : Mem K) :
    TM2.stepAux a.compile s m = ⟨(a.run m).1, none, (a.run m).2⟩ := by
  induction a generalizing s m with
  | stop l => cases l <;> rfl
  | drop k a ih => exact ih _ _
  | push k b a ih => exact ih _ _
  | peek k f ih =>
    cases h : (m k).head? with
    | none => simpa [compile,run,TM2.stepAux,h] using ih none none m
    | some b => cases b <;> simp [compile,run,TM2.stepAux,h,ih]

end Action

variable {K Λ : Type} [DecidableEq K] [Fintype K] [Fintype Λ]
/-- An ordinary bundled Mathlib machine, with Boolean alphabets on every stack. -/
def machine (entry : Λ) (io : K) (code : Λ → Action K Λ) : TM2ComputableAux Bool Bool where
  tm := { K := K, k₀ := io, k₁ := io, Γ := fun _ => Bool, Λ := Λ,
          main := entry, σ := Option Bool, initialState := none, m := fun l => (code l).compile }
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool

def isolated (k : K) (s : List Bool) : Mem K :=
  (initList (machine () k (fun _ => .stop none)).tm s).stk

/-- Exactly n bit-stack instructions from a live or halted configuration. -/
inductive Path (code : Λ → Action K Λ) : Option Λ → Mem K → ℕ → Option Λ → Mem K → Prop where
  | refl (l m) : Path code l m 0 l m
  | step {l m} : Path code (some l) m 1 ((code l).run m).1 ((code l).run m).2
  | join {a m b n z p k h} : Path code a m k b n → Path code b n h z p → Path code a m (k+h) z p

theorem Path.outputs {entry io code src dst t bound} (h : Path (K:=K) (Λ:=Λ)
    code (some entry) (isolated (K:=K) io src) t none (isolated (K:=K) io dst)) (hb : t ≤ bound) :
    HMBinPacking.OutputsWithin (machine entry io code) src dst bound := by
  let M := machine entry io code
  let c (l m) : M.tm.Cfg := ⟨l,none,m⟩
  have sem {l m j r n} (p : Path code l m j r n) :
      (flip bind M.tm.step)^[j] (some (c l m)) = some (c r n) := by
    induction p with
    | refl => rfl
    | @step l m =>
      change some (TM2.stepAux (code l).compile none m) = _
      rw [Action.correct]; rfl
    | @join _ _ _ _ _ _ k g _ _ a b => rw [Nat.add_comm k g,Function.iterate_add_apply,a,b]
  have init : initList M.tm (src.map M.inputAlphabet.symm) = c (some entry) (isolated (K:=K) io src) := by
    have eqmap : src.map M.inputAlphabet.symm = src := List.map_id _
    rw [eqmap]
    rfl
  have halt : haltList M.tm (dst.map M.outputAlphabet.symm) = c none (isolated (K:=K) io dst) := by
    have eqmap : dst.map M.outputAlphabet.symm = dst := List.map_id _
    rw [eqmap]
    rfl
  refine ⟨⟨⟨t,?_⟩,hb⟩⟩
  change (flip bind M.tm.step)^[t] (some (initList M.tm (src.map M.inputAlphabet.symm))) =
    some (haltList M.tm (dst.map M.outputAlphabet.symm))
  rw [init,halt]; exact sem h

end BitStacks

namespace BitStacks
open Action
variable {K K' Λ Λ' : Type} [DecidableEq K] [DecidableEq K']

/-- Install a hardware operation in a larger finite machine by renaming its
registers injectively and its labels. No additional steps are charged. -/
def Action.rename (r : K ↪ K') (l : Option Λ → Option Λ') : Action K Λ → Action K' Λ'
  | .stop x => .stop (l x)
  | .peek k f => .peek (r k) (fun b => (f b).rename r l)
  | .drop k a => .drop (r k) (a.rename r l)
  | .push k b a => .push (r k) b (a.rename r l)

def Agrees (r : K ↪ K') (m : Mem K) (n : Mem K') : Prop := ∀ k, n (r k) = m k

private theorem sameUpdate (r : K ↪ K') {m n} (h : Agrees r m n) (k : K) (s : List Bool) :
    Agrees r (Function.update m k s) (Function.update n (r k) s) := by
  intro i; by_cases e : i=k
  · subst i; simp
  · rw [Function.update_of_ne e,Function.update_of_ne (r.injective.ne e)]
    exact h i

theorem renameRun (a : Action K Λ) (r : K ↪ K') (l : Option Λ → Option Λ')
    (m : Mem K) (n : Mem K') (h : Agrees r m n) :
    let small := a.run m
    let large := (a.rename r l).run n
    large.1=l small.1 ∧ Agrees r small.2 large.2 ∧
      ∀ k, (∀ j, r j ≠ k) → large.2 k = n k := by
  induction a generalizing m n with
  | stop z => exact ⟨rfl,h,fun _ _ => rfl⟩
  | peek k f ih =>
    simp only [Action.rename,Action.run,h k]
    exact ih _ m n h
  | drop k a ih =>
    obtain ⟨hl,ha,ho⟩ := ih _ _ (sameUpdate r h k (m k).tail)
    simp only [Action.rename,Action.run,h k]
    refine ⟨hl,ha,?_⟩
    intro p hp;rw [ho p hp,Function.update_of_ne (Ne.symm (hp k))]
  | push k b a ih =>
    obtain ⟨hl,ha,ho⟩ := ih _ _ (sameUpdate r h k (b::m k))
    simp only [Action.rename,Action.run,h k]
    refine ⟨hl,ha,?_⟩
    intro p hp; rw [ho p hp,Function.update_of_ne (Ne.symm (hp k))]

/-- A finite trace can be assembled as a subroutine. The caller may replace a
halt by a continuation and every unused caller register is preserved. -/
theorem Path.rename {program : Λ → Action K Λ} {i m t o n}
    (p : Path program i m t o n) (r : K ↪ K') (label : Λ → Λ') (exit : Option Λ')
    (code : Λ' → Action K' Λ')
    (implementation : ∀ j, code (label j) =
      (program j).rename r (fun q => q.elim exit (fun v => some (label v))))
    (before : Mem K') (h : Agrees r m before) :
    ∃ after : Mem K', Path code (i.elim exit (fun v => some (label v))) before t
        (o.elim exit (fun v => some (label v))) after ∧ Agrees r n after ∧
      ∀ k, (∀ j, r j ≠ k) → after k = before k := by
  induction p generalizing before with
  | refl l m => exact ⟨before,Path.refl _ _,h,fun _ _ => rfl⟩
  | @step j m =>
    have info := renameRun (program j) r (fun q => q.elim exit (fun v => some (label v))) m before h
    have st := Path.step (code:=code) (l:=label j) (m:=before)
    rw [implementation] at st
    exact ⟨_,info.1 ▸ st, info.2⟩
  | @join _ _ _ _ _ _ _ _ _ _ h₁ h₂ =>
    obtain ⟨middle,p₁,a₁,rest₁⟩ := h₁ _ h
    obtain ⟨after,p₂,a₂,rest₂⟩ := h₂ _ a₁
    exact ⟨after,p₁.join p₂,a₂,fun k hk => (rest₂ k hk).trans (rest₁ k hk)⟩

end BitStacks

open Turing
namespace BitStacks
variable {K J : Type} [DecidableEq K] [Fintype K] [Fintype J]

/-- A bounded Prove2Me run of a compiled stack program can itself be used as a
bounded subroutine trace. No reflection or new time assumption is needed. -/
theorem ofOutputs {entry : J} {io : K} {code : J→Action K J} {s w : List Bool} {T : ℕ}
    (h : HMBinPacking.OutputsWithin (machine entry io code) s w T) :
    ∃ t≤T,Path code (some entry) (isolated io s) t none (isolated io w) := by
  let M:=machine entry io code
  let c (l : Option J) (m : Mem K) : M.tm.Cfg := ⟨l,none,m⟩
  have soundBack (t : ℕ) (l l' : Option J) (m n : Mem K)
      (e : (flip bind M.tm.step)^[t] (some (c l m))=some (c l' n)) : Path code l m t l' n := by
    induction t generalizing l m with
    | zero =>
      change some (c l m)=some (c l' n) at e
      have a:= congrArg (fun q => q.l) (Option.some.inj e)
      have b:= congrArg (fun q => q.stk) (Option.some.inj e)
      change l=l' at a;change m=n at b;subst l';subst n;exact .refl _ _
    | succ t ih =>
      rw [Function.iterate_succ_apply] at e
      cases l with
      | none =>
        have stay (k : ℕ) : (flip bind M.tm.step)^[k] none=none := by induction k with
          | zero=>rfl
          | succ k ih => rw [Function.iterate_succ_apply];exact ih
        change (flip bind M.tm.step)^[t] none=some _ at e
        rw [stay] at e;cases e
      | some l =>
        have s1 : flip bind M.tm.step (some (c (some l) m))=some (c ((code l).run m).1 ((code l).run m).2) := by
          change some (TM2.stepAux (code l).compile none m)=_;rw [Action.correct];rfl
        rw [s1] at e
        simpa [Nat.add_comm 1] using (Path.step (code:=code) (l:=l) (m:=m)).join (ih _ _ e)
  obtain ⟨⟨trace,clock⟩⟩ := h
  obtain ⟨t,e⟩:=trace
  refine ⟨t,clock,?_⟩
  apply soundBack
  have eqmap (x : List Bool) : x.map M.inputAlphabet.symm=x := List.map_id _
  have eqout (x : List Bool) : x.map M.outputAlphabet.symm=x := List.map_id _
  change (flip bind M.tm.step)^[t] (some (initList M.tm (s.map M.inputAlphabet.symm)))=
    some (haltList M.tm (w.map M.outputAlphabet.symm)) at e
  rw [eqmap,eqout] at e;exact e
end BitStacks

open HMBinPacking Turing
namespace BitStacks.Oracle
variable {K J : Type} [DecidableEq K] [DecidableEq J] [Fintype K] [Fintype J]

def model (start : J) (io qs : K) (ask resume : J) (program : J→Action K J) : OracleMachine where
  M:=machine start io program
  qs:=qs
  qsAlphabet:=Equiv.refl _
  ask:=ask
  resume:=resume
  decEqΛ:=inferInstanceAs (DecidableEq J)

private theorem ordinaryStep (OM : OracleMachine) (O : List Bool→List Bool) (c : OCfg OM) (h : c.l≠some OM.ask) :
    oStep OM O c=OM.M.tm.step c := by
  letI:=OM.decEqΛ
  exact if_neg h

private theorem queryStep (OM : OracleMachine) (O : List Bool→List Bool) (c : OCfg OM) (h : c.l=some OM.ask) :
    oStep OM O c=some ⟨some OM.resume,c.var,Function.update c.stk OM.qs ((O ((c.stk OM.qs).map OM.qsAlphabet)).map OM.qsAlphabet.symm)⟩ := by
  letI:=OM.decEqΛ
  exact if_pos h

inductive Trace (program : J→Action K J) (O : List Bool→List Bool) (qs : K) (ask resume : J) (Q : ℕ) :
    Option J→Mem K→ℕ→Option J→Mem K→Prop where
  | refl (l m) : Trace program O qs ask resume Q l m 0 l m
  | bits {l m} (ordinary : l≠ask) : Trace program O qs ask resume Q (some l) m 1
      ((program l).run m).1 ((program l).run m).2
  | call {m : Mem K} (bounded : (m qs).length≤Q) : Trace program O qs ask resume Q (some ask) m 1
      (some resume) (Function.update m qs (O (m qs)))
  | join {i m t j n u k z} : Trace program O qs ask resume Q i m t j n →
      Trace program O qs ask resume Q j n u k z → Trace program O qs ask resume Q i m (t+u) k z

theorem Trace.registered {pg : J→Action K J} {O qs ak re Q} {src dst : List Bool} {start io t T}
    (path : Trace pg O qs ak re Q (some start) (isolated io src) t none (isolated io dst)) (clock : t≤T) :
    ORunsWithin (model start io qs ak re pg) O src dst T Q := by
  let OM:=model start io qs ak re pg
  let cfg (l : Option J) (m : Mem K) : OCfg OM := ⟨l,none,m⟩
  let step : Option (OCfg OM)→Option (OCfg OM) := flip bind (oStep OM O)
  have sem {l m j r n} (p : Trace pg O qs ak re Q l m j r n) :
      step^[j] (some (cfg l m))=some (cfg r n) ∧
      ∀ i<j,∀ c,step^[i] (some (cfg l m))=some c → c.l=some OM.ask → (c.stk OM.qs).length≤Q := by
    induction p with
    | refl l m => exact ⟨rfl,fun _ lt => (Nat.not_lt_zero _ lt).elim⟩
    | @bits l m hs =>
      refine ⟨?_,?_⟩
      · change oStep OM O (cfg (some l) m)=some _
        rw [ordinaryStep OM O _ (show (cfg (some l) m).l≠some OM.ask by exact fun h=>hs (Option.some.inj h))]
        change some (TM2.stepAux (pg l).compile none m)=_
        rw [Action.correct];rfl
      · intro i hi c e a
        have z : i=0:=by omega
        subst i
        change some (cfg (some l) m)=some c at e;cases e
        exact (hs (Option.some.inj a)).elim
    | @call m hl =>
      refine ⟨?_,?_⟩
      · change oStep OM O (cfg (some ak) m)=some _
        rw [queryStep OM O _ rfl]
        change some (cfg (some re) (Function.update m qs ((O ((m qs).map id)).map id)))=_
        simp
      · intro i hi c e _
        have z : i=0:=by omega
        subst i
        change some (cfg (some ak) m)=some c at e;cases e;exact hl
    | @join l m j r n k v z p q hp hq =>
      constructor
      · rw [Nat.add_comm j k,Function.iterate_add_apply,hp.1,hq.1]
      · intro i hi c e a
        by_cases le : i<j
        · exact hp.2 _ le _ e a
        · have dec : i=(i-j)+j := by omega
          rw [dec,Function.iterate_add_apply,hp.1] at e
          exact hq.2 _ (by omega) _ e a
  have proof:=sem path
  have ini : initList OM.M.tm (src.map OM.M.inputAlphabet.symm)=cfg (some start) (isolated io src) := by
    rw [show src.map OM.M.inputAlphabet.symm=src from List.map_id _];rfl
  have endc : haltList OM.M.tm (dst.map OM.M.outputAlphabet.symm)=cfg none (isolated io dst) := by
    rw [show dst.map OM.M.outputAlphabet.symm=dst from List.map_id _];rfl
  refine ⟨t,clock,?_,?_⟩
  · change step^[t] (some (initList OM.M.tm (src.map OM.M.inputAlphabet.symm)))=some _
    rw [ini,endc];exact proof.1
  · intro i le c e a
    change step^[i] (some (initList OM.M.tm (src.map OM.M.inputAlphabet.symm)))=some c at e
    rw [ini] at e;exact proof.2 _ le _ e a
end BitStacks.Oracle

namespace BitStacks.Oracle
variable {K A J : Type} [DecidableEq K] [DecidableEq J]

theorem lift {ac : A→Action K A} {i m t j n} (h : Path ac i m t j n)
    (O : List Bool→List Bool) (qs : K) (ak re : J) (Q : ℕ) (code : J→Action K J)
    (lbl : A→J) (exit : Option J) (ordinary : ∀ j,lbl j≠ak)
    (impl : ∀ j,code (lbl j)=(ac j).rename (Function.Embedding.refl _) (fun l=>l.elim exit (fun x=>some (lbl x)))) :
    Trace code O qs ak re Q (i.elim exit (fun x=>some (lbl x))) m t (j.elim exit (fun x=>some (lbl x))) n := by
  induction h with
  | refl => exact .refl _ _
  | join _ _ hp hq => exact hp.join hq
  | @step l m =>
    have eq:=renameRun (ac l) (Function.Embedding.refl _) (fun o=>o.elim exit (fun x=>some (lbl x))) m m (fun _=>rfl)
    let z:=(code (lbl l)).run m
    have el : z.1=((ac l).run m).1.elim exit (fun x=>some (lbl x)) := by simpa [z,impl] using eq.1
    have mem : z.2=((ac l).run m).2 := funext (fun k=>by simpa [z,impl] using eq.2.1 k)
    have step:=Trace.bits (program:=code) (O:=O) (qs:=qs) (resume:=re) (Q:=Q) (m:=m) (ordinary l)
    change Trace code O qs ak re Q (some (lbl l)) m 1 z.1 z.2 at step
    rwa [el,mem] at step
end BitStacks.Oracle

namespace BitStacks
variable {Q Λ : Type}
open Action

/-- The four public stacks used by a binary transducer. -/
inductive ZipReg | x | y | rx | ry deriving DecidableEq
instance : Fintype ZipReg := ⟨{.x,.y,.rx,.ry}, by intro k; cases k <;> decide⟩
namespace ZipReg
def store (a b c d : List Bool) : Mem ZipReg
  | x => a | y => b | rx => c | ry => d
@[simp] theorem setX (a b c d s : List Bool) : Function.update (store a b c d) x s = store s b c d := by
  funext k; cases k <;> rfl
@[simp] theorem setY (a b c d s : List Bool) : Function.update (store a b c d) y s = store a s c d := by
  funext k; cases k <;> rfl
@[simp] theorem setA (a b c d s : List Bool) : Function.update (store a b c d) rx s = store a b s d := by
  funext k; cases k <;> rfl
@[simp] theorem setB (a b c d s : List Bool) : Function.update (store a b c d) ry s = store a b c s := by
  funext k; cases k <;> rfl
end ZipReg
open ZipReg

/-- A bitwise finite-state transducer. A missing input bit is explicit, so the
two operands need not have equal lengths. -/
structure Gate (Q : Type) where
  onBits : Q → Option Bool → Option Bool → Q × Option Bool × Option Bool
  finish : Q → Option Bool × Option Bool
  returnBit : Q → Bool := fun _ => false
private abbrev Label (Q : Type) := (Fin 4) × Q
private def emit (r : ZipReg) (o : Option Bool) (a : Action ZipReg Λ) :=
  match o with | none => a | some b => Action.push r b a
private def prepend (o : Option Bool) (a : List Bool) := match o with | none => a | some b => b::a

def zipper (g : Gate Q) (l : Label Q) : Action ZipReg (Label Q) :=
  if l.1=0 then
    .peek x (fun a => .peek y (fun b =>
      if a.isNone && b.isNone then
        emit rx (g.finish l.2).1 (emit ry (g.finish l.2).2 (.stop (some (1,l.2))))
      else
        let out := g.onBits l.2 a b
        .drop x (.drop y (emit rx out.2.1 (emit ry out.2.2 (.stop (some (0,out.1))))))))
  else if l.1=1 then
    .peek rx (fun b => match b with
      | none => .stop (some (2,l.2))
      | some d => .drop rx (.push x d (.stop (some (1,l.2)))))
  else if l.1=2 then
    .peek ry (fun b => match b with
      | none => .stop (some (3,l.2))
      | some d => .drop ry (.push y d (.stop (some (2,l.2)))))
  else .push rx (g.returnBit l.2) (.stop none)

private theorem zstep (g : Gate Q) (q : Q) (a b r s : List Bool) (hv : a≠[] ∨ b≠[]) :
    let out := g.onBits q a.head? b.head?
    Path (zipper g) (some (0,q)) (store a b r s) 1 (some (0,out.1))
      (store a.tail b.tail (prepend out.2.1 r) (prepend out.2.2 s)) := by
  have cond : (a.head?.isNone && b.head?.isNone) = false := by
    cases a <;> cases b <;> simp_all
  have h := Path.step (code:=zipper g) (l:=(0,q)) (m:=store a b r s)
  have nonempty : ¬ (a=[] ∧ b=[]) := by tauto
  generalize eqo : g.onBits q a.head? b.head? = o at *
  obtain ⟨q',p,v⟩ := o
  cases p <;> cases v <;>
    simpa [zipper,Action.run,emit,prepend,store,cond,nonempty,eqo] using h

private theorem zend (g : Gate Q) (q : Q) (r s : List Bool) :
    Path (zipper g) (some (0,q)) (store [] [] r s) 1 (some (1,q))
      (store [] [] (prepend (g.finish q).1 r) (prepend (g.finish q).2 s)) := by
  have h := Path.step (code:=zipper g) (l:=(0,q)) (m:=store [] [] r s)
  generalize eqo : g.finish q = o
  obtain ⟨p,v⟩ := o
  cases p <;> cases v <;> simpa [zipper,Action.run,emit,prepend,store,eqo] using h

private theorem restoreX (g : Gate Q) (q : Q) (a b r s : List Bool) :
    Path (zipper g) (some (1,q)) (store a b r s) (r.length+1) (some (2,q))
      (store (r.reverse++a) b [] s) := by
  induction r generalizing a with
  | nil =>
    have h := Path.step (code:=zipper g) (l:=(1,q)) (m:=store a b [] s)
    simpa [zipper,Action.run,store] using h
  | cons z zs ih =>
    have h := Path.step (code:=zipper g) (l:=(1,q)) (m:=store a b (z::zs) s)
    have p : Path (zipper g) (some (1,q)) (store a b (z::zs) s) 1 (some (1,q)) (store (z::a) b zs s) := by
      simpa [zipper,Action.run,store] using h
    have z := p.join (ih (z::a))
    simpa [List.append_assoc,Nat.add_comm 1] using z

private theorem restoreY (g : Gate Q) (q : Q) (a b s : List Bool) :
    Path (zipper g) (some (2,q)) (store a b [] s) (s.length+1) (some (3,q))
      (store a (s.reverse++b) [] []) := by
  induction s generalizing b with
  | nil =>
    have h := Path.step (code:=zipper g) (l:=(2,q)) (m:=store a b [] [])
    simpa [zipper,Action.run,store] using h
  | cons z zs ih =>
    have h := Path.step (code:=zipper g) (l:=(2,q)) (m:=store a b [] (z::zs))
    have p : Path (zipper g) (some (2,q)) (store a b [] (z::zs)) 1 (some (2,q)) (store a (z::b) [] zs) := by
      simpa [zipper,Action.run,store] using h
    simpa [List.append_assoc,Nat.add_comm 1] using p.join (ih (z::b))

def revPre (o : Option Bool) (xs : List Bool) := match o with | none => xs | some b => b::xs

/-- Logical result of running the gate on the two words, from least to most significant
bit. Missing bits are passed as none. -/
def execute (g : Gate Q) : Q → List Bool → List Bool → Q × List Bool × List Bool
  | q, [], [] => (q,revPre (g.finish q).1 [],revPre (g.finish q).2 [])
  | q, bitX::xs, [] =>
    let r := g.onBits q (some bitX) none
    let z := execute g r.1 xs []
    (z.1,revPre r.2.1 z.2.1,revPre r.2.2 z.2.2)
  | q, [], bitY::ys =>
    let r := g.onBits q none (some bitY)
    let z := execute g r.1 [] ys
    (z.1,revPre r.2.1 z.2.1,revPre r.2.2 z.2.2)
  | q, bitX::xs, bitY::ys =>
    let r := g.onBits q (some bitX) (some bitY)
    let z := execute g r.1 xs ys
    (z.1,revPre r.2.1 z.2.1,revPre r.2.2 z.2.2)
termination_by _ xs ys => xs.length+ys.length
decreasing_by all_goals simp_wf <;> omega

private theorem revPre_rev (o : Option Bool) (a r : List Bool) :
    (revPre o a).reverse++r = a.reverse++prepend o r := by
  cases o <;> simp [revPre,prepend,List.append_assoc]

private theorem stream (g : Gate Q) (q : Q) (a b r s : List Bool) :
    let z := execute g q a b
    Path (zipper g) (some (0,q)) (store a b r s) (max a.length b.length+1) (some (1,z.1))
      (store [] [] (z.2.1.reverse++r) (z.2.2.reverse++s)) := by
  match a,b with
  | [],[] =>
    simpa [execute,revPre_rev] using zend g q r s
  | bitX::xs,[] =>
    let o := g.onBits q (some bitX) none
    have p := zstep g q (bitX::xs) [] r s (by simp)
    have t := stream g o.1 xs [] (prepend o.2.1 r) (prepend o.2.2 s)
    simpa [execute,o,revPre_rev,Nat.add_comm 1] using p.join t
  | [],bitY::ys =>
    let o := g.onBits q none (some bitY)
    have p := zstep g q [] (bitY::ys) r s (by simp)
    have t := stream g o.1 [] ys (prepend o.2.1 r) (prepend o.2.2 s)
    simpa [execute,o,revPre_rev,Nat.add_comm 1] using p.join t
  | bitX::xs,bitY::ys =>
    let o := g.onBits q (some bitX) (some bitY)
    have p := zstep g q (bitX::xs) (bitY::ys) r s (by simp)
    have t := stream g o.1 xs ys (prepend o.2.1 r) (prepend o.2.2 s)
    simpa [execute,o,revPre_rev,Nat.add_comm 1] using p.join t
termination_by a.length+b.length
decreasing_by all_goals simp_wf <;> omega

/-- A finite-state column scan runs on an actual compiled TM2. Both output words
are restored to least-significant-bit-first order; no scratch data remains. -/
theorem zipper_path (g : Gate Q) (q : Q) (a b : List Bool) :
    let z := execute g q a b
    Path (zipper g) (some (0,q)) (store a b [] [])
      (max a.length b.length+1+(z.2.1.length+1)+(z.2.2.length+1))
      (some (3,z.1)) (store z.2.1 z.2.2 [] []) := by
  let z := execute g q a b
  have p := stream g q a b [] []
  change Path _ _ _ _ _ (store [] [] (z.2.1.reverse++[]) (z.2.2.reverse++[])) at p
  simp only [List.append_nil] at p
  have s := restoreX g z.1 [] [] z.2.1.reverse z.2.2.reverse
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at s
  have t := restoreY g z.1 z.2.1 [] z.2.2.reverse
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at t
  exact (p.join s).join t

end BitStacks

namespace BitStacks
variable {Q : Type}
def val : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*val bs

private def digit (a : Option Bool) := (a.getD false).toNat
private def addBits (c : Bool) (a b : Option Bool) :=
  let n := c.toNat+digit a+digit b
  (decide (2 ≤ n), some (decide (n%2=1)), b)

def addGate : Gate Bool := ⟨addBits,fun c => (if c then some true else none,none),id⟩

private def subBits (c : Bool) (a b : Option Bool) :=
  let debt := digit b+c.toNat
  let x := digit a
  (decide (x<debt),some (decide ((x+2-debt)%2=1)),b)

def subGate : Gate Bool := ⟨subBits,fun _ => (none,none),id⟩

private def compareBits (c : Bool) (a b : Option Bool) :=
  let x := a.getD false
  let y := b.getD false
  (if x=y then c else y,a,b)
def compareGate : Gate Bool := ⟨compareBits,fun _ => (none,none),id⟩

private def carryLE (c : Bool) (x y : ℕ) := decide (x<y ∨ x=y ∧ c=true)
private theorem lowLE (c x y : Bool) (a b : ℕ) :
    carryLE (if x=y then c else y) a b = carryLE c (x.toNat+2*a) (y.toNat+2*b) := by
  apply Bool.eq_iff_iff.mpr; cases c <;> cases x <;> cases y <;> simp [carryLE] <;> omega

private abbrev norm := @revPre

private theorem decomp (g : Gate Q) (c : Q) (a b : List Bool) (h : a≠[] ∨ b≠[]) :
    let r := g.onBits c a.head? b.head?
    let z := execute g r.1 a.tail b.tail
    execute g c a b = (z.1,norm r.2.1 z.2.1,norm r.2.2 z.2.2) := by
  cases a <;> cases b <;> first | (solve | simp at h) | rw [execute];rfl

private theorem valH (a : List Bool) : val a = digit a.head? + 2*val a.tail := by
  cases a <;> rfl
private theorem joinHead (a : List Bool) : norm a.head? a.tail = a := by cases a <;> rfl
private theorem lenStep (a b : List Bool) (h : a≠[] ∨ b≠[]) :
    max a.length b.length = max a.tail.length b.tail.length + 1 := by
  cases a <;> cases b <;> simp_all <;> omega

/-- Bit-serial addition preserves its second operand and computes an unbounded
integer sum; its result has at most one extra digit. -/
theorem add_correct (c : Bool) (a b : List Bool) :
    let z := execute addGate c a b
    val z.2.1 = val a+val b+c.toNat ∧ z.2.2=b ∧
      z.2.1.length ≤ max a.length b.length + 1 := by
  by_cases h : a=[] ∧ b=[]
  · obtain ⟨rfl,rfl⟩ := h; cases c <;> simp [execute,addGate,revPre,val]
  · have live : a≠[] ∨ b≠[] := by tauto
    let r := addBits c a.head? b.head?
    have ih := add_correct r.1 a.tail b.tail
    obtain ⟨iv,iw,il⟩ := ih
    have H : r.1.toNat*2+(decide ((c.toNat+digit a.head?+digit b.head?)%2=1)).toNat =
        c.toNat+digit a.head?+digit b.head? := by
      have digitLaw (c : Bool) (x y : Option Bool) :
          (addBits c x y).1.toNat*2+(decide ((c.toNat+digit x+digit y)%2=1)).toNat =
            c.toNat + digit x + digit y := by
        cases c <;> rcases x with _|(_|_) <;> rcases y with _|(_|_) <;> rfl
      exact digitLaw c _ _
    rw [decomp addGate c a b live]
    let low := decide ((c.toNat+digit a.head?+digit b.head?)%2=1)
    let z := execute addGate r.1 a.tail b.tail
    change val (low::z.2.1) = _ ∧ norm b.head? z.2.2=b ∧ (low::z.2.1).length ≤ _
    change val z.2.1 = _ at iv
    change z.2.2 = _ at iw
    change z.2.1.length ≤ _ at il
    change r.1.toNat*2+low.toNat = _ at H
    rw [val,iv,iw,joinHead, valH a,valH b,lenStep _ _ live]
    have h' := Nat.mul_comm r.1.toNat 2
    refine ⟨?_,rfl,?_⟩ <;> (try simp only [List.length_cons]) <;> omega
termination_by a.length+b.length
decreasing_by
  have : a≠[] ∨ b≠[] := by tauto
  cases a <;> cases b <;> simp_all <;> omega

/-- The borrow bit records underflow modulo exactly 2^(max bit length).
This also handles unequal lengths and leading zeroes. -/
theorem sub_correct (c : Bool) (a b : List Bool) :
    let z := execute subGate c a b
    val a+z.1.toNat*2^(max a.length b.length) = val z.2.1+val b+c.toNat ∧
      z.2.2=b ∧ z.2.1.length = max a.length b.length := by
  by_cases h : a=[] ∧ b=[]
  · obtain ⟨rfl,rfl⟩ := h;cases c <;> simp [execute,subGate,revPre,val]
  · have live : a≠[] ∨ b≠[] := by tauto
    let r := subBits c a.head? b.head?
    let low := decide ((digit a.head?+2-(digit b.head?+c.toNat))%2=1)
    let z := execute subGate r.1 a.tail b.tail
    obtain ⟨iv,iw,il⟩ := sub_correct r.1 a.tail b.tail
    have e (c : Bool) (x y : Option Bool) :
          digit x + (subBits c x y).1.toNat*2 =
            (decide ((digit x+2-(digit y+c.toNat))%2=1)).toNat + digit y+c.toNat := by
      cases c <;> rcases x with _|(_|_) <;> rcases y with _|(_|_) <;> rfl
    have H : digit a.head? + r.1.toNat*2 = low.toNat + digit b.head?+c.toNat := e _ _ _
    rw [decomp subGate c a b live]
    change val a+z.1.toNat*2^(max a.length b.length) = val (low::z.2.1)+val b+c.toNat ∧
      norm b.head? z.2.2=b ∧ (low::z.2.1).length = max a.length b.length
    change val a.tail+z.1.toNat*_ = val z.2.1+val b.tail+r.1.toNat at iv
    change z.2.2 = _ at iw
    change z.2.1.length = _ at il
    rw [valH a,valH b,val,iw,joinHead,lenStep _ _ live,pow_succ]
    refine ⟨?_,rfl,by simp [il]⟩
    have doub := congrArg (fun n : ℕ => 2*n) iv
    nlinarith only [H,doub]
termination_by a.length+b.length
decreasing_by
  have : a≠[] ∨ b≠[] := by tauto
  cases a <;> cases b <;> simp_all <;> omega

/-- The order gate returns the comparison in finite control, leaving both register
words unchanged. Starting with true gives the non-strict ordering. -/
theorem cmp_correct (c : Bool) (a b : List Bool) :
    let z := execute compareGate c a b
    z.1 = carryLE c (val a) (val b) ∧ z.2.1=a ∧ z.2.2=b := by
  by_cases h : a=[] ∧ b=[]
  · obtain ⟨rfl,rfl⟩ := h;cases c <;> simp [execute,compareGate,revPre,val,carryLE]
  · have live : a≠[] ∨ b≠[] := by tauto
    let r := compareBits c a.head? b.head?
    let z := execute compareGate r.1 a.tail b.tail
    obtain ⟨iv,ix,iy⟩ := cmp_correct r.1 a.tail b.tail
    rw [decomp compareGate c a b live]
    change z.1 = carryLE c (val a) (val b) ∧ norm a.head? z.2.1 = a ∧ norm b.head? z.2.2 = b
    change z.1 = _ at iv
    change z.2.1 = _ at ix
    change z.2.2 = _ at iy
    rw [ix,iy,joinHead,joinHead,iv,valH a,valH b]
    exact ⟨lowLE c _ _ _ _,rfl,rfl⟩
termination_by a.length+b.length
decreasing_by
  have : a≠[] ∨ b≠[] := by tauto
  cases a <;> cases b <;> simp_all <;> omega

theorem le_correct (a b : List Bool) :
    let z := execute compareGate true a b
    z.1=decide (val a≤val b) ∧ z.2.1=a ∧ z.2.2=b := by
  have h := cmp_correct true a b
  have e : carryLE true (val a) (val b) = decide (val a≤val b) := by
    apply Bool.eq_iff_iff.mpr; simp [carryLE]; omega
  exact ⟨h.1.trans e,h.2⟩

end BitStacks

namespace BitStacks
variable {R Λ : Type}

/-- Two private work stacks and any finite number of public (Boolean) stacks. -/
abbrev Bank (R : Type) := Bool ⊕ R
def tmp : Bank R := .inl true
def tmp2 : Bank R := .inl false
def reg (i : R) : Bank R := .inr i

inductive BinaryOp | add | sub | le deriving DecidableEq
def BinaryOp.gate : BinaryOp → Gate Bool
  | .add => addGate | .sub => subGate | .le => compareGate
def BinaryOp.initial : BinaryOp → Bool
  | .le => true | _ => false
theorem BinaryOp.ret (s : BinaryOp) (q : Bool) : s.gate.returnBit q = q := by cases s <;> rfl

inductive Macro (R Λ : Type)
  | bits (a : Action (Bank R) Λ)
  | binary (op : BinaryOp) (i j : R) (h : i ≠ j) (next : Λ)

def ports (i j : R) (h : i≠j) : ZipReg ↪ Bank R where
  toFun | .x => reg i | .y => reg j | .rx => tmp | .ry => tmp2
  inj' := by intro x y; cases x <;> cases y <;> simp_all [reg,tmp,tmp2] <;> tauto

abbrev WordLabel (Λ : Type) := Λ ⊕ (Λ × (Fin 4 × Bool))
def wordCode (P : Λ → Macro R Λ) : WordLabel Λ → Action (Bank R) (WordLabel Λ)
  | .inl k => match P k with
    | .bits a => a.rename (Function.Embedding.refl _) (Option.map Sum.inl)
    | .binary op _ _ _ _ => .stop (some (.inr (k,(0,op.initial))))
  | .inr (k,q) => match P k with
    | .bits _ => .stop none
    | .binary op i j h next =>
      (zipper op.gate q).rename (ports i j h)
        (fun z => z.elim (some (.inl next)) (fun s => some (.inr (k,s))))

variable [DecidableEq R]

def afterGate (m : Mem (Bank R)) (i j : R) (z : Bool × List Bool × List Bool) : Mem (Bank R) :=
  Function.update (Function.update (Function.update m (reg i) z.2.1) (reg j) z.2.2) tmp [z.1]

/-- A binary macro has a trace in the exact bit-stack machine; the result/borrow/comparison
is left on tmp, the two public registers are updated and every other register is unchanged. -/
theorem binary_trace (P : Λ → Macro R Λ) (k n : Λ) (op : BinaryOp) (i j : R) (ne : i≠j)
    (ins : P k = .binary op i j ne n) (m : Mem (Bank R)) (ht : m tmp=[]) (hu : m tmp2=[]) :
    let a := m (reg i)
    let b := m (reg j)
    let z := execute op.gate op.initial a b
    Path (wordCode P) (some (.inl k)) m
      (1+(max a.length b.length+1+(z.2.1.length+1)+(z.2.2.length+1)+1))
      (some (.inl n)) (afterGate m i j z) := by
  let a := m (reg i)
  let b := m (reg j)
  let z := execute op.gate op.initial a b
  let r := ports i j ne
  have p := zipper_path op.gate op.initial a b
  have fin := Path.step (code:=zipper op.gate) (l:=(3,z.1))
    (m:=ZipReg.store z.2.1 z.2.2 [] [])
  have e : Path (zipper op.gate) (some (3,z.1)) (ZipReg.store z.2.1 z.2.2 [] []) 1 none
      (ZipReg.store z.2.1 z.2.2 [z.1] []) := by
    simpa [zipper,Action.run,ZipReg.store,BinaryOp.ret] using fin
  have x := p.join e
  let label (s : Fin 4 × Bool) : WordLabel Λ := .inr (k,s)
  have sub : ∀ l, wordCode P (label l) =
      (zipper op.gate l).rename r (fun q => q.elim (some (.inl n)) (fun v => some (label v))) := by
    intro l; simp [wordCode,label,ins,r]
  have start : Agrees r (ZipReg.store a b [] []) m := by
    intro j; cases j <;> first | rfl | exact ht | exact hu
  obtain ⟨v,trace,agrees,outside⟩ := x.rename r label (some (.inl n)) (wordCode P) sub m start
  have eqout : v=afterGate m i j z := by
    funext s
    cases s with
    | inl c =>
      cases c with
      | true =>
        have vv := agrees ZipReg.rx
        simpa [afterGate,tmp,reg,r,ports,ZipReg.store] using vv
      | false =>
        have vv := agrees ZipReg.ry
        change v tmp2 = _; simp [afterGate,tmp,tmp2,reg] at *; exact vv.trans hu.symm
    | inr k =>
      by_cases ki : k=i
      · subst k; have vv := agrees ZipReg.x
        simpa [afterGate,reg,tmp,ne,r,ports,ZipReg.store] using vv
      · by_cases kj : k=j
        · subst k; have vv := agrees ZipReg.y
          simpa [afterGate,reg,tmp,r,ports,ZipReg.store] using vv
        · have all : ∀ p, r p ≠ .inr k := by
            intro p; cases p <;> simp_all [r,ports,reg,tmp,tmp2,Ne.symm]
          simpa [afterGate,reg,tmp,ki,kj] using outside _ all
  have step := Path.step (code:=wordCode P) (l:=.inl k) (m:=m)
  have beginP : Path (wordCode P) (some (.inl k)) m 1 (some (label (0,op.initial))) m := by
    simpa [wordCode,ins,Action.run,label] using step
  rw [eqout] at trace
  exact beginP.join trace

end BitStacks

namespace BitStacks
variable {R Λ : Type} [DecidableEq R]
def gateResult (op : BinaryOp) (m : Mem (Bank R)) (i j : R) :=
  execute op.gate op.initial (m (reg i)) (m (reg j))
def gateTime (op : BinaryOp) (m : Mem (Bank R)) (i j : R) :=
  let z := gateResult op m i j
  1+(max (m (reg i)).length (m (reg j)).length+1+(z.2.1.length+1)+(z.2.2.length+1)+1)
inductive MacroPath (P : Λ → Macro R Λ) :
    Option Λ → Mem (Bank R) → ℕ → Option Λ → Mem (Bank R) → Prop where
  | refl (l m) : MacroPath P l m 0 l m
  | bits {l m a} (ins : P l = .bits a) : MacroPath P (some l) m 1 (a.run m).1 (a.run m).2
  | binary {l} {m : Mem (Bank R)} {op i j h n} (ins : P l=.binary op i j h n) (hx : m tmp=[]) (hy : m tmp2=[]) :
      MacroPath P (some l) m (gateTime op m i j) (some n) (afterGate m i j (gateResult op m i j))
  | join {l m n a k b t u} : MacroPath P l m t n a → MacroPath P n a u k b →
      MacroPath P l m (t+u) k b

theorem MacroPath.sound {P : Λ → Macro R Λ} {l m n a t} (h : MacroPath P l m t n a) :
    Path (wordCode P) (l.map Sum.inl) m t (n.map Sum.inl) a := by
  induction h with
  | refl l m => exact Path.refl _ _
  | join _ _ a b => exact a.join b
  | binary ins hx hy => exact binary_trace _ _ _ _ _ _ _ ins _ hx hy
  | @bits l m a ins =>
    have p := Path.step (code:=wordCode P) (l:=.inl l) (m:=m)
    have e := renameRun a (Function.Embedding.refl _) (Option.map (@Sum.inl Λ (Λ × (Fin 4 × Bool))))
      m m (fun _ => rfl)
    have eqn : ((a.rename (Function.Embedding.refl _) (Option.map (@Sum.inl Λ (Λ × (Fin 4 × Bool))))).run m).2 =
        (a.run m).2 := funext (fun k => e.2.1 k)
    simp only [wordCode,ins] at p
    rw [eqn,e.1] at p
    exact p

theorem MacroPath.outputs [Fintype R] [Fintype Λ] {P : Λ → Macro R Λ} {l : Λ} {io : Bank R}
    {a b : List Bool} {t T : ℕ}
    (h : MacroPath P (some l) (isolated io a) t none (isolated io b)) (bound : t≤T) :
    HMBinPacking.OutputsWithin (machine (Sum.inl l) io (wordCode P)) a b T :=
  h.sound.outputs bound
end BitStacks

namespace BitStacks
variable {R Λ J : Type} [DecidableEq R]
def Macro.mapLabels (f : Λ → J) : Macro R Λ → Macro R J
  | .bits a => .bits (a.rename (Function.Embedding.refl _) (Option.map f))
  | .binary op i j h n => .binary op i j h (f n)
theorem MacroPath.mapLabels {P : Λ → Macro R Λ} {Q : J → Macro R J} (f : Λ → J)
    (link : ∀ l, Q (f l)=(P l).mapLabels f) {i m t o n} (p : MacroPath P i m t o n) :
    MacroPath Q (i.map f) m t (o.map f) n := by
  induction p with
  | refl l m => exact .refl _ _
  | join _ _ a b => exact a.join b
  | @binary l m op i j h n inst x y =>
    exact MacroPath.binary (show Q (f l)=_ by rw [link,inst];rfl) x y
  | @bits l m a ins =>
    have h := MacroPath.bits (P:=Q) (l:=f l) (m:=m) (a:=a.rename (Function.Embedding.refl _) (Option.map f))
      (by rw [link,ins];rfl)
    have e := renameRun a (Function.Embedding.refl _) (Option.map f) m m (fun _ => rfl)
    have em : ((a.rename (Function.Embedding.refl _) (Option.map f)).run m).2=(a.run m).2 :=
      funext (fun k => e.2.1 k)
    simpa [e.1,em] using h
end BitStacks

namespace OneTypeTM
open BitStacks 
inductive R | tape | rem | den | bins | items | prod | first | second | rev | width | dim deriving DecidableEq
open R
instance : Fintype R := ⟨{tape,rem,den,bins,items,prod,first,second,rev,width,dim},by intro r;cases r <;> decide⟩
abbrev L := (Fin 3 × Fin 5) ⊕ (Fin 10 ⊕ Fin 10)
def H (p : Fin 5) : L := .inl (0,p)
def D (p : Fin 5) : L := .inl (1,p)
def V (p : Fin 5) : L := .inl (2,p)
def A (j : Fin 10) : L := .inr (.inl j)
def C (j : Fin 10) : L := .inr (.inr j)
def dest (p : Fin 5) : R := match p.val with | 0 => rem | 1 => dim | 2 => den | 3 => items | _ => bins
def cleanup (j : Fin 10) : R := match j.val with
  | 0 => rem | 1 => den | 2 => bins | 3 => items | 4 => prod
  | 5 => first | 6 => second | 7 => rev | 8 => width | _ => dim
def jump (l : L) : Action (Bank R) L := .stop (some l)
def next (p : Fin 5) := if p=4 then A 0 else H (p+1)
def code : L → Macro R L
  | .inl (tag,p) =>
    if tag=0 then .bits (.peek (reg tape) (fun v =>
      .drop (reg tape) (if v.getD false then
        .push (reg width) true (if p=0 then .push (reg first) true (.push (reg second) true (jump (H p)))
                                 else jump (H p))
        else jump (D p))))
    else if tag=1 then .bits (.peek (reg width) (fun v => if v.isSome then
      .drop (reg width) (.peek (reg tape) (fun b => .drop (reg tape)
        (.push (reg rev) (b.getD false) (jump (D p))))) else jump (V p)))
    else .bits (.peek (reg rev) (fun b => match b with
      | none => jump (next p) | some bit => .drop (reg rev) (.push (reg (dest p)) bit (jump (V p)))))
  | .inr (.inl j) => match j.val with
    | 0 => .bits (.peek (reg first) (fun b => if b.isSome then
              .drop (reg first) (.push (reg den) false (jump (A 0))) else jump (A 1)))
    | 1 => .bits (.peek (reg second) (fun b => if b.isSome then
              .drop (reg second) (.push (reg rem) false (.push (reg prod) false (jump (A 2))))
              else jump (A 8)))
    | 2 => .binary .le den rem (by decide) (A 3)
    | 3 => .bits (.peek tmp (fun b => .drop tmp (jump (if b.getD false then A 4 else A 1))))
    | 4 => .binary .sub rem den (by decide) (A 5)
    | 5 => .bits (.drop tmp (jump (A 6)))
    | 6 => .binary .add prod bins (by decide) (A 7)
    | 7 => .bits (.drop tmp (jump (A 1)))
    | 8 => .binary .le items prod (by decide) (A 9)
    | _ => .bits (.peek tmp (fun b => .drop tmp (.push (reg tape) (b.getD false) (jump (C 0)))))
  | .inr (.inr j) => .bits (.peek (reg (cleanup j)) (fun v => if v.isSome then
        .drop (reg (cleanup j)) (jump (C j)) else if j=9 then .stop none else jump (C (j+1))))

def machine := BitStacks.machine (.inl (H 0)) (reg tape) (wordCode code)

structure Cells where
  input : List Bool := []
  remainder : List Bool := []
  divisor : List Bool := []
  binCount : List Bool := []
  itemCount : List Bool := []
  product : List Bool := []
  prep : List Bool := []
  todo : List Bool := []
  reversed : List Bool := []
  scratch : List Bool := []
  dimension : List Bool := []
  flag : List Bool := []
  spare : List Bool := []

def Cells.mem (s : Cells) : Mem (Bank R)
  | .inl true => s.flag | .inl false => s.spare
  | .inr .tape => s.input | .inr .rem => s.remainder | .inr .den => s.divisor
  | .inr .bins => s.binCount | .inr .items => s.itemCount | .inr .prod => s.product
  | .inr .first => s.prep | .inr .second => s.todo | .inr .rev => s.reversed
  | .inr .width => s.scratch | .inr .dim => s.dimension
@[simp] theorem Cells.get_input (s : Cells) : s.mem (reg R.tape) = s.input := rfl
@[simp] theorem Cells.get_remainder (s : Cells) : s.mem (reg R.rem) = s.remainder := rfl
@[simp] theorem Cells.get_divisor (s : Cells) : s.mem (reg R.den) = s.divisor := rfl
@[simp] theorem Cells.get_binCount (s : Cells) : s.mem (reg R.bins) = s.binCount := rfl
@[simp] theorem Cells.get_itemCount (s : Cells) : s.mem (reg R.items) = s.itemCount := rfl
@[simp] theorem Cells.get_product (s : Cells) : s.mem (reg R.prod) = s.product := rfl
@[simp] theorem Cells.get_prep (s : Cells) : s.mem (reg R.first) = s.prep := rfl
@[simp] theorem Cells.get_todo (s : Cells) : s.mem (reg R.second) = s.todo := rfl
@[simp] theorem Cells.get_reversed (s : Cells) : s.mem (reg R.rev) = s.reversed := rfl
@[simp] theorem Cells.get_scratch (s : Cells) : s.mem (reg R.width) = s.scratch := rfl
@[simp] theorem Cells.get_dimension (s : Cells) : s.mem (reg R.dim) = s.dimension := rfl
@[simp] theorem Cells.get_flag (s : Cells) : s.mem tmp = s.flag := rfl
@[simp] theorem Cells.get_spare (s : Cells) : s.mem tmp2 = s.spare := rfl

@[simp] theorem Cells.up_input (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.tape) v = ({s with input:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_remainder (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.rem) v = ({s with remainder:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_divisor (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.den) v = ({s with divisor:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_binCount (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.bins) v = ({s with binCount:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_itemCount (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.items) v = ({s with itemCount:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_product (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.prod) v = ({s with product:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_prep (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.first) v = ({s with prep:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_todo (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.second) v = ({s with todo:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_reversed (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.rev) v = ({s with reversed:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_scratch (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.width) v = ({s with scratch:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_dimension (s : Cells) (v : List Bool) :
    Function.update s.mem (reg R.dim) v = ({s with dimension:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_flag (s : Cells) (v : List Bool) :
    Function.update s.mem tmp v = ({s with flag:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl
@[simp] theorem Cells.up_spare (s : Cells) (v : List Bool) :
    Function.update s.mem tmp2 v = ({s with spare:=v} : Cells).mem := by
  funext p; cases p with
  | inl a => cases a <;> rfl
  | inr a => cases a <;> rfl

abbrev Goes (l : L) (s : Cells) (t : ℕ) (l' : Option L) (z : Cells) :=
  MacroPath code (some l) s.mem t l' z.mem

end OneTypeTM

namespace OneTypeTM
open BitStacks R
def atClear (j : Fin 10) (s : Cells) : List Bool := match j.val with
  | 0 => s.remainder
  | 1 => s.divisor
  | 2 => s.binCount
  | 3 => s.itemCount
  | 4 => s.product
  | 5 => s.prep
  | 6 => s.todo
  | 7 => s.reversed
  | 8 => s.scratch
  | _ => s.dimension
def setClear (j : Fin 10) (w : List Bool) (s : Cells) : Cells := match j.val with
  | 0 => {s with remainder:=w}
  | 1 => {s with divisor:=w}
  | 2 => {s with binCount:=w}
  | 3 => {s with itemCount:=w}
  | 4 => {s with product:=w}
  | 5 => {s with prep:=w}
  | 6 => {s with todo:=w}
  | 7 => {s with reversed:=w}
  | 8 => {s with scratch:=w}
  | _ => {s with dimension:=w}

def nextClear (j : Fin 10) : Option L := if j=9 then none else some (C (j+1))

theorem clearStep (j : Fin 10) (w : List Bool) (s : Cells) :
    Goes (C j) (setClear j w s) (w.length+1) (nextClear j) (setClear j [] s) := by
  induction w with
  | nil =>
    have e := MacroPath.bits (P:=code) (l:=C j) (m:=(setClear j [] s).mem) (a:=_) (by rfl)
    fin_cases j <;> simpa [code,C,cleanup,setClear,Action.run,jump,nextClear] using e
  | cons b bs ih =>
    have e := MacroPath.bits (P:=code) (l:=C j) (m:=(setClear j (b::bs) s).mem) (a:=_) (by rfl)
    have step : Goes (C j) (setClear j (b::bs) s) 1 (C j) (setClear j bs s) := by
      fin_cases j <;> simpa [code,C,cleanup,setClear,Action.run,jump] using e
    simpa [Nat.add_comm 1] using step.join ih

def costClear (s : Cells) :=
  s.remainder.length + s.divisor.length + s.binCount.length + s.itemCount.length + s.product.length + s.prep.length + s.todo.length + s.reversed.length + s.scratch.length + s.dimension.length + 11

theorem finish (s : Cells) (b : Bool) (hi : s.input=[]) (hflag : s.flag=[b]) (hsp : s.spare=[]) :
    Goes (A 9) s (costClear s) none ({input:=[b]} : Cells) := by
  have e := MacroPath.bits (P:=code) (l:=A 9) (m:=s.mem) (a:=_) (by rfl)
  let m0 := {s with input:=[b],flag:=[]}
  have p0 : Goes (A 9) s 1 (C 0) m0 := by
    simpa [m0,code,A,Action.run,jump,hi,hflag] using e
  let m1 := {m0 with remainder:=[]}
  have p1 : Goes (C 0) m0 (s.remainder.length+1) (C 1) m1 := clearStep 0 _ m0
  let m2 := {m1 with divisor:=[]}
  have p2 : Goes (C 1) m1 (s.divisor.length+1) (C 2) m2 := clearStep 1 _ m1
  let m3 := {m2 with binCount:=[]}
  have p3 : Goes (C 2) m2 (s.binCount.length+1) (C 3) m3 := clearStep 2 _ m2
  let m4 := {m3 with itemCount:=[]}
  have p4 : Goes (C 3) m3 (s.itemCount.length+1) (C 4) m4 := clearStep 3 _ m3
  let m5 := {m4 with product:=[]}
  have p5 : Goes (C 4) m4 (s.product.length+1) (C 5) m5 := clearStep 4 _ m4
  let m6 := {m5 with prep:=[]}
  have p6 : Goes (C 5) m5 (s.prep.length+1) (C 6) m6 := clearStep 5 _ m5
  let m7 := {m6 with todo:=[]}
  have p7 : Goes (C 6) m6 (s.todo.length+1) (C 7) m7 := clearStep 6 _ m6
  let m8 := {m7 with reversed:=[]}
  have p8 : Goes (C 7) m7 (s.reversed.length+1) (C 8) m8 := clearStep 7 _ m7
  let m9 := {m8 with scratch:=[]}
  have p9 : Goes (C 8) m8 (s.scratch.length+1) (C 9) m9 := clearStep 8 _ m8
  let m10 := {m9 with dimension:=[]}
  have p10 : Goes (C 9) m9 (s.dimension.length+1) none m10 := clearStep 9 _ m9
  have path := ((((((((((p0.join p1).join p2).join p3).join p4).join p5).join p6).join p7).join p8).join p9).join p10)
  have final : m10 = ({input:=[b]} : Cells) := by simp [m10,m9,m8,m7,m6,m5,m4,m3,m2,m1,m0,hsp]
  rw [final] at path
  convert path using 1 <;> simp [costClear] <;> omega
end OneTypeTM

namespace DimensionEmitter
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
open ExponomialAssortment.FPTAS (encodeRat)
abbrev L := Bool ⊕ ((Fin 3 × Fin 2) ⊕ (Fin 8 ⊕ OneTypeTM.L))
def init (m : Bool) : L := .inl m
def old (l : OneTypeTM.L) : L := .inr (.inr (.inr l))
def H (p : Fin 2) : L := .inr (.inl (0,p))
def D (p : Fin 2) : L := .inr (.inl (1,p))
def V (p : Fin 2) : L := .inr (.inl (2,p))
def A (j : Fin 8) : L := .inr (.inr (.inl j))
def block (m : Bool) : List Bool := if m then encodeRat 0 else [false]
def suffix (m : Bool) : List Bool := if m then encodeRat (-1) else []
def tagWord (m : Bool) : List Bool := if m then [false] else []
def pushWord : List Bool → Action (Bank R) L → Action (Bank R) L
  | [],a => a
  | b::bs,a => pushWord bs (.push (reg tape) b a)
def jump (l : L) : Action (Bank R) L := .stop (some l)
def next (p : Fin 2) : L := if p=0 then H 1 else A 0
def dest (p : Fin 2) : R := if p=0 then rem else dim
def code : L → Macro R L
  | .inl m => .bits (.push (reg items) m (jump (H 0)))
  | .inr (.inr (.inr l)) => (OneTypeTM.code l).mapLabels old
  | .inr (.inl (tag,p)) =>
    if tag=0 then .bits (.peek (reg tape) (fun v => .drop (reg tape)
      (if v.getD false then .push (reg width) true (jump (H p)) else jump (D p))))
    else if tag=1 then .bits (.peek (reg width) (fun v => if v.isSome then
      .drop (reg width) (.peek (reg tape) (fun b => .drop (reg tape)
        (.push (reg rev) (b.getD false) (jump (D p))))) else jump (V p)))
    else .bits (.peek (reg rev) (fun b => match b with
      | none => jump (next p) | some bit => .drop (reg rev) (.push (reg (dest p)) bit (jump (V p)))))
  | .inr (.inr (.inl j)) => match j.val with
    | 0 => .bits (.peek (reg tape) (fun b => if b.isSome then .drop (reg tape) (jump (A 0)) else
        .peek (reg items) (fun m => pushWord (suffix (m.getD false)) (.push (reg den) true (jump (A 5))))))
    | 3 => .binary .sub dim den (by decide) (A 4)
    | 4 => .bits (.drop tmp (.peek (reg items) (fun m => pushWord (block (m.getD false)) (jump (A 5)))))
    | 5 => .binary .le dim prod (by decide) (A 6)
    | 6 => .bits (.peek tmp (fun b=>.drop tmp (jump (if b.getD false then A 7 else A 3))))
    | _ => .bits (.peek (reg items) (fun m => pushWord (tagWord (m.getD false)) (jump (old (OneTypeTM.C 0)))))
def machine (m : Bool) := BitStacks.machine (.inl (init m)) (reg tape) (wordCode code)
abbrev Goes (l : L) (s : Cells) (t : ℕ) (o : Option L) (z : Cells) :=
  MacroPath code (some l) s.mem t o z.mem
def Runs (l : L) (s : Cells) (bound : ℕ) (out : Option L) (t : Cells) : Prop := ∃ n ≤ bound, Goes l s n out t
theorem Runs.mono {i s a o t b} (h : Runs i s a o t) (le : a≤b) : Runs i s b o t := by
  obtain ⟨n,u,v⟩:=h; exact ⟨n,u.trans le,v⟩
theorem Runs.seq {i s a j t b k v} (h : Runs i s a (some j) t) (q : Runs j t b k v) : Runs i s (a+b) k v := by
  obtain ⟨n,u,x⟩:=h;obtain ⟨m,z,y⟩:=q;exact ⟨n+m,Nat.add_le_add u z,x.join y⟩
theorem smallRun {i s t o z} (h : Goes i s t o z) : Runs i s t o z := ⟨t,le_rfl,h⟩
theorem pushRun (w : List Bool) (a : Action (Bank R) L) (s : Cells) :
    (pushWord w a).run s.mem=a.run ({s with input:=w++s.input}:Cells).mem := by
  induction w generalizing a with
  | nil => rfl
  | cons b bs ih => rw [pushWord,ih];simp [Action.run]

theorem clean (s : Cells) (hf : s.flag=[]) (hsp : s.spare=[]) :
    Runs (old (OneTypeTM.C 0)) s (OneTypeTM.costClear s) none ({input:=s.input}:Cells) := by
  let m0 := s
  let m1 := {m0 with remainder:=[]}
  have p1 : OneTypeTM.Goes (OneTypeTM.C 0) m0 (s.remainder.length+1) (OneTypeTM.C 1) m1 := OneTypeTM.clearStep 0 _ m0
  let m2 := {m1 with divisor:=[]}
  have p2 : OneTypeTM.Goes (OneTypeTM.C 1) m1 (s.divisor.length+1) (OneTypeTM.C 2) m2 := OneTypeTM.clearStep 1 _ m1
  let m3 := {m2 with binCount:=[]}
  have p3 : OneTypeTM.Goes (OneTypeTM.C 2) m2 (s.binCount.length+1) (OneTypeTM.C 3) m3 := OneTypeTM.clearStep 2 _ m2
  let m4 := {m3 with itemCount:=[]}
  have p4 : OneTypeTM.Goes (OneTypeTM.C 3) m3 (s.itemCount.length+1) (OneTypeTM.C 4) m4 := OneTypeTM.clearStep 3 _ m3
  let m5 := {m4 with product:=[]}
  have p5 : OneTypeTM.Goes (OneTypeTM.C 4) m4 (s.product.length+1) (OneTypeTM.C 5) m5 := OneTypeTM.clearStep 4 _ m4
  let m6 := {m5 with prep:=[]}
  have p6 : OneTypeTM.Goes (OneTypeTM.C 5) m5 (s.prep.length+1) (OneTypeTM.C 6) m6 := OneTypeTM.clearStep 5 _ m5
  let m7 := {m6 with todo:=[]}
  have p7 : OneTypeTM.Goes (OneTypeTM.C 6) m6 (s.todo.length+1) (OneTypeTM.C 7) m7 := OneTypeTM.clearStep 6 _ m6
  let m8 := {m7 with reversed:=[]}
  have p8 : OneTypeTM.Goes (OneTypeTM.C 7) m7 (s.reversed.length+1) (OneTypeTM.C 8) m8 := OneTypeTM.clearStep 7 _ m7
  let m9 := {m8 with scratch:=[]}
  have p9 : OneTypeTM.Goes (OneTypeTM.C 8) m8 (s.scratch.length+1) (OneTypeTM.C 9) m9 := OneTypeTM.clearStep 8 _ m8
  let m10 := {m9 with dimension:=[]}
  have p10 : OneTypeTM.Goes (OneTypeTM.C 9) m9 (s.dimension.length+1) none m10 := OneTypeTM.clearStep 9 _ m9
  have path := (((((((((p1.join p2).join p3).join p4).join p5).join p6).join p7).join p8).join p9).join p10)
  have final : m10 = ({input:=s.input} : Cells) := by simp [m10,m9,m8,m7,m6,m5,m4,m3,m2,m1,m0,hsp,hf]
  rw [final] at path
  have sim := path.mapLabels (Q:=code) old (by intro l;rfl)
  refine ⟨_,?_,sim⟩
  simp [OneTypeTM.costClear];omega
end DimensionEmitter

namespace DimensionEmitter
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
private theorem val_small (w : List Bool) : val w < 2^w.length := by
  induction w with
  | nil => decide
  | cons b bs ih => cases b <;> simp [val,pow_succ] <;> omega

theorem decrement (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) (a : s.divisor=[true])
    (mode : Bool) (type : s.itemCount=[mode]) (n : ℕ) (v : val s.dimension=n+1) :
    ∃ d : List Bool, Runs (A 3) s (3*(s.dimension.length+1)+8) (A 5) {s with dimension:=d,flag:=[],input:=block mode++s.input} ∧
      val d=n ∧ d.length ≤ max s.dimension.length 1 := by
  have e := MacroPath.binary (P:=code) (l:=A 3) (m:=s.mem) (op:=.sub) (i:=dim) (j:=den)
    (h:=by decide) (n:=A 4) (by rfl) f sp
  let z := execute subGate false s.dimension s.divisor
  obtain ⟨eq,right,len⟩ := sub_correct false s.dimension s.divisor
  change val s.dimension+z.1.toNat*2^(max s.dimension.length s.divisor.length)=val z.2.1+val s.divisor+0 at eq
  change z.2.2=_ at right;change z.2.1.length=_ at len
  have one : val s.divisor=1 := by rw [a];rfl
  have value : val z.2.1=n := by
    have sm := val_small z.2.1
    rw [len] at sm
    cases h : z.1 <;> rw [h,one,v] at eq <;> simp at eq <;> omega
  have zl : gateResult .sub s.mem dim den = z := rfl
  let mid := {s with dimension:=z.2.1,flag:=[z.1]}
  have gate : Goes (A 3) s (gateTime .sub s.mem dim den) (A 4) mid := by simpa [zl,afterGate,mid,right] using e
  have step := MacroPath.bits (P:=code) (l:=A 4) (m:=mid.mem) (a:=_) (by rfl)
  have pop : Goes (A 4) mid 1 (A 5) {s with dimension:=z.2.1,flag:=[],input:=block mode++s.input} := by simpa [mid,code,A,Action.run,jump,pushRun,type] using step
  refine ⟨z.2.1,⟨_,?_,gate.join pop⟩,value,by simpa [a] using len.le⟩
  simp [gateTime,zl,right,len,a]; omega

theorem testDim (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) (a : s.divisor=[true]) (prod0 : s.product=[]) :
    Runs (A 5) s (3*s.dimension.length+7)
      (if val s.dimension=0 then A 7 else A 3)
      {s with flag:=[]} := by
  have e := MacroPath.binary (P:=code) (l:=A 5) (m:=s.mem) (op:=.le) (i:=dim) (j:=prod)
    (h:=by decide) (n:=A 6) (by rfl) f sp
  let z := execute compareGate true s.dimension s.product
  obtain ⟨ans,left,right⟩ := le_correct s.dimension s.product
  change z.1=_ at ans; change z.2.1=_ at left; change z.2.2=_ at right
  have zl : gateResult .le s.mem dim prod = z := rfl
  let mid := {s with flag:=[z.1]}
  have gate : Goes (A 5) s (gateTime .le s.mem dim prod) (A 6) mid := by simpa [zl,afterGate,mid,left,right] using e
  have step := MacroPath.bits (P:=code) (l:=A 6) (m:=mid.mem) (a:=_) (by rfl)
  have pop : Goes (A 6) mid 1 (if val s.dimension=0 then A 7 else A 3)
      {s with flag:=[]} := by
    by_cases c : val s.dimension=0 <;> simpa [mid,code,A,Action.run,jump,ans,prod0,val,c,a] using step
  refine ⟨_,?_,gate.join pop⟩
  simp [gateTime,zl,left,right,prod0]; omega


end DimensionEmitter

open BitStacks
open ExponomialAssortment.FPTAS (encodeNat)
namespace DimensionEmitter
open OneTypeTM (Cells R)
open OneTypeTM.R

def putWord (p : Fin 2) (w : List Bool) (m : Cells) : Cells :=
  if p=0 then {m with remainder:=w++m.remainder} else {m with dimension:=w++m.dimension}
def putInput (_ : Fin 2) (w : List Bool) (m : Cells) : Cells := {m with input:=w}

private theorem HT (p : Fin 2) (m : Cells) (bs : List Bool) :
    Goes (H p) (putInput p (true::bs) m) 1 (H p)
      (putInput p bs {m with scratch:=true::m.scratch}) := by
  have e := MacroPath.bits (P:=code) (l:=H p) (m:=(putInput p (true::bs) m).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,H,putInput,Action.run,jump] using e

private theorem HF (p : Fin 2) (m : Cells) (bs : List Bool) :
    Goes (H p) (putInput p (false::bs) m) 1 (D p) (putInput p bs m) := by
  have e := MacroPath.bits (P:=code) (l:=H p) (m:=(putInput p (false::bs) m).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,H,D,putInput,Action.run,jump] using e

private theorem header (p : Fin 2) (k : ℕ) (m : Cells) (t : List Bool) :
    Goes (H p) (putInput p (List.replicate k true ++ false::t) m) (k+1) (D p)
      (putInput p t {m with scratch:=List.replicate k true++m.scratch}) := by
  induction k generalizing m with
  | zero => simpa using HF p m t
  | succ k ih =>
    have st := HT p m (List.replicate k true ++ false::t)
    have eqc (c : List Bool) : List.replicate k true ++ true::c = true::(List.replicate k true ++ c) := by
      calc
        _ = (List.replicate k true ++ [true])++c := by simp
        _ = _ := by rw [←List.replicate_succ',List.replicate_succ,List.cons_append]
    have e := st.join (ih {m with scratch:=true::m.scratch})
    simpa [List.replicate_succ,eqc,Nat.add_comm 1] using e

private theorem DT (p : Fin 2) (m : Cells) (b : Bool) (t c : List Bool) :
    Goes (D p) (putInput p (b::t) {m with scratch:=true::c}) 1 (D p)
      (putInput p t {m with scratch:=c,reversed:=b::m.reversed}) := by
  have e := MacroPath.bits (P:=code) (l:=D p) (m:=(putInput p (b::t) {m with scratch:=true::c}).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,D,putInput,Action.run,jump] using e
private theorem DF (p : Fin 2) (m : Cells) :
    Goes (D p) {m with scratch:=[]} 1 (V p) {m with scratch:=[]} := by
  have e := MacroPath.bits (P:=code) (l:=D p) (m:=({m with scratch:=[]}:Cells).mem) (a:=_) (by rfl)
  simpa [code,D,V,Action.run,jump] using e

private theorem digits (p : Fin 2) (bs t : List Bool) (m : Cells) :
    Goes (D p) (putInput p (bs++t) {m with scratch:=List.replicate bs.length true})
      (bs.length+1) (V p) (putInput p t {m with scratch:=[],reversed:=bs.reverse++m.reversed}) := by
  induction bs generalizing m with
  | nil =>
    have f := DF p (putInput p t m)
    fin_cases p <;> simpa [putInput] using f
  | cons b bs ih =>
    have st := DT p m b (bs++t) (List.replicate bs.length true)
    have z := st.join (ih {m with reversed:=b::m.reversed})
    simpa [List.replicate_succ,List.append_assoc,Nat.add_comm 1] using z

private theorem VT (p : Fin 2) (m : Cells) (b : Bool) (r : List Bool) :
    Goes (V p) {m with reversed:=b::r} 1 (V p) (putWord p [b] {m with reversed:=r}) := by
  have e := MacroPath.bits (P:=code) (l:=V p) (m:=({m with reversed:=b::r}:Cells).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,V,Action.run,jump,putWord,dest] using e

private theorem VF (p : Fin 2) (m : Cells) :
    Goes (V p) {m with reversed:=[]} 1 (next p) {m with reversed:=[]} := by
  have e := MacroPath.bits (P:=code) (l:=V p) (m:=({m with reversed:=[]}:Cells).mem) (a:=_) (by rfl)
  simpa [code,V,Action.run,jump] using e

private theorem backwards (p : Fin 2) (bs : List Bool) (m : Cells) :
    Goes (V p) {m with reversed:=bs} (bs.length+1) (next p) (putWord p bs.reverse {m with reversed:=[]}) := by
  induction bs generalizing m with
  | nil => fin_cases p <;> simpa [putWord] using VF _ m
  | cons b bs ih =>
    have st := VT p m b bs
    have t := ih (putWord p [b] m)
    fin_cases p <;> simp [putWord] at st t ⊢ <;>
      first | simpa [List.append_assoc,Nat.add_comm 1] using st.join t

theorem field (p : Fin 2) (n : ℕ) (t : List Bool) (m : Cells) (hs : m.scratch=[]) (hr : m.reversed=[]) :
    Goes (H p) (putInput p (encodeNat n++t) m) (3*(n.bits.length+1)) (next p)
      (putWord p n.bits (putInput p t m)) := by
  have h := header p n.bits.length m (n.bits++t)
  have d := digits p n.bits t m
  have r := backwards p n.bits.reverse (putInput p t m)
  fin_cases p <;> simp [putInput,hs,hr] at h d r ⊢ <;>
    have z := (h.join d).join r <;>
    simpa [encodeNat,List.append_assoc,Nat.mul_comm,Nat.mul_add,Nat.mul_succ,Nat.add_assoc,hs,hr] using z

end DimensionEmitter

namespace DimensionEmitter.Extended
open DimensionEmitter
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat)
def repeatWord (m : Bool) : ℕ → List Bool
  | 0 => []
  | n+1 => block m++repeatWord m n

private theorem repeat_last (m : Bool) (n : ℕ) : repeatWord m n++block m=block m++repeatWord m n := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simp [repeatWord,List.append_assoc,ih]

private theorem remaining (bs : List Bool) (s : Cells) (m : Bool) (type : s.itemCount=[m]) :
    Goes (A 0) {s with input:=bs} (bs.length+1) (A 5) {s with input:=suffix m,divisor:=true::s.divisor} := by
  induction bs with
  | nil =>
    have a := MacroPath.bits (P:=code) (l:=A 0) (m:=({s with input:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,A,Action.run,jump,pushRun,type] using a
  | cons b bs ih =>
    have a := MacroPath.bits (P:=code) (l:=A 0) (m:=({s with input:=b::bs}:Cells).mem) (a:=_) (by rfl)
    have one : Goes (A 0) {s with input:=b::bs} 1 (A 0) {s with input:=bs} := by
      simpa [code,A,Action.run,jump] using a
    simpa [Nat.add_comm 1] using one.join ih

private theorem loop (n K : ℕ) (s : Cells) (m : Bool) (type : s.itemCount=[m])
    (v : val s.dimension=n) (unit : s.divisor=[true]) (zero : s.product=[])
    (f : s.flag=[]) (sp : s.spare=[]) (lim : s.dimension.length≤K) (pos : 1≤K) :
    ∃ ds : List Bool, Runs (A 5) s ((n+1)*(10*(K+3))) (A 7)
      {s with dimension:=ds,flag:=[],input:=repeatWord m n++s.input} ∧ ds.length≤K := by
  induction n generalizing s with
  | zero =>
    have check := testDim s f sp unit zero
    simp [v] at check
    refine ⟨s.dimension,?_,lim⟩
    simpa [repeatWord] using check.mono (show 3*s.dimension.length+7≤(0+1)*(10*(K+3)) by omega)
  | succ n ih =>
    have check := testDim s f sp unit zero
    simp [v] at check
    obtain ⟨ds,dec,eq,len⟩ := decrement {s with flag:=[]} rfl sp unit m type n v
    let t := {s with dimension:=ds,flag:=[],input:=block m++s.input}
    have dsl : ds.length≤K := by change ds.length ≤ max s.dimension.length 1 at len;omega
    obtain ⟨ws,lp,ll⟩ := ih t type eq unit zero rfl sp dsl
    have path := (check.seq dec).seq lp
    refine ⟨ws,?_,ll⟩
    have tm : 3*s.dimension.length+7+(3*(s.dimension.length+1)+8)+((n+1)*(10*(K+3)))≤(n+1+1)*(10*(K+3)) := by
      rw [Nat.succ_mul (n+1)];omega
    simpa [t,repeatWord,←List.append_assoc,repeat_last] using path.mono tm

private theorem bitsValue (n : ℕ) : val n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b k h ih => rw [Nat.bits_append_bit _ _ h,val,ih,Nat.bit_val];omega

private theorem isolatedWord (w : List Bool) : ({input:=w}:Cells).mem = isolated (reg tape) w := by
  funext k
  cases k with
  | inl z => cases z <;>rfl
  | inr z => cases z <;>rfl

def raw (B d : ℕ) (t : List Bool) := encodeNat B++(encodeNat d++t)
def result (m : Bool) (d : ℕ) := tagWord m++(repeatWord m d ++ suffix m)

theorem emitLarge (m : Bool) (B d : ℕ) (t : List Bool) :
    OutputsWithin (machine m) (raw B d t) (result m d) (100*((raw B d t).length+1+d)^2) := by
  let word := raw B d t
  let K := word.length+1
  let initCells : Cells := {input:=word}
  let initial := {initCells with itemCount:=[m]}
  have a := MacroPath.bits (P:=code) (l:=init m) (m:=initCells.mem) (a:=_) (by rfl)
  have start : Goes (init m) initCells 1 (H 0) initial := by simpa [code,init,initial,Action.run,jump] using a
  let s0 : Cells := {itemCount:=[m]}
  let s1 := {s0 with input:=encodeNat d++t,remainder:=B.bits}
  let s2 := {s1 with input:=t,dimension:=d.bits}
  let s3 := {s2 with input:=suffix m,divisor:=[true]}
  have f0 : Goes (H 0) initial (3*(B.bits.length+1)) (H 1) s1 := by
    simpa [initial,initCells,word,raw,s0,s1,putWord,putInput,next] using field 0 B (encodeNat d++t) s0 rfl rfl
  have f1 : Goes (H 1) s1 (3*(d.bits.length+1)) (A 0) s2 := by
    simpa [s1,s2,s0,putWord,putInput,next] using field 1 d t s1 rfl rfl
  have purge : Goes (A 0) s2 (t.length+1) (A 5) s3 := remaining t s2 m rfl
  have size : 2*(B.bits.length+d.bits.length)+2+t.length+1=K := by simp [K,word,raw,encodeNat];omega
  obtain ⟨ds,lp,dsl⟩ := loop d K s3 m rfl (bitsValue _) rfl rfl rfl rfl (by dsimp [s3,s2];omega) (by omega)
  let z := {s3 with dimension:=ds,flag:=[],input:=repeatWord m d++suffix m}
  let out := {z with input:=result m d}
  have g := MacroPath.bits (P:=code) (l:=A 7) (m:=z.mem) (a:=_) (by rfl)
  have finish : Goes (A 7) z 1 (old (OneTypeTM.C 0)) out := by
    simpa [z,s3,s2,s1,s0,out,code,A,Action.run,jump,result,pushRun] using g
  have done := clean out rfl rfl
  obtain ⟨n,nt,path⟩:=((((((smallRun start).seq (smallRun f0)).seq (smallRun f1)).seq (smallRun purge)).seq lp).seq (smallRun finish)).seq done
  apply MacroPath.outputs (t:=n)
  · rw [←isolatedWord,←isolatedWord];exact path
  · have c : OneTypeTM.costClear out≤3*K+14 := by simp [out,z,s3,s2,s1,s0,OneTypeTM.costClear];omega
    have bd : d+1≤K+d := by omega
    have bound:=Nat.mul_le_mul_right (10*(K+3)) bd
    change n≤100*(K+d)^2
    nlinarith only [nt,bound,c,size]
end DimensionEmitter.Extended

set_option synthInstance.maxSize 2000
namespace CenteredOracle
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks HMBinPacking ExponomialAssortment.FPTAS
abbrev L := Fin 9 ⊕ WordLabel DimensionEmitter.L
private def baseEq : DecidableEq DimensionEmitter.L := inferInstance
local instance wordEq : DecidableEq (WordLabel DimensionEmitter.L) := by
  letI : DecidableEq DimensionEmitter.L := baseEq
  exact inferInstanceAs (DecidableEq (DimensionEmitter.L ⊕ (DimensionEmitter.L × (Fin 4 × Bool))))
instance : DecidableEq L := inferInstanceAs (DecidableEq (Fin 9 ⊕ WordLabel DimensionEmitter.L))
def A (j : Fin 9) : L := .inl j
def sub (l : WordLabel DimensionEmitter.L) : L := .inr l
def jump (j : L) : Action (Bank R) L := .stop (some j)
def put (r : R) : List Bool→Action (Bank R) L→Action (Bank R) L
  | [],a=>a
  | b::bs,a=>put r bs (.push (reg r) b a)
def code : L→Action (Bank R) L
  | .inr l => (wordCode DimensionEmitter.code l).rename (Function.Embedding.refl _)
        (fun o=>o.elim (some (A 1)) (fun k=>some (sub k)))
  | .inl j => match j.val with
    | 0 => .push (reg tape) false (jump (sub (.inl (DimensionEmitter.init false))))
    | 1 => .peek (reg tape) (fun x=>if x.isSome then .drop (reg tape)
      (put first (encodeRat 0) (put second (encodeInt 0) (jump (A 1)))) else jump (A 2))
    | 2 => .stop none
    | 3 => .peek (reg first) (fun v=> .drop (reg first) (jump (if v.getD false then A 6 else A 4)))
    | 4 => .peek (reg first) (fun v=>if v.isSome then .drop (reg first) (jump (A 4)) else jump (A 5))
    | 5 => .peek (reg second) (fun v=>if v.isSome then .drop (reg second) (jump (A 5)) else .push (reg tape) false (.stop none))
    | 6 => .peek (reg second) (fun v=>match v with
      | none=>jump (A 7) | some b=>.drop (reg second) (.push (reg rev) b (jump (A 6))))
    | 7 => .peek (reg rev) (fun v=>match v with
      | none=> .push (reg tape) true (.stop none) | some b=>.drop (reg rev) (.push (reg tape) b (jump (A 7))))
    | _=>.stop none
def oracle := Oracle.model (A 0) (reg tape) (reg first) (A 2) (A 3) code
abbrev Goes (O : List Bool→List Bool) (Q : ℕ) (l : L) (s : Cells) (n : ℕ) (j : Option L) (t : Cells) :=
   Oracle.Trace code O (reg first) (A 2) (A 3) Q (some l) s.mem n j t.mem
private theorem putFirst (w : List Bool) (a : Action (Bank R) L) (s : Cells) :
    (put first w a).run s.mem=a.run ({s with prep:=w++s.prep}:Cells).mem := by
  induction w generalizing a with
  | nil=>rfl
  | cons b bs ih=>rw [put,ih];simp [Action.run]
private theorem putSecond (w : List Bool) (a : Action (Bank R) L) (s : Cells) :
    (put second w a).run s.mem=a.run ({s with todo:=w++s.todo}:Cells).mem := by
  induction w generalizing a with
  | nil=>rfl
  | cons b bs ih=>rw [put,ih];simp [Action.run]
def repeating (w : List Bool) : ℕ→List Bool
  | 0=>[]
  | d+1=>w++repeating w d
private theorem repLast (w : List Bool) (n : ℕ) : repeating w n++w=w++repeating w n := by
  induction n with
  | zero=>simp [repeating]
  | succ n ih=>simp [repeating,List.append_assoc,ih]

theorem prepare (O : List Bool→List Bool) (Q n : ℕ) (s : Cells) :
    Goes O Q (A 1) {s with input:=List.replicate n false} (n+1) (A 2)
      {s with input:=[],prep:=repeating (encodeRat 0) n++s.prep,todo:=repeating (encodeInt 0) n++s.todo} := by
  induction n generalizing s with
  | zero =>
    have p:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=A 3) (Q:=Q) (m:=({s with input:=[]}:Cells).mem)
      (show A 1≠A 2 by decide)
    simpa [Goes,code,A,Action.run,jump,repeating] using p
  | succ n ih =>
    let t:={s with prep:=encodeRat 0++s.prep,todo:=encodeInt 0++s.todo}
    have p:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=A 3) (Q:=Q)
      (m:=({s with input:=false::List.replicate n false}:Cells).mem) (show A 1≠A 2 by decide)
    have st : Goes O Q (A 1) {s with input:=false::List.replicate n false} 1 (A 1) {t with input:=List.replicate n false} := by
      simpa [Goes,code,A,Action.run,jump,t,putFirst,putSecond] using p
    simpa [t,repeating,List.replicate_succ,←List.append_assoc,repLast,Nat.add_comm 1] using st.join (ih t)
end CenteredOracle

namespace CenteredOracle
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks HMBinPacking ExponomialAssortment.FPTAS
theorem clear4 (O : List Bool→List Bool) (Q : ℕ) (s : Cells) (bs : List Bool) :
    Goes O Q (A 4) {s with prep:=bs} (bs.length+1) (A 5) {s with prep:=[]} := by
  induction bs with
  | nil =>
    have st:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=A 3) (Q:=Q)
      (m:=({s with prep:=[]}:Cells).mem) (show A 4≠A 2 by decide)
    simpa [Goes,code,A,Action.run,jump] using st
  | cons b bs ih =>
    have st:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=A 3) (Q:=Q)
      (m:=({s with prep:=b::bs}:Cells).mem) (show A 4≠A 2 by decide)
    have one : Goes O Q (A 4) {s with prep:=b::bs} 1 (A 4) {s with prep:=bs} := by
      simpa [Goes,code,A,Action.run,jump] using st
    simpa [Nat.add_comm 1] using one.join ih
theorem clear5 (O : List Bool→List Bool) (Q : ℕ) (s : Cells) (bs : List Bool) :
    Goes O Q (A 5) {s with todo:=bs} (bs.length+1) none {s with todo:=[],input:=false::s.input} := by
  induction bs with
  | nil =>
    have st:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=A 3) (Q:=Q)
      (m:=({s with todo:=[]}:Cells).mem) (show A 5≠A 2 by decide)
    simpa [Goes,code,A,Action.run,jump] using st
  | cons b bs ih =>
    have st:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=A 3) (Q:=Q)
      (m:=({s with todo:=b::bs}:Cells).mem) (show A 5≠A 2 by decide)
    have one : Goes O Q (A 5) {s with todo:=b::bs} 1 (A 5) {s with todo:=bs} := by
      simpa [Goes,code,A,Action.run,jump] using st
    simpa [Nat.add_comm 1] using one.join ih
theorem move6 (O : List Bool→List Bool) (Q : ℕ) (s : Cells) (bs : List Bool) :
    Goes O Q (A 6) {s with todo:=bs} (bs.length+1) (A 7) {s with todo:=[],reversed:=bs.reverse++s.reversed} := by
  induction bs generalizing s with
  | nil =>
    have st:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=A 3) (Q:=Q)
      (m:=({s with todo:=[]}:Cells).mem) (show A 6≠A 2 by decide)
    simpa [Goes,code,A,Action.run,jump] using st
  | cons b bs ih =>
    have st:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=A 3) (Q:=Q)
      (m:=({s with todo:=b::bs}:Cells).mem) (show A 6≠A 2 by decide)
    have one : Goes O Q (A 6) {s with todo:=b::bs} 1 (A 6) {s with todo:=bs,reversed:=b::s.reversed} := by
      simpa [Goes,code,A,Action.run,jump] using st
    simpa [Nat.add_comm 1,List.append_assoc] using one.join (ih {s with reversed:=b::s.reversed})
theorem move7 (O : List Bool→List Bool) (Q : ℕ) (s : Cells) (bs : List Bool) :
    Goes O Q (A 7) {s with reversed:=bs} (bs.length+1) none {s with reversed:=[],input:=true::(bs.reverse++s.input)} := by
  induction bs generalizing s with
  | nil =>
    have st:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=A 3) (Q:=Q)
      (m:=({s with reversed:=[]}:Cells).mem) (show A 7≠A 2 by decide)
    simpa [Goes,code,A,Action.run,jump] using st
  | cons b bs ih =>
    have st:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=A 3) (Q:=Q)
      (m:=({s with reversed:=b::bs}:Cells).mem) (show A 7≠A 2 by decide)
    have one : Goes O Q (A 7) {s with reversed:=b::bs} 1 (A 7) {s with reversed:=bs,input:=b::s.input} := by
      simpa [Goes,code,A,Action.run,jump] using st
    simpa [Nat.add_comm 1,List.append_assoc] using one.join (ih {s with input:=b::s.input})
end CenteredOracle

namespace CenteredOracle
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks HMBinPacking ExponomialAssortment.FPTAS

private theorem flattenRep {w : List Bool} (d : ℕ) : repeating w d=(List.ofFn (fun _ : Fin d=>w)).flatten := by
  induction d with
  | zero=>simp [repeating]
  | succ d ih=>simp [repeating,List.ofFn_succ,ih]

theorem qVec (n : ℕ) : repeating (encodeRat 0) n=encVec (fun _ : Fin n=>(0:ℚ)) := by rw [flattenRep,encVec]
theorem xVec (n : ℕ) : repeating (encodeInt 0) n=encodeIntVec (fun _ : Fin n=>(0:ℤ)) := by rw [flattenRep,encodeIntVec]
theorem repLen (w : List Bool) (n : ℕ) : (repeating w n).length=n*w.length := by
  induction n with
  | zero=>simp [repeating]
  | succ n h=>simp [repeating,h,Nat.succ_mul,Nat.add_comm]

private theorem zeros (n : ℕ) : DimensionEmitter.Extended.result false n=List.replicate n false := by
  have rep : DimensionEmitter.Extended.repeatWord false n=List.replicate n false := by
    induction n with
    | zero=>rfl
    | succ n ih=>simp [DimensionEmitter.Extended.repeatWord,DimensionEmitter.block,ih,List.replicate_succ]
  simp [DimensionEmitter.Extended.result,DimensionEmitter.tagWord,DimensionEmitter.suffix,rep]

private theorem isol (w : List Bool) : ({input:=w}:Cells).mem = isolated (reg tape) w := by
  funext k;cases k with | inl r=>cases r <;>rfl | inr d=>cases d <;>rfl

theorem inspect (O : List Bool→List Bool) (n : ℕ) (t : List Bool) (bit : Bool) (extra : List Bool)
    (reply : O (repeating (encodeRat 0) n)=bit::extra) (yes : bit=true→extra=[]) :
    let w:=encodeNat n++t
    let q:=(repeating (encodeRat 0) n).length
    ORunsWithin oracle O w (if bit then true::repeating (encodeInt 0) n else [false])
      (100*(w.length+n+2)^2+extra.length+10*n+15) q := by
  let w:=encodeNat n++t
  let cert:=repeating (encodeInt 0) n
  let query:=repeating (encodeRat 0) n
  let Q:=query.length
  let zero:Cells:={}
  let m:Cells:={input:=w}
  have start:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=A 3) (Q:=Q) (m:=m.mem) (show A 0≠A 2 by decide)
  have start' : Goes O Q (A 0) m 1 (sub (.inl (DimensionEmitter.init false))) ({input:=false::w}:Cells) := by
    simpa [Goes,m,code,A,jump,Action.run] using start
  have os:=DimensionEmitter.Extended.emitLarge false 0 n t
  have raw : DimensionEmitter.Extended.raw 0 n t=false::w := by simp [DimensionEmitter.Extended.raw,w,encodeNat]
  rw [raw,zeros] at os
  obtain ⟨tt,tm,path⟩:=ofOutputs os
  have module:=Oracle.lift path O (reg first) (A 2) (A 3) Q code sub (some (A 1)) (by intro j;simp [sub,A]) (by intro j;rfl)
  rw [←isol,←isol] at module
  have prep:=prepare O Q n zero
  let u:Cells:={prep:=query,todo:=cert}
  have before : Goes O Q (A 0) m (1+tt+(n+1)) (A 2) u := by
    simpa [cert,query,u,zero] using (start'.join module).join prep
  have ac:=Oracle.Trace.call (program:=code) (O:=O) (qs:=reg first) (ask:=A 2) (resume:=A 3) (Q:=Q)
    (m:=u.mem) (show (u.mem (reg first)).length≤Q from le_rfl)
  let v:Cells:={prep:=bit::extra,todo:=cert}
  have changeQ : Goes O Q (A 2) u 1 (A 3) v := by simpa [Goes,u,v,query,reply] using ac
  have scanned:=before.join changeQ
  have inspectBit:=Oracle.Trace.bits (program:=code) (O:=O) (qs:=reg first) (resume:=A 3) (Q:=Q)
    (m:=v.mem) (show A 3≠A 2 by decide)
  have lc : cert.length=2*n := by
    rw [show cert=repeating (encodeInt 0) n from rfl,repLen,show (encodeInt 0).length=2 by decide,Nat.mul_comm]
  have clock : tt≤100*(w.length+n+2)^2 := by
    rwa [show (false::w).length+1+n=w.length+n+2 by simp;omega] at tm
  cases bit with
  | false =>
    let z:Cells:={prep:=extra,todo:=cert}
    have step : Goes O Q (A 3) v 1 (A 4) z := by simpa [Goes,code,v,z,A,Action.run,jump] using inspectBit
    have drop:=clear4 O Q z extra
    have done:=clear5 O Q ({todo:=cert}:Cells) cert
    have path:=((scanned.join step).join drop).join done
    change Oracle.Trace code O (reg first) (A 2) (A 3) Q (some (A 0)) ({input:=w}:Cells).mem _ none ({input:=[false]}:Cells).mem at path
    rw [isol,isol] at path
    apply path.registered
    change 1+tt+(n+1)+1+1+(extra.length+1)+(cert.length+1)≤100*(w.length+n+2)^2+extra.length+10*n+15
    omega
  | true =>
    have nil:=yes rfl
    subst extra
    let z:Cells:={todo:=cert}
    have step : Goes O Q (A 3) v 1 (A 6) z := by simpa [Goes,code,v,z,A,Action.run,jump] using inspectBit
    have flip:=move6 O Q z cert
    have back:=move7 O Q ({reversed:=cert.reverse}:Cells) cert.reverse
    simp [z] at flip back
    have path:=((scanned.join step).join flip).join back
    change Oracle.Trace code O (reg first) (A 2) (A 3) Q (some (A 0)) ({input:=w}:Cells).mem _ none ({input:=true::cert}:Cells).mem at path
    rw [isol,isol] at path
    apply path.registered
    change 1+tt+(n+1)+1+1+(cert.length+1)+(cert.length+1)≤100*(w.length+n+2)^2+0+10*n+15
    omega
end CenteredOracle

open HMBinPacking ExponomialAssortment.FPTAS
namespace CenteredOracle

private theorem natLength (k : ℕ) : (encodeNat k).length≤2*k+1 := by
  have size : k.size≤k := Nat.size_le.mpr (Nat.lt_two_pow_self)
  simp [encodeNat,Nat.size_eq_bits_len];omega

private theorem zero_mem {n : ℕ} {Q : Set (Fin n→ℝ)} (cv : Convex ℝ Q)
    (symm : ∀ x∈Q,-x∈Q) (ne : Q.Nonempty) : (0:Fin n→ℝ)∈Q := by
  obtain ⟨x,hx⟩:=ne
  have m := cv hx (symm x hx) (show (0:ℝ)≤1/2 by norm_num) (show (0:ℝ)≤1/2 by norm_num)
    (show (1:ℝ)/2+1/2=1 by norm_num)
  have z : (1/2:ℝ) • x+(1/2:ℝ) • (-x)=0 := by simp
  simpa [z] using m

private theorem budgets (e n σ : ℕ) (hn : 1≤n) (hnσ : n≤σ)
    (N lf : ℕ) (raw : N≤4*σ+2) (hlen : lf≤(σ+5*n)^e) :
    let c:=4*e+16
    100*(N+n+2)^2+lf+10*n+15 ≤ 2^(c*n^3)*σ^c ∧ 5*n≤2^(c*n^3)*σ^c := by
  let c:=4*e+16
  have pos : 1≤σ := by omega
  have L : (N+n+2)^2 ≤ (9*σ)^2 := Nat.pow_le_pow_left (by omega) _
  have X : (σ+5*n)^e≤(6*σ)^e := Nat.pow_le_pow_left (by omega) _
  rw [Nat.mul_pow] at X
  have factor : 6^e≤16^e := Nat.pow_le_pow_left (by decide) _
  have z : 1≤16^e := Nat.one_le_pow _ _ (by decide)
  have sq : σ^2≤σ^c := Nat.pow_le_pow_right pos (by dsimp [c];omega)
  have big : σ^e≤σ^c := Nat.pow_le_pow_right pos (by dsimp [c];omega)
  have small : σ≤σ^2 := by nlinarith only [pos]
  have rest : 100*(N+n+2)^2+10*n+15≤8125*σ^2 := by nlinarith only [L,small,hnσ,pos]
  have coef : 8125+6^e≤2^c := by
    change _ ≤ 2^(4*e+16);rw [pow_add,pow_mul]
    norm_num;nlinarith only [factor,z]
  have d3 : 1≤n^3 := Nat.one_le_pow _ _ hn
  have tpow := Nat.pow_le_pow_right (show 1≤2 by decide) (show c≤c*n^3 by simpa using Nat.mul_le_mul_left c d3)
  have total := Nat.mul_le_mul_right (σ^c) (coef.trans tpow)
  rw [Nat.add_mul] at total
  have ss := Nat.mul_le_mul_left 8125 sq
  have b := Nat.mul_le_mul_left (6^e) big
  constructor <;> change _ ≤ 2^(c*n^3)*σ^c <;> omega
end CenteredOracle

/-- The registered integer-feasibility oracle theorem for centrally symmetric
convex sets, in every dimension and at every admissible radius. -/
theorem solution :
    ∀ e : ℕ, ∃ (c : ℕ) (OM : OracleMachine),
      ∀ n : ℕ, 1≤n → ∀ T : ℚ, 1≤T → ∀ σ : ℕ, n+enc T≤σ →
      ∀ Q : Set (Fin n→ℝ), IsClosed Q → Convex ℝ Q → (∀ x∈Q,∀ i,|x i|≤(T:ℝ)) →
      (∀ x∈Q,-x∈Q) → ∀ O : List Bool→List Bool,
        (∀ y : Fin n→ℚ, IsSepAnswer Q y (O (encVec y)) ∧ (O (encVec y)).length≤(σ+(encVec y).length)^e) →
        ∃ w : List Bool, ORunsWithin OM O (encodeNat n++encodeRat T++encodeNat σ) w
          (2^(c*n^3)*σ^c) (2^(c*n^3)*σ^c) ∧
          ((∃ x : Fin n→ℤ, w=true::encodeIntVec x ∧ zCast x∈Q) ∨
           (w=[false] ∧ ∀ x : Fin n→ℤ,zCast x∉Q)) := by
  intro e
  refine ⟨4*e+16,CenteredOracle.oracle,?_⟩
  intro n hn T _ σ size Q _ convex _ symm O oracle
  let y:Fin n→ℚ:=fun _=>0
  let raw:=encodeNat n++encodeRat T++encodeNat σ
  let tail:=encodeRat T++encodeNat σ
  let out:=O (encVec y)
  obtain ⟨response,ol⟩:=oracle y
  have yzero : qCast y=(0:Fin n→ℝ) := by ext;simp [qCast,y]
  have castZero : zCast (fun _ : Fin n=>(0:ℤ))=(0:Fin n→ℝ) := by ext;simp [zCast]
  have query : CenteredOracle.repeating (encodeRat 0) n=encVec y := CenteredOracle.qVec n
  have qlen : (encVec y).length=5*n := by
    rw [←query,CenteredOracle.repLen,show (encodeRat 0).length=5 by decide,Nat.mul_comm]
  rw [qlen] at ol
  have lenRaw : raw.length≤4*σ+2 := by
    have nn:=CenteredOracle.natLength n
    have sn:=CenteredOracle.natLength σ
    change n+(encodeRat T).length≤σ at size
    simp [raw];omega
  have tm (bit : Bool) (xs : List Bool) (h : out=bit::xs) (hb : bit=true→xs=[]) :
      ORunsWithin CenteredOracle.oracle O raw (if bit then true::encodeIntVec (fun _ : Fin n=>(0:ℤ)) else [false])
        (2^((4*e+16)*n^3)*σ^(4*e+16)) (2^((4*e+16)*n^3)*σ^(4*e+16)) := by
    have hl : xs.length≤(σ+5*n)^e := by change out.length≤_ at ol;rw [h,List.length_cons] at ol;omega
    have bounds:=CenteredOracle.budgets e n σ hn (by omega) raw.length xs.length lenRaw hl
    have tt:=CenteredOracle.inspect O n tail bit xs (by rw [query];exact h) hb
    rw [query,qlen,CenteredOracle.xVec] at tt
    have eq : encodeNat n++tail=raw := by simp [tail,raw,List.append_assoc]
    rw [eq] at tt
    obtain ⟨t,cl,halt,qs⟩:=tt
    exact ⟨t,cl.trans bounds.1,halt,fun j hj c hc hc' => (qs j hj c hc hc').trans bounds.2⟩
  rcases response with ⟨h,mem⟩|⟨u,a,h,valid,strict⟩
  · refine ⟨_,tm true [] h (by simp),Or.inl ⟨fun _=>0,rfl,?_⟩⟩
    rwa [castZero,←yzero]
  · refine ⟨_,tm false _ h (by simp),Or.inr ⟨rfl,?_⟩⟩
    intro x hx
    have z:=CenteredOracle.zero_mem convex symm ⟨_,hx⟩
    have weak:=valid (qCast y) (yzero ▸ z)
    have eq : (∑ i,(u i:ℝ)*(qCast y i))=(∑ i,(u i:ℝ)*(y i:ℝ)) := rfl
    rw [eq] at weak;exact strict.not_ge weak
