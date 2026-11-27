-- Prove2me | solution 1 for HMBinPacking.empty_residue_detection_with_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:31:59.916453+00:00
-- url     : https://prove2.me/submissions/6a79e5d0-faef-4a28-b836-373c3ea106b4

import Definitions.Def_HMBinPacking_OutputsWithin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Definitions.Def_HMBinPacking_Encoding
import Mathlib.Tactic.Ring
import Theorems.Thm_HMBinPacking_lenstra_residue_optimization
import Definitions.Def_HMBinPacking_Oracles
import Mathlib.Algebra.BigOperators.Ring.Finset
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

namespace BitStacks.BranchCompose
variable {K A B : Type} [DecidableEq K]
abbrev R (K : Type) := K ⊕ Bool
abbrev L (A B : Type) := Fin 5 ⊕ (A ⊕ B)
def ix : K ↪ R K := ⟨Sum.inl,Sum.inl_injective⟩
def atA (a : A) : L A B := .inr (.inl a)
def atB (b : B) : L A B := .inr (.inr b)
def ctrl (i : Fin 5) : L A B := .inl i
def frame (m : Mem K) (saved tmp : List Bool) : Mem (R K)
  | .inl k => m k
  | .inr false => saved
  | .inr true => tmp
@[simp] theorem read {m : Mem K} {s t : List Bool} (k : K) : frame m s t (.inl k)=m k := rfl
@[simp] theorem saveWord {m : Mem K} {s t : List Bool} : frame m s t (.inr false)=s := rfl
@[simp] theorem tempWord {m : Mem K} {s t : List Bool} : frame m s t (.inr true)=t := rfl
@[simp] theorem wr (m : Mem K) (s t w : List Bool) (k : K) :
    Function.update (frame m s t) (.inl k) w=frame (Function.update m k w) s t := by
  funext j;cases j with
  | inr i => cases i <;>simp [frame,Function.update]
  | inl i => by_cases h:i=k <;>simp [frame,Function.update,h]
@[simp] theorem ws (m : Mem K) (s t w : List Bool) :
    Function.update (frame m s t) (.inr false) w=frame m w t := by
  funext j;cases j with
  | inr i => cases i <;>simp [frame,Function.update]
  | inl i => simp [frame,Function.update]
@[simp] theorem wt (m : Mem K) (s t w : List Bool) :
    Function.update (frame m s t) (.inr true) w=frame m s w := by
  funext j;cases j with
  | inr i => cases i <;>simp [frame,Function.update]
  | inl i => simp [frame,Function.update]

def code (io : K) (ae : A) (be : B) (ac : A→Action K A) (bc : B→Action K B) :
    L A B→Action (R K) (L A B)
  | .inr (.inl a) => (ac a).rename ix (fun l=>l.elim (some (ctrl 2)) (fun v=>some (atA v)))
  | .inr (.inr b) => (bc b).rename ix (fun l=>l.elim none (fun v=>some (atB v)))
  | .inl i => match i.val with
    | 0 => .peek (.inl io) (fun v=>match v with
      | some b=>.drop (.inl io) (.push (.inr false) b (.push (.inr true) b (.stop (some (ctrl 0)))))
      | none=>.stop (some (ctrl 1)))
    | 1 => .peek (.inr true) (fun v=>match v with
      | some b=>.drop (.inr true) (.push (.inl io) b (.stop (some (ctrl 1))))
      | none=>.stop (some (atA ae)))
    | 2 => .peek (.inl io) (fun v=>if v.getD false then .stop (some (ctrl 3)) else .drop (.inl io) (.stop (some (ctrl 4))))
    | 3 => .peek (.inr false) (fun v=>if v.isSome then .drop (.inr false) (.stop (some (ctrl 3))) else .stop none)
    | _ => .peek (.inr false) (fun v=>match v with
      | some b=>.drop (.inr false) (.push (.inl io) b (.stop (some (ctrl 4))))
      | none=>.stop (some (atB be)))

section
variable [Fintype K] [Fintype A] [Fintype B]
variable (io : K) (ae : A) (be : B) (ac : A→Action K A) (bc : B→Action K B)
local notation "P" => code io ae be ac bc
local notation "F" => fun (w a b : List Bool) => frame (isolated io w) a b

private theorem readIO (s : List Bool) : isolated io s io=s := by simp [isolated,Turing.initList,machine];rfl
private theorem setIO (s t : List Bool) : Function.update (isolated io s) io t=isolated io t := by
  funext i;by_cases e:i=io
  · subst i;simp [readIO]
  · simp [Function.update,isolated,Turing.initList,machine,e]

private theorem clone1 (w a b : List Bool) : Path P (some (ctrl 0)) (F w a b) (w.length+1)
    (some (ctrl 1)) (F [] (w.reverse++a) (w.reverse++b)) := by
  induction w generalizing a b with
  | nil => simpa [code,ctrl,Action.run,readIO] using Path.step (code:=P) (l:=ctrl 0) (m:=F [] a b)
  | cons v vs ih =>
    have st:=Path.step (code:=P) (l:=ctrl 0) (m:=F (v::vs) a b)
    have step : Path P (some (ctrl 0)) (F (v::vs) a b) 1 (some (ctrl 0)) (F vs (v::a) (v::b)) := by
      simpa [code,ctrl,Action.run,readIO,setIO] using st
    simpa [List.append_assoc,Nat.add_comm 1] using step.join (ih (v::a) (v::b))

private theorem rewind (w a b : List Bool) : Path P (some (ctrl 1)) (F w a b) (b.length+1)
    (some (atA ae)) (F (b.reverse++w) a []) := by
  induction b generalizing w with
  | nil => simpa [code,ctrl,Action.run] using Path.step (code:=P) (l:=ctrl 1) (m:=F w a [])
  | cons v vs ih =>
    have st:=Path.step (code:=P) (l:=ctrl 1) (m:=F w a (v::vs))
    have step : Path P (some (ctrl 1)) (F w a (v::vs)) 1 (some (ctrl 1)) (F (v::w) a vs) := by
      simpa [code,ctrl,Action.run,readIO,setIO] using st
    simpa [List.append_assoc,Nat.add_comm 1] using step.join (ih (v::w))

private theorem wipe (w a : List Bool) : Path P (some (ctrl 3)) (F w a []) (a.length+1) none (F w [] []) := by
  induction a with
  | nil => simpa [code,ctrl,Action.run] using Path.step (code:=P) (l:=ctrl 3) (m:=F w [] [])
  | cons v vs ih =>
    have st:=Path.step (code:=P) (l:=ctrl 3) (m:=F w (v::vs) [])
    have step : Path P (some (ctrl 3)) (F w (v::vs) []) 1 (some (ctrl 3)) (F w vs []) := by
      simpa [code,ctrl,Action.run] using st
    simpa [Nat.add_comm 1] using step.join ih

private theorem restore (w a : List Bool) : Path P (some (ctrl 4)) (F w a []) (a.length+1) (some (atB be)) (F (a.reverse++w) [] []) := by
  induction a generalizing w with
  | nil => simpa [code,ctrl,Action.run] using Path.step (code:=P) (l:=ctrl 4) (m:=F w [] [])
  | cons v vs ih =>
    have st:=Path.step (code:=P) (l:=ctrl 4) (m:=F w (v::vs) [])
    have step : Path P (some (ctrl 4)) (F w (v::vs) []) 1 (some (ctrl 4)) (F (v::w) vs []) := by
      simpa [code,ctrl,Action.run,readIO,setIO] using st
    simpa [List.append_assoc,Nat.add_comm 1] using step.join (ih (v::w))

private theorem framed (w : List Bool) : F w [] [] = isolated (.inl io : R K) w := by
  funext i
  cases i with
  | inl k => by_cases h:k=io <;>simp [frame,isolated,Turing.initList,machine,h]
  | inr v => cases v <;>simp [frame,isolated,Turing.initList,machine]

private theorem exactFrame {m n : Mem K} {s t : List Bool} {w : Mem (R K)}
    (agree : Agrees ix n w) (keep : ∀ k,(∀ j,ix j ≠ k)→w k=frame m s t k) : w=frame n s t := by
  funext k;cases k with
  | inl a => exact agree a
  | inr b => cases b <;> exact keep _ (by intro i;simp [ix])

def guarded := machine (ctrl 0) (.inl io : R K) P

theorem run {w out : List Bool} {bit : Bool} {ta tb : ℕ}
    (pred : HMBinPacking.OutputsWithin (machine ae io ac) w [bit] ta)
    (onFalse : bit=false→HMBinPacking.OutputsWithin (machine be io bc) w out tb) :
    HMBinPacking.OutputsWithin (guarded io ae be ac bc) w (if bit then [true] else out)
      (ta+tb+3*w.length+4) := by
  obtain ⟨n,nt,a⟩:=ofOutputs pred
  have p0:=clone1 io ae be ac bc w [] []
  have p1:=rewind io ae be ac bc [] w.reverse w.reverse
  simp at p0 p1
  obtain ⟨endA,sub,ag,kept⟩:=a.rename ix atA (some (ctrl 2)) P (by intro l;rfl)
    (F w w.reverse []) (by intro i;rfl)
  have mid:=exactFrame ag kept
  rw [mid] at sub
  have head:=(p0.join p1).join sub
  cases bit with
  | true =>
    have st:=Path.step (code:=P) (l:=ctrl 2) (m:=F [true] w.reverse [])
    have check : Path P (some (ctrl 2)) (F [true] w.reverse []) 1 (some (ctrl 3)) (F [true] w.reverse []) := by
      simpa [code,ctrl,Action.run,readIO] using st
    have fin:=(head.join check).join (wipe io ae be ac bc [true] w.reverse)
    have checked : Path P (some (ctrl 0)) (isolated (.inl io) w) (w.length+1+(w.length+1)+n+1+(w.reverse.length+1)) none (isolated (.inl io) [true]) := by
      rw [←framed io w,←framed io [true]];exact fin
    exact checked.outputs (by rw [List.length_reverse];omega)
  | false =>
    obtain ⟨k,kt,b⟩:=ofOutputs (onFalse rfl)
    have st:=Path.step (code:=P) (l:=ctrl 2) (m:=F [false] w.reverse [])
    have check : Path P (some (ctrl 2)) (F [false] w.reverse []) 1 (some (ctrl 4)) (F [] w.reverse []) := by
      simpa [code,ctrl,Action.run,readIO,setIO] using st
    have rr:=restore io ae be ac bc [] w.reverse
    simp at rr
    obtain ⟨endB,pathB,agB,keptB⟩:= b.rename ix atB none P (by intro l;rfl) (F w [] []) (by intro j;rfl)
    rw [exactFrame agB keptB] at pathB
    have fin:=((head.join check).join rr).join pathB
    have checked : Path P (some (ctrl 0)) (isolated (.inl io) w) (w.length+1+(w.length+1)+n+1+(w.length+1)+k) none (isolated (.inl io) out) := by
      rw [←framed io w,←framed io out];exact fin
    exact checked.outputs (by omega)
end
end BitStacks.BranchCompose

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

namespace ResidueWeight
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
abbrev L := OneTypeTM.L ⊕ ((Fin 3 × Fin 6) ⊕ (Fin 15 ⊕ (Bool × Fin 4)))
def old (l : OneTypeTM.L) : L := .inl l
def H (p : Fin 6) : L := .inr (.inl (0,p))
def D (p : Fin 6) : L := .inr (.inl (1,p))
def V (p : Fin 6) : L := .inr (.inl (2,p))
def A (j : Fin 15) : L := .inr (.inr (.inl j))
def M (right : Bool) (j : Fin 4) : L := .inr (.inr (.inr (right,j)))
def jump (l : L) : Action (Bank R) L := .stop (some l)
def next (p : Fin 6) : L := match p.val with
 | 0 => H 1 | 1 => A 0 | 2 => A 3 | 3 => H 4 | 4 => M false 0 | _ => A 7
def src (p : Fin 6) : R := if p=4 then first else tape
def dest (p : Fin 6) : R := match p.val with | 0 => rem | 1 => dim | 3 => bins | _ => den
def factor (right : Bool) : R := if right then rem else den
def accum (right : Bool) : R := if right then prod else items
def code : L → Macro R L
  | .inl l => (OneTypeTM.code l).mapLabels old
  | .inr (.inl (tag,p)) =>
    if tag=0 then .bits (.peek (reg (src p)) (fun v =>
      .drop (reg (src p)) (if v.getD false then .push (reg width) true (jump (H p)) else jump (D p))))
    else if tag=1 then .bits (.peek (reg width) (fun v => if v.isSome then
      .drop (reg width) (.peek (reg (src p)) (fun b => .drop (reg (src p))
        (.push (reg rev) (b.getD false) (jump (D p))))) else jump (V p)))
    else .bits (.peek (reg rev) (fun b => match b with
      | none => jump (next p) | some bit => .drop (reg rev) (if p=2 ∨ p=5 then jump (V p)
        else .push (reg (dest p)) bit (jump (V p)))))
  | .inr (.inr (.inl j)) => match j.val with
    | 0 => .bits (.peek (reg tape) (fun v => match v with
         | none => jump (A 1) | some b => .drop (reg tape) (.push (reg second) b (jump (A 0)))))
    | 1 => .bits (.peek (reg second) (fun v => match v with
         | none => .push (reg dim) false (.push (reg den) true (jump (H 2)))
         | some b => .drop (reg second) (.push (reg tape) b (.push (reg first) b (jump (A 1))))))
    | 3 => .binary .sub dim den (by decide) (A 4)
    | 4 => .bits (.drop tmp (.push (reg second) true (jump (A 5))))
    | 5 => .binary .le dim prod (by decide) (A 6)
    | 6 => .bits (.peek tmp (fun b => .drop tmp (if b.getD false then .drop (reg den) (jump (H 5)) else jump (H 2))))
    | 7 => .bits (.peek (reg second) (fun b=>if b.isSome then .drop (reg second) (.drop (reg second) (jump (H 3))) else jump (A 10)))
    | 8 => .bits (.peek (reg bins) (fun b => if b.isSome then .drop (reg bins) (jump (A 8)) else jump (A 7)))
    | 10 => .bits (.peek (reg tape) (fun b=>if b.isSome then .drop (reg tape) (jump (A 10)) else jump (A 11)))
    | _ => .binary .le items rem (by decide) (old (OneTypeTM.A 9))
  | .inr (.inr (.inr (right,j))) => match j.val with
    | 0 => .bits (.peek (reg (factor right)) (fun b => match b with
           | none => jump (if right then A 9 else A 8)
           | some x => .drop (reg (factor right)) (jump (if x then M right 1 else M right 3))))
    | 1 => .binary .add (accum right) bins (by cases right <;> decide) (M right 2)
    | 2 => .bits (.drop tmp (jump (M right 3)))
    | _ => .bits (.push (reg bins) false (jump (M right 0)))
def machine := BitStacks.machine (.inl (H 0)) (reg tape) (wordCode code)
abbrev Goes (l : L) (s : Cells) (t : ℕ) (o : Option L) (z : Cells) :=
  MacroPath code (some l) s.mem t o z.mem
def Runs (l : L) (s : Cells) (bound : ℕ) (out : Option L) (t : Cells) : Prop := ∃ n ≤ bound, Goes l s n out t
theorem Runs.mono {i s a o t b} (h : Runs i s a o t) (le : a≤b) : Runs i s b o t := by
  obtain ⟨n,u,v⟩:=h; exact ⟨n,u.trans le,v⟩
theorem Runs.seq {i s a j t b k v} (h : Runs i s a (some j) t) (q : Runs j t b k v) : Runs i s (a+b) k v := by
  obtain ⟨n,u,x⟩:=h;obtain ⟨m,z,y⟩:=q;exact ⟨n+m,Nat.add_le_add u z,x.join y⟩
theorem smallRun {i s t o z} (h : Goes i s t o z) : Runs i s t o z := ⟨t,le_rfl,h⟩
end ResidueWeight

open BitStacks
open ExponomialAssortment.FPTAS (encodeNat)
namespace ResidueWeight
open OneTypeTM (Cells R)
open OneTypeTM.R

def putWord (p : Fin 6) (w : List Bool) (m : Cells) : Cells := match p.val with
  | 0 => {m with remainder:=w++m.remainder} | 1 => {m with dimension:=w++m.dimension}
  | 2 => m | 3 => {m with binCount:=w++m.binCount} | 4 => {m with divisor:=w++m.divisor} | _ => m

def putInput (p : Fin 6) (w : List Bool) (m : Cells) : Cells :=
  if p=4 then {m with prep:=w} else {m with input:=w}

private theorem HT (p : Fin 6) (m : Cells) (bs : List Bool) :
    Goes (H p) (putInput p (true::bs) m) 1 (H p)
      (putInput p bs {m with scratch:=true::m.scratch}) := by
  have e := MacroPath.bits (P:=code) (l:=H p) (m:=(putInput p (true::bs) m).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,H,putInput,src,Action.run,jump] using e

private theorem HF (p : Fin 6) (m : Cells) (bs : List Bool) :
    Goes (H p) (putInput p (false::bs) m) 1 (D p) (putInput p bs m) := by
  have e := MacroPath.bits (P:=code) (l:=H p) (m:=(putInput p (false::bs) m).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,H,D,putInput,src,Action.run,jump] using e

private theorem header (p : Fin 6) (k : ℕ) (m : Cells) (t : List Bool) :
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

private theorem DT (p : Fin 6) (m : Cells) (b : Bool) (t c : List Bool) :
    Goes (D p) (putInput p (b::t) {m with scratch:=true::c}) 1 (D p)
      (putInput p t {m with scratch:=c,reversed:=b::m.reversed}) := by
  have e := MacroPath.bits (P:=code) (l:=D p) (m:=(putInput p (b::t) {m with scratch:=true::c}).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,D,putInput,src,Action.run,jump] using e
private theorem DF (p : Fin 6) (m : Cells) :
    Goes (D p) {m with scratch:=[]} 1 (V p) {m with scratch:=[]} := by
  have e := MacroPath.bits (P:=code) (l:=D p) (m:=({m with scratch:=[]}:Cells).mem) (a:=_) (by rfl)
  simpa [code,D,V,Action.run,jump] using e

private theorem digits (p : Fin 6) (bs t : List Bool) (m : Cells) :
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

private theorem VT (p : Fin 6) (m : Cells) (b : Bool) (r : List Bool) :
    Goes (V p) {m with reversed:=b::r} 1 (V p) (putWord p [b] {m with reversed:=r}) := by
  have e := MacroPath.bits (P:=code) (l:=V p) (m:=({m with reversed:=b::r}:Cells).mem) (a:=_) (by rfl)
  fin_cases p <;> simpa [code,V,Action.run,jump,putWord,dest] using e

private theorem VF (p : Fin 6) (m : Cells) :
    Goes (V p) {m with reversed:=[]} 1 (next p) {m with reversed:=[]} := by
  have e := MacroPath.bits (P:=code) (l:=V p) (m:=({m with reversed:=[]}:Cells).mem) (a:=_) (by rfl)
  simpa [code,V,Action.run,jump] using e

private theorem backwards (p : Fin 6) (bs : List Bool) (m : Cells) :
    Goes (V p) {m with reversed:=bs} (bs.length+1) (next p) (putWord p bs.reverse {m with reversed:=[]}) := by
  induction bs generalizing m with
  | nil => fin_cases p <;> simpa [putWord] using VF _ m
  | cons b bs ih =>
    have st := VT p m b bs
    have t := ih (putWord p [b] m)
    fin_cases p <;> simp [putWord] at st t ⊢ <;>
      first | simpa [List.append_assoc,Nat.add_comm 1] using st.join t

theorem field (p : Fin 6) (n : ℕ) (t : List Bool) (m : Cells) (hs : m.scratch=[]) (hr : m.reversed=[]) :
    Goes (H p) (putInput p (encodeNat n++t) m) (3*(n.bits.length+1)) (next p)
      (putWord p n.bits (putInput p t m)) := by
  have h := header p n.bits.length m (n.bits++t)
  have d := digits p n.bits t m
  have r := backwards p n.bits.reverse (putInput p t m)
  fin_cases p <;> simp [putInput,hs,hr] at h d r ⊢ <;>
    have z := (h.join d).join r <;>
    simpa [encodeNat,List.append_assoc,Nat.mul_comm,Nat.mul_add,Nat.mul_succ,Nat.add_assoc,hs,hr] using z

end ResidueWeight

namespace ResidueWeight
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks

private theorem sweep (xs : List Bool) (s : Cells) :
    Goes (A 0) {s with input:=xs} (xs.length+1) (A 1) {s with input:=[],todo:=xs.reverse++s.todo} := by
  induction xs generalizing s with
  | nil =>
    have e := MacroPath.bits (P:=code) (l:=A 0) (m:=({s with input:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,A,Action.run,jump] using e
  | cons b xs ih =>
    have e := MacroPath.bits (P:=code) (l:=A 0) (m:=({s with input:=b::xs}:Cells).mem) (a:=_) (by rfl)
    have p : Goes (A 0) {s with input:=b::xs} 1 (A 0) {s with input:=xs,todo:=b::s.todo} := by
      simpa [code,A,Action.run,jump] using e
    have tr := p.join (ih {s with todo:=b::s.todo})
    simpa [List.append_assoc,Nat.add_comm 1] using tr

private theorem restore (xs : List Bool) (s : Cells) :
    Goes (A 1) {s with todo:=xs} (xs.length+1) (H 2)
      {s with todo:=[],input:=xs.reverse++s.input,prep:=xs.reverse++s.prep,divisor:=true::s.divisor,dimension:=false::s.dimension} := by
  induction xs generalizing s with
  | nil =>
    have e := MacroPath.bits (P:=code) (l:=A 1) (m:=({s with todo:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,A,Action.run,jump] using e
  | cons b xs ih =>
    have e := MacroPath.bits (P:=code) (l:=A 1) (m:=({s with todo:=b::xs}:Cells).mem) (a:=_) (by rfl)
    have p : Goes (A 1) {s with todo:=b::xs} 1 (A 1) {s with todo:=xs,input:=b::s.input,prep:=b::s.prep} := by
      simpa [code,A,Action.run,jump] using e
    have tr := p.join (ih {s with input:=b::s.input,prep:=b::s.prep})
    simpa [List.append_assoc,Nat.add_comm 1] using tr

theorem duplicate (s : Cells) (h : s.todo=[]) (p : s.prep=[]) :
    Goes (A 0) s (2*(s.input.length+1)) (H 2) {s with prep:=s.input,divisor:=true::s.divisor,dimension:=false::s.dimension} := by
  have a := sweep s.input s
  have b := restore s.input.reverse {s with input:=[]}
  simp [h,p] at a b
  have total := a.join b
  cases s; simp_all [two_mul]
end ResidueWeight

namespace ResidueWeight
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
private theorem val_small (w : List Bool) : val w < 2^w.length := by
  induction w with
  | nil => decide
  | cons b bs ih => cases b <;> simp [val,pow_succ] <;> omega

theorem decrement (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) (a : s.divisor=[true])
    (n : ℕ) (v : val s.dimension=n+1) :
    ∃ d : List Bool, Runs (A 3) s (3*(s.dimension.length+1)+8) (A 5) {s with dimension:=d,flag:=[],todo:=true::s.todo} ∧
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
  have pop : Goes (A 4) mid 1 (A 5) {s with dimension:=z.2.1,flag:=[],todo:=true::s.todo} := by simpa [mid,code,A,Action.run,jump] using step
  refine ⟨z.2.1,⟨_,?_,gate.join pop⟩,value,by simpa [a] using len.le⟩
  simp [gateTime,zl,right,len,a]; omega

theorem testDim (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) (a : s.divisor=[true]) (prod0 : s.product=[]) :
    Runs (A 5) s (3*s.dimension.length+7)
      (if val s.dimension=0 then H 5 else H 2)
      {s with divisor:=if val s.dimension=0 then [] else s.divisor,flag:=[]} := by
  have e := MacroPath.binary (P:=code) (l:=A 5) (m:=s.mem) (op:=.le) (i:=dim) (j:=prod)
    (h:=by decide) (n:=A 6) (by rfl) f sp
  let z := execute compareGate true s.dimension s.product
  obtain ⟨ans,left,right⟩ := le_correct s.dimension s.product
  change z.1=_ at ans; change z.2.1=_ at left; change z.2.2=_ at right
  have zl : gateResult .le s.mem dim prod = z := rfl
  let mid := {s with flag:=[z.1]}
  have gate : Goes (A 5) s (gateTime .le s.mem dim prod) (A 6) mid := by simpa [zl,afterGate,mid,left,right] using e
  have step := MacroPath.bits (P:=code) (l:=A 6) (m:=mid.mem) (a:=_) (by rfl)
  have pop : Goes (A 6) mid 1 (if val s.dimension=0 then H 5 else H 2)
      {s with divisor:=if val s.dimension=0 then [] else s.divisor,flag:=[]} := by
    by_cases c : val s.dimension=0 <;> simpa [mid,code,A,Action.run,jump,ans,prod0,val,c,a] using step
  refine ⟨_,?_,gate.join pop⟩
  simp [gateTime,zl,left,right,prod0]; omega


end ResidueWeight

namespace ResidueWeight
open OneTypeTM (Cells R)
open BitStacks
open ExponomialAssortment.FPTAS (encodeNat)

def words (xs : List ℕ) := xs.flatMap encodeNat
@[simp] theorem words_nil : words []=[] := rfl
@[simp] theorem words_cons (x : ℕ) (xs : List ℕ) : words (x::xs)=encodeNat x++words xs := rfl
theorem bits_lt (x : ℕ) : x.bits.length+1 ≤ (encodeNat x).length := by simp [encodeNat]
theorem count_words (xs : List ℕ) : xs.length≤(words xs).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp; have := bits_lt x;omega
theorem val_bits (n : ℕ) : val n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b k h ih => rw [Nat.bits_append_bit _ _ h,val,ih,Nat.bit_val]; omega

def headState (B d : ℕ) (rest : List Bool) : Cells :=
  {input:=rest,prep:=rest,remainder:=B.bits,dimension:=false::d.bits,divisor:=[true]}

theorem head (B d : ℕ) (rest : List Bool) :
    Goes (H 0) ({input:=encodeNat B++(encodeNat d++rest)}:Cells)
      (3*(B.bits.length+1)+3*(d.bits.length+1)+2*(rest.length+1)) (H 2) (headState B d rest) := by
  let m0 : Cells := {}
  let m1 := putWord 0 B.bits (putInput 0 (encodeNat d++rest) m0)
  let m2 := putWord 1 d.bits (putInput 1 rest m1)
  have a := field 0 B (encodeNat d++rest) m0 rfl rfl
  have b := field 1 d rest m1 rfl rfl
  have c := duplicate m2 rfl rfl
  have p := (a.join b).join c
  simpa [m0,m1,m2,next,putWord,putInput,headState] using p
theorem sizes (xs : List ℕ) (tail : List Bool) (s : Cells) (K : ℕ) (hk : 1≤K)
    (d : val s.dimension=xs.length+1) (size : s.dimension.length≤K)
    (inp : s.input=words xs++tail) (len : (words xs).length≤K) (it : s.divisor=[true])
    (f : s.flag=[]) (sp : s.spare=[]) (p : s.product=[]) (hs : s.scratch=[]) (hr : s.reversed=[]) :
    ∃ ds : List Bool, Runs (A 3) s ((xs.length+1)*(20*(K+1))) (H 5)
      {s with dimension:=ds,input:=tail,divisor:=[],flag:=[],todo:=List.replicate (xs.length+1) true++s.todo} ∧ ds.length≤K := by
  induction xs generalizing s with
  | nil =>
    obtain ⟨ds,dec,v,l⟩ := decrement s f sp it 0 (by simpa using d)
    let u := {s with dimension:=ds,flag:=[],todo:=true::s.todo}
    have check := testDim u rfl sp it p
    have fin := dec.seq (by simpa [u,v] using check)
    have lim : ds.length≤K := by omega
    refine ⟨ds,?_,lim⟩
    simpa [u,inp] using fin.mono (show _ ≤ 20*(K+1) by omega)
  | cons x xs ih =>
    obtain ⟨ds,dec,v,l⟩ := decrement s f sp it (xs.length+1) (by simpa using d)
    let u := {s with dimension:=ds,flag:=[],todo:=true::s.todo}
    let after := {u with input:=words xs++tail}
    have check := testDim u rfl sp it p
    have step := field 2 x (words xs++tail) u hs hr
    have c : Runs (A 5) u (3*ds.length+7) (H 2) u := by simpa [u,v] using check
    have read : Goes (H 2) u (3*(x.bits.length+1)) (A 3) after := by
      simpa [u,after,inp,next,putWord,putInput,List.append_assoc] using step
    have lim : ds.length≤K := by omega
    have lh : (words xs).length≤K := by simp at len;omega
    obtain ⟨di,path,li⟩ := ih after v lim rfl lh it rfl sp p hs hr
    have total := ((dec.seq c).seq (smallRun read)).seq path
    have rep : List.replicate (xs.length+1) true++true::s.todo=List.replicate (xs.length+1+1) true++s.todo := by
      calc
        _=(List.replicate (xs.length+1) true++[true])++s.todo := by simp
        _=_ := by rw [←List.replicate_succ']
    refine ⟨di,?_,li⟩
    have bl := bits_lt x
    simp only [words_cons,List.length_append] at len
    simp only [List.length_cons,after,u,rep] at total ⊢
    apply total.mono
    simp only [List.length_cons,Nat.succ_mul,Nat.add_mul]; omega

end ResidueWeight

namespace ResidueWeight
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
def xWord (r : Bool) (s : Cells) := if r then s.remainder else s.divisor
def zWord (r : Bool) (s : Cells) := if r then s.product else s.itemCount
def putX (r : Bool) (w : List Bool) (s : Cells) : Cells := if r then {s with remainder:=w} else {s with divisor:=w}
def putZ (r : Bool) (w : List Bool) (s : Cells) : Cells := if r then {s with product:=w} else {s with itemCount:=w}
def mulExit (r : Bool) := if r then A 9 else A 8
def mulOut (r : Bool) (n : ℕ) (z : List Bool) (s : Cells) := putZ r z (putX r []
  {s with binCount:=List.replicate n false ++ s.binCount,flag:=[]})

private theorem advance (r : Bool) (s : Cells) (b : Bool) (bs : List Bool) (h : xWord r s=b::bs) :
    Goes (M r 0) s 1 (if b then M r 1 else M r 3) (putX r bs s) := by
  have step := MacroPath.bits (P:=code) (l:=M r 0) (m:=s.mem) (a:=_) (by rfl)
  cases r <;> cases b <;> simp [xWord] at h <;> simpa [M,code,putX,factor,Action.run,jump,h] using step

private theorem doneMul (r : Bool) (s : Cells) (h : xWord r s=[]) :
    Goes (M r 0) s 1 (mulExit r) s := by
  have step := MacroPath.bits (P:=code) (l:=M r 0) (m:=s.mem) (a:=_) (by rfl)
  cases r <;> simp [xWord] at h <;> simpa [M,code,factor,mulExit,Action.run,jump,h] using step

private theorem shift (r : Bool) (s : Cells) : Goes (M r 3) s 1 (M r 0) {s with binCount:=false::s.binCount} := by
  have step := MacroPath.bits (P:=code) (l:=M r 3) (m:=s.mem) (a:=_) (by rfl)
  simpa [M,code,Action.run,jump] using step

private theorem addTo (r : Bool) (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) :
    ∃ z : List Bool, Runs (M r 1) s (3*(max (zWord r s).length s.binCount.length+3)) (M r 3)
      (putZ r z {s with flag:=[]}) ∧ val z=val (zWord r s)+val s.binCount ∧
      z.length ≤ max (zWord r s).length s.binCount.length+1 := by
  have e := MacroPath.binary (P:=code) (l:=M r 1) (m:=s.mem) (op:=.add) (i:=accum r) (j:=bins)
    (h:=by cases r <;> decide) (n:=M r 2) (by rfl) f sp
  let z := execute addGate false (zWord r s) s.binCount
  obtain ⟨v,c,l⟩ := add_correct false (zWord r s) s.binCount
  change val z.2.1=_ at v;change z.2.2=_ at c;change z.2.1.length≤_ at l
  have zl : gateResult .add s.mem (accum r) bins=z := by cases r <;> rfl
  let mid := putZ r z.2.1 {s with flag:=[z.1]}
  have gate : Goes (M r 1) s (gateTime .add s.mem (accum r) bins) (M r 2) mid := by
    rw [zl] at e
    cases r <;> simpa [afterGate,mid,accum,putZ,c] using e
  have one := MacroPath.bits (P:=code) (l:=M r 2) (m:=mid.mem) (a:=_) (by rfl)
  have drop : Goes (M r 2) mid 1 (M r 3) (putZ r z.2.1 {s with flag:=[]}) := by
    cases r <;> simpa [M,code,mid,putZ,Action.run,jump] using one
  refine ⟨z.2.1,⟨_,?_,gate.join drop⟩,by simpa using v,l⟩
  have inp : s.mem (reg (accum r))=zWord r s := by cases r <;>rfl
  simp [gateTime,zl,c,inp]; omega

private theorem oneBit (r : Bool) (s : Cells) (b : Bool) (bs : List Bool) (h : xWord r s=b::bs)
    (f : s.flag=[]) (sp : s.spare=[]) (S : ℕ) (hz : (zWord r s).length≤S) (hy : s.binCount.length≤S) :
    ∃ z : List Bool, Runs (M r 0) s (4*(S+4)) (M r 0) (putZ r z (putX r bs {s with binCount:=false::s.binCount,flag:=[]})) ∧
      val z=val (zWord r s)+b.toNat*val s.binCount ∧ z.length≤S+1 := by
  let t := putX r bs s
  have adv := smallRun (advance r s b bs h)
  have zt : zWord r t = zWord r s := by cases r <;>rfl
  have yt : t.binCount=s.binCount := by cases r <;>rfl
  have ft : t.flag=[] := by cases r <;> exact f
  have st : t.spare=[] := by cases r <;> exact sp
  cases b with
  | false =>
    have path := adv.seq (smallRun (shift r t))
    refine ⟨zWord r s,?_,by simp,by omega⟩
    have ht : 1+1≤4*(S+4) := by omega
    cases r <;> simpa [t,putX,putZ,zWord,f] using path.mono ht
  | true =>
    obtain ⟨z,plus,v,l⟩ := addTo r t ft st
    have path := (adv.seq plus).seq (smallRun (shift r _))
    have ht : 1+3*(max (zWord r t).length t.binCount.length+3)+1≤4*(S+4) := by rw [zt,yt];omega
    refine ⟨z,?_,by simpa [zt,yt] using v,by rw [zt,yt] at l;omega⟩
    cases r <;> simpa [t,putX,putZ] using path.mono ht

theorem multiplyAcc (r : Bool) (xs : List Bool) (s : Cells) (S K : ℕ)
    (h : xWord r s=xs) (f : s.flag=[]) (sp : s.spare=[]) (hz : (zWord r s).length≤S)
    (hy : s.binCount.length≤S) (space : S+xs.length≤K) :
    ∃ z : List Bool, Runs (M r 0) s (xs.length*(4*(K+4))+1) (mulExit r) (mulOut r xs.length z s) ∧
      val z=val (zWord r s)+val xs*val s.binCount ∧ z.length≤S+xs.length := by
  induction xs generalizing s S with
  | nil =>
    refine ⟨zWord r s,?_,by simp [val],by simpa using hz⟩
    have p := smallRun (doneMul r s h)
    cases s
    cases r <;> simp [xWord] at h <;> dsimp only at f <;> simpa [mulOut,putX,putZ,zWord,h,f] using p
  | cons b bs ih =>
    obtain ⟨z,first,v,l⟩ := oneBit r s b bs h f sp S hz hy
    let t := putZ r z (putX r bs {s with binCount:=false::s.binCount,flag:=[]})
    have x' : xWord r t=bs := by cases r <;>rfl
    have z' : zWord r t=z := by cases r <;>rfl
    have y' : t.binCount=false::s.binCount := by cases r <;>rfl
    have fm : t.flag=[] := by cases r <;>rfl
    have sm : t.spare=[] := by cases r <;>exact sp
    obtain ⟨out,tail,vo,lo⟩ := ih t (S+1) x' fm sm (z' ▸ l) (by rw [y'];simp;omega) (by simp at space;omega)
    have path := first.seq tail
    have sl : S≤K := by omega
    have tm : 4*(S+4)+(bs.length*(4*(K+4))+1) ≤ (b::bs).length*(4*(K+4))+1 := by simp [Nat.succ_mul];omega
    have rep (a : List Bool) : List.replicate bs.length false ++ false::a=false::(List.replicate bs.length false++a) := by
      calc
        _ = (List.replicate bs.length false ++ [false])++a := by simp
        _ = _ := by rw [←List.replicate_succ',List.replicate_succ,List.cons_append]
    refine ⟨out,?_,?_,by simp;omega⟩
    · cases r <;> simpa [t,putZ,putX,mulOut,List.replicate_succ,rep] using path.mono tm
    · rw [z',y',v] at vo; simp [val] at vo ⊢;nlinarith only [vo]
end ResidueWeight

namespace ResidueWeight
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks
open ExponomialAssortment.FPTAS (encodeNat)
def sizesWord (ps : List (ℕ×ℕ)) := words (ps.map Prod.fst)
def countsWord (ps : List (ℕ×ℕ)) := words (ps.map Prod.snd)
def pairMass (ps : List (ℕ×ℕ)) := (ps.map fun x => x.1*x.2).sum
@[simp] theorem sizes_nil : sizesWord []=[] := rfl
@[simp] theorem counts_nil : countsWord []=[] := rfl
@[simp] theorem sizes_cons (x y : ℕ) (ps : List (ℕ×ℕ)) : sizesWord ((x,y)::ps)=encodeNat x++sizesWord ps := rfl
@[simp] theorem counts_cons (x y : ℕ) (ps : List (ℕ×ℕ)) : countsWord ((x,y)::ps)=encodeNat y++countsWord ps := rfl

theorem clearBins (s : Cells) (bs : List Bool) : Goes (A 8) {s with binCount:=bs} (bs.length+1)
    (A 7) {s with binCount:=[]} := by
  induction bs with
  | nil =>
    have st := MacroPath.bits (P:=code) (l:=A 8) (m:=({s with binCount:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,A,Action.run,jump] using st
  | cons b bs ih =>
    have st := MacroPath.bits (P:=code) (l:=A 8) (m:=({s with binCount:=b::bs}:Cells).mem) (a:=_) (by rfl)
    have one : Goes (A 8) {s with binCount:=b::bs} 1 (A 8) {s with binCount:=bs} := by simpa [code,A,Action.run,jump] using st
    simpa [Nat.add_comm 1] using one.join ih

def fuel (ps : List (ℕ×ℕ)) := (sizesWord ps).length+(countsWord ps).length+1

theorem pairs (ps : List (ℕ×ℕ)) (back tail : List Bool) (s : Cells) (K : ℕ)
    (inp : s.input=countsWord ps++tail) (saved : s.prep=sizesWord ps++back)
    (markers : s.todo=List.replicate (2*ps.length) true)
    (room : s.itemCount.length+(sizesWord ps).length+(countsWord ps).length≤K)
    (bf : s.binCount=[]) (df : s.divisor=[]) (f : s.flag=[]) (sp : s.spare=[])
    (hs : s.scratch=[]) (hr : s.reversed=[]) :
    ∃ w : List Bool, Runs (A 7) s (fuel ps*(20*(K+4))) (A 10)
      {s with itemCount:=w,binCount:=[],input:=tail,prep:=back,divisor:=[],flag:=[],todo:=[]} ∧
      val w=val s.itemCount+pairMass ps ∧ w.length≤K := by
  induction ps generalizing s with
  | nil =>
    have st:=MacroPath.bits (P:=code) (l:=A 7) (m:=s.mem) (a:=_) (by rfl)
    have stop : Goes (A 7) s 1 (A 10) s := by simpa [code,A,Action.run,jump,markers] using st
    have t := (smallRun stop).mono (show 1≤fuel []*(20*(K+4)) by simp [fuel];omega)
    refine ⟨s.itemCount,?_,by simp [pairMass],by simpa using room⟩
    simp at markers saved inp
    cases s;dsimp only at markers saved inp bf df f;simpa [markers,saved,inp,bf,df,f] using t
  | cons xy ps ih =>
    obtain ⟨x,y⟩ := xy
    let rest := countsWord ps++tail
    let mirror := sizesWord ps++back
    let flagless := {s with todo:=List.replicate (2*ps.length) true}
    let u := {flagless with input:=rest,binCount:=y.bits}
    let v := {u with prep:=mirror,divisor:=x.bits}
    have st:=MacroPath.bits (P:=code) (l:=A 7) (m:=s.mem) (a:=_) (by rfl)
    have marks : s.todo=true::true::flagless.todo := by simpa [flagless,Nat.mul_succ,List.replicate_succ] using markers
    have go : Goes (A 7) s 1 (H 3) flagless := by simpa [code,A,flagless,marks,Action.run,jump] using st
    have fromY := field 3 y rest flagless hs hr
    have py : Goes (H 3) flagless (3*(y.bits.length+1)) (H 4) u := by
      cases s;simp [List.append_assoc] at inp;simpa [u,flagless,rest,inp,bf,next,putWord,putInput] using fromY
    have fromX := field 4 x mirror u hs hr
    have px : Goes (H 4) u (3*(x.bits.length+1)) (M false 0) v := by
      cases s; simp [List.append_assoc] at saved;simpa [u,v,flagless,mirror,saved,df,next,putWord,putInput] using fromX
    let S := max s.itemCount.length y.bits.length
    have lx := bits_lt x;have ly := bits_lt y
    simp only [sizes_cons,counts_cons,List.length_append] at room
    have space : S+x.bits.length≤K := by dsimp [S];omega
    obtain ⟨z,mult,vz,lz⟩ := multiplyAcc false x.bits v S K rfl f sp
      (by dsimp [v,u,flagless,zWord,S];omega) (by dsimp [v,u,flagless,S];omega) space
    let post := mulOut false x.bits.length z v
    let dst := {v with divisor:=[],binCount:=[],itemCount:=z,flag:=[]}
    have cl : Goes (A 8) post (x.bits.length+y.bits.length+1) (A 7) dst := by
      simpa [post,dst,mulOut,putX,putZ,u,v,flagless] using clearBins post post.binCount
    have rm : dst.itemCount.length+(sizesWord ps).length+(countsWord ps).length≤K := by dsimp [dst];dsimp [S] at lz;omega
    obtain ⟨w,recP,vw,lw⟩ := ih dst rfl rfl rfl rm rfl rfl rfl sp hs hr
    have path := ((((smallRun go).seq (smallRun py)).seq (smallRun px)).seq mult).seq (smallRun cl)
    have total := path.seq recP
    refine ⟨w,?_,?_,lw⟩
    · apply total.mono
      simp only [fuel,sizes_cons,counts_cons,List.length_append]
      have xx := Nat.mul_le_mul_right (4*(K+4)) lx
      nlinarith only [xx,lx,ly]
    · change val w=val z+pairMass ps at vw
      change val z=val s.itemCount+val x.bits*val y.bits at vz
      rw [vw,vz,val_bits,val_bits];simp [pairMass,Nat.add_assoc]
end ResidueWeight

namespace ResidueWeight
open OneTypeTM (Cells R)
open OneTypeTM.R BitStacks HMBinPacking
open ExponomialAssortment.FPTAS (encodeNat)
private theorem finalCmp (s : Cells) (f : s.flag=[]) (sp : s.spare=[]) :
    Runs (A 11) s (3*(max s.itemCount.length s.remainder.length+2)) (old (OneTypeTM.A 9))
      {s with flag:=[decide (val s.itemCount≤val s.remainder)]} := by
  have e := MacroPath.binary (P:=code) (l:=A 11) (m:=s.mem) (op:=.le) (i:=items) (j:=rem)
    (h:=by decide) (n:=old (OneTypeTM.A 9)) (by rfl) f sp
  let z := execute compareGate true s.itemCount s.remainder
  obtain ⟨a,x,y⟩ := le_correct s.itemCount s.remainder
  change z.1=_ at a;change z.2.1=_ at x;change z.2.2=_ at y
  have zl : gateResult .le s.mem items rem=z := rfl
  refine ⟨gateTime .le s.mem items rem,?_,?_⟩
  · simp [gateTime,zl,x,y];omega
  · simpa [afterGate,zl,a,x,y] using e

private theorem isolatedWord (w : List Bool) : ({input:=w}:Cells).mem=isolated (reg R.tape) w := by
  funext k
  cases k with
  | inl z => cases z <;>rfl
  | inr z => cases z <;>rfl

theorem purge (s : Cells) (bs : List Bool) : Goes (A 10) {s with input:=bs} (bs.length+1)
    (A 11) {s with input:=[]} := by
  induction bs with
  | nil =>
    have st := MacroPath.bits (P:=code) (l:=A 10) (m:=({s with input:=[]}:Cells).mem) (a:=_) (by rfl)
    simpa [code,A,Action.run,jump] using st
  | cons b bs ih =>
    have st := MacroPath.bits (P:=code) (l:=A 10) (m:=({s with input:=b::bs}:Cells).mem) (a:=_) (by rfl)
    have one : Goes (A 10) {s with input:=b::bs} 1 (A 10) {s with input:=bs} := by simpa [code,A,Action.run,jump] using st
    simpa [Nat.add_comm 1] using one.join ih

def dataWord (B d : ℕ) (ps : List (ℕ×ℕ)) (a : List ℕ) (b : ℕ) (query : List Bool) :=
  encodeNat B++(encodeNat d++(sizesWord ps++(words a++(encodeNat b++(countsWord ps++query)))))

private theorem words_append (a b : List ℕ) : words (a++b)=words a++words b := by simp [words]

theorem residueTest (B d : ℕ) (ps : List (ℕ×ℕ)) (a : List ℕ) (b : ℕ) (query : List Bool)
    (dp : 0<d) (ds : d=ps.length) (da : d=a.length) :
    OutputsWithin machine (dataWord B d ps a b query) [decide (pairMass ps≤B)]
      (600*((dataWord B d ps a b query).length+1)^2) := by
  cases ps with
  | nil => simp at ds;omega
  | cons xy ps =>
    obtain ⟨x,y⟩:=xy
    let xs:=(x,y)::ps
    let back:=words a++(encodeNat b++(countsWord xs++query))
    let aft:=encodeNat b++(countsWord xs++query)
    let rest:=sizesWord xs++back
    let skip:=(ps.map Prod.fst)++a
    let m:=headState B d rest
    let v:={m with input:=words skip++aft}
    let K:=(dataWord B d xs a b query).length
    have L : (encodeNat B).length+(encodeNat d).length+(sizesWord xs).length+back.length=K := by
      simp [K,dataWord,back,Nat.add_assoc]
    have sl : (sizesWord xs).length=(encodeNat x).length+(sizesWord ps).length := by simp [xs]
    have bk : back.length=(words a).length+aft.length := List.length_append
    have al : aft.length=(encodeNat b).length+(countsWord xs).length+query.length := by simp [aft];omega
    have skipLen : (words skip).length=(sizesWord ps).length+(words a).length := by simp [skip,sizesWord,words_append]
    have card : skip.length+1=2*d := by simp [skip];simp at ds;omega
    have sk : skip.length≤(words skip).length := count_words _
    have scount : xs.length=d := by simpa [xs] using ds.symm
    have enB:=bits_lt B;have endim:=bits_lt d;have enX:=bits_lt x;have enb:=bits_lt b
    have start := smallRun (head B d rest)
    have read := field 2 x (words skip++aft) m rfl rfl
    have first : Goes (H 2) m (3*(x.bits.length+1)) (A 3) v := by
      simpa [m,v,headState,rest,xs,skip,back,aft,sizesWord,words_append,putWord,putInput,next,List.append_assoc] using read
    obtain ⟨ds',scan,dl⟩ := sizes skip aft v K (by omega)
      (by simpa [v,m,headState,val,val_bits,Nat.mul_comm] using card.symm) (by simp [v,m,headState];omega)
      rfl (by omega) rfl rfl rfl rfl rfl rfl
    let t := {v with dimension:=ds',input:=aft,divisor:=[],flag:=[],todo:=List.replicate (2*xs.length) true}
    have cscan : Runs (A 3) v ((skip.length+1)*(20*(K+1))) (H 5) t := by
      simpa [t,v,m,headState,card,scount] using scan
    let u := {t with input:=countsWord xs++query}
    have bin : Goes (H 5) t (3*(b.bits.length+1)) (A 7) u := by
      simpa [u,t,v,m,headState,aft,putInput,putWord,next] using field 5 b (countsWord xs++query) t rfl rfl
    obtain ⟨w,measure,vw,lw⟩ := pairs xs back query u K rfl rfl rfl (by change 0+_+_≤K;omega)
      rfl rfl rfl rfl rfl rfl
    let z := {u with itemCount:=w,binCount:=[],input:=query,prep:=back,divisor:=[],flag:=[],todo:=[]}
    have value : val w=pairMass xs := by simpa [u,t,v,m,headState,val] using vw
    have wipe := purge z query
    let cz:={z with input:=[]}
    have cmp:=finalCmp cz rfl rfl
    have bit : decide (val cz.itemCount≤val cz.remainder)=decide (pairMass xs≤B) := by change decide (val w≤val B.bits)=_;rw [value,val_bits]
    rw [bit] at cmp
    let fz:={cz with flag:=[decide (pairMass xs≤B)]}
    have halt:=OneTypeTM.finish fz (decide (pairMass xs≤B)) rfl rfl rfl
    have lift : Goes (old (OneTypeTM.A 9)) fz (OneTypeTM.costClear fz) none ({input:=[decide (pairMass xs≤B)]}:Cells) :=
      halt.mapLabels (Q:=code) old (by intro l;rfl)
    have path := (((((((start.seq (smallRun first)).seq cscan).seq (smallRun bin)).seq measure).seq (smallRun wipe)).seq cmp).seq (smallRun lift))
    obtain ⟨n,clock,path⟩:=path
    apply MacroPath.outputs (t:=n)
    · rw [←isolatedWord,←isolatedWord];exact path
    · have c : OneTypeTM.costClear fz≤5*K+11 := by simp [fz,cz,z,u,t,v,m,headState,OneTypeTM.costClear];omega
      have c2 : 3*(max cz.itemCount.length cz.remainder.length+2)≤3*(K+2) := by change 3*(max w.length B.bits.length+2)≤_;omega
      have a1 : (skip.length+1)*(20*(K+1))≤(K+1)*(20*(K+1)) := Nat.mul_le_mul_right _ (by omega)
      have a2 : fuel xs*(20*(K+4))≤(K+1)*(20*(K+4)) := Nat.mul_le_mul_right _ (by unfold fuel;omega)
      have rl : rest.length=(sizesWord xs).length+back.length := List.length_append
      change n≤600*(K+1)^2
      nlinarith only [clock,c,c2,a1,a2,enB,endim,enX,enb,L,bk,al,sl,rl]
end ResidueWeight

namespace DimensionEmitter
open HMBinPacking Finset

def base (I : Instance) (r : Fin I.d→Fin I.d) := ∑ i,I.s i*(r i : ℕ)
def available (I : Instance) (r : Fin I.d→Fin I.d) (i : Fin I.d) := base I r+I.d*I.s i≤I.B

theorem empty (I : Instance) (r : Fin I.d→Fin I.d) (no : I.B<base I r) : Pr I r=∅ := by
  have none : Sr I r=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨nn,capacity⟩,⟨v,e⟩⟩
    have coord (i) : x i=(r i:ℕ)+(I.d:ℤ)*v i := by simpa [Pi.smul_apply,zsmul_eq_mul] using congrFun e i
    have lower (i) : ((r i : ℕ):ℤ) ≤ x i := by
      have h : 0 ≤ v i := by
        by_contra! h
        have dpos : (0:ℤ)≤I.d := by exact_mod_cast Nat.zero_le I.d
        have t:=mul_le_mul_of_nonneg_left (show v i≤-1 by omega) dpos
        have rr : ((r i:ℕ):ℤ) < I.d := by exact_mod_cast (r i).isLt
        have nx:=nn i
        rw [coord i] at nx;linarith
      rw [coord i];have : 0≤(I.d:ℤ)*v i:=mul_nonneg (by positivity) h;omega
    have ge := Finset.sum_le_sum (s:=univ) (fun i _=>mul_le_mul_of_nonneg_left (lower i) (show (0:ℤ)≤I.s i by positivity))
    have bound : base I r≤I.B := by unfold base;exact_mod_cast ge.trans capacity
    omega
  simp [Pr,none]

private theorem decomp (I : Instance) (r : Fin I.d→Fin I.d) (y : Fin I.d→ℕ) :
    ∑ i,I.s i*((r i:ℕ)+I.d*y i)=base I r+I.d*(∑ i,I.s i*y i) := by
  rw [Finset.mul_sum,base,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl;intro i _;ring

theorem zeroBest (I : Instance) (r : Fin I.d→Fin I.d) (u : Fin I.d→ℚ) (fit : base I r≤I.B)
    (noImprove : ∀ i,available I r i→u i≤0) :
    IsGreatest ((fun y' : Fin I.d → ℕ => ∑ i,(u i:ℝ)*(((r i:ℕ)+I.d*y' i:ℕ):ℝ)) ''
            {y' | ∑ i,I.s i*((r i:ℕ)+I.d*y' i)≤I.B})
        (∑ i,(u i:ℝ)*((r i:ℕ):ℝ)) := by
  constructor
  · exact ⟨fun _=>0,by simpa [base] using fit,by simp⟩
  · rintro _ ⟨v,hv,rfl⟩
    change ∑ i,I.s i*((r i:ℕ)+I.d*v i)≤I.B at hv
    rw [decomp] at hv
    apply Finset.sum_le_sum;intro i _
    by_cases p : v i=0
    · simp [p]
    · have h1 := Nat.le_mul_of_pos_right (I.s i) (Nat.pos_of_ne_zero p)
      have h2:=Finset.single_le_sum (f:=fun j=>I.s j*v j) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
      have h3:=Nat.mul_le_mul_left I.d (h1.trans h2)
      have reachable : available I r i := by unfold available;omega
      have hneg : (u i:ℝ)≤0 := by exact_mod_cast noImprove i reachable
      apply mul_le_mul_of_nonpos_left _ hneg
      exact_mod_cast Nat.le_add_right (r i:ℕ) (I.d*v i)

theorem zeroBest_iff (I : Instance) (r : Fin I.d→Fin I.d) (u : Fin I.d→ℚ) (fit : base I r≤I.B) :
    IsGreatest ((fun v : Fin I.d→ℕ => ∑ i,(u i:ℝ)*(((r i:ℕ)+I.d*v i:ℕ):ℝ)) ''
            {v | ∑ i,I.s i*((r i:ℕ)+I.d*v i)≤I.B})
        (∑ i,(u i:ℝ)*((r i:ℕ):ℝ)) ↔ ∀ i,available I r i→u i≤0 := by
  classical
  constructor
  · intro h i ha
    let v (j : Fin I.d) := if j=i then 1 else 0
    have cap : ∑ j,I.s j*((r j:ℕ)+I.d*v j)≤I.B := by
      rw [decomp]
      simpa [v,mul_ite,available] using ha
    have upper := h.2 ⟨v,cap,rfl⟩
    have split : (∑ j,(u j:ℝ)*(((r j:ℕ)+I.d*v j:ℕ):ℝ)) =
        ∑ j,(u j:ℝ)*((r j:ℕ):ℝ)+(u i:ℝ)*(I.d:ℝ) := by
      simp only [Nat.cast_add,Nat.cast_mul,mul_add,Finset.sum_add_distrib]
      congr 1
      simp [v,mul_ite]
    dsimp only at upper;rw [split] at upper
    have dp : (0:ℝ) < I.d := by exact_mod_cast I.d_pos
    have ans : (u i:ℝ)≤0 := by nlinarith
    exact_mod_cast ans
  · exact zeroBest I r u fit
end DimensionEmitter

open HMBinPacking ExponomialAssortment.FPTAS
namespace ResidueWeight
private theorem vec {d : ℕ} (f : Fin d→ℕ) : words (List.ofFn f)=encodeNatVec f := by
  rw [words,List.flatMap_def,List.map_ofFn];rfl
theorem actual (I : Instance) (r : Fin I.d→Fin I.d) (y : Fin I.d→ℚ) :
    let w := encodeInstance I++encodeResidue r++encVec y
    OutputsWithin machine w [decide (DimensionEmitter.base I r≤I.B)] (600*(w.length+1)^2) := by
  let ps := List.ofFn (fun i : Fin I.d=>(I.s i,(r i:ℕ)))
  let a := List.ofFn I.a
  have ws : sizesWord ps=encodeNatVec I.s := by
    rw [sizesWord,show ps.map Prod.fst=List.ofFn I.s by simp [ps,List.map_ofFn,Function.comp_def],vec]
  have wr : countsWord ps=encodeResidue r := by
    rw [countsWord,show ps.map Prod.snd=List.ofFn (fun i=>(r i:ℕ)) by simp [ps,List.map_ofFn,Function.comp_def],vec];rfl
  have data : pairMass ps=DimensionEmitter.base I r := by
    rw [pairMass,show ps.map (fun x=>x.1*x.2)=List.ofFn (fun i=>I.s i*(r i:ℕ)) by simp [ps,List.map_ofFn,Function.comp_def]]
    exact List.sum_ofFn
  have eq : dataWord I.B I.d ps a I.b (encVec y)=encodeInstance I++encodeResidue r++encVec y := by
    simp [a,dataWord,encodeInstance,ws,wr,vec,List.append_assoc]
  simpa [eq,data] using residueTest I.B I.d ps a I.b (encVec y) I.d_pos (by simp [ps]) (by simp [a])

theorem nonempty_iff (I : Instance) (r : Fin I.d→Fin I.d) : (Pr I r).Nonempty ↔ DimensionEmitter.base I r≤I.B := by
  constructor
  · intro h
    by_contra! no
    rw [DimensionEmitter.empty I r no] at h;exact Set.not_nonempty_empty h
  · intro fit
    obtain ⟨_,_,mem,_⟩:=lenstra_residue_optimization I r fit
    exact ⟨_,mem (fun _=>0) (by simpa [DimensionEmitter.base] using fit)⟩
end ResidueWeight

/-- Unconditional detection of the empty-residue branch of Lemma 7 in every dimension. -/
theorem ResidueWeight.unconditional :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∀ (I : Instance) (r : Fin I.d→Fin I.d) (y : Fin I.d→ℚ),
      let input:=encodeInstance I++encodeResidue r++encVec y
      ((Pr I r).Nonempty → OutputsWithin M input [true] (600*(input.length+1)^2)) ∧
      (Pr I r=∅ → OutputsWithin M input [false] (600*(input.length+1)^2)) := by
  refine ⟨ResidueWeight.machine,?_⟩
  intro I r y
  have res:=ResidueWeight.actual I r y
  have chan:=ResidueWeight.nonempty_iff I r
  constructor
  · intro pos;simpa [chan.mp pos] using res
  · intro empty
    have no : ¬DimensionEmitter.base I r≤I.B := fun h=>by
      have yes:=chan.mpr h;rw [empty] at yes;exact Set.not_nonempty_empty yes
    simpa [no] using res

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

namespace DimensionEmitter
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

theorem emit (m : Bool) (B d : ℕ) (t : List Bool) (small : d≤(raw B d t).length) :
    OutputsWithin (machine m) (raw B d t) (result m d) (100*((raw B d t).length+1)^2) := by
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
    have bd : d+1≤K := by simpa [K,word] using Nat.add_le_add_right small 1
    have bound := Nat.mul_le_mul_right (10*(K+3)) bd
    change n≤100*K^2
    nlinarith only [nt,bound,c,size]
end DimensionEmitter

namespace DimensionEmitter
open HMBinPacking ExponomialAssortment.FPTAS Finset

private theorem flat {n : ℕ} (f : Fin n → List Bool) : (List.ofFn f).flatten.length=∑ i,(f i).length := by
  simp [List.sum_ofFn,Function.comp_def]
private theorem count (I : Instance) : I.d+3 ≤ inputLength I := by
  have lo : I.d≤(encodeNatVec I.s).length := by
    rw [encodeNatVec,flat]
    simpa using (Finset.sum_le_sum (s:=univ) (f:=fun _ : Fin I.d => 1)
      (g:=fun i => (encodeNat (I.s i)).length) (fun i _ => by simp [encodeNat];omega))
  simp [inputLength,encodeInstance,encodeNat];omega
private theorem residueLen (I : Instance) (r : Fin I.d→Fin I.d) : (encodeResidue r).length≤I.d*inputLength I := by
  have dim : (encodeNat I.d).length ≤ inputLength I := by simp [inputLength,encodeInstance];omega
  have one (i) : (encodeNat (r i)).length ≤ inputLength I := by
    apply le_trans _ dim
    have := Nat.size_le_size (r i).isLt.le
    simp [encodeNat,Nat.size_eq_bits_len];omega
  rw [encodeResidue,encodeNatVec,flat]
  simpa using Finset.sum_le_sum (s:=univ) (fun i _ => one i)

private theorem repeat_eq (m : Bool) (n : ℕ) :
    repeatWord m n=(List.ofFn (fun _ : Fin n => block m)).flatten := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simp [repeatWord,List.ofFn_succ,ih]
theorem optWord (d : ℕ) : result false d=encodeNatVec (fun _ : Fin d=>0) := by
  simp [result,tagWord,suffix,repeat_eq,encodeNatVec,block,encodeNat]
theorem sepWord (d : ℕ) : result true d=false::(encVec (fun _ : Fin d=>(0:ℚ))++encodeRat (-1)) := by
  simp [result,tagWord,suffix,repeat_eq,encVec,block]
theorem sepLength (d : ℕ) : (result true d).length≤8+5*d := by
  have zero : (encodeRat 0).length=5 := by decide
  have neg : (encodeRat (-1)).length=7 := by decide
  rw [sepWord]
  simp [encVec,flat,zero,neg];omega

theorem budget (m : Bool) (I : Instance) (r : Fin I.d→Fin I.d) (y : Fin I.d→ℚ) :
    OutputsWithin (machine m) (encodeInstance I++encodeResidue r++encVec y) (result m I.d)
      (2^(16*I.d^3)*(inputLength I+(encVec y).length)^16) := by
  let rest:=encodeNatVec I.s++encodeNatVec I.a++encodeNat I.b++encodeResidue r++encVec y
  let W:=encodeInstance I++encodeResidue r++encVec y
  let N:=inputLength I+(encVec y).length
  have le:=count I
  have len : W.length=N+(encodeResidue r).length := by simp [W,N,inputLength];omega
  have et : W=raw I.B I.d rest := by simp [W,rest,raw,encodeInstance,List.append_assoc]
  have dn : I.d≤W.length := by dsimp [N] at len;omega
  have run:=emit m I.B I.d rest (by rw [←et];exact dn)
  rw [←et] at run
  obtain ⟨⟨trace,ct⟩⟩:=run
  have pos : 1≤N := by dsimp [N];omega
  have ll := residueLen I r
  have h1 : I.d*inputLength I≤N*N := Nat.mul_le_mul (by dsimp [N];omega) (by dsimp [N];omega)
  have n2 : N≤N^2 := by nlinarith only [pos]
  have bound : W.length+1≤3*N^2 := by rw [←pow_two] at h1;omega
  have b4 := Nat.pow_le_pow_left bound 2
  have pow : N^4≤N^16 := Nat.pow_le_pow_right pos (by decide)
  have d3 : 1≤I.d^3 := Nat.one_le_pow _ _ I.d_pos
  have factor : 900≤2^(16*I.d^3) := by
    exact (by decide : 900≤2^16).trans (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨⟨trace,ct.trans ?_⟩⟩
  calc
    100*(W.length+1)^2 ≤ 100*(3*N^2)^2 := Nat.mul_le_mul_left _ b4
    _ = 900*N^4 := by ring
    _ ≤ _ := Nat.mul_le_mul factor pow

theorem quadraticBudget (I : Instance) (r : Fin I.d→Fin I.d) (y : Fin I.d→ℚ) :
    let W := encodeInstance I++encodeResidue r++encVec y
    800*(W.length+1)^2≤2^(16*I.d^3)*(inputLength I+(encVec y).length)^16 := by
  let W:=encodeInstance I++encodeResidue r++encVec y
  let N:=inputLength I+(encVec y).length
  have le:=count I
  have len : W.length=N+(encodeResidue r).length := by simp [W,N,inputLength];omega
  have pos : 1≤N := by dsimp [N];omega
  have ll := residueLen I r
  have h1 : I.d*inputLength I≤N*N := Nat.mul_le_mul (by dsimp [N];omega) (by dsimp [N];omega)
  have n2 : N≤N^2 := by nlinarith only [pos]
  have bound : W.length+1≤3*N^2 := by rw [←pow_two] at h1;omega
  have b4 := Nat.pow_le_pow_left bound 2
  have pow : N^4≤N^16 := Nat.pow_le_pow_right pos (by decide)
  have d3 : 1≤I.d^3 := Nat.one_le_pow _ _ I.d_pos
  have factor : 7200≤2^(16*I.d^3) := by
    exact (by decide : 7200≤2^16).trans (Nat.pow_le_pow_right (by decide) (by omega))
  calc
    800*(W.length+1)^2 ≤ 800*(3*N^2)^2 := Nat.mul_le_mul_left _ b4
    _ = 7200*N^4 := by ring
    _ ≤ _ := Nat.mul_le_mul factor pow

theorem outputBound (I : Instance) (y : Fin I.d→ℚ) :
    (result true I.d).length≤(I.d+inputLength I+(encVec y).length)^16 := by
  let X:=I.d+inputLength I+(encVec y).length
  have countI:=count I
  have dp:=I.d_pos
  have x : I.d+4≤X := by dsimp [X];omega
  have z : 8+5*I.d≤X^2 := by nlinarith only [x]
  exact (sepLength _).trans (z.trans (Nat.pow_le_pow_right (show 1≤X by omega) (by decide)))
end DimensionEmitter

namespace BranchOracle
open HMBinPacking BitStacks ExponomialAssortment.FPTAS
private abbrev io := reg OneTypeTM.R.tape
def sep := BranchCompose.guarded io (.inl (ResidueWeight.H 0)) (.inl (DimensionEmitter.init true))
  (wordCode ResidueWeight.code) (wordCode DimensionEmitter.code)

theorem run (I : Instance) (r : Fin I.d→Fin I.d) (q : Fin I.d→ℚ) :
    let w:=encodeInstance I++encodeResidue r++encVec q
    let allowed:=decide (DimensionEmitter.base I r≤I.B)
    HMBinPacking.OutputsWithin sep w (if allowed then [true] else false::(encVec (fun _ : Fin I.d=>(0:ℚ))++encodeRat (-1)))
      (800*(w.length+1)^2) := by
  let w:=encodeInstance I++encodeResidue r++encVec q
  let bit:=decide (DimensionEmitter.base I r≤I.B)
  have pred:=ResidueWeight.actual I r q
  let tail:=encodeNatVec I.s++encodeNatVec I.a++encodeNat I.b++encodeResidue r++encVec q
  have et : w=DimensionEmitter.raw I.B I.d tail := by simp [w,tail,DimensionEmitter.raw,encodeInstance,List.append_assoc]
  have lenVec : I.d≤(encodeNatVec I.s).length := by
    rw [encodeNatVec,show (List.ofFn (fun i=>encodeNat (I.s i))).flatten.length=∑ i,(encodeNat (I.s i)).length by simp [List.sum_ofFn,Function.comp_def]]
    simpa using Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ : Fin I.d=>1)
      (g:=fun i=>(encodeNat (I.s i)).length) (fun i _=>by simp [encodeNat];omega)
  have bound : I.d≤w.length := by simp [w,encodeInstance];omega
  have emit:=DimensionEmitter.emit true I.B I.d tail (by rw [←et];exact bound)
  rw [←et] at emit
  let aEntry : ResidueWeight.L ⊕ (ResidueWeight.L × (Fin 4 × Bool)) := .inl (ResidueWeight.H 0)
  let bEntry : DimensionEmitter.L ⊕ (DimensionEmitter.L × (Fin 4 × Bool)) := .inl (DimensionEmitter.init true)
  change OutputsWithin (BitStacks.machine aEntry io (wordCode ResidueWeight.code)) w [bit] (600*(w.length+1)^2) at pred
  change OutputsWithin (BitStacks.machine bEntry io (wordCode DimensionEmitter.code)) w (DimensionEmitter.result true I.d) (100*(w.length+1)^2) at emit
  have together:=BranchCompose.run io aEntry bEntry
    (wordCode ResidueWeight.code) (wordCode DimensionEmitter.code) pred (fun _=>emit)
  rw [DimensionEmitter.sepWord] at together
  obtain ⟨⟨path,time⟩⟩:=together
  exact ⟨⟨path,time.trans (by change 600*(w.length+1)^2+100*(w.length+1)^2+3*w.length+4≤800*(w.length+1)^2;nlinarith)⟩⟩

theorem correct (I : Instance) (r : Fin I.d→Fin I.d) (q : Fin I.d→ℚ) :
    let word:=if DimensionEmitter.base I r≤I.B then [true] else false::(encVec (fun _ : Fin I.d=>(0:ℚ))++encodeRat (-1))
    (word=[true] ↔ (Pr I r).Nonempty) ∧
    ((Pr I r=∅ ∨ qCast q∈Pr I r) → IsSepAnswer (Pr I r) q word) := by
  by_cases base : DimensionEmitter.base I r≤I.B
  · have pos := (ResidueWeight.nonempty_iff I r).mpr base
    simp only [if_pos base]
    refine ⟨by simp [pos],?_⟩
    rintro (empty|mem)
    · rw [empty] at pos;exact (Set.not_nonempty_empty pos).elim
    · exact Or.inl ⟨rfl,mem⟩
  · have empty:=DimensionEmitter.empty I r (by omega)
    simp only [if_neg base]
    refine ⟨by simp [empty],?_⟩
    intro _
    right; refine ⟨fun _=>0,-1,rfl,?_,?_⟩
    · rw [empty];simp
    · simp
end BranchOracle
open HMBinPacking ExponomialAssortment.FPTAS
/-- The empty branch is detected and certified in the same machine run. -/
theorem solution :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∀ (I : Instance) (r : Fin I.d→Fin I.d) (q : Fin I.d→ℚ),
      let input:=encodeInstance I++encodeResidue r++encVec q
      ∃ w : List Bool, OutputsWithin M input w (800*(input.length+1)^2) ∧
        OutputsWithin M input w (2^(16*I.d^3)*(inputLength I+(encVec q).length)^16) ∧
        (w=[true] ↔ (Pr I r).Nonempty) ∧
        (Pr I r=∅ → w=false::(encVec (fun _ : Fin I.d=>(0:ℚ))++encodeRat (-1))) ∧
        ((Pr I r=∅ ∨ qCast q∈Pr I r) → IsSepAnswer (Pr I r) q w) ∧
        ((∀ i,q i=((r i:ℕ):ℚ)) → IsSepAnswer (Pr I r) q w) ∧
        w.length≤(I.d+inputLength I+(encVec q).length)^16 := by
  refine ⟨BranchOracle.sep,?_⟩
  intro I r q
  let w:=if DimensionEmitter.base I r≤I.B then [true] else false::(encVec (fun _ : Fin I.d=>(0:ℚ))++encodeRat (-1))
  have run:=BranchOracle.run I r q
  have h:=BranchOracle.correct I r q
  have raw : OutputsWithin BranchOracle.sep (encodeInstance I++encodeResidue r++encVec q) w
      (800*((encodeInstance I++encodeResidue r++encVec q).length+1)^2) := by simpa [w] using run
  have raw0:=raw
  obtain ⟨⟨tr,t⟩⟩:=raw0
  refine ⟨w,raw,⟨⟨tr,t.trans (DimensionEmitter.quadraticBudget I r q)⟩⟩,h.1,?_,h.2,?_,?_⟩
  · intro empty
    have no : ¬DimensionEmitter.base I r≤I.B := fun b=>by
      have p:=(ResidueWeight.nonempty_iff I r).mpr b;rw [empty] at p;exact Set.not_nonempty_empty p
    simp [w,no]
  · intro point
    by_cases fit : DimensionEmitter.base I r≤I.B
    · obtain ⟨_,_,mem,_⟩:=lenstra_residue_optimization I r fit
      have pin := mem (fun _=>0) (by simpa [DimensionEmitter.base] using fit)
      apply h.2 (Or.inr ?_)
      have eq : qCast q=fun i=>((r i:ℕ):ℝ) := by ext i;simp [qCast,point]
      simpa [eq] using pin
    · exact h.2 (Or.inl (DimensionEmitter.empty I r (by omega)))
  · by_cases base : DimensionEmitter.base I r≤I.B
    · simp only [w,if_pos base,List.length_singleton]
      exact Nat.one_le_pow _ _ (by have := I.d_pos;omega)
    · simpa [w,base,DimensionEmitter.sepWord] using DimensionEmitter.outputBound I q
