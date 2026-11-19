-- Prove2me | solution 1 for Lax759944Proofs.TapeRamGenericTime.genericTime_of_lowering_finite_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:40:24.055495+00:00
-- url     : https://prove2.me/submissions/000c7141-2ccb-4580-9e7d-daac30fec567

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_EdgeSublinearMWIS_Main_NativeOperationalInterfaces
import Theorems.Thm_Lax759944Proofs_RamToTM_finite_sparseStep_correct

section

namespace Lax759944Proofs.Legacy.RamPolytime

open Lax759944Proofs.Legacy.Ram
open Lax759944.BinaryWordEncoding

def FitsInWords (w:ℕ) (x:List ℕ):Prop:=
  ∀ a∈ x,a < 2 ^ w

def RamPolytime (f:List ℕ→ List ℕ):Prop:=
  ∃ (p:Program) (wordBound timeBound:Polynomial ℕ),
    ∀ x:List ℕ,
      FitsInWords (wordBound.eval (bitSize x)) ((x.length::x) ++ f x)∧
        ∀ w:ℕ,wordBound.eval (bitSize x)≤ w→
          ∃ t≤ timeBound.eval (bitSize x),
            RunsTo w p (x.length::x) (f x) t

end Lax759944Proofs.Legacy.RamPolytime

end

section

namespace Lax759944Proofs.Encoding

open Lax759944.BinaryWordEncoding

@[simp] theorem encode_nil:encode []=[]:=rfl

@[simp] theorem encode_cons (a:ℕ) (x:List ℕ):
    encode (a::x)=encodeNat a ++ encode x:=rfl

@[simp] theorem bitSize_nil:bitSize []=0:=rfl

theorem bitSize_cons (a:ℕ) (x:List ℕ):
    bitSize (a::x)=(Nat.bits a).length + 1 + bitSize x:=by
  simp [bitSize,encode,encodeNat,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem length_le_bitSize (x:List ℕ):x.length≤ bitSize x:=by
  induction x with
  | nil => simp
  | cons a x ih =>
      rw [bitSize_cons]
      simp only [List.length_cons]
      omega

end Lax759944Proofs.Encoding

end

section

namespace Lax759944Proofs.Microcode

structure State where

  pc:ℕ

  acc:ℕ

  mem:ℕ→ ℕ

  inp:List ℕ

  out:List ℕ

def setCell (w:ℕ) (m:ℕ→ ℕ) (a v:ℕ):ℕ→ ℕ:=
  fun b => if b=a % 2 ^ w then v % 2 ^ w else m b

def Instr.effect (w:ℕ):Instr→ State→ Option State
  | read a,s =>
      s.inp.head?.map fun v =>
        { s with pc:=s.pc + 1,mem:=setCell w s.mem a v,inp:=s.inp.tail }
  | write o,s =>
      some { s with pc:=s.pc + 1,out:=s.out ++ [o.value w s.mem % 2 ^ w] }
  | load o,s => some { s with pc:=s.pc + 1,acc:=o.value w s.mem % 2 ^ w }
  | store a,s => some { s with pc:=s.pc + 1,mem:=setCell w s.mem a s.acc }
  | storeInd a,s =>
      some { s with pc:=s.pc + 1,mem:=setCell w s.mem (s.mem (a % 2 ^ w)) s.acc }
  | add o,s => some { s with pc:=s.pc + 1,acc:=(s.acc + o.value w s.mem) % 2 ^ w }
  | sub o,s => some { s with pc:=s.pc + 1,acc:=(s.acc - o.value w s.mem) % 2 ^ w }
  | mul o,s => some { s with pc:=s.pc + 1,acc:=(s.acc * o.value w s.mem) % 2 ^ w }
  | div o,s => some { s with pc:=s.pc + 1,acc:=(s.acc / o.value w s.mem) % 2 ^ w }
  | and o,s => some { s with pc:=s.pc + 1,acc:=Nat.land s.acc (o.value w s.mem) % 2 ^ w }
  | or o,s => some { s with pc:=s.pc + 1,acc:=Nat.lor s.acc (o.value w s.mem) % 2 ^ w }
  | xor o,s => some { s with pc:=s.pc + 1,acc:=Nat.xor s.acc (o.value w s.mem) % 2 ^ w }
  | compl _,s =>
      some { s with pc:=s.pc + 1,acc:=(2 ^ w - 1 - s.acc % 2 ^ w) % 2 ^ w }
  | shiftl o,s =>
      some { s with pc:=s.pc + 1,acc:=s.acc * 2 ^ o.value w s.mem % 2 ^ w }
  | shiftr o,s =>
      some { s with pc:=s.pc + 1,acc:=s.acc / 2 ^ o.value w s.mem % 2 ^ w }
  | jump l,s => some { s with pc:=l }
  | jzero l,s => some { s with pc:=if s.acc=0 then l else s.pc + 1 }
  | jgtz l,s => some { s with pc:=if 0 < s.acc then l else s.pc + 1 }
  | halt,_ => none

def step (w:ℕ) (p:Program) (s:State):Option State:=
  p[s.pc]?.bind fun i => i.effect w s

def run (w:ℕ) (p:Program):ℕ→ State→ Option State
  | 0,s => some s
  | t + 1,s => (step w p s).bind (run w p t)

def initState (x:List ℕ):State where
  pc:=0
  acc:=0
  mem:=fun _ => 0
  inp:=x
  out:= []

def RunsTo (w:ℕ) (p:Program) (x y:List ℕ) (t:ℕ):Prop:=
  ∃ s:State,run w p t (initState x)=some s∧ step w p s=none∧ s.out=y

end Lax759944Proofs.Microcode

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

@[simp] theorem SparseMemory.read_nil (a:ℕ):SparseMemory.read [] a=0:=rfl

theorem SparseMemory.read_write (w:ℕ) (m:SparseMemory) (a v b:ℕ):
    (m.write w a v).read b =
      if b=a % 2 ^ w then v % 2 ^ w else m.read b:=by
  simp [SparseMemory.write,SparseMemory.read]

theorem SparseMemory.write_toMem (w:ℕ) (m:SparseMemory) (a v:ℕ):
    (m.write w a v).read=setCell w m.read a v:=by
  funext b
  simp [SparseMemory.read_write,setCell]

theorem SparseMemory.write_length_le (w:ℕ) (m:SparseMemory) (a v:ℕ):
    (m.write w a v).length≤ m.length + 1:=
  by simp [SparseMemory.write]

def SparseState.toState (s:SparseState):State where
  pc:=s.pc
  acc:=s.acc
  mem:=s.mem.read
  inp:=s.inp
  out:=s.out

@[simp] theorem SparseState.toState_pc (s:SparseState):s.toState.pc=s.pc:=rfl
@[simp] theorem SparseState.toState_acc (s:SparseState):s.toState.acc=s.acc:=rfl
@[simp] theorem SparseState.toState_mem (s:SparseState):s.toState.mem=s.mem.read:=rfl
@[simp] theorem SparseState.toState_inp (s:SparseState):s.toState.inp=s.inp:=rfl
@[simp] theorem SparseState.toState_out (s:SparseState):s.toState.out=s.out:=rfl

def sparseInitState (x:List ℕ):SparseState where
  pc:=0
  acc:=0
  mem:= []
  inp:=x
  out:= []

@[simp] theorem sparseInitState_toState (x:List ℕ):
    (sparseInitState x).toState=initState x:=by
  rfl

theorem sparseEffect_toState (w:ℕ) (i:Instr) (s:SparseState):
    Option.map SparseState.toState (sparseEffect w i s)=i.effect w s.toState:=by
  cases i <;> simp [sparseEffect,Instr.effect,sparseValue,SparseState.toState,
    SparseMemory.write_toMem]
  case read a => cases s.inp <;> simp [sparseEffect,Instr.effect,SparseState.toState,
    SparseMemory.write_toMem]

theorem sparseEffect_mem_length_le {w:ℕ} {i:Instr} {s s':SparseState}
    (h:sparseEffect w i s=some s'):s'.mem.length≤ s.mem.length + 1:=by
  cases i <;> simp [sparseEffect] at h
  case read a =>
    cases hin:s.inp with
    | nil => simp [hin] at h
    | cons v xs =>
      simp [hin] at h
      subst s'
      exact SparseMemory.write_length_le w s.mem a v
  all_goals
    subst s'
    simp only [SparseState.mem]
    first
    | exact SparseMemory.write_length_le _ _ _ _
    | omega

theorem sparseStep_toState (w:ℕ) (p:Program) (s:SparseState):
    Option.map SparseState.toState (sparseStep w p s)=step w p s.toState:=by
  simp only [sparseStep,step,SparseState.toState_pc]
  cases hfetch:p[s.pc]? with
  | none => simp [hfetch]
  | some i => simp [hfetch,sparseEffect_toState]

theorem sparseStep_mem_length_le {w:ℕ} {p:Program} {s s':SparseState}
    (h:sparseStep w p s=some s'):s'.mem.length≤ s.mem.length + 1:=by
  unfold sparseStep at h
  cases hi:p[s.pc]? with
  | none => simp [hi] at h
  | some i =>
    simp [hi] at h
    exact sparseEffect_mem_length_le (w:=w) (i:=i) (s:=s) h

def sparseRun (w:ℕ) (p:Program):ℕ→ SparseState→ Option SparseState
  | 0,s => some s
  | t + 1,s => (sparseStep w p s).bind (sparseRun w p t)

theorem sparseRun_toState (w:ℕ) (p:Program) (t:ℕ) (s:SparseState):
    Option.map SparseState.toState (sparseRun w p t s)=run w p t s.toState:=by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
      simp only [sparseRun,run]
      cases hs:sparseStep w p s with
      | none =>
        have hdense:step w p s.toState=none:=by
          have h:=sparseStep_toState w p s
          simpa [hs] using h.symm
        simp [hs,hdense]
      | some s' =>
        have hdense:step w p s.toState=some s'.toState:=by
          have h:=sparseStep_toState w p s
          simpa [hs] using h.symm
        simp [hs,hdense,ih]

theorem sparseRun_mem_length_le {w:ℕ} {p:Program} {t:ℕ} {s s':SparseState}
    (h:sparseRun w p t s=some s'):s'.mem.length≤ s.mem.length + t:=by
  induction t generalizing s with
  | zero =>
      simp [sparseRun] at h
      subst s'
      omega
  | succ t ih =>
      simp only [sparseRun] at h
      cases hs:sparseStep w p s with
      | none => simp [hs] at h
      | some s₁ =>
        simp [hs] at h
        have hone:=sparseStep_mem_length_le hs
        have hrest:=ih (s:=s₁) h
        omega

theorem sparseRun_init_mem_length_le {w:ℕ} {p:Program} {x:List ℕ}
    {t:ℕ} {s:SparseState} (h:sparseRun w p t (sparseInitState x)=some s):
    s.mem.length≤ t:=by
  simpa [sparseInitState] using sparseRun_mem_length_le h

theorem sparseRun_exists_of_run {w:ℕ} {p:Program} {x:List ℕ} {t:ℕ}
    {s:State} (h:run w p t (initState x)=some s):
    ∃ ss,sparseRun w p t (sparseInitState x)=some ss∧ ss.toState=s:=by
  have hm:=sparseRun_toState w p t (sparseInitState x)
  rw [sparseInitState_toState,h] at hm
  cases hs:sparseRun w p t (sparseInitState x) with
  | none => simp [hs] at hm
  | some ss =>
      simp [hs] at hm
      exact ⟨ss,rfl,hm⟩

theorem sparse_halts_of_runsTo {w:ℕ} {p:Program} {x y:List ℕ} {t:ℕ}
    (h:RunsTo w p x y t):
    ∃ ss,sparseRun w p t (sparseInitState x)=some ss∧
      sparseStep w p ss=none∧ ss.out=y∧ ss.mem.length≤ t:=by
  rcases h with ⟨s,hrun,hhalt,hout⟩
  rcases sparseRun_exists_of_run hrun with ⟨ss,hsrun,hstate⟩
  have hstepMap:=sparseStep_toState w p ss
  rw [hstate,hhalt] at hstepMap
  have hshalt:sparseStep w p ss=none:=by
    cases hs:sparseStep w p ss with
    | none => rfl
    | some ss' => simp [hs] at hstepMap
  refine ⟨ss,hsrun,hshalt, ?_,sparseRun_init_mem_length_le hsrun⟩
  simpa [← hstate] using hout

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Polynomial

theorem polynomial_eval_mono (p:Polynomial ℕ) {m n:ℕ} (h:m≤ n):
    p.eval m≤ p.eval n:=by
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

theorem polynomial_eval_le_coeffSum_mul (p:Polynomial ℕ) (n:ℕ):
    p.eval n≤ polyCoeffSum p * (n + 1) ^ p.natDegree:=by
  rw [Polynomial.eval_eq_sum]
  calc
    p.sum (fun i a => a * n ^ i)≤
        p.support.sum (fun i => p.coeff i * (n + 1) ^ p.natDegree):=by
      apply Finset.sum_le_sum
      intro i hi
      apply Nat.mul_le_mul_left
      exact (Nat.pow_le_pow_left (by omega) i).trans
        (Nat.pow_le_pow_right (by omega) (Polynomial.le_natDegree_of_mem_supp i hi))
    _=polyCoeffSum p * (n + 1) ^ p.natDegree:=by
      rw [polyCoeffSum,Finset.sum_mul]

@[simp] theorem polynomialSimpleMajorant_eval (p:Polynomial ℕ) (n:ℕ):
    (polynomialSimpleMajorant p).eval n =
      polyCoeffSum p * (n + 1) ^ p.natDegree:=by
  simp [polynomialSimpleMajorant]

theorem polynomial_eval_le_simpleMajorant (p:Polynomial ℕ) (n:ℕ):
    p.eval n≤ (polynomialSimpleMajorant p).eval n:=by
  simpa using polynomial_eval_le_coeffSum_mul p n

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

def bitsValue:List Bool→ ℕ
  | [] => 0
  | b::bs => Nat.bit b (bitsValue bs)

@[simp] theorem fixedBits_length (w n:ℕ):(fixedBits w n).length=w:=by
  induction w generalizing n <;> simp [fixedBits, *]

theorem bit_mod_two_pow (b:Bool) (n w:ℕ):
    Nat.bit b (n % 2 ^ w)=Nat.bit b n % 2 ^ (w + 1):=by
  simp only [Nat.bit_val,pow_succ]
  let M:=2 ^ w
  have hM:0 < M:=by simp [M]
  have hn:n % M < M:=Nat.mod_lt _ hM
  have hb:b.toNat≤ 1:=by cases b <;> simp
  have hsmall:2 * (n % M) + b.toNat < M * 2:=by omega
  rw [← Nat.mod_eq_of_lt hsmall]
  simpa [M,Nat.mul_comm] using!
    (Nat.ModEq.mul_left' 2 (Nat.mod_modEq n M)).add
      (Nat.ModEq.rfl:b.toNat ≡ b.toNat [MOD 2 * M])

@[simp] theorem bitsValue_fixedBits (w n:ℕ):
    bitsValue (fixedBits w n)=n % 2 ^ w:=by
  induction w generalizing n with
  | zero => simp [fixedBits,bitsValue,Nat.mod_one]
  | succ w ih =>
      simp only [fixedBits,bitsValue,ih]
      rw [bit_mod_two_pow,Nat.bit_bodd_div2]

theorem bitsValue_fixedBits_of_lt {w n:ℕ} (h:n < 2 ^ w):
    bitsValue (fixedBits w n)=n:=by
  simp [bitsValue_fixedBits,Nat.mod_eq_of_lt h]

theorem bitsValue_injective_of_length:∀ {xs ys:List Bool},
    xs.length=ys.length→ bitsValue xs=bitsValue ys→ xs=ys
  | [], [],_,_ => rfl
  | [],_::_,hlen,_ => by simp at hlen
  | _::_, [],hlen,_ => by simp at hlen
  | x::xs,y::ys,hlen,hval => by
      have hxy:x=y:=by
        have:=congrArg Nat.bodd hval
        simpa [bitsValue,Nat.bodd_bit] using this
      have htail:bitsValue xs=bitsValue ys:=by
        have:=congrArg Nat.div2 hval
        simpa [bitsValue,Nat.div2_bit] using this
      subst y
      have hlen':xs.length=ys.length:=by simpa using hlen
      exact congrArg (x::·) (bitsValue_injective_of_length hlen' htail)

@[simp] theorem fixedBits_mod_word (w n:ℕ):
    fixedBits w (n % 2 ^ w)=fixedBits w n:=by
  apply bitsValue_injective_of_length
  · simp
  · simp [Nat.mod_eq_of_lt (Nat.mod_lt n (Nat.two_pow_pos w))]

theorem fullAdder_value (a b carry:Bool):
    (fullAdder a b carry).1.toNat + 2 * (fullAdder a b carry).2.toNat =
      a.toNat + b.toNat + carry.toNat:=by
  cases a <;> cases b <;> cases carry <;> decide

def addBits:List Bool→ List Bool→ Bool→ List Bool
  | a::as,b::bs,carry =>
      let q:=fullAdder a b carry
      q.1::addBits as bs q.2
  | _,_,_ => []

theorem addBits_length_of_eq {as bs:List Bool} (carry:Bool)
    (h:as.length=bs.length):(addBits as bs carry).length=as.length:=by
  induction as generalizing bs carry with
  | nil => simp [addBits]
  | cons a as ih =>
      cases bs with
      | nil => simp at h
      | cons b bs =>
        simp at h
        simp [addBits,ih _ h]

theorem div2_add_carry (a b:ℕ) (carry:Bool):
    (a + b + carry.toNat).div2 =
      a.div2 + b.div2 + (fullAdder a.bodd b.bodd carry).2.toNat:=by
  have ha:=Nat.bodd_add_div2 a
  have hb:=Nat.bodd_add_div2 b
  have hf:=fullAdder_value a.bodd b.bodd carry
  cases hca:a.bodd <;> cases hcb:b.bodd <;> cases carry <;>
    simp_all [Nat.div2_val,fullAdder] <;> omega

theorem bodd_add_carry (a b:ℕ) (carry:Bool):
    (a + b + carry.toNat).bodd=(fullAdder a.bodd b.bodd carry).1:=by
  cases carry <;> simp [fullAdder,Nat.bodd_add,Bool.xor_assoc]

theorem fixedBits_add_carry (w a b:ℕ) (carry:Bool):
    fixedBits w (a + b + carry.toNat) =
      addBits (fixedBits w a) (fixedBits w b) carry:=by
  induction w generalizing a b carry with
  | zero => rfl
  | succ w ih =>
      simp only [fixedBits,addBits]
      rw [bodd_add_carry,div2_add_carry,ih]

@[simp] theorem fixedBits_zero (w:ℕ):
    fixedBits w 0=List.replicate w false:=by
  induction w <;> simp [fixedBits,List.replicate_succ, *]

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def addCarryOut:List Bool→ List Bool→ Bool→ Bool
  | a::as,b::bs,carry => (addCarryOut as bs (fullAdder a b carry).2)
  | _,_,carry => carry

inductive MoveStack | source | target
  deriving DecidableEq,Fintype,Inhabited

inductive MoveLabel | loop | done
  deriving DecidableEq,Fintype,Inhabited

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive CompareStack | left | right | leftBackup | rightBackup
  deriving DecidableEq,Fintype,Inhabited

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

@[simp] theorem encodeFixedWord_length (w n:ℕ):
    (encodeFixedWord w n).length=w + 1:=by
  simp [encodeFixedWord]

@[simp] theorem encodeWordList_length (w:ℕ) (xs:List ℕ):
    (encodeWordList w xs).length=xs.length * (w + 1):=by
  induction xs with
  | nil => simp [encodeWordList]
  | cons x xs ih => simp [encodeWordList,ih,Nat.add_mul]; omega

@[simp] theorem encodeSparseCell_length (w:ℕ) (cell:ℕ × ℕ):
    (encodeSparseCell w cell).length=2 * w + 3:=by
  simp [encodeSparseCell]
  omega

@[simp] theorem encodeSparseMemory_length (w:ℕ) (m:SparseMemory):
    (encodeSparseMemory w m).length=m.length * (2 * w + 3):=by
  induction m with
  | nil => simp [encodeSparseMemory]
  | cons cell m ih => simp [encodeSparseMemory,ih,Nat.add_mul]; omega

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

def SparseSymbol.bitValue:SparseSymbol→ Bool
  | .bit b => b
  | _ => false

@[simp] theorem SparseSymbol.bitValue_bit (b:Bool):
    (SparseSymbol.bit b).bitValue=b:=rfl

@[simp] theorem drop_one_cons {α:Type} (a:α) (xs:List α):
    (a::xs).drop 1=xs:=rfl

def consumeMarker:List SparseSymbol→ List SparseSymbol
  | [] => []
  | _::xs => xs

@[simp] theorem consumeMarker_cons (a:SparseSymbol) (xs:List SparseSymbol):
    consumeMarker (a::xs)=xs:=rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

@[simp] theorem SparseMemory.normalized_nil (w:ℕ):
    SparseMemory.Normalized w []:=by simp [SparseMemory.Normalized]

theorem SparseMemory.write_normalized (w:ℕ) {m:SparseMemory}
    (hm:m.Normalized w) (a v:ℕ):
    (m.write w a v).Normalized w:=by
  exact ⟨Nat.mod_lt _ (by positivity),Nat.mod_lt _ (by positivity),hm⟩

theorem sparseEffect_mem_normalized {w:ℕ} {i:Instr} {s s':SparseState}
    (hm:s.mem.Normalized w) (h:sparseEffect w i s=some s'):
    s'.mem.Normalized w:=by
  cases i <;> simp [sparseEffect] at h
  case read a =>
    cases hin:s.inp with
    | nil => simp [hin] at h
    | cons v inp =>
      simp [hin] at h
      subst s'
      exact SparseMemory.write_normalized w hm a v
  all_goals
    subst s'
    first
    | exact SparseMemory.write_normalized _ hm _ _
    | exact hm

theorem sparseStep_mem_normalized {w:ℕ} {p:Program} {s s':SparseState}
    (hm:s.mem.Normalized w) (h:sparseStep w p s=some s'):
    s'.mem.Normalized w:=by
  unfold sparseStep at h
  cases hi:p[s.pc]? with
  | none => simp [hi] at h
  | some i =>
      simp [hi] at h
      exact sparseEffect_mem_normalized hm h

theorem sparseRun_mem_normalized {w:ℕ} {p:Program} {t:ℕ}
    {s s':SparseState} (hm:s.mem.Normalized w)
    (h:sparseRun w p t s=some s'):s'.mem.Normalized w:=by
  induction t generalizing s with
  | zero =>
      simp [sparseRun] at h
      subst s'
      exact hm
  | succ t ih =>
      simp only [sparseRun] at h
      cases hs:sparseStep w p s with
      | none => simp [hs] at h
      | some s₁ =>
        simp [hs] at h
        exact ih (sparseStep_mem_normalized hm hs) h

theorem sparseRun_init_mem_normalized {w:ℕ} {p:Program} {x:List ℕ}
    {t:ℕ} {s:SparseState}
    (h:sparseRun w p t (sparseInitState x)=some s):
    s.mem.Normalized w:=
  sparseRun_mem_normalized (SparseMemory.normalized_nil w) h

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def symbolsEqual:List SparseSymbol→ List SparseSymbol→ Bool→ Bool
  | a::as,b::bs,equal => symbolsEqual as bs (equal && decide (a=b))
  | _,_,equal => equal

structure SymbolEqualControl where
  equal:Bool
  left:Option SparseSymbol
  right:Option SparseSymbol
  deriving DecidableEq,Fintype,Inhabited

inductive SymbolEqualStack | left | right | leftBackup | rightBackup
  deriving DecidableEq,Fintype,Inhabited

@[simp] theorem symbolsEqual_false (as bs:List SparseSymbol):
    symbolsEqual as bs false=false:=by
  induction as generalizing bs with
  | nil => simp [symbolsEqual]
  | cons a as ih =>
      cases bs <;> simp [symbolsEqual,ih]

theorem symbolsEqual_true_of_length (as bs:List SparseSymbol)
    (hlen:as.length=bs.length):symbolsEqual as bs true=decide (as=bs):=by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [symbolsEqual]
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
        simp at hlen
        by_cases hab:a=b
        · subst b
          simp [symbolsEqual,ih bs hlen]
        · simp [symbolsEqual,hab]

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

def SparseMemory.find?:SparseMemory→ ℕ→ Option ℕ
  | [],_ => none
  | (a,v)::m,target =>
      if target=a then some v else SparseMemory.find? m target

@[simp] theorem SparseMemory.find?_getD (m:SparseMemory) (a:ℕ):
    (SparseMemory.find? m a).getD 0=m.read a:=by
  induction m with
  | nil => rfl
  | cons cell m ih =>
      rcases cell with ⟨b,v⟩
      by_cases h:a=b <;> simp [SparseMemory.find?,SparseMemory.read,h,ih]

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def symbolMoveStacks (source target:List SparseSymbol):
    SymbolMoveStack→ List SparseSymbol
  | .source => source
  | .target => target

def symbolMoveCfg (source target:List SparseSymbol):symbolMoveMachine.Cfg where
  l:=some .loop
  var:=default
  stk:=symbolMoveStacks source target

def symbolMoveCfgState (state:SymbolMoveControl)
    (source target:List SparseSymbol):symbolMoveMachine.Cfg where
  l:=some .loop
  var:=state
  stk:=symbolMoveStacks source target

def symbolMoveDoneCfg (target:List SparseSymbol):symbolMoveMachine.Cfg where
  l:=some .done
  var:=default
  stk:=symbolMoveStacks [] target

@[simp] theorem symbolMove_step_state_nil (state:SymbolMoveControl)
    (target:List SparseSymbol):
    symbolMoveMachine.step (symbolMoveCfgState state [] target) =
      some (symbolMoveDoneCfg target):=by
  change some (TM2.stepAux
    (symbolMoveIteration SymbolMoveStack.source SymbolMoveStack.target
      SymbolMoveLabel.loop SymbolMoveLabel.done)
    state (symbolMoveStacks [] target))=_
  simp [symbolMoveIteration,symbolMoveDoneCfg,symbolMoveCfgState,
    symbolMoveStacks]
  congr 2

@[simp] theorem symbolMove_step_state_cons (state:SymbolMoveControl)
    (a:SparseSymbol) (source target:List SparseSymbol):
    symbolMoveMachine.step (symbolMoveCfgState state (a::source) target) =
      some (symbolMoveCfg source (a::target)):=by
  change some (TM2.stepAux
    (symbolMoveIteration SymbolMoveStack.source SymbolMoveStack.target
      SymbolMoveLabel.loop SymbolMoveLabel.done)
    state (symbolMoveStacks (a::source) target))=_
  simp [symbolMoveIteration,symbolMoveCfgState,symbolMoveCfg,
    symbolMoveStacks]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem symbolMove_step_nil (target:List SparseSymbol):
    symbolMoveMachine.step (symbolMoveCfg [] target) =
      some (symbolMoveDoneCfg target):=by
  change some (TM2.stepAux
    (symbolMoveIteration SymbolMoveStack.source SymbolMoveStack.target
      SymbolMoveLabel.loop SymbolMoveLabel.done)
    default (symbolMoveStacks [] target))=_
  simp [symbolMoveIteration,symbolMoveDoneCfg,symbolMoveStacks]
  congr 2

@[simp] theorem symbolMove_step_cons (a:SparseSymbol)
    (source target:List SparseSymbol):
    symbolMoveMachine.step (symbolMoveCfg (a::source) target) =
      some (symbolMoveCfg source (a::target)):=by
  change some (TM2.stepAux
    (symbolMoveIteration SymbolMoveStack.source SymbolMoveStack.target
      SymbolMoveLabel.loop SymbolMoveLabel.done)
    default (symbolMoveStacks (a::source) target))=_
  simp [symbolMoveIteration,symbolMoveCfg,symbolMoveStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem symbolMove_iterate (source target:List SparseSymbol):
    ((fun o:Option symbolMoveMachine.Cfg => o.bind symbolMoveMachine.step)^[source.length])
        (some (symbolMoveCfg source target)) =
      some (symbolMoveCfg [] (source.reverse ++ target)):=by
  induction source generalizing target with
  | nil => rfl
  | cons a source ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,symbolMove_step_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem symbolMove_reaches_done (source target:List SparseSymbol):
    ((fun o:Option symbolMoveMachine.Cfg => o.bind symbolMoveMachine.step)^[source.length + 1])
        (some (symbolMoveCfg source target)) =
      some (symbolMoveDoneCfg (source.reverse ++ target)):=by
  rw [Nat.add_comm,Function.iterate_add_apply,symbolMove_iterate]
  simp only [Function.iterate_one,Option.bind_some,symbolMove_step_nil]

theorem symbolMove_reaches_done_from (state:SymbolMoveControl)
    (source target:List SparseSymbol):
    ((fun o:Option symbolMoveMachine.Cfg => o.bind symbolMoveMachine.step)^[
      source.length + 1])
      (some (symbolMoveCfgState state source target)) =
      some (symbolMoveDoneCfg (source.reverse ++ target)):=by
  cases source with
  | nil => simpa using! symbolMove_step_state_nil state target
  | cons a source =>
      rw [List.length_cons,
        show source.length + 1 + 1=(source.length + 1) + 1 by omega,
        Function.iterate_succ_apply]
      simp only [Option.bind_some,symbolMove_step_state_cons]
      simpa [List.reverse_cons,List.append_assoc] using
        symbolMove_reaches_done source (a::target)

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive LookupCellStack
  | source | address | value | cellBackup | query | addressBackup | queryBackup
  deriving DecidableEq,Fintype,Inhabited

inductive LookupCellLabel | address | value | cellEnd | compare | done
  deriving DecidableEq,Fintype,Inhabited

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

theorem sparseEffect_out_length_le {w:ℕ} {i:Instr} {s s':SparseState}
    (h:sparseEffect w i s=some s'):s'.out.length≤ s.out.length + 1:=by
  cases i <;> simp [sparseEffect] at h
  case read a =>
    cases hin:s.inp with
    | nil => simp [hin] at h
    | cons v inp => simp [hin] at h; subst s'; simp
  all_goals subst s' <;> simp

theorem sparseStep_out_length_le {w:ℕ} {p:Program} {s s':SparseState}
    (h:sparseStep w p s=some s'):s'.out.length≤ s.out.length + 1:=by
  unfold sparseStep at h
  cases hi:p[s.pc]? with
  | none => simp [hi] at h
  | some i =>
      simp [hi] at h
      exact sparseEffect_out_length_le h

theorem sparseRun_out_length_le {w:ℕ} {p:Program} {t:ℕ}
    {s s':SparseState} (h:sparseRun w p t s=some s'):
    s'.out.length≤ s.out.length + t:=by
  induction t generalizing s with
  | zero => simp [sparseRun] at h; subst s'; omega
  | succ t ih =>
      simp only [sparseRun] at h
      cases hs:sparseStep w p s with
      | none => simp [hs] at h
      | some s₁ =>
        simp [hs] at h
        have hstep:=sparseStep_out_length_le hs
        have hrest:=ih h
        omega

theorem sparseRun_init_out_length_le {w:ℕ} {p:Program} {x:List ℕ}
    {t:ℕ} {s:SparseState}
    (h:sparseRun w p t (sparseInitState x)=some s):
    s.out.length≤ t:=by
  simpa [sparseInitState] using sparseRun_out_length_le h

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def lookupScanStacks (source address value cellBackup query addressBackup queryBackup
    processed trash:List SparseSymbol):LookupScanStack→ List SparseSymbol
  | .source => source
  | .address => address
  | .value => value
  | .cellBackup => cellBackup
  | .query => query
  | .addressBackup => addressBackup
  | .queryBackup => queryBackup
  | .processed => processed
  | .trash => trash

def lookupScanCfg (label:LookupScanLabel) (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):lookupScanMachine.Cfg where
  l:=some label
  var:= ⟨none,equal,none,none⟩
  stk:=lookupScanStacks source address value cellBackup query addressBackup queryBackup
    processed trash

@[simp] theorem lookupScan_step_empty_memory (equal:Bool)
    (address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .scan equal [.memoryEnd] address value
      cellBackup query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .restoreMissing equal [.memoryEnd] address value cellBackup
      query addressBackup queryBackup processed trash):=by
  change some (TM2.stepAux
    (.peek LookupScanStack.source
      (fun s a => { s with held:=a }) <|
      .branch (fun s => s.held=some SparseSymbol.memoryEnd)
        (.load LookupCellControl.clearHeld <| .goto fun _ => LookupScanLabel.restoreMissing)
        (.load (fun s => { (LookupCellControl.clearHeld s) with equal:=true }) <|
          .goto fun _ => LookupScanLabel.address))
    ⟨none,equal,none,none⟩
    (lookupScanStacks [.memoryEnd] address value cellBackup query addressBackup
      queryBackup processed trash))=_
  simp [LookupCellControl.clearHeld,lookupScanCfg,lookupScanStacks]

theorem lookupScan_step_cell_start (equal:Bool) (a:SparseSymbol)
    (ha:a ≠ .memoryEnd)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .scan equal (a::source) address value
      cellBackup query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .address true (a::source) address value cellBackup query
      addressBackup queryBackup processed trash):=by
  change some (TM2.stepAux
    (.peek LookupScanStack.source (fun s a => { s with held:=a }) <|
      .branch (fun s => s.held=some SparseSymbol.memoryEnd)
        (.load LookupCellControl.clearHeld <| .goto fun _ => LookupScanLabel.restoreMissing)
        (.load (fun s => { (LookupCellControl.clearHeld s) with equal:=true }) <|
          .goto fun _ => LookupScanLabel.address))
    ⟨none,equal,none,none⟩
    (lookupScanStacks (a::source) address value cellBackup query addressBackup
      queryBackup processed trash))=_
  simp [ha,LookupCellControl.clearHeld,lookupScanCfg,lookupScanStacks]

theorem lookupScan_step_encoded_cell (equal:Bool) (w a v:ℕ)
    (suffix address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .scan equal
      (encodeSparseCell w (a,v) ++ suffix) address value cellBackup query addressBackup
      queryBackup processed trash) =
    some (lookupScanCfg .address true (encodeSparseCell w (a,v) ++ suffix) address
      value cellBackup query addressBackup queryBackup processed trash):=by
  cases w with
  | zero =>
      simpa [encodeSparseCell,encodeFixedWord,fixedBits] using
        lookupScan_step_cell_start equal SparseSymbol.wordEnd (by simp)
          (encodeFixedWord 0 v ++ .cellEnd::suffix) address value cellBackup query
          addressBackup queryBackup processed trash
  | succ w =>
      simpa [encodeSparseCell,encodeFixedWord,fixedBits] using
        lookupScan_step_cell_start equal (.bit a.bodd) (by simp)
          ((fixedBits w a.div2).map SparseSymbol.bit ++ .wordEnd::
            (encodeFixedWord (w + 1) v ++ .cellEnd::suffix))
          address value cellBackup query addressBackup queryBackup processed trash

@[simp] theorem lookupScan_step_address_bit (equal:Bool) (b:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .address equal (.bit b::source) address
      value cellBackup query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .address equal source (.bit b::address) value
      (.bit b::cellBackup) query addressBackup queryBackup processed trash):=by
  change some (TM2.stepAux
    (lookupCellWordIteration LookupScanStack.source LookupScanStack.address
      LookupScanStack.cellBackup LookupScanLabel.address LookupScanLabel.value)
    ⟨none,equal,none,none⟩
    (lookupScanStacks (.bit b::source) address value cellBackup query addressBackup
      queryBackup processed trash))=_
  simp [lookupCellWordIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem lookupScan_step_address_end (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .address equal (.wordEnd::source) address
      value cellBackup query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .value equal source address value (.wordEnd::cellBackup)
      query addressBackup queryBackup processed trash):=by
  change some (TM2.stepAux
    (lookupCellWordIteration LookupScanStack.source LookupScanStack.address
      LookupScanStack.cellBackup LookupScanLabel.address LookupScanLabel.value)
    ⟨none,equal,none,none⟩
    (lookupScanStacks (.wordEnd::source) address value cellBackup query addressBackup
      queryBackup processed trash))=_
  simp [lookupCellWordIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem lookupScan_step_value_bit (equal:Bool) (b:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .value equal (.bit b::source) address
      value cellBackup query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .value equal source address (.bit b::value)
      (.bit b::cellBackup) query addressBackup queryBackup processed trash):=by
  change some (TM2.stepAux
    (lookupCellWordIteration LookupScanStack.source LookupScanStack.value
      LookupScanStack.cellBackup LookupScanLabel.value LookupScanLabel.cellEnd)
    ⟨none,equal,none,none⟩
    (lookupScanStacks (.bit b::source) address value cellBackup query addressBackup
      queryBackup processed trash))=_
  simp [lookupCellWordIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem lookupScan_step_value_end (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .value equal (.wordEnd::source) address
      value cellBackup query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .cellEnd equal source address value (.wordEnd::cellBackup)
      query addressBackup queryBackup processed trash):=by
  change some (TM2.stepAux
    (lookupCellWordIteration LookupScanStack.source LookupScanStack.value
      LookupScanStack.cellBackup LookupScanLabel.value LookupScanLabel.cellEnd)
    ⟨none,equal,none,none⟩
    (lookupScanStacks (.wordEnd::source) address value cellBackup query addressBackup
      queryBackup processed trash))=_
  simp [lookupCellWordIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem lookupScan_step_cellEnd (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .cellEnd equal (.cellEnd::source) address
      value cellBackup query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .compare equal source address value (.cellEnd::cellBackup)
      query addressBackup queryBackup processed trash):=by
  change some (TM2.stepAux
    (.pop LookupScanStack.source (fun s a => { s with held:=a }) <|
      .push LookupScanStack.cellBackup (fun s => s.held.getD .cellEnd) <|
        .load LookupCellControl.clearHeld <| .goto fun _ => LookupScanLabel.compare)
    ⟨none,equal,none,none⟩
    (lookupScanStacks (.cellEnd::source) address value cellBackup query addressBackup
      queryBackup processed trash))=_
  simp [LookupCellControl.clearHeld,lookupScanCfg,lookupScanStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem lookupScan_step_compare_cons (equal:Bool) (a b:SparseSymbol)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .compare equal source (a::address) value
      cellBackup (b::query) addressBackup queryBackup processed trash) =
    some (lookupScanCfg .compare (equal && decide (a=b)) source address value
      cellBackup query (a::addressBackup) (b::queryBackup) processed trash):=by
  change some (TM2.stepAux
    (lookupCellCompareIteration LookupScanStack.address LookupScanStack.query
      LookupScanStack.addressBackup LookupScanStack.queryBackup LookupScanLabel.compare
      LookupScanLabel.decide)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source (a::address) value cellBackup (b::query)
      addressBackup queryBackup processed trash))=_
  simp [lookupCellCompareIteration,LookupCellControl.compareAdvance,lookupScanCfg,
    lookupScanStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem lookupScan_step_compare_nil (equal:Bool)
    (source value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .compare equal source [] value cellBackup
      query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .decide equal source [] value cellBackup query addressBackup
      queryBackup processed trash):=by
  change some (TM2.stepAux
    (lookupCellCompareIteration LookupScanStack.address LookupScanStack.query
      LookupScanStack.addressBackup LookupScanStack.queryBackup LookupScanLabel.compare
      LookupScanLabel.decide)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source [] value cellBackup query addressBackup queryBackup
      processed trash))=_
  simp [lookupCellCompareIteration,lookupScanCfg,lookupScanStacks]

theorem lookupScan_address_iterate (equal:Bool) (xs:List Bool)
    (suffix address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[xs.length])
      (some (lookupScanCfg .address equal
        (xs.map SparseSymbol.bit ++ .wordEnd::suffix) address value cellBackup query
        addressBackup queryBackup processed trash)) =
    some (lookupScanCfg .address equal (.wordEnd::suffix)
      (xs.reverse.map SparseSymbol.bit ++ address) value
      (xs.reverse.map SparseSymbol.bit ++ cellBackup) query addressBackup queryBackup
      processed trash):=by
  induction xs generalizing address cellBackup with
  | nil => rfl
  | cons b xs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [List.map_cons,List.cons_append,Option.bind_some,
        lookupScan_step_address_bit]
      rw [ih]
      simp [List.reverse_cons,List.map_append,List.append_assoc]

theorem lookupScan_value_iterate (equal:Bool) (xs:List Bool)
    (suffix address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[xs.length])
      (some (lookupScanCfg .value equal
        (xs.map SparseSymbol.bit ++ .wordEnd::suffix) address value cellBackup query
        addressBackup queryBackup processed trash)) =
    some (lookupScanCfg .value equal (.wordEnd::suffix) address
      (xs.reverse.map SparseSymbol.bit ++ value)
      (xs.reverse.map SparseSymbol.bit ++ cellBackup) query addressBackup queryBackup
      processed trash):=by
  induction xs generalizing value cellBackup with
  | nil => rfl
  | cons b xs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [List.map_cons,List.cons_append,Option.bind_some,
        lookupScan_step_value_bit]
      rw [ih]
      simp [List.reverse_cons,List.map_append,List.append_assoc]

theorem lookupScan_compare_iterate (equal:Bool)
    (address query source value cellBackup addressBackup queryBackup processed trash:
      List SparseSymbol) (hlen:address.length=query.length):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      address.length])
      (some (lookupScanCfg .compare equal source address value cellBackup query
        addressBackup queryBackup processed trash)) =
    some (lookupScanCfg .compare (symbolsEqual address query equal) source [] value
      cellBackup [] (address.reverse ++ addressBackup) (query.reverse ++ queryBackup)
      processed trash):=by
  induction address generalizing query equal addressBackup queryBackup with
  | nil =>
      cases query with
      | nil => rfl
      | cons q query => simp at hlen
  | cons a address ih =>
      cases query with
      | nil => simp at hlen
      | cons b query =>
        simp at hlen
        rw [List.length_cons,Function.iterate_succ_apply]
        simp only [Option.bind_some,lookupScan_step_compare_cons]
        rw [ih (query:=query) (equal:=equal && decide (a=b))
          (addressBackup:=a::addressBackup)
          (queryBackup:=b::queryBackup) hlen]
        simp [symbolsEqual,List.reverse_cons,List.append_assoc]

theorem lookupScan_compare_reaches_decide (equal:Bool)
    (address query source value cellBackup addressBackup queryBackup processed trash:
      List SparseSymbol) (hlen:address.length=query.length):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      address.length + 1])
      (some (lookupScanCfg .compare equal source address value cellBackup query
        addressBackup queryBackup processed trash)) =
    some (lookupScanCfg .decide (symbolsEqual address query equal) source [] value
      cellBackup [] (address.reverse ++ addressBackup) (query.reverse ++ queryBackup)
      processed trash):=by
  rw [Nat.add_comm,Function.iterate_add_apply,
    lookupScan_compare_iterate equal address query source value cellBackup
      addressBackup queryBackup processed trash hlen]
  simp only [Function.iterate_one,Option.bind_some,lookupScan_step_compare_nil]

theorem lookupScan_parse_fixed (equal:Bool) (w a v:ℕ)
    (suffix query processed trash:List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      2 * w + 3])
      (some (lookupScanCfg .address equal (encodeSparseCell w (a,v) ++ suffix)
        [] [] [] query [] [] processed trash)) =
    some (lookupScanCfg .compare equal suffix
      ((fixedBits w a).reverse.map SparseSymbol.bit)
      ((fixedBits w v).reverse.map SparseSymbol.bit)
      (.cellEnd::.wordEnd::(fixedBits w v).reverse.map SparseSymbol.bit ++
        .wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit)
      query [] [] processed trash):=by
  let stepO:=fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step
  have haRun:=lookupScan_address_iterate equal (fixedBits w a)
    (encodeFixedWord w v ++ .cellEnd::suffix) [] [] [] query [] [] processed trash
  have haEnd:(stepO^[1])
      (some (lookupScanCfg .address equal
        (.wordEnd::(encodeFixedWord w v ++ .cellEnd::suffix))
        ((fixedBits w a).reverse.map SparseSymbol.bit) []
        ((fixedBits w a).reverse.map SparseSymbol.bit) query [] [] processed trash)) =
      some (lookupScanCfg .value equal
        (encodeFixedWord w v ++ .cellEnd::suffix)
        ((fixedBits w a).reverse.map SparseSymbol.bit) []
        (.wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit) query [] []
        processed trash):=by
    simpa [stepO,List.map_reverse] using
      lookupScan_step_address_end equal
        (encodeFixedWord w v ++ .cellEnd::suffix)
        ((fixedBits w a).reverse.map SparseSymbol.bit) []
        ((fixedBits w a).reverse.map SparseSymbol.bit) query [] [] processed trash
  have hvRun:=lookupScan_value_iterate equal (fixedBits w v) (.cellEnd::suffix)
    ((fixedBits w a).reverse.map SparseSymbol.bit) []
    (.wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit) query [] [] processed trash
  have hvRun':(stepO^[w])
      (some (lookupScanCfg .value equal
        (encodeFixedWord w v ++ .cellEnd::suffix)
        ((fixedBits w a).reverse.map SparseSymbol.bit) []
        (.wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit) query [] []
        processed trash)) =
      some (lookupScanCfg .value equal (.wordEnd::.cellEnd::suffix)
        ((fixedBits w a).reverse.map SparseSymbol.bit)
        ((fixedBits w v).reverse.map SparseSymbol.bit)
        ((fixedBits w v).reverse.map SparseSymbol.bit ++
          (.wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit)) query [] []
        processed trash):=by
    simpa [stepO,encodeFixedWord,List.append_assoc] using hvRun
  have hvEnd:(stepO^[1])
      (some (lookupScanCfg .value equal (.wordEnd::.cellEnd::suffix)
        ((fixedBits w a).reverse.map SparseSymbol.bit)
        ((fixedBits w v).reverse.map SparseSymbol.bit)
        ((fixedBits w v).reverse.map SparseSymbol.bit ++
          (.wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit)) query [] []
        processed trash)) =
      some (lookupScanCfg .cellEnd equal (.cellEnd::suffix)
        ((fixedBits w a).reverse.map SparseSymbol.bit)
        ((fixedBits w v).reverse.map SparseSymbol.bit)
        (.wordEnd::((fixedBits w v).reverse.map SparseSymbol.bit ++
          (.wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit))) query [] []
        processed trash):=by
    simpa [stepO,List.map_reverse] using
      lookupScan_step_value_end equal (.cellEnd::suffix)
        ((fixedBits w a).reverse.map SparseSymbol.bit)
        ((fixedBits w v).reverse.map SparseSymbol.bit)
        ((fixedBits w v).reverse.map SparseSymbol.bit ++
          (.wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit)) query [] []
        processed trash
  have hcEnd:(stepO^[1])
      (some (lookupScanCfg .cellEnd equal (.cellEnd::suffix)
        ((fixedBits w a).reverse.map SparseSymbol.bit)
        ((fixedBits w v).reverse.map SparseSymbol.bit)
        (.wordEnd::((fixedBits w v).reverse.map SparseSymbol.bit ++
          (.wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit))) query [] []
        processed trash)) =
      some (lookupScanCfg .compare equal suffix
        ((fixedBits w a).reverse.map SparseSymbol.bit)
        ((fixedBits w v).reverse.map SparseSymbol.bit)
        (.cellEnd::.wordEnd::((fixedBits w v).reverse.map SparseSymbol.bit ++
          (.wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit))) query [] []
        processed trash):=by
    simpa [stepO,List.map_reverse] using
      lookupScan_step_cellEnd equal suffix
        ((fixedBits w a).reverse.map SparseSymbol.bit)
        ((fixedBits w v).reverse.map SparseSymbol.bit)
        (.wordEnd::((fixedBits w v).reverse.map SparseSymbol.bit ++
          (.wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit))) query [] []
        processed trash
  simp only [fixedBits_length,List.append_nil] at haRun hvRun
  have chain {m n:ℕ} {x y z:Option lookupScanMachine.Cfg}
      (h₁:(stepO^[m]) x=y) (h₂:(stepO^[n]) y=z):
      (stepO^[n + m]) x=z:=by
    rw [Function.iterate_add_apply,h₁,h₂]
  have hrun:=chain (chain (chain (chain haRun haEnd) hvRun') hvEnd) hcEnd
  have hexp:1 + (1 + (w + (1 + w)))=2 * w + 3:=by omega
  rw [hexp] at hrun
  simpa [stepO,encodeSparseCell,encodeFixedWord,List.append_assoc] using hrun

theorem lookupScan_fixed_reaches_decide (w a v query:ℕ)
    (ha:a < 2 ^ w) (hq:query < 2 ^ w)
    (suffix processed trash:List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      3 * w + 4])
      (some (lookupScanCfg .address true (encodeSparseCell w (a,v) ++ suffix)
        [] [] [] ((fixedBits w query).reverse.map SparseSymbol.bit) [] []
        processed trash)) =
    some (lookupScanCfg .decide (decide (a=query)) suffix []
      ((fixedBits w v).reverse.map SparseSymbol.bit)
      (.cellEnd::.wordEnd::(fixedBits w v).reverse.map SparseSymbol.bit ++
        .wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit)
      [] ((fixedBits w a).map SparseSymbol.bit)
      ((fixedBits w query).map SparseSymbol.bit) processed trash):=by
  let stepO:=fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step
  have hparse:=lookupScan_parse_fixed true w a v suffix
    ((fixedBits w query).reverse.map SparseSymbol.bit) processed trash
  have hcompare:=lookupScan_compare_reaches_decide true
    ((fixedBits w a).reverse.map SparseSymbol.bit)
    ((fixedBits w query).reverse.map SparseSymbol.bit) suffix
    ((fixedBits w v).reverse.map SparseSymbol.bit)
    (.cellEnd::.wordEnd::(fixedBits w v).reverse.map SparseSymbol.bit ++
      .wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit) [] [] processed trash
    (by simp)
  simp only [List.length_map,List.length_reverse,fixedBits_length] at hcompare
  have chain {m n:ℕ} {x y z:Option lookupScanMachine.Cfg}
      (h₁:(stepO^[m]) x=y) (h₂:(stepO^[n]) y=z):
      (stepO^[n + m]) x=z:=by
    rw [Function.iterate_add_apply,h₁,h₂]
  have hrun:=chain hparse hcompare
  have hexp:(w + 1) + (2 * w + 3)=3 * w + 4:=by omega
  rw [hexp] at hrun
  change (stepO^[3 * w + 4])
      (some (lookupScanCfg .address true (encodeSparseCell w (a,v) ++ suffix)
        [] [] [] ((fixedBits w query).reverse.map SparseSymbol.bit) [] []
        processed trash))=_
  rw [hrun,symbolsEqual_true_of_length _ _ (by simp)]
  have heq:
      decide ((fixedBits w a).reverse.map SparseSymbol.bit =
        (fixedBits w query).reverse.map SparseSymbol.bit)=decide (a=query):=by
    by_cases h:a=query
    · subst query
      simp
    · have hplain:¬((fixedBits w a).map SparseSymbol.bit =
          (fixedBits w query).map SparseSymbol.bit):=by
        intro hm
        apply h
        have hv:=congrArg (List.map SparseSymbol.bitValue) hm
        have hfun:SparseSymbol.bitValue ∘ SparseSymbol.bit=id:=by
          funext bit
          cases bit <;> rfl
        have hbits:fixedBits w a=fixedBits w query:=by
          simpa only [List.map_map,hfun,List.map_id] using hv
        have hvalues:=congrArg bitsValue hbits
        simpa [bitsValue_fixedBits_of_lt ha,bitsValue_fixedBits_of_lt hq] using hvalues
      simp [h,hplain]
  rw [heq]
  simp

@[simp] theorem lookupScan_step_preserveCell_nil (equal:Bool)
    (source address value query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .preserveCell equal source address value []
      query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .moveCell equal source address value [] query addressBackup
      queryBackup processed trash):=by
  change some (TM2.stepAux
    (lookupScanMoveIteration LookupScanStack.cellBackup LookupScanStack.trash
      LookupScanLabel.preserveCell LookupScanLabel.moveCell)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source address value [] query addressBackup queryBackup processed
      trash))=_
  simp [lookupScanMoveIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks]

@[simp] theorem lookupScan_step_preserveCell_cons (equal:Bool) (a:SparseSymbol)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .preserveCell equal source address value
      (a::cellBackup) query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .preserveCell equal source address value cellBackup query
      addressBackup queryBackup processed (a::trash)):=by
  change some (TM2.stepAux
    (lookupScanMoveIteration LookupScanStack.cellBackup LookupScanStack.trash
      LookupScanLabel.preserveCell LookupScanLabel.moveCell)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source address value (a::cellBackup) query addressBackup
      queryBackup processed trash))=_
  simp [lookupScanMoveIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem lookupScan_preserveCell_reaches_moveCell (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      cellBackup.length + 1])
      (some (lookupScanCfg .preserveCell equal source address value cellBackup query
        addressBackup queryBackup processed trash)) =
    some (lookupScanCfg .moveCell equal source address value [] query addressBackup
      queryBackup processed (cellBackup.reverse ++ trash)):=by
  induction cellBackup generalizing trash with
  | nil =>
      simp only [List.length_nil,Nat.zero_add,Function.iterate_one,
        Option.bind_some,lookupScan_step_preserveCell_nil,List.reverse_nil,
        List.nil_append]
  | cons a cellBackup ih =>
      rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
      simp only [Option.bind_some,lookupScan_step_preserveCell_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

@[simp] theorem lookupScan_step_moveCell_nil (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .moveCell equal source address value cellBackup
      query addressBackup queryBackup processed []) =
    some (lookupScanCfg .afterMove equal source address value cellBackup query
      addressBackup queryBackup processed []):=by
  change some (TM2.stepAux
    (lookupScanMoveIteration LookupScanStack.trash LookupScanStack.processed
      LookupScanLabel.moveCell LookupScanLabel.afterMove)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source address value cellBackup query addressBackup queryBackup
      processed []))=_
  simp [lookupScanMoveIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks]

@[simp] theorem lookupScan_step_moveCell_cons (equal:Bool) (a:SparseSymbol)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .moveCell equal source address value
      cellBackup query addressBackup queryBackup processed (a::trash)) =
    some (lookupScanCfg .moveCell equal source address value cellBackup query
      addressBackup queryBackup (a::processed) trash):=by
  change some (TM2.stepAux
    (lookupScanMoveIteration LookupScanStack.trash LookupScanStack.processed
      LookupScanLabel.moveCell LookupScanLabel.afterMove)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source address value cellBackup query addressBackup
      queryBackup processed (a::trash)))=_
  simp [lookupScanMoveIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem lookupScan_moveCell_iterate (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      trash.length])
      (some (lookupScanCfg .moveCell equal source address value cellBackup query
        addressBackup queryBackup processed trash)) =
    some (lookupScanCfg .moveCell equal source address value cellBackup query addressBackup
      queryBackup (trash.reverse ++ processed) []):=by
  induction trash generalizing processed with
  | nil => rfl
  | cons a trash ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,lookupScan_step_moveCell_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem lookupScan_moveCell_reaches_afterMove (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      trash.length + 1])
      (some (lookupScanCfg .moveCell equal source address value cellBackup query
        addressBackup queryBackup processed trash)) =
    some (lookupScanCfg .afterMove equal source address value cellBackup query addressBackup
      queryBackup (trash.reverse ++ processed) []):=by
  rw [Nat.add_comm,Function.iterate_add_apply,lookupScan_moveCell_iterate]
  simp only [Function.iterate_one,Option.bind_some,lookupScan_step_moveCell_nil]

@[simp] theorem lookupScan_step_discardValue_nil (equal:Bool)
    (source address cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .discardValue equal source address []
      cellBackup query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .preserveCell equal source address [] cellBackup query
      addressBackup queryBackup processed trash):=by
  change some (TM2.stepAux
    (lookupScanDiscardIteration LookupScanStack.value LookupScanLabel.discardValue
      LookupScanLabel.preserveCell)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source address [] cellBackup query addressBackup queryBackup
      processed trash))=_
  simp [lookupScanDiscardIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks]

@[simp] theorem lookupScan_step_discardValue_cons (equal:Bool) (a:SparseSymbol)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .discardValue equal source address
      (a::value) cellBackup query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .discardValue equal source address value cellBackup query
      addressBackup queryBackup processed trash):=by
  change some (TM2.stepAux
    (lookupScanDiscardIteration LookupScanStack.value LookupScanLabel.discardValue
      LookupScanLabel.preserveCell)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source address (a::value) cellBackup query addressBackup
      queryBackup processed trash))=_
  simp [lookupScanDiscardIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem lookupScan_discardValue_reaches_preserveCell (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      value.length + 1])
      (some (lookupScanCfg .discardValue equal source address value cellBackup query
        addressBackup queryBackup processed trash)) =
    some (lookupScanCfg .preserveCell equal source address [] cellBackup query
      addressBackup queryBackup processed trash):=by
  induction value with
  | nil =>
      simp only [List.length_nil,Nat.zero_add,Function.iterate_one,
        Option.bind_some,lookupScan_step_discardValue_nil]
  | cons a value ih =>
      rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
      simp only [Option.bind_some,lookupScan_step_discardValue_cons]
      exact ih

@[simp] theorem lookupScan_step_decide (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .decide equal source address value cellBackup
      query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .restoreQuery equal source address value cellBackup query
      addressBackup queryBackup processed trash):=by
  cases equal <;> simp [lookupScanMachine,lookupScanCfg,lookupScanStacks]
  all_goals congr 2

@[simp] theorem lookupScan_step_restoreQuery_nil (equal:Bool)
    (source address value cellBackup query addressBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .restoreQuery equal source address value
      cellBackup query addressBackup [] processed trash) =
    some (lookupScanCfg .discardAddress equal source address value cellBackup query
      addressBackup [] processed trash):=by
  change some (TM2.stepAux
    (lookupScanMoveIteration LookupScanStack.queryBackup LookupScanStack.query
      LookupScanLabel.restoreQuery LookupScanLabel.discardAddress)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source address value cellBackup query addressBackup [] processed
      trash))=_
  simp [lookupScanMoveIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks]

@[simp] theorem lookupScan_step_restoreQuery_cons (equal:Bool) (a:SparseSymbol)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .restoreQuery equal source address value
      cellBackup query addressBackup (a::queryBackup) processed trash) =
    some (lookupScanCfg .restoreQuery equal source address value cellBackup
      (a::query) addressBackup queryBackup processed trash):=by
  change some (TM2.stepAux
    (lookupScanMoveIteration LookupScanStack.queryBackup LookupScanStack.query
      LookupScanLabel.restoreQuery LookupScanLabel.discardAddress)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source address value cellBackup query addressBackup
      (a::queryBackup) processed trash))=_
  simp [lookupScanMoveIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem lookupScan_restoreQuery_reaches_discardAddress (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      queryBackup.length + 1])
      (some (lookupScanCfg .restoreQuery equal source address value cellBackup query
        addressBackup queryBackup processed trash)) =
    some (lookupScanCfg .discardAddress equal source address value cellBackup
      (queryBackup.reverse ++ query) addressBackup [] processed trash):=by
  induction queryBackup generalizing query with
  | nil =>
      simp only [List.length_nil,Nat.zero_add,Function.iterate_one,
        Option.bind_some,lookupScan_step_restoreQuery_nil,List.reverse_nil,
        List.nil_append]
  | cons a queryBackup ih =>
      rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
      simp only [Option.bind_some,lookupScan_step_restoreQuery_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

@[simp] theorem lookupScan_step_discardAddress_nil (equal:Bool)
    (source address value cellBackup query queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .discardAddress equal source address value
      cellBackup query [] queryBackup processed trash) =
    some (lookupScanCfg .afterCleanup equal source address value cellBackup query []
      queryBackup processed trash):=by
  change some (TM2.stepAux
    (lookupScanDiscardIteration LookupScanStack.addressBackup
      LookupScanLabel.discardAddress LookupScanLabel.afterCleanup)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source address value cellBackup query [] queryBackup processed
      trash))=_
  simp [lookupScanDiscardIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks]

@[simp] theorem lookupScan_step_discardAddress_cons (equal:Bool) (a:SparseSymbol)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .discardAddress equal source address value
      cellBackup query (a::addressBackup) queryBackup processed trash) =
    some (lookupScanCfg .discardAddress equal source address value cellBackup query
      addressBackup queryBackup processed trash):=by
  change some (TM2.stepAux
    (lookupScanDiscardIteration LookupScanStack.addressBackup
      LookupScanLabel.discardAddress LookupScanLabel.afterCleanup)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source address value cellBackup query (a::addressBackup)
      queryBackup processed trash))=_
  simp [lookupScanDiscardIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem lookupScan_discardAddress_reaches_afterCleanup (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      addressBackup.length + 1])
      (some (lookupScanCfg .discardAddress equal source address value cellBackup query
        addressBackup queryBackup processed trash)) =
    some (lookupScanCfg .afterCleanup equal source address value cellBackup query []
      queryBackup processed trash):=by
  induction addressBackup with
  | nil =>
      simp only [List.length_nil,Nat.zero_add,Function.iterate_one,
        Option.bind_some,lookupScan_step_discardAddress_nil]
  | cons a addressBackup ih =>
      rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
      simp only [Option.bind_some,lookupScan_step_discardAddress_cons]
      exact ih

@[simp] theorem lookupScan_step_afterCleanup_true
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .afterCleanup true source address value
      cellBackup query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .preserveCell true source address value cellBackup query
      addressBackup queryBackup processed trash):=by
  simp [lookupScanMachine,lookupScanCfg,lookupScanStacks]

@[simp] theorem lookupScan_step_afterCleanup_false
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .afterCleanup false source address value
      cellBackup query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .discardValue false source address value cellBackup query
      addressBackup queryBackup processed trash):=by
  simp [lookupScanMachine,lookupScanCfg,lookupScanStacks]

@[simp] theorem lookupScan_step_afterMove_true
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .afterMove true source address value
      cellBackup query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .restoreFound true source address value cellBackup query
      addressBackup queryBackup processed trash):=by
  simp [lookupScanMachine,lookupScanCfg,lookupScanStacks]

@[simp] theorem lookupScan_step_afterMove_false
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .afterMove false source address value
      cellBackup query addressBackup queryBackup processed trash) =
    some (lookupScanCfg .scan false source address value cellBackup query
      addressBackup queryBackup processed trash):=by
  simp [lookupScanMachine,lookupScanCfg,lookupScanStacks]

@[simp] theorem lookupScan_step_restoreFound_nil (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .restoreFound equal source address value
      cellBackup query addressBackup queryBackup [] trash) =
    some (lookupScanCfg .found equal source address value cellBackup query
      addressBackup queryBackup [] trash):=by
  change some (TM2.stepAux
    (lookupScanMoveIteration LookupScanStack.processed LookupScanStack.source
      LookupScanLabel.restoreFound LookupScanLabel.found)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source address value cellBackup query addressBackup queryBackup []
      trash))=_
  simp [lookupScanMoveIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks]

@[simp] theorem lookupScan_step_restoreFound_cons (equal:Bool) (a:SparseSymbol)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .restoreFound equal source address value
      cellBackup query addressBackup queryBackup (a::processed) trash) =
    some (lookupScanCfg .restoreFound equal (a::source) address value cellBackup query
      addressBackup queryBackup processed trash):=by
  change some (TM2.stepAux
    (lookupScanMoveIteration LookupScanStack.processed LookupScanStack.source
      LookupScanLabel.restoreFound LookupScanLabel.found)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source address value cellBackup query addressBackup queryBackup
      (a::processed) trash))=_
  simp [lookupScanMoveIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem lookupScan_restoreFound_reaches_found (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      processed.length + 1])
      (some (lookupScanCfg .restoreFound equal source address value cellBackup query
        addressBackup queryBackup processed trash)) =
    some (lookupScanCfg .found equal (processed.reverse ++ source) address value
      cellBackup query addressBackup queryBackup [] trash):=by
  induction processed generalizing source with
  | nil =>
      simp only [List.length_nil,Nat.zero_add,Function.iterate_one,
        Option.bind_some,lookupScan_step_restoreFound_nil,List.reverse_nil,
        List.nil_append]
  | cons a processed ih =>
      rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
      simp only [Option.bind_some,lookupScan_step_restoreFound_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

@[simp] theorem lookupScan_step_restoreMissing_nil (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .restoreMissing equal source address value
      cellBackup query addressBackup queryBackup [] trash) =
    some (lookupScanCfg .missing equal source address value cellBackup query
      addressBackup queryBackup [] trash):=by
  change some (TM2.stepAux
    (lookupScanMoveIteration LookupScanStack.processed LookupScanStack.source
      LookupScanLabel.restoreMissing LookupScanLabel.missing)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source address value cellBackup query addressBackup queryBackup []
      trash))=_
  simp [lookupScanMoveIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks]

@[simp] theorem lookupScan_step_restoreMissing_cons (equal:Bool) (a:SparseSymbol)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    lookupScanMachine.step (lookupScanCfg .restoreMissing equal source address value
      cellBackup query addressBackup queryBackup (a::processed) trash) =
    some (lookupScanCfg .restoreMissing equal (a::source) address value cellBackup query
      addressBackup queryBackup processed trash):=by
  change some (TM2.stepAux
    (lookupScanMoveIteration LookupScanStack.processed LookupScanStack.source
      LookupScanLabel.restoreMissing LookupScanLabel.missing)
    ⟨none,equal,none,none⟩
    (lookupScanStacks source address value cellBackup query addressBackup queryBackup
      (a::processed) trash))=_
  simp [lookupScanMoveIteration,LookupCellControl.clearHeld,lookupScanCfg,
    lookupScanStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem lookupScan_restoreMissing_reaches_missing (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      processed.length + 1])
      (some (lookupScanCfg .restoreMissing equal source address value cellBackup query
        addressBackup queryBackup processed trash)) =
    some (lookupScanCfg .missing equal (processed.reverse ++ source) address value
      cellBackup query addressBackup queryBackup [] trash):=by
  induction processed generalizing source with
  | nil =>
      simp only [List.length_nil,Nat.zero_add,Function.iterate_one,
        Option.bind_some,lookupScan_step_restoreMissing_nil,List.reverse_nil,
        List.nil_append]
  | cons a processed ih =>
      rw [List.length_cons,Nat.succ_add,Function.iterate_succ_apply]
      simp only [Option.bind_some,lookupScan_step_restoreMissing_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem lookupScan_failed_cell (w a v query:ℕ)
    (ha:a < 2 ^ w) (hq:query < 2 ^ w) (hne:a ≠ query)
    (suffix processed:List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      10 * w + 18])
      (some (lookupScanCfg .address true (encodeSparseCell w (a,v) ++ suffix)
        [] [] [] ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])) =
    some (lookupScanCfg .scan false suffix [] [] []
      ((fixedBits w query).reverse.map SparseSymbol.bit) [] []
      ((encodeSparseCell w (a,v)).reverse ++ processed) []):=by
  let stepO:=fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step
  let backup:List SparseSymbol:=
    .cellEnd::.wordEnd::(fixedBits w v).reverse.map SparseSymbol.bit ++
      .wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit
  have hbackup:backup=(encodeSparseCell w (a,v)).reverse:=by
    simp [backup,encodeSparseCell,encodeFixedWord,List.reverse_append,
      List.map_reverse,List.append_assoc]
  have h0:=lookupScan_fixed_reaches_decide w a v query ha hq suffix processed []
  simp only [hne,decide_false] at h0
  change (stepO^[3 * w + 4])
      (some (lookupScanCfg .address true (encodeSparseCell w (a,v) ++ suffix)
        [] [] [] ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])) =
    some (lookupScanCfg .decide false suffix []
      ((fixedBits w v).reverse.map SparseSymbol.bit) backup []
      ((fixedBits w a).map SparseSymbol.bit) ((fixedBits w query).map SparseSymbol.bit)
      processed []) at h0
  have oneStep {x y:lookupScanMachine.Cfg}
      (h:lookupScanMachine.step x=some y):
      (stepO^[1]) (some x)=some y:=by
    simpa [stepO] using h
  have h1:=lookupScan_step_decide false suffix []
    ((fixedBits w v).reverse.map SparseSymbol.bit) backup []
    ((fixedBits w a).map SparseSymbol.bit) ((fixedBits w query).map SparseSymbol.bit)
    processed []
  have h1':=oneStep h1
  have h2:=lookupScan_restoreQuery_reaches_discardAddress false suffix []
    ((fixedBits w v).reverse.map SparseSymbol.bit) backup []
    ((fixedBits w a).map SparseSymbol.bit) ((fixedBits w query).map SparseSymbol.bit)
    processed []
  have h2':=h2
  simp only [List.append_nil,List.map_reverse] at h2'
  have h3:=lookupScan_discardAddress_reaches_afterCleanup false suffix []
    ((fixedBits w v).reverse.map SparseSymbol.bit) backup
    ((fixedBits w query).reverse.map SparseSymbol.bit)
    ((fixedBits w a).map SparseSymbol.bit) [] processed []
  have h4:=lookupScan_step_afterCleanup_false suffix []
    ((fixedBits w v).reverse.map SparseSymbol.bit) backup
    ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed []
  have h4':=oneStep h4
  have h5:=lookupScan_discardValue_reaches_preserveCell false suffix []
    ((fixedBits w v).reverse.map SparseSymbol.bit) backup
    ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed []
  have h6:=lookupScan_preserveCell_reaches_moveCell false suffix [] [] backup
    ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed []
  have h7:=lookupScan_moveCell_reaches_afterMove false suffix [] [] []
    ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed backup.reverse
  have h6':=h6
  simp only [List.append_nil] at h6'
  have h7':=h7
  simp only [List.reverse_reverse] at h7'
  have h8:=lookupScan_step_afterMove_false suffix [] [] []
    ((fixedBits w query).reverse.map SparseSymbol.bit) [] []
    (backup ++ processed) []
  have h8':=oneStep h8
  have chain {m n:ℕ} {x y z:Option lookupScanMachine.Cfg}
      (hm:(stepO^[m]) x=y) (hn:(stepO^[n]) y=z):
      (stepO^[n + m]) x=z:=by
    rw [Function.iterate_add_apply,hm,hn]
  simp only [← List.map_reverse] at h0 h1' h2' h3 h4' h5 h6' h7' h8'
  have hrun:=chain (chain (chain (chain (chain (chain (chain (chain h0 h1') h2') h3)
    h4') h5) h6') h7') h8'
  simp only [List.length_map,List.length_reverse,fixedBits_length] at hrun
  rw [hbackup] at hrun
  simp only [List.length_reverse,encodeSparseCell_length] at hrun
  have hexp:1 + ((2 * w + 3 + 1) + ((2 * w + 3 + 1) +
      ((w + 1) + (1 + ((w + 1) + ((w + 1) + (1 + (3 * w + 4)))))))) =
      10 * w + 18:=by omega
  rw [hexp] at hrun
  simpa [stepO,List.map_reverse,List.append_assoc] using hrun

theorem lookupScan_matching_cell (w a v:ℕ) (ha:a < 2 ^ w)
    (suffix processed:List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      11 * w + processed.length + 21])
      (some (lookupScanCfg .address true (encodeSparseCell w (a,v) ++ suffix)
        [] [] [] ((fixedBits w a).reverse.map SparseSymbol.bit) [] [] processed [])) =
    some (lookupScanCfg .found true
      (processed.reverse ++ encodeSparseCell w (a,v) ++ suffix) []
      ((fixedBits w v).reverse.map SparseSymbol.bit) []
      ((fixedBits w a).reverse.map SparseSymbol.bit) [] [] [] []):=by
  let stepO:=fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step
  let backup:List SparseSymbol:=
    .cellEnd::.wordEnd::(fixedBits w v).reverse.map SparseSymbol.bit ++
      .wordEnd::(fixedBits w a).reverse.map SparseSymbol.bit
  have hbackup:backup=(encodeSparseCell w (a,v)).reverse:=by
    simp [backup,encodeSparseCell,encodeFixedWord,List.reverse_append,
      List.map_reverse,List.append_assoc]
  have h0:=lookupScan_fixed_reaches_decide w a v a ha ha suffix processed []
  simp only [decide_true] at h0
  change (stepO^[3 * w + 4])
      (some (lookupScanCfg .address true (encodeSparseCell w (a,v) ++ suffix)
        [] [] [] ((fixedBits w a).reverse.map SparseSymbol.bit) [] [] processed [])) =
    some (lookupScanCfg .decide true suffix []
      ((fixedBits w v).reverse.map SparseSymbol.bit) backup []
      ((fixedBits w a).map SparseSymbol.bit) ((fixedBits w a).map SparseSymbol.bit)
      processed []) at h0
  have oneStep {x y:lookupScanMachine.Cfg}
      (h:lookupScanMachine.step x=some y):
      (stepO^[1]) (some x)=some y:=by
    simpa [stepO] using h
  have h1:=oneStep (lookupScan_step_decide true suffix []
    ((fixedBits w v).reverse.map SparseSymbol.bit) backup []
    ((fixedBits w a).map SparseSymbol.bit) ((fixedBits w a).map SparseSymbol.bit)
    processed [])
  have h2:=lookupScan_restoreQuery_reaches_discardAddress true suffix []
    ((fixedBits w v).reverse.map SparseSymbol.bit) backup []
    ((fixedBits w a).map SparseSymbol.bit) ((fixedBits w a).map SparseSymbol.bit)
    processed []
  have h2':=h2
  simp only [List.append_nil,List.map_reverse] at h2'
  have h3:=lookupScan_discardAddress_reaches_afterCleanup true suffix []
    ((fixedBits w v).reverse.map SparseSymbol.bit) backup
    ((fixedBits w a).reverse.map SparseSymbol.bit)
    ((fixedBits w a).map SparseSymbol.bit) [] processed []
  have h4:=oneStep (lookupScan_step_afterCleanup_true suffix []
    ((fixedBits w v).reverse.map SparseSymbol.bit) backup
    ((fixedBits w a).reverse.map SparseSymbol.bit) [] [] processed [])
  have h5:=lookupScan_preserveCell_reaches_moveCell true suffix []
    ((fixedBits w v).reverse.map SparseSymbol.bit) backup
    ((fixedBits w a).reverse.map SparseSymbol.bit) [] [] processed []
  have h5':=h5
  simp only [List.append_nil] at h5'
  have h6:=lookupScan_moveCell_reaches_afterMove true suffix []
    ((fixedBits w v).reverse.map SparseSymbol.bit) []
    ((fixedBits w a).reverse.map SparseSymbol.bit) [] [] processed backup.reverse
  have h6':=h6
  simp only [List.reverse_reverse] at h6'
  have h7:=oneStep (lookupScan_step_afterMove_true suffix []
    ((fixedBits w v).reverse.map SparseSymbol.bit) []
    ((fixedBits w a).reverse.map SparseSymbol.bit) [] [] (backup ++ processed) [])
  have h8:=lookupScan_restoreFound_reaches_found true suffix []
    ((fixedBits w v).reverse.map SparseSymbol.bit) []
    ((fixedBits w a).reverse.map SparseSymbol.bit) [] [] (backup ++ processed) []
  have chain {m n:ℕ} {x y z:Option lookupScanMachine.Cfg}
      (hm:(stepO^[m]) x=y) (hn:(stepO^[n]) y=z):
      (stepO^[n + m]) x=z:=by
    rw [Function.iterate_add_apply,hm,hn]
  simp only [← List.map_reverse] at h0 h1 h2' h3 h4 h5' h6' h7 h8
  have hrun:=chain (chain (chain (chain (chain (chain (chain (chain h0 h1) h2') h3)
    h4) h5') h6') h7) h8
  simp only [List.length_map,List.length_reverse,fixedBits_length,
    List.length_append] at hrun
  rw [hbackup] at hrun
  simp only [List.length_reverse,encodeSparseCell_length,List.reverse_append,
    List.reverse_reverse] at hrun
  have hexp:(2 * w + 3 + processed.length + 1) +
      (1 + (2 * w + 3 + 1 + (2 * w + 3 + 1 +
        (1 + (w + 1 + (w + 1 + (1 + (3 * w + 4)))))))) =
      11 * w + processed.length + 21:=by omega
  rw [hexp] at hrun
  simpa [stepO,List.map_reverse,List.append_assoc] using hrun

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

theorem lookupScan_skip_missing_prefix (w query:ℕ) (hq:query < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (hmissing:SparseMemory.find? m query=none)
    (equal:Bool) (suffix processed:List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      m.length * (10 * w + 19)])
      (some (lookupScanCfg .scan equal (encodeSparseMemory w m ++ suffix) [] [] []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])) =
    some (lookupScanCfg .scan (equal && decide m.isEmpty) suffix [] [] []
      ((fixedBits w query).reverse.map SparseSymbol.bit) [] []
      ((encodeSparseMemory w m).reverse ++ processed) []):=by
  induction m generalizing equal processed with
  | nil => simp [encodeSparseMemory]
  | cons cell m ih =>
      rcases cell with ⟨a,v⟩
      rcases hm with ⟨ha,hv,hm⟩
      have hqa:query ≠ a:=by
        intro h
        simp [SparseMemory.find?,h] at hmissing
      have hne:a ≠ query:=Ne.symm hqa
      have htail:SparseMemory.find? m query=none:=by
        simpa [SparseMemory.find?,hqa] using hmissing
      let stepO:=fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step
      let rest:=encodeSparseMemory w m ++ suffix
      have hscan:=lookupScan_step_encoded_cell equal w a v rest [] [] []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed []
      have hscan':(stepO^[1])
          (some (lookupScanCfg .scan equal (encodeSparseCell w (a,v) ++ rest)
            [] [] [] ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])) =
          some (lookupScanCfg .address true (encodeSparseCell w (a,v) ++ rest)
            [] [] [] ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed []):=by
        simpa [stepO] using! hscan
      have hcell:=lookupScan_failed_cell w a v query ha hq hne rest processed
      have htailRun:=ih hm htail false
        ((encodeSparseCell w (a,v)).reverse ++ processed)
      have chain {r s:ℕ} {x y z:Option lookupScanMachine.Cfg}
          (hr:(stepO^[r]) x=y) (hs:(stepO^[s]) y=z):
          (stepO^[s + r]) x=z:=by
        rw [Function.iterate_add_apply,hr,hs]
      have hrun:=chain (chain hscan' hcell) htailRun
      have hexp:m.length * (10 * w + 19) + ((10 * w + 18) + 1) =
          (m.length + 1) * (10 * w + 19):=by
        rw [Nat.add_mul,Nat.one_mul]
      rw [hexp] at hrun
      simpa [stepO,rest,encodeSparseMemory,List.reverse_append,
        List.append_assoc] using hrun

theorem lookupScan_found_after_prefix (w query v:ℕ) (hq:query < 2 ^ w)
    (pref:SparseMemory) (hp:pref.Normalized w)
    (hmissing:SparseMemory.find? pref query=none)
    (suffix processed:List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      pref.length * (12 * w + 22) + 11 * w + processed.length + 22])
      (some (lookupScanCfg .scan true
        (encodeSparseMemory w pref ++ encodeSparseCell w (query,v) ++ suffix)
        [] [] [] ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])) =
    some (lookupScanCfg .found true
      (processed.reverse ++ encodeSparseMemory w pref ++
        encodeSparseCell w (query,v) ++ suffix)
      [] ((fixedBits w v).reverse.map SparseSymbol.bit) []
      ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] []):=by
  let stepO:=fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step
  let rest:=encodeSparseCell w (query,v) ++ suffix
  let processed':=(encodeSparseMemory w pref).reverse ++ processed
  let scanEqual:=true && decide pref.isEmpty
  have hprefix:=lookupScan_skip_missing_prefix w query hq pref hp hmissing true
    rest processed
  have hscan:=lookupScan_step_encoded_cell scanEqual w query v suffix [] [] []
    ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed' []
  have hscan':(stepO^[1])
      (some (lookupScanCfg .scan scanEqual (encodeSparseCell w (query,v) ++ suffix)
        [] [] [] ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed' [])) =
      some (lookupScanCfg .address true (encodeSparseCell w (query,v) ++ suffix)
        [] [] [] ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed' []):=by
    simpa [stepO] using! hscan
  have hmatch:=lookupScan_matching_cell w query v hq suffix processed'
  have chain {r s:ℕ} {x y z:Option lookupScanMachine.Cfg}
      (hr:(stepO^[r]) x=y) (hs:(stepO^[s]) y=z):
      (stepO^[s + r]) x=z:=by
    rw [Function.iterate_add_apply,hr,hs]
  have hrun:=chain (chain hprefix hscan') hmatch
  dsimp only [processed'] at hrun
  simp only [List.length_append,List.length_reverse,
    encodeSparseMemory_length] at hrun
  have hexp:
      (11 * w + (pref.length * (2 * w + 3) + processed.length) + 21) +
          (1 + pref.length * (10 * w + 19)) =
        pref.length * (12 * w + 22) + 11 * w + processed.length + 22:=by
    ring
  rw [hexp] at hrun
  simpa [stepO,rest,processed',List.reverse_append,List.reverse_reverse,
    List.append_assoc] using hrun

theorem SparseMemory.normalized_append_left {w:ℕ} (p s:SparseMemory)
    (h:SparseMemory.Normalized w (List.append p s)):p.Normalized w:=by
  induction p with
  | nil => exact SparseMemory.normalized_nil w
  | cons cell p ih =>
      rcases cell with ⟨a,v⟩
      rcases h with ⟨ha,hv,htail⟩
      exact ⟨ha,hv,ih htail⟩

theorem SparseMemory.find?_eq_some_decompose {m:SparseMemory} {query value:ℕ}
    (h:SparseMemory.find? m query=some value):
    ∃ p s:SparseMemory,
      m=List.append p ((query,value)::s)∧
        SparseMemory.find? p query=none:=by
  induction m with
  | nil => simp [SparseMemory.find?] at h
  | cons cell m ih =>
      rcases cell with ⟨a,v⟩
      by_cases hqa:query=a
      · subst a
        simp [SparseMemory.find?] at h
        subst v
        exact ⟨[],m,by simp,by simp [SparseMemory.find?]⟩
      · have htail:SparseMemory.find? m query=some value:=by
          simpa [SparseMemory.find?,hqa] using h
        rcases ih htail with ⟨p,s,hm,hp⟩
        refine ⟨(a,v)::p,s, ?_, ?_⟩
        · simp [hm]
        · simp [SparseMemory.find?,hqa,hp]

theorem lookupScan_found (w query value:ℕ) (hq:query < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (hfind:m.find? query=some value) (processed:List SparseSymbol):
    ∃ n≤ m.length * (12 * w + 22) + 11 * w + processed.length + 22,
      ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[n])
        (some (lookupScanCfg .scan true
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])) =
      some (lookupScanCfg .found true
        (processed.reverse ++ encodeSparseMemory w m ++ [.memoryEnd]) []
        ((fixedBits w value).reverse.map SparseSymbol.bit) []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] []):=by
  rcases SparseMemory.find?_eq_some_decompose hfind with ⟨p,s,rfl,hpfind⟩
  have hp:p.Normalized w:=
    SparseMemory.normalized_append_left p ((query,value)::s) hm
  let n:=p.length * (12 * w + 22) + 11 * w + processed.length + 22
  refine ⟨n, ?_, ?_⟩
  · dsimp [n]
    have hlen:p.length≤ (List.append p ((query,value)::s)).length:=by simp
    exact Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) (11 * w))
      (processed.length + 22)
  · have hrun:=lookupScan_found_after_prefix w query value hq p hp hpfind
      (encodeSparseMemory w s ++ [.memoryEnd]) processed
    simpa [n,encodeSparseMemory,List.append_assoc] using! hrun

theorem lookupScan_all_missing (w query:ℕ) (hq:query < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (hmissing:SparseMemory.find? m query=none)
    (equal:Bool) (processed:List SparseSymbol):
    ((fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step)^[
      m.length * (12 * w + 22) + processed.length + 2])
      (some (lookupScanCfg .scan equal
        (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])) =
    some (lookupScanCfg .missing (equal && decide m.isEmpty)
      (processed.reverse ++ encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
      ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] []):=by
  induction m generalizing equal processed with
  | nil =>
      let stepO:=fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step
      have h0:=lookupScan_step_empty_memory equal [] [] []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed []
      have h0':(stepO^[1])
          (some (lookupScanCfg .scan equal [.memoryEnd] [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])) =
          some (lookupScanCfg .restoreMissing equal [.memoryEnd] [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed []):=by
        simpa [stepO] using! h0
      have h1:=lookupScan_restoreMissing_reaches_missing equal [.memoryEnd] [] [] []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed []
      have chain {r s:ℕ} {x y z:Option lookupScanMachine.Cfg}
          (hr:(stepO^[r]) x=y) (hs:(stepO^[s]) y=z):
          (stepO^[s + r]) x=z:=by
        rw [Function.iterate_add_apply,hr,hs]
      have hrun:=chain h0' h1
      simpa [stepO,List.append_assoc,Nat.add_comm,Nat.add_left_comm,
        Nat.add_assoc] using! hrun
  | cons cell m ih =>
      rcases cell with ⟨a,v⟩
      rcases hm with ⟨ha,hv,hm⟩
      have hqa:query ≠ a:=by
        intro h
        simp [SparseMemory.find?,h] at hmissing
      have hne:a ≠ query:=Ne.symm hqa
      have htail:SparseMemory.find? m query=none:=by
        simpa [SparseMemory.find?,hqa] using hmissing
      let stepO:=fun o:Option lookupScanMachine.Cfg => o.bind lookupScanMachine.step
      let suffix:=encodeSparseMemory w m ++ [.memoryEnd]
      have hscan:=lookupScan_step_encoded_cell equal w a v suffix [] [] []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed []
      have hscan':(stepO^[1])
          (some (lookupScanCfg .scan equal (encodeSparseCell w (a,v) ++ suffix)
            [] [] [] ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed [])) =
          some (lookupScanCfg .address true (encodeSparseCell w (a,v) ++ suffix)
            [] [] [] ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] processed []):=by
        simpa [stepO] using! hscan
      have hcell:=lookupScan_failed_cell w a v query ha hq hne suffix processed
      have htailRun:=ih hm htail false
        ((encodeSparseCell w (a,v)).reverse ++ processed)
      have chain {r s:ℕ} {x y z:Option lookupScanMachine.Cfg}
          (hr:(stepO^[r]) x=y) (hs:(stepO^[s]) y=z):
          (stepO^[s + r]) x=z:=by
        rw [Function.iterate_add_apply,hr,hs]
      have hrun:=chain (chain hscan' hcell) htailRun
      simp only [List.length_append,List.length_reverse,encodeSparseCell_length] at hrun
      have hexp:
          (m.length * (12 * w + 22) + (2 * w + 3 + processed.length) + 2) +
              ((10 * w + 18) + 1) =
            (m.length + 1) * (12 * w + 22) + processed.length + 2:=by
        rw [Nat.add_mul,Nat.one_mul]
        omega
      rw [hexp] at hrun
      simpa [stepO,suffix,encodeSparseMemory,List.reverse_append,
        List.reverse_reverse,List.append_assoc] using hrun

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def zeroWordStacks (query backup result:List SparseSymbol):
    ZeroWordStack→ List SparseSymbol
  | .query => query
  | .backup => backup
  | .result => result

def zeroWordCfg (label:ZeroWordLabel) (query backup result:List SparseSymbol):
    zeroWordMachine.Cfg where
  l:=some label
  var:=default
  stk:=zeroWordStacks query backup result

def zeroWordCfgState (label:ZeroWordLabel) (state:ZeroWordControl)
    (query backup result:List SparseSymbol):
    TM2.Cfg (fun _:ZeroWordStack => SparseSymbol)
      ZeroWordLabel ZeroWordControl where
  l:=some label
  var:=state
  stk:=zeroWordStacks query backup result

theorem zeroWord_first_step_independent (state:ZeroWordControl)
    (query backup result:List SparseSymbol):
    TM2.step zeroWordProgram
        (zeroWordCfgState .fill state query backup result) =
      TM2.step zeroWordProgram (zeroWordCfg .fill query backup result):=by
  cases query with
  | nil =>
      simp [TM2.step,zeroWordProgram,zeroWordMachine,zeroWordCfgState,
        zeroWordCfg,zeroWordStacks]
  | cons a query =>
      simp [TM2.step,zeroWordProgram,zeroWordMachine,zeroWordCfgState,
        zeroWordCfg,zeroWordStacks]

@[simp] theorem zeroWord_step_fill_nil (backup result:List SparseSymbol):
    zeroWordMachine.step (zeroWordCfg .fill [] backup result) =
      some (zeroWordCfg .restore [] backup result):=by
  simp [zeroWordMachine,zeroWordCfg,zeroWordStacks]

@[simp] theorem zeroWord_step_fill_cons (a:SparseSymbol)
    (query backup result:List SparseSymbol):
    zeroWordMachine.step (zeroWordCfg .fill (a::query) backup result) =
      some (zeroWordCfg .fill query (a::backup) (.bit false::result)):=by
  simp [zeroWordMachine,zeroWordCfg,zeroWordStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem zeroWord_step_restore_nil (query result:List SparseSymbol):
    zeroWordMachine.step (zeroWordCfg .restore query [] result) =
      some (zeroWordCfg .done query [] result):=by
  simp [zeroWordMachine,zeroWordCfg,zeroWordStacks]

@[simp] theorem zeroWord_step_restore_cons (a:SparseSymbol)
    (query backup result:List SparseSymbol):
    zeroWordMachine.step (zeroWordCfg .restore query (a::backup) result) =
      some (zeroWordCfg .restore (a::query) backup result):=by
  simp [zeroWordMachine,zeroWordCfg,zeroWordStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem replicate_append_same_cons (n:ℕ) (a:SparseSymbol)
    (result:List SparseSymbol):
    List.replicate n a ++ a::result=a::(List.replicate n a ++ result):=by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]

theorem zeroWord_fill_iterate (query backup result:List SparseSymbol):
    ((fun o:Option zeroWordMachine.Cfg => o.bind zeroWordMachine.step)^[query.length])
      (some (zeroWordCfg .fill query backup result)) =
    some (zeroWordCfg .fill [] (query.reverse ++ backup)
      (List.replicate query.length (.bit false) ++ result)):=by
  induction query generalizing backup result with
  | nil => rfl
  | cons a query ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,zeroWord_step_fill_cons]
      rw [ih]
      congr 2
      · simp [List.reverse_cons,List.append_assoc]
      · exact replicate_append_same_cons query.length (.bit false) result

theorem zeroWord_restore_iterate (query backup result:List SparseSymbol):
    ((fun o:Option zeroWordMachine.Cfg => o.bind zeroWordMachine.step)^[backup.length])
      (some (zeroWordCfg .restore query backup result)) =
    some (zeroWordCfg .restore (backup.reverse ++ query) [] result):=by
  induction backup generalizing query with
  | nil => rfl
  | cons a backup ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,zeroWord_step_restore_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem zeroWord_correct (query result:List SparseSymbol):
    ((fun o:Option zeroWordMachine.Cfg => o.bind zeroWordMachine.step)^[
      2 * query.length + 2])
      (some (zeroWordCfg .fill query [] result)) =
    some (zeroWordCfg .done query []
      (List.replicate query.length (.bit false) ++ result)):=by
  let stepO:=fun o:Option zeroWordMachine.Cfg => o.bind zeroWordMachine.step
  have hfill:=zeroWord_fill_iterate query [] result
  have hfillEnd:=zeroWord_step_fill_nil query.reverse
    (List.replicate query.length (.bit false) ++ result)
  have hfillEnd':(stepO^[1])
      (some (zeroWordCfg .fill [] query.reverse
        (List.replicate query.length (.bit false) ++ result))) =
      some (zeroWordCfg .restore [] query.reverse
        (List.replicate query.length (.bit false) ++ result)):=by
    simpa [stepO] using hfillEnd
  have hrestore:=zeroWord_restore_iterate [] query.reverse
    (List.replicate query.length (.bit false) ++ result)
  have hrestoreEnd:=zeroWord_step_restore_nil query
    (List.replicate query.length (.bit false) ++ result)
  have hrestoreEnd':(stepO^[1])
      (some (zeroWordCfg .restore query []
        (List.replicate query.length (.bit false) ++ result))) =
      some (zeroWordCfg .done query []
        (List.replicate query.length (.bit false) ++ result)):=by
    simpa [stepO] using hrestoreEnd
  have chain {r s:ℕ} {x y z:Option zeroWordMachine.Cfg}
      (hr:(stepO^[r]) x=y) (hs:(stepO^[s]) y=z):
      (stepO^[s + r]) x=z:=by
    rw [Function.iterate_add_apply,hr,hs]
  have hrestore':=hrestore
  simp only [List.reverse_reverse,List.append_nil] at hrestore'
  have hfill':=hfill
  simp only [List.append_nil] at hfill'
  have hrun:=chain (chain (chain hfill' hfillEnd') hrestore') hrestoreEnd'
  simp only [List.length_reverse] at hrun
  have hexp:1 + (query.length + (1 + query.length))=2 * query.length + 2:=by
    omega
  rw [hexp] at hrun
  simpa [stepO] using hrun

theorem zeroWord_correct_from (state:ZeroWordControl)
    (query result:List SparseSymbol):
    ((fun o:Option zeroWordMachine.Cfg => o.bind (TM2.step zeroWordProgram))^[
      2 * query.length + 2])
      (some (zeroWordCfgState .fill state query [] result)) =
    some (zeroWordCfg .done query []
      (List.replicate query.length (.bit false) ++ result)):=by
  rw [show 2 * query.length + 2=(2 * query.length + 1) + 1 by omega,
    Function.iterate_succ_apply]
  simp only [Option.bind_some,zeroWord_first_step_independent]
  have h:=zeroWord_correct query result
  rw [show 2 * query.length + 2=(2 * query.length + 1) + 1 by omega,
    Function.iterate_succ_apply] at h
  exact h

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def literalWordStacks (query backup result:List SparseSymbol):
    LiteralWordStack→ List SparseSymbol
  | .query => query
  | .backup => backup
  | .result => result

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

def operandWordValue (w:ℕ) (o:Op) (m:SparseMemory):ℕ:=
  sparseValue w o m % 2 ^ w

theorem SparseMemory.read_lt_of_normalized {w:ℕ} {m:SparseMemory}
    (hm:m.Normalized w) (a:ℕ):m.read a < 2 ^ w:=by
  induction m with
  | nil => simp [SparseMemory.read]
  | cons cell m ih =>
      rcases cell with ⟨b,v⟩
      rcases hm with ⟨_,hv,hm⟩
      by_cases hab:a=b
      · simpa [SparseMemory.read,hab] using hv
      · simpa [SparseMemory.read,hab] using ih hm

@[simp] theorem operandWordValue_lit (w n:ℕ) (m:SparseMemory):
    operandWordValue w (.lit n) m=n % 2 ^ w:=rfl

@[simp] theorem operandWordValue_mem (w a:ℕ) (m:SparseMemory):
    operandWordValue w (.mem a) m=m.read (a % 2 ^ w) % 2 ^ w:=rfl

@[simp] theorem operandWordValue_ind (w a:ℕ) (m:SparseMemory):
    operandWordValue w (.ind a) m =
      m.read (m.read (a % 2 ^ w) % 2 ^ w) % 2 ^ w:=rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

theorem iterate_optionBind_none {α:Type} (f:α→ Option α) (n:ℕ):
    ((fun o:Option α => o.bind f)^[n]) none=none:=by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem sparseBitDecode_encode (b:Bool):
    sparseBitDecode (sparseBitEncode b)=b:=rfl

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def divStacks (dividend divisor remainder quotient divisorBackup remainderBackup
    differenceReverse shiftTemp:List Bool):DivStack→ List Bool
  | .dividend => dividend
  | .divisor => divisor
  | .remainder => remainder
  | .quotient => quotient
  | .divisorBackup => divisorBackup
  | .remainderBackup => remainderBackup
  | .differenceReverse => differenceReverse
  | .shiftTemp => shiftTemp

def divCfg (label:DivLabel) (state:DivControl)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp:List Bool):divMachine.Cfg where
  l:=some label
  var:=state
  stk:=divStacks dividend divisor remainder quotient divisorBackup remainderBackup
    differenceReverse shiftTemp

def divCleanCfg (label:DivLabel) (divisorNonzero:Bool)
    (dividend divisor remainder quotient divisorBackup:List Bool):
    divMachine.Cfg:=
  divCfg label { (default:DivControl) with divisorNonzero:=divisorNonzero }
    dividend divisor remainder quotient divisorBackup [] [] []

def divPhaseCfg (label:DivLabel) (selected borrow:Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp:List Bool):divMachine.Cfg:=
  divCfg label
    { (default:DivControl) with
      selected:=selected,borrow:=borrow,
      divisorNonzero:=true }
    dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp

@[simp] theorem div_step_dispatch_false
    (dividend divisor remainder quotient:List Bool):
    divMachine.step (divCleanCfg .dispatch false dividend divisor remainder quotient []) =
      some (divCleanCfg .zeroLoop false dividend divisor remainder quotient []):=by
  rfl

@[simp] theorem div_step_dispatch_true
    (dividend divisor remainder quotient:List Bool):
    divMachine.step (divCleanCfg .dispatch true dividend divisor remainder quotient []) =
      some (divCleanCfg .outer true dividend divisor remainder quotient []):=by
  rfl

@[simp] theorem div_step_choose_true (selected:Bool)
    (dividend divisor quotient remainderBackup differenceReverse:List Bool):
    divMachine.step (divPhaseCfg .choose selected true dividend divisor [] quotient []
        remainderBackup differenceReverse []) =
      some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup differenceReverse []):=by
  rfl

@[simp] theorem div_step_choose_false (selected:Bool)
    (dividend divisor quotient remainderBackup differenceReverse:List Bool):
    divMachine.step (divPhaseCfg .choose selected false dividend divisor [] quotient []
        remainderBackup differenceReverse []) =
      some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        remainderBackup differenceReverse []):=by
  rfl

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

@[simp] theorem fetch_boundPC (p:Program) (pc:ℕ):
    (boundPC p pc).fetch=p[pc]?:=by
  by_cases h:pc < p.length
  · simp [BoundedPC.fetch,boundPC,h]
  · have hout:p[pc]?=none:=List.getElem?_eq_none (by omega)
    simp [BoundedPC.fetch,boundPC,h,hout]

inductive DispatchLabel (p:Program)
  | fetch (pc:BoundedPC p)
  | stopped
  deriving DecidableEq,Fintype,Inhabited

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

@[simp] theorem coreStacks_set_pc (w pc:ℕ) (s:SparseState):
    coreStacks w { s with pc:=pc }=coreStacks w s:=by
  funext k
  cases k <;> rfl

@[simp] theorem encodeAccumulator_length (w a:ℕ):
    (encodeAccumulator w a).length=w:=by
  simp [encodeAccumulator]

@[simp] theorem encodeMemoryStack_length (w:ℕ) (m:SparseMemory):
    (encodeMemoryStack w m).length=m.length * (2 * w + 3) + 1:=by
  simp [encodeMemoryStack]

@[simp] theorem encodeInputStack_length (w:ℕ) (input:List ℕ):
    (encodeInputStack w input).length=input.length * (w + 1) + 1:=by
  simp [encodeInputStack]

@[simp] theorem encodeOutputStack_length (w:ℕ) (output:List ℕ):
    (encodeOutputStack w output).length=output.length * (w + 1) + 1:=by
  simp [encodeOutputStack]

def coreSize (w:ℕ) (s:SparseState):ℕ:=
  (coreStacks w s .accumulator).length +
    (coreStacks w s .memory).length +
    (coreStacks w s .input).length +
    (coreStacks w s .output).length

theorem coreSize_eq (w:ℕ) (s:SparseState):
    coreSize w s=w + s.mem.length * (2 * w + 3) +
      s.inp.length * (w + 1) + s.out.length * (w + 1) + 3:=by
  simp [coreSize,coreStacks]
  omega

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

def controlDispatchCfg (p:Program) (label:ControlDispatchLabel p)
    (state:DispatchControl) (tapes:CoreStack→ List SparseSymbol):
    (controlDispatchMachine p).Cfg where
  l:=some label
  var:=state
  stk:=tapes

@[simp] theorem control_step_stopped (p:Program) (state:DispatchControl)
    (tapes:CoreStack→ List SparseSymbol):
    (controlDispatchMachine p).step
      (controlDispatchCfg p .stopped state tapes) =
      some { l:=none,var:=state,stk:=tapes }:=by
  rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def AvoidsDone {α K Λ σ:Type} [DecidableEq K]
    (program:Λ→ TM2.Stmt (fun _:K => α) Λ σ)
    (done:Λ):ℕ→ TM2.Cfg (fun _:K => α) Λ σ→ Prop
  | 0,_ => True
  | n + 1,c => c.l ≠ some done∧
      match TM2.step program c with
      | none => True
      | some c' => AvoidsDone program done n c'

theorem step_at_halt_label {K Λ σ:Type} {α:K→ Type} [DecidableEq K]
    (program:Λ→ TM2.Stmt α Λ σ) (done:Λ)
    (hdone:program done=.halt)
    (state:σ) (stk:(k:K)→ List (α k)):
    TM2.step program
      ({ l:=some done,var:=state,stk:=stk }:
        TM2.Cfg α Λ σ) =
      some { l:=none,var:=state,stk:=stk }:=by
  simp [TM2.step,hdone]

theorem avoidsDone_of_reaches_done {α K Λ σ:Type} [DecidableEq K]
    (program:Λ→ TM2.Stmt (fun _:K => α) Λ σ) (done:Λ)
    (hdone:program done=.halt) {n:ℕ}
    {c d:TM2.Cfg (fun _:K => α) Λ σ}
    (hrun:((fun o => o.bind (TM2.step program))^[n]) (some c)=some d)
    (hd:d.l=some done):AvoidsDone program done n c:=by
  induction n generalizing c with
  | zero => trivial
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun
      simp only [Option.bind_some] at hrun
      cases hstep:TM2.step program c with
      | none =>
          rw [hstep,iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          rw [hstep] at hrun
          have hc:c.l ≠ some done:=by
            intro hcDone
            rcases c with ⟨label,state,stk⟩
            simp only at hcDone
            subst label
            have hs:=step_at_halt_label program done hdone state stk
            rw [hstep] at hs
            have hc'eq:=Option.some.inj hs
            subst c'
            cases n with
            | zero =>
                simp only [Function.iterate_zero_apply] at hrun
                have heq:=Option.some.inj hrun
                rw [← heq] at hd
                simp at hd
            | succ n =>
                rw [Function.iterate_succ_apply] at hrun
                simp only [Option.bind_some] at hrun
                change ((fun o => o.bind (TM2.step program))^[n + 1]) none =
                  some d at hrun
                rw [iterate_optionBind_none] at hrun
                contradiction
          refine ⟨hc, ?_⟩
          simpa [AvoidsDone,hstep] using ih hrun

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def lookupScanMacroCfg (label:LookupScanLabel) (equal:Bool)
    (source address value cellBackup query addressBackup queryBackup processed trash:
      List SparseSymbol):
    TM2.Cfg (fun _:LookupScanStack => SparseSymbol) LookupScanLabel
      LookupCellControl where
  l:=some label
  var:= ⟨none,equal,none,none⟩
  stk:=lookupScanStacks source address value cellBackup query addressBackup queryBackup
    processed trash

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

theorem StackRenaming.encode_injective {K K':Type} (e:StackRenaming K K'):
    Function.Injective e.encode:=by
  intro a b h
  have:=congrArg e.decode h
  simpa [e.decode_encode] using this

def renamedStacks {α K K':Type} (e:StackRenaming K K')
    (inner:K→ List α) (ambient:K'→ List α):K'→ List α:=
  fun k' => match e.decode k' with
    | some k => inner k
    | none => ambient k'

@[simp] theorem renamedStacks_encode {α K K':Type} (e:StackRenaming K K')
    (inner:K→ List α) (ambient:K'→ List α) (k:K):
    renamedStacks e inner ambient (e.encode k)=inner k:=by
  simp [renamedStacks,e.decode_encode]

theorem update_renamedStacks {α K K':Type} [DecidableEq K]
    [DecidableEq K'] (e:StackRenaming K K')
    (inner:K→ List α) (ambient:K'→ List α) (k:K) (xs:List α):
    Function.update (renamedStacks e inner ambient) (e.encode k) xs =
      renamedStacks e (Function.update inner k xs) ambient:=by
  funext j
  cases hdecode:e.decode j with
  | none =>
      have hne:j ≠ e.encode k:=by
        intro h
        subst j
        rw [e.decode_encode] at hdecode
        contradiction
      simp [renamedStacks,hdecode,hne]
  | some jlocal =>
      have hj:e.encode jlocal=j:=e.encode_decode hdecode
      by_cases h:jlocal=k
      · subst jlocal
        subst j
        simp [renamedStacks,e.decode_encode]
      · have hne:j ≠ e.encode k:=by
          intro heq
          rw [← hj] at heq
          exact h (e.encode_injective heq)
        simp [renamedStacks,hdecode,h,hne]

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem renamedStacks_literal_accumulator
    (inner:LiteralWordStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks literalWordCoreRenaming inner ambient .accumulator =
      inner .query:=by rfl

@[simp] theorem renamedStacks_literal_result
    (inner:LiteralWordStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks literalWordCoreRenaming inner ambient .work0 =
      inner .result:=by rfl

@[simp] theorem renamedStacks_literalQuery_result
    (inner:LiteralWordStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks literalQueryCoreRenaming inner ambient .work1 =
      inner .result:=by rfl

@[simp] theorem renamedStacks_zero_query
    (inner:ZeroWordStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks zeroWordCoreRenaming inner ambient .accumulator =
      inner .query:=by rfl

@[simp] theorem renamedStacks_zero_result
    (inner:ZeroWordStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks zeroWordCoreRenaming inner ambient .work0 =
      inner .result:=by rfl

@[simp] theorem renamedStacks_lookup_memory
    (inner:LookupScanStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks lookupCoreRenaming inner ambient .memory=inner .source:=by rfl

@[simp] theorem renamedStacks_lookup_value
    (inner:LookupScanStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks lookupCoreRenaming inner ambient .work0=inner .value:=by rfl

@[simp] theorem renamedStacks_lookup_query
    (inner:LookupScanStack→ List SparseSymbol)
    (ambient:CoreStack→ List SparseSymbol):
    renamedStacks lookupCoreRenaming inner ambient .work1=inner .query:=by rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

def divCoreEncode:DivStack→ CoreStack
  | .dividend => .accumulator
  | .divisor => .work1
  | .remainder => .work2
  | .quotient => .work0
  | .divisorBackup => .work3
  | .remainderBackup => .work4
  | .differenceReverse => .work5
  | .shiftTemp => .work6

def divCoreDecode:CoreStack→ Option DivStack
  | .accumulator => some .dividend
  | .work1 => some .divisor
  | .work2 => some .remainder
  | .work0 => some .quotient
  | .work3 => some .divisorBackup
  | .work4 => some .remainderBackup
  | .work5 => some .differenceReverse
  | .work6 => some .shiftTemp
  | _ => none

def divCoreRenaming:StackRenaming DivStack CoreStack where
  encode:=divCoreEncode
  decode:=divCoreDecode
  decode_encode:=by intro k; cases k <;> rfl
  encode_decode:=by
    intro k' k h
    cases k' <;> cases k <;> simp [divCoreDecode,divCoreEncode] at h ⊢

@[simp] theorem renamedStacks_binary_left
    (inner:AddStack→ List SparseSymbol) (ambient:CoreStack→ List SparseSymbol):
    renamedStacks binaryCoreRenaming inner ambient .accumulator=inner .left:=by rfl

@[simp] theorem renamedStacks_binary_result
    (inner:AddStack→ List SparseSymbol) (ambient:CoreStack→ List SparseSymbol):
    renamedStacks binaryCoreRenaming inner ambient .work0=inner .result:=by rfl

@[simp] theorem renamedStacks_mul_result
    (inner:MulStack→ List SparseSymbol) (ambient:CoreStack→ List SparseSymbol):
    renamedStacks mulCoreRenaming inner ambient .work0=inner .accumulator:=by rfl

@[simp] theorem renamedStacks_div_quotient
    (inner:DivStack→ List SparseSymbol) (ambient:CoreStack→ List SparseSymbol):
    renamedStacks divCoreRenaming inner ambient .work0=inner .quotient:=by rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def symbolMoveLocalCfg (label:SymbolMoveLabel)
    (source target:List SparseSymbol):
    TM2.Cfg (fun _:SymbolMoveStack => SparseSymbol)
      SymbolMoveLabel SymbolMoveControl where
  l:=some label
  var:=default
  stk:=symbolMoveStacks source target

def symbolMoveLocalCfgState (label:SymbolMoveLabel)
    (state:SymbolMoveControl) (source target:List SparseSymbol):
    TM2.Cfg (fun _:SymbolMoveStack => SparseSymbol)
      SymbolMoveLabel SymbolMoveControl where
  l:=some label
  var:=state
  stk:=symbolMoveStacks source target

theorem symbolMoveLocal_correct_from (state:SymbolMoveControl)
    (source target:List SparseSymbol):
    ((fun o => o.bind (TM2.step symbolMoveCoreProgram))^[source.length + 1])
      (some (symbolMoveLocalCfgState .loop state source target)) =
      some (symbolMoveLocalCfg .done [] (source.reverse ++ target)):=by
  change ((fun o:Option symbolMoveMachine.Cfg =>
      o.bind symbolMoveMachine.step)^[source.length + 1])
      (some (symbolMoveCfgState state source target)) =
      some (symbolMoveDoneCfg (source.reverse ++ target))
  exact symbolMove_reaches_done_from state source target

theorem symbolMoveLocal_correct (source target:List SparseSymbol):
    ((fun o => o.bind (TM2.step symbolMoveCoreProgram))^[source.length + 1])
      (some (symbolMoveLocalCfg .loop source target)) =
      some (symbolMoveLocalCfg .done [] (source.reverse ++ target)):=by
  have hp:symbolMoveCoreProgram=symbolMoveMachine.m:=by
    funext l
    rfl
  rw [hp]
  simpa [symbolMoveLocalCfg,symbolMoveCfg,symbolMoveDoneCfg] using!
    symbolMove_reaches_done source target

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def StateLens.first (σ τ:Type):StateLens σ (σ × τ) where
  get:=Prod.fst
  put:=fun outer inner => (inner,outer.2)
  get_put:=by intros; rfl
  put_get:=by intro outer; cases outer; rfl
  put_put:=by intros; rfl

def StateLens.second (σ τ:Type):StateLens τ (σ × τ) where
  get:=Prod.snd
  put:=fun outer inner => (outer.1,inner)
  get_put:=by intros; rfl
  put_get:=by intro outer; cases outer; rfl
  put_put:=by intros; rfl

def lensRenamedCfg {α K K' Λ Λx σ Ω:Type}
    (stackMap:StackRenaming K K') (state:StateLens σ Ω)
    (c:TM2.Cfg (fun _:K => α) Λ σ) (ambientState:Ω)
    (ambientStacks:K'→ List α):
    TM2.Cfg (fun _:K' => α) (Sum Λ Λx) Ω where
  l:=c.l.map Sum.inl
  var:=state.put ambientState c.var
  stk:=renamedStacks stackMap c.stk ambientStacks

theorem stepAux_lensRenameStmt {α K K' Λ Λx σ Ω:Type}
    [DecidableEq K] [DecidableEq K'] (stackMap:StackRenaming K K')
    (lens:StateLens σ Ω) (q:TM2.Stmt (fun _:K => α) Λ σ)
    (localState:σ) (ambientState:Ω) (inner:K→ List α)
    (ambientStacks:K'→ List α):
    TM2.stepAux (lensRenameStmt (Λx:=Λx) stackMap lens q)
        (lens.put ambientState localState)
        (renamedStacks stackMap inner ambientStacks) =
      lensRenamedCfg stackMap lens (TM2.stepAux q localState inner)
        ambientState ambientStacks:=by
  induction q generalizing localState inner with
  | push k f q ih =>
      simp only [lensRenameStmt,TM2.stepAux,lens.get_put,renamedStacks_encode]
      rw [update_renamedStacks]
      exact ih _ _
  | peek k f q ih =>
      simp only [lensRenameStmt,TM2.stepAux,lens.get_put,renamedStacks_encode,
        lens.put_put]
      exact ih _ _
  | pop k f q ih =>
      simp only [lensRenameStmt,TM2.stepAux,lens.get_put,renamedStacks_encode,
        lens.put_put]
      rw [update_renamedStacks]
      exact ih _ _
  | load f q ih =>
      simp only [lensRenameStmt,TM2.stepAux,lens.get_put,lens.put_put]
      exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [lensRenameStmt,TM2.stepAux,lens.get_put]
      cases h:f localState <;> simp [h]
      · exact ih₂ _ _
      · exact ih₁ _ _
  | goto f =>
      simp [lensRenameStmt,TM2.stepAux,lensRenamedCfg,lens.get_put]
  | halt =>
      simp [lensRenameStmt,TM2.stepAux,lensRenamedCfg]

def lensSpliceProgram {α K K' Λ Λx σ Ω:Type} [DecidableEq K]
    [DecidableEq K'] [DecidableEq Λ] (stackMap:StackRenaming K K')
    (lens:StateLens σ Ω)
    (left:Λ→ TM2.Stmt (fun _:K => α) Λ σ) (done:Λ)
    (returnLabel:Λx)
    (right:Λx→ TM2.Stmt (fun _:K' => α) (Sum Λ Λx) Ω):
    Sum Λ Λx→ TM2.Stmt (fun _:K' => α) (Sum Λ Λx) Ω
  | .inl l => if l=done then .goto fun _ => .inr returnLabel
      else lensRenameStmt stackMap lens (left l)
  | .inr l => right l

def lensReturnCfg {α K K' Λ Λx σ Ω:Type}
    (stackMap:StackRenaming K K') (lens:StateLens σ Ω)
    (returnLabel:Λx) (c:TM2.Cfg (fun _:K => α) Λ σ)
    (ambientState:Ω) (ambientStacks:K'→ List α):
    TM2.Cfg (fun _:K' => α) (Sum Λ Λx) Ω:=
  { lensRenamedCfg (Λx:=Λx) stackMap lens c ambientState ambientStacks with
      l:=some (.inr returnLabel) }

theorem step_lensSpliceProgram {α K K' Λ Λx σ Ω:Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (stackMap:StackRenaming K K') (lens:StateLens σ Ω)
    (left:Λ→ TM2.Stmt (fun _:K => α) Λ σ) (done:Λ)
    (returnLabel:Λx)
    (right:Λx→ TM2.Stmt (fun _:K' => α) (Sum Λ Λx) Ω)
    (c:TM2.Cfg (fun _:K => α) Λ σ) (hc:c.l ≠ some done)
    (ambientState:Ω) (ambientStacks:K'→ List α):
    TM2.step (lensSpliceProgram stackMap lens left done returnLabel right)
        (lensRenamedCfg stackMap lens c ambientState ambientStacks) =
      (TM2.step left c).map
        (fun c' => lensRenamedCfg stackMap lens c' ambientState ambientStacks):=by
  rcases c with ⟨label,localState,inner⟩
  cases label with
  | none => rfl
  | some label =>
      have hlabel:label ≠ done:=by
        intro h
        subst label
        exact hc rfl
      simp only [lensRenamedCfg,Option.map_some,TM2.step,lensSpliceProgram,
        hlabel,if_false]
      rw [stepAux_lensRenameStmt]
      rfl

theorem step_lensSpliceProgram_done {α K K' Λ Λx σ Ω:Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (stackMap:StackRenaming K K') (lens:StateLens σ Ω)
    (left:Λ→ TM2.Stmt (fun _:K => α) Λ σ) (done:Λ)
    (returnLabel:Λx)
    (right:Λx→ TM2.Stmt (fun _:K' => α) (Sum Λ Λx) Ω)
    (c:TM2.Cfg (fun _:K => α) Λ σ) (hc:c.l=some done)
    (ambientState:Ω) (ambientStacks:K'→ List α):
    TM2.step (lensSpliceProgram stackMap lens left done returnLabel right)
        (lensRenamedCfg stackMap lens c ambientState ambientStacks) =
      some (lensReturnCfg stackMap lens returnLabel c ambientState ambientStacks):=by
  rcases c with ⟨label,localState,inner⟩
  simp only at hc
  subst label
  simp [TM2.step,lensSpliceProgram,lensRenamedCfg,lensReturnCfg]

def lensRenamedOption {α K K' Λ Λx σ Ω:Type}
    (stackMap:StackRenaming K K') (lens:StateLens σ Ω)
    (c:Option (TM2.Cfg (fun _:K => α) Λ σ))
    (ambientState:Ω) (ambientStacks:K'→ List α):
    Option (TM2.Cfg (fun _:K' => α) (Sum Λ Λx) Ω):=
  c.map fun d => lensRenamedCfg stackMap lens d ambientState ambientStacks

theorem iterate_lensSpliceProgram {α K K' Λ Λx σ Ω:Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (stackMap:StackRenaming K K') (lens:StateLens σ Ω)
    (left:Λ→ TM2.Stmt (fun _:K => α) Λ σ) (done:Λ)
    (returnLabel:Λx)
    (right:Λx→ TM2.Stmt (fun _:K' => α) (Sum Λ Λx) Ω)
    (n:ℕ) (c:TM2.Cfg (fun _:K => α) Λ σ)
    (ambientState:Ω) (ambientStacks:K'→ List α)
    (havoid:AvoidsDone left done n c):
    ((fun o => o.bind (TM2.step
      (lensSpliceProgram stackMap lens left done returnLabel right)))^[n])
        (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) =
      lensRenamedOption stackMap lens
        (((fun o => o.bind (TM2.step left))^[n]) (some c))
        ambientState ambientStacks:=by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
      simp only [Option.bind_some]
      rw [step_lensSpliceProgram stackMap lens left done returnLabel right c
        havoid.1 ambientState ambientStacks]
      cases hstep:TM2.step left c with
      | none =>
          simp only [hstep,Option.map_none,Option.bind_none]
          rw [iterate_optionBind_none,iterate_optionBind_none]
          rfl
      | some c' =>
          simp only [hstep,Option.map_some,Option.bind_some]
          apply ih c'
          simpa [AvoidsDone,hstep] using havoid.2

theorem transport_lensHaltingMacro_and_return {α K K' Λ Λx σ Ω:Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (stackMap:StackRenaming K K') (lens:StateLens σ Ω)
    (left:Λ→ TM2.Stmt (fun _:K => α) Λ σ) (done:Λ)
    (hdone:left done=.halt) (returnLabel:Λx)
    (right:Λx→ TM2.Stmt (fun _:K' => α) (Sum Λ Λx) Ω)
    {n:ℕ} {c d:TM2.Cfg (fun _:K => α) Λ σ}
    (hrun:((fun o => o.bind (TM2.step left))^[n]) (some c)=some d)
    (hd:d.l=some done) (ambientState:Ω)
    (ambientStacks:K'→ List α):
    ((fun o => o.bind (TM2.step
      (lensSpliceProgram stackMap lens left done returnLabel right)))^[n + 1])
        (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) =
      some (lensReturnCfg stackMap lens returnLabel d ambientState ambientStacks):=by
  let stepO:=fun o:Option
      (TM2.Cfg (fun _:K' => α) (Sum Λ Λx) Ω) =>
    o.bind (TM2.step (lensSpliceProgram stackMap lens left done returnLabel right))
  have hAvoid:=avoidsDone_of_reaches_done left done hdone hrun hd
  have hmacro:=iterate_lensSpliceProgram stackMap lens left done returnLabel right
    n c ambientState ambientStacks hAvoid
  have hreturn:=step_lensSpliceProgram_done stackMap lens left done returnLabel
    right d hd ambientState ambientStacks
  have hmacro':
      ((fun o => o.bind (TM2.step
        (lensSpliceProgram stackMap lens left done returnLabel right)))^[n])
          (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) =
        some (lensRenamedCfg stackMap lens d ambientState ambientStacks):=by
    rw [hmacro]
    simp [lensRenamedOption,hrun]
  change (stepO^[n + 1])
    (some (lensRenamedCfg stackMap lens c ambientState ambientStacks))=_
  rw [Nat.add_comm,Function.iterate_add_apply,hmacro']
  simpa [stepO] using hreturn

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

set_option maxRecDepth 10000
set_option maxSynthPendingDepth 10000

def InterpreterMacroState.dispatchLens:
    StateLens DispatchControl InterpreterMacroState where
  get:=fun s => s.a.dispatch
  put:=fun s v => { s with a:= { s.a with dispatch:=v } }
  get_put:=by intros; rfl
  put_get:=by intro s; cases s; rfl
  put_put:=by intros; rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def mapLabelCfg {K Λ Λ' σ:Type} {α:K→ Type} (encode:Λ→ Λ')
    (c:TM2.Cfg α Λ σ):TM2.Cfg α Λ' σ where
  l:=c.l.map encode
  var:=c.var
  stk:=c.stk

@[simp] theorem mapLabelCfg_var {K Λ Λ' σ:Type} {α:K→ Type}
    (encode:Λ→ Λ') (c:TM2.Cfg α Λ σ):
    (mapLabelCfg encode c).var=c.var:=rfl

@[simp] theorem mapLabelCfg_stk {K Λ Λ' σ:Type} {α:K→ Type}
    (encode:Λ→ Λ') (c:TM2.Cfg α Λ σ):
    (mapLabelCfg encode c).stk=c.stk:=rfl

theorem stepAux_mapLabelStmt {K Λ Λ' σ:Type} {α:K→ Type} [DecidableEq K]
    (encode:Λ→ Λ') (q:TM2.Stmt α Λ σ)
    (state:σ) (tapes:(k:K)→ List (α k)):
    TM2.stepAux (mapLabelStmt encode q) state tapes =
      mapLabelCfg encode (TM2.stepAux q state tapes):=by
  induction q generalizing state tapes with
  | push k f q ih => simp only [mapLabelStmt,TM2.stepAux]; exact ih _ _
  | peek k f q ih => simp only [mapLabelStmt,TM2.stepAux]; exact ih _ _
  | pop k f q ih => simp only [mapLabelStmt,TM2.stepAux]; exact ih _ _
  | load f q ih => simp only [mapLabelStmt,TM2.stepAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [mapLabelStmt,TM2.stepAux]
      cases h:f state <;> simp [h]
      · exact ih₂ _ _
      · exact ih₁ _ _
  | goto f => rfl
  | halt => rfl

theorem step_liftRightProgram {α K Λx Λ σ:Type} [DecidableEq K]
    (left:Λx→ TM2.Stmt (fun _:K => α) (Sum Λx Λ) σ)
    (right:Λ→ TM2.Stmt (fun _:K => α) Λ σ)
    (c:TM2.Cfg (fun _:K => α) Λ σ):
    TM2.step (liftRightProgram left right) (mapLabelCfg Sum.inr c) =
      (TM2.step right c).map (mapLabelCfg Sum.inr):=by
  rcases c with ⟨label,state,tapes⟩
  cases label with
  | none => rfl
  | some label =>
      simp only [mapLabelCfg,Option.map_some,TM2.step,liftRightProgram]
      rw [stepAux_mapLabelStmt]
      rfl

def mapLabelOption {α K Λ Λ' σ:Type} (encode:Λ→ Λ')
    (c:Option (TM2.Cfg (fun _:K => α) Λ σ)):
    Option (TM2.Cfg (fun _:K => α) Λ' σ):=c.map (mapLabelCfg encode)

theorem iterate_liftRightProgram {α K Λx Λ σ:Type} [DecidableEq K]
    (left:Λx→ TM2.Stmt (fun _:K => α) (Sum Λx Λ) σ)
    (right:Λ→ TM2.Stmt (fun _:K => α) Λ σ)
    (n:ℕ) (c:TM2.Cfg (fun _:K => α) Λ σ):
    ((fun o => o.bind (TM2.step (liftRightProgram left right)))^[n])
      (some (mapLabelCfg Sum.inr c)) =
      mapLabelOption Sum.inr
        (((fun o => o.bind (TM2.step right))^[n]) (some c)):=by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
      simp only [Option.bind_some,step_liftRightProgram]
      cases hstep:TM2.step right c with
      | none =>
          simp only [Option.map_none,Option.bind_none]
          rw [iterate_optionBind_none,iterate_optionBind_none]
          rfl
      | some c' =>
          simp only [Option.map_some,Option.bind_some]
          exact ih c'

theorem transport_iterate_liftRightProgram {α K Λx Λ σ:Type}
    [DecidableEq K]
    (left:Λx→ TM2.Stmt (fun _:K => α) (Sum Λx Λ) σ)
    (right:Λ→ TM2.Stmt (fun _:K => α) Λ σ)
    {n:ℕ} {c d:TM2.Cfg (fun _:K => α) Λ σ}
    (hrun:((fun o => o.bind (TM2.step right))^[n]) (some c)=some d):
    ((fun o => o.bind (TM2.step (liftRightProgram left right)))^[n])
      (some (mapLabelCfg Sum.inr c))=some (mapLabelCfg Sum.inr d):=by
  rw [iterate_liftRightProgram]
  simp [mapLabelOption,hrun]

theorem chain_liftRightProgram {α K Λx Λ σ:Type} [DecidableEq K]
    (left:Λx→ TM2.Stmt (fun _:K => α) (Sum Λx Λ) σ)
    (right:Λ→ TM2.Stmt (fun _:K => α) Λ σ)
    {m n:ℕ} {a:TM2.Cfg (fun _:K => α) (Sum Λx Λ) σ}
    {b c:TM2.Cfg (fun _:K => α) Λ σ}
    (hfirst:
      ((fun o => o.bind (TM2.step (liftRightProgram left right)))^[m])
        (some a)=some (mapLabelCfg Sum.inr b))
    (hright:((fun o => o.bind (TM2.step right))^[n]) (some b)=some c):
    ((fun o => o.bind (TM2.step (liftRightProgram left right)))^[m + n])
      (some a)=some (mapLabelCfg Sum.inr c):=by
  have hlift:=transport_iterate_liftRightProgram left right hright
  rw [Nat.add_comm,Function.iterate_add_apply,hfirst,hlift]

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def phaseReturnCfg {α K K' Λ R σ Ω:Type}
    (stackMap:StackRenaming K K') (lens:StateLens σ Ω)
    (entry:R) (c:TM2.Cfg (fun _:K => α) Λ σ)
    (ambientState:Ω) (ambientStacks:K'→ List α):
    TM2.Cfg (fun _:K' => α) R Ω where
  l:=some entry
  var:=lens.put ambientState c.var
  stk:=renamedStacks stackMap c.stk ambientStacks

theorem lensSplice_eq_liftRightProgram {α K K' Λ R σ Ω:Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (stackMap:StackRenaming K K') (lens:StateLens σ Ω)
    (program:Λ→ TM2.Stmt (fun _:K => α) Λ σ) (done:Λ)
    (entry:R) (right:R→ TM2.Stmt (fun _:K' => α) R Ω):
    lensSpliceProgram stackMap lens program done entry
        (fun label => mapLabelStmt Sum.inr (right label)) =
      liftRightProgram (lensPhaseLeft stackMap lens program done entry) right:=by
  funext label
  cases label <;> rfl

theorem run_lensPhase_to_right {α K K' Λ R σ Ω:Type}
    [DecidableEq K] [DecidableEq K'] [DecidableEq Λ]
    (stackMap:StackRenaming K K') (lens:StateLens σ Ω)
    (program:Λ→ TM2.Stmt (fun _:K => α) Λ σ) (done:Λ)
    (hdone:program done=.halt) (entry:R)
    (right:R→ TM2.Stmt (fun _:K' => α) R Ω)
    {n:ℕ} {c d:TM2.Cfg (fun _:K => α) Λ σ}
    (hrun:((fun o => o.bind (TM2.step program))^[n]) (some c)=some d)
    (hd:d.l=some done) (ambientState:Ω)
    (ambientStacks:K'→ List α):
    ((fun o => o.bind (TM2.step
      (liftRightProgram (lensPhaseLeft stackMap lens program done entry) right)))^[n + 1])
      (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) =
      some (mapLabelCfg Sum.inr
        (phaseReturnCfg stackMap lens entry d ambientState ambientStacks)):=by
  rw [← lensSplice_eq_liftRightProgram stackMap lens program done entry right]
  have h:=transport_lensHaltingMacro_and_return stackMap lens program done hdone
    entry (fun label => mapLabelStmt Sum.inr (right label)) hrun hd
    ambientState ambientStacks
  simpa [lensReturnCfg,phaseReturnCfg,mapLabelCfg,lensRenamedCfg] using h

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def AvoidsHalts {K Λ σ:Type} {α:K→ Type} [DecidableEq K]
    (program:Λ→ TM2.Stmt α Λ σ):
    ℕ→ TM2.Cfg α Λ σ→ Prop
  | 0,_ => True
  | n + 1,c =>
      (∀ l,c.l=some l→ program l ≠ .halt)∧
        match TM2.step program c with
        | none => True
        | some c' => AvoidsHalts program n c'

theorem avoidsHalts_of_reaches_labeled {K Λ σ:Type} {α:K→ Type}
    [DecidableEq K] (program:Λ→ TM2.Stmt α Λ σ)
    {n:ℕ} {c d:TM2.Cfg α Λ σ}
    (hrun:((fun o => o.bind (TM2.step program))^[n]) (some c)=some d)
    (hd:d.l.isSome):AvoidsHalts program n c:=by
  induction n generalizing c with
  | zero => trivial
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun
      simp only [Option.bind_some] at hrun
      cases hstep:TM2.step program c with
      | none =>
          rw [hstep,iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          rw [hstep] at hrun
          constructor
          · intro l hlabel hhalt
            rcases c with ⟨label,state,tapes⟩
            simp only at hlabel
            subst label
            have hs:=step_at_halt_label program l hhalt state tapes
            rw [hstep] at hs
            have hc':=Option.some.inj hs
            subst c'
            have hnone:TM2.step program
                ({ l:=none,var:=state,stk:=tapes }:
                  TM2.Cfg α Λ σ)=none:=rfl
            cases n with
            | zero =>
                simp only [Function.iterate_zero_apply] at hrun
                have heq:=Option.some.inj hrun
                subst d
                simp at hd
            | succ n =>
                rw [Function.iterate_succ_apply] at hrun
                simp only [Option.bind_some,hnone]
                  at hrun
                rw [iterate_optionBind_none] at hrun
                contradiction
          · simpa [AvoidsHalts,hstep] using ih hrun

def multiPhaseReturnCfg {α K K' Λ R σ Ω:Type}
    (stackMap:StackRenaming K K') (lens:StateLens σ Ω)
    (next:R) (onExit:Ω→ Ω)
    (c:TM2.Cfg (fun _:K => α) Λ σ) (ambientState:Ω)
    (ambientStacks:K'→ List α):
    TM2.Cfg (fun _:K' => α) R Ω where
  l:=some next
  var:=onExit (lens.put ambientState c.var)
  stk:=renamedStacks stackMap c.stk ambientStacks

theorem step_lensMultiPhase_nonexit {α K K' Λ R σ Ω:Type}
    [DecidableEq K] [DecidableEq K']
    (stackMap:StackRenaming K K') (lens:StateLens σ Ω)
    (program:Λ→ TM2.Stmt (fun _:K => α) Λ σ)
    (exit:Λ→ Option R) (onExit:Λ→ Ω→ Ω)
    (right:R→ TM2.Stmt (fun _:K' => α) R Ω)
    (c:TM2.Cfg (fun _:K => α) Λ σ)
    (ambientState:Ω) (ambientStacks:K'→ List α)
    (hnone:∀ l,c.l=some l→ exit l=none):
    TM2.step (liftRightProgram
        (lensMultiPhaseLeft stackMap lens program exit onExit) right)
        (lensRenamedCfg (Λx:=R) stackMap lens c ambientState ambientStacks) =
      (TM2.step program c).map
        (fun c' => lensRenamedCfg stackMap lens c' ambientState ambientStacks):=by
  rcases c with ⟨label,localState,tapes⟩
  cases label with
  | none => rfl
  | some label =>
      have h:=hnone label rfl
      simp [TM2.step,liftRightProgram,lensMultiPhaseLeft,h,lensRenamedCfg]
      rw [stepAux_lensRenameStmt]
      rfl

theorem iterate_lensMultiPhase {α K K' Λ R σ Ω:Type}
    [DecidableEq K] [DecidableEq K']
    (stackMap:StackRenaming K K') (lens:StateLens σ Ω)
    (program:Λ→ TM2.Stmt (fun _:K => α) Λ σ)
    (exit:Λ→ Option R) (onExit:Λ→ Ω→ Ω)
    (hexitHalt:∀ l, (exit l).isSome→ program l=.halt)
    (right:R→ TM2.Stmt (fun _:K' => α) R Ω)
    (n:ℕ) (c:TM2.Cfg (fun _:K => α) Λ σ)
    (ambientState:Ω) (ambientStacks:K'→ List α)
    (havoid:AvoidsHalts program n c):
    ((fun o => o.bind (TM2.step
      (liftRightProgram
        (lensMultiPhaseLeft stackMap lens program exit onExit) right)))^[n])
      (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) =
    lensRenamedOption stackMap lens
      (((fun o => o.bind (TM2.step program))^[n]) (some c))
      ambientState ambientStacks:=by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
      simp only [Option.bind_some]
      have hnone:∀ l,c.l=some l→ exit l=none:=by
        intro l hl
        cases he:exit l with
        | none => rfl
        | some r =>
            have hh:=hexitHalt l (by simp [he])
            exact False.elim (havoid.1 l hl hh)
      rw [step_lensMultiPhase_nonexit stackMap lens program exit onExit right c
        ambientState ambientStacks hnone]
      cases hstep:TM2.step program c with
      | none =>
          simp only [hstep,Option.map_none,Option.bind_none]
          rw [iterate_optionBind_none,iterate_optionBind_none]
          rfl
      | some c' =>
          simp only [hstep,Option.map_some,Option.bind_some]
          apply ih c'
          simpa [AvoidsHalts,hstep] using havoid.2

theorem run_lensMultiPhase_to_right {α K K' Λ R σ Ω:Type}
    [DecidableEq K] [DecidableEq K']
    (stackMap:StackRenaming K K') (lens:StateLens σ Ω)
    (program:Λ→ TM2.Stmt (fun _:K => α) Λ σ)
    (exit:Λ→ Option R) (onExit:Λ→ Ω→ Ω)
    (hexitHalt:∀ l, (exit l).isSome→ program l=.halt)
    (right:R→ TM2.Stmt (fun _:K' => α) R Ω)
    {n:ℕ} {c d:TM2.Cfg (fun _:K => α) Λ σ}
    (hrun:((fun o => o.bind (TM2.step program))^[n]) (some c)=some d)
    {done:Λ} {next:R} (hd:d.l=some done)
    (hexit:exit done=some next)
    (ambientState:Ω) (ambientStacks:K'→ List α):
    ((fun o => o.bind (TM2.step
      (liftRightProgram
        (lensMultiPhaseLeft stackMap lens program exit onExit) right)))^[n + 1])
      (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) =
    some (mapLabelCfg Sum.inr
      (multiPhaseReturnCfg stackMap lens next (onExit done) d
        ambientState ambientStacks)):=by
  have hAvoid:=avoidsHalts_of_reaches_labeled program hrun (by simp [hd])
  have hiter:=iterate_lensMultiPhase stackMap lens program exit onExit
    hexitHalt right n c ambientState ambientStacks hAvoid
  have hiter':
      ((fun o => o.bind (TM2.step
        (liftRightProgram
          (lensMultiPhaseLeft stackMap lens program exit onExit) right)))^[n])
        (some (lensRenamedCfg stackMap lens c ambientState ambientStacks)) =
      some (lensRenamedCfg stackMap lens d ambientState ambientStacks):=by
    simpa [lensRenamedOption,hrun] using hiter
  rw [Nat.add_comm,Function.iterate_add_apply,hiter']
  rcases d with ⟨label,localState,tapes⟩
  simp only at hd
  subst label
  simp [TM2.step,liftRightProgram,lensMultiPhaseLeft,hexit,
    lensRenamedCfg,multiPhaseReturnCfg,mapLabelCfg]

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def boundedLiteralWordCfg (N:ℕ) (label:LiteralWordLabel)
    (remaining:Fin (N + 1)) (query backup result:List SparseSymbol):
    TM2.Cfg (fun _:LiteralWordStack => SparseSymbol)
      LiteralWordLabel (BoundedLiteralControl N) where
  l:=some label
  var:= ⟨none,remaining⟩
  stk:=literalWordStacks query backup result

@[simp] theorem boundedLiteralWord_step_emit_nil (N:ℕ)
    (remaining:Fin (N + 1)) (backup result:List SparseSymbol):
    TM2.step (boundedLiteralWordProgram N)
      (boundedLiteralWordCfg N .emit remaining [] backup result) =
    some (boundedLiteralWordCfg N .restore remaining [] backup result):=by
  simp [boundedLiteralWordProgram,boundedLiteralWordCfg,literalWordStacks]

@[simp] theorem boundedLiteralWord_step_emit_cons (N:ℕ)
    (remaining:Fin (N + 1)) (a:SparseSymbol)
    (query backup result:List SparseSymbol):
    TM2.step (boundedLiteralWordProgram N)
      (boundedLiteralWordCfg N .emit remaining (a::query) backup result) =
    some (boundedLiteralWordCfg N .emit
      ⟨remaining.val.div2,
        lt_of_le_of_lt (Nat.div_le_self _ _) remaining.isLt⟩
      query (a::backup) (.bit remaining.val.bodd::result)):=by
  simp [boundedLiteralWordProgram,BoundedLiteralControl.advance,
    boundedLiteralWordCfg,literalWordStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem boundedLiteralWord_step_restore_nil (N:ℕ)
    (remaining:Fin (N + 1)) (query result:List SparseSymbol):
    TM2.step (boundedLiteralWordProgram N)
      (boundedLiteralWordCfg N .restore remaining query [] result) =
    some (boundedLiteralWordCfg N .done remaining query [] result):=by
  simp [boundedLiteralWordProgram,boundedLiteralWordCfg,literalWordStacks]

@[simp] theorem boundedLiteralWord_step_restore_cons (N:ℕ)
    (remaining:Fin (N + 1)) (a:SparseSymbol)
    (query backup result:List SparseSymbol):
    TM2.step (boundedLiteralWordProgram N)
      (boundedLiteralWordCfg N .restore remaining query (a::backup) result) =
    some (boundedLiteralWordCfg N .restore remaining
      (a::query) backup result):=by
  simp [boundedLiteralWordProgram,boundedLiteralWordCfg,
    literalWordStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem boundedLiteralWord_emit_iterate (N:ℕ)
    (remaining:Fin (N + 1)) (query backup result:List SparseSymbol):
    ((fun o:Option (TM2.Cfg (fun _:LiteralWordStack => SparseSymbol)
      LiteralWordLabel (BoundedLiteralControl N)) =>
        o.bind (TM2.step (boundedLiteralWordProgram N)))^[query.length])
      (some (boundedLiteralWordCfg N .emit remaining query backup result)) =
    some (boundedLiteralWordCfg N .emit
      ⟨remaining.val / 2 ^ query.length,
        lt_of_le_of_lt (Nat.div_le_self _ _) remaining.isLt⟩
      [] (query.reverse ++ backup)
      ((fixedBits query.length remaining.val).reverse.map SparseSymbol.bit ++
        result)):=by
  induction query generalizing remaining backup result with
  | nil => simp [boundedLiteralWordCfg,fixedBits]
  | cons a query ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,boundedLiteralWord_step_emit_cons]
      rw [ih]
      congr 2
      · apply Fin.ext
        simp only [Nat.div2_val,Nat.div_div_eq_div_mul,pow_succ]
        rw [Nat.mul_comm]
      · simp [List.reverse_cons,List.append_assoc]
      · simp [fixedBits,List.map_reverse,List.append_assoc]

theorem boundedLiteralWord_restore_iterate (N:ℕ)
    (remaining:Fin (N + 1)) (query backup result:List SparseSymbol):
    ((fun o:Option (TM2.Cfg (fun _:LiteralWordStack => SparseSymbol)
      LiteralWordLabel (BoundedLiteralControl N)) =>
        o.bind (TM2.step (boundedLiteralWordProgram N)))^[backup.length])
      (some (boundedLiteralWordCfg N .restore remaining query backup result)) =
    some (boundedLiteralWordCfg N .restore remaining
      (backup.reverse ++ query) [] result):=by
  induction backup generalizing query with
  | nil => rfl
  | cons a backup ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,boundedLiteralWord_step_restore_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem boundedLiteralWord_correct_exact (N n:ℕ) (hn:n≤ N)
    (query result:List SparseSymbol):
    ((fun o:Option (TM2.Cfg (fun _:LiteralWordStack => SparseSymbol)
      LiteralWordLabel (BoundedLiteralControl N)) =>
        o.bind (TM2.step (boundedLiteralWordProgram N)))^[
          2 * query.length + 2])
      (some (boundedLiteralWordCfg N .emit ⟨n,by omega⟩ query [] result)) =
    some (boundedLiteralWordCfg N .done
      ⟨n / 2 ^ query.length,by
        exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
      query []
      ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result)):=by
  let stepO:=fun o:Option
      (TM2.Cfg (fun _:LiteralWordStack => SparseSymbol)
        LiteralWordLabel (BoundedLiteralControl N)) =>
    o.bind (TM2.step (boundedLiteralWordProgram N))
  let initial:Fin (N + 1):= ⟨n,by omega⟩
  let remaining:Fin (N + 1):=
    ⟨n / 2 ^ query.length,
      lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
  have h0:=boundedLiteralWord_emit_iterate N initial query [] result
  have h1raw:=boundedLiteralWord_step_emit_nil N remaining query.reverse
    ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result)
  have h1:(stepO^[1])
      (some (boundedLiteralWordCfg N .emit remaining [] query.reverse
        ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result))) =
    some (boundedLiteralWordCfg N .restore remaining [] query.reverse
      ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result)):=by
    simpa [stepO] using h1raw
  have h2:=boundedLiteralWord_restore_iterate N remaining [] query.reverse
    ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result)
  have h2':=h2
  simp only [List.reverse_reverse,List.append_nil] at h2'
  have h3raw:=boundedLiteralWord_step_restore_nil N remaining query
    ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result)
  have h3:(stepO^[1])
      (some (boundedLiteralWordCfg N .restore remaining query []
        ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result))) =
    some (boundedLiteralWordCfg N .done remaining query []
      ((fixedBits query.length n).reverse.map SparseSymbol.bit ++ result)):=by
    simpa [stepO] using h3raw
  have chain {r s:ℕ}
      {x y z:Option (TM2.Cfg (fun _:LiteralWordStack => SparseSymbol)
        LiteralWordLabel (BoundedLiteralControl N))}
      (hr:(stepO^[r]) x=y) (hs:(stepO^[s]) y=z):
      (stepO^[s + r]) x=z:=by
    rw [Function.iterate_add_apply,hr,hs]
  have h0':=h0
  simp only [List.append_nil] at h0'
  have hrun:=chain (chain (chain h0' h1) h2') h3
  simp only [List.length_reverse] at hrun
  have hexp:1 + (query.length + (1 + query.length)) =
      2 * query.length + 2:=by omega
  rw [hexp] at hrun
  simpa [stepO,initial,remaining] using hrun

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def discardStacks (data:List SparseSymbol):
    DiscardStack→ List SparseSymbol
  | .data => data

def discardCfg (label:DiscardLabel) (data:List SparseSymbol):
    TM2.Cfg (fun _:DiscardStack => SparseSymbol)
      DiscardLabel SymbolMoveControl where
  l:=some label
  var:=default
  stk:=discardStacks data

def discardCfgState (label:DiscardLabel) (state:SymbolMoveControl)
    (data:List SparseSymbol):
    TM2.Cfg (fun _:DiscardStack => SparseSymbol)
      DiscardLabel SymbolMoveControl where
  l:=some label
  var:=state
  stk:=discardStacks data

@[simp] theorem discard_step_state_nil (state:SymbolMoveControl):
    TM2.step discardProgram (discardCfgState .loop state []) =
      some (discardCfg .done []):=by
  simp [TM2.step,discardProgram,discardCfgState,discardCfg,discardStacks]

@[simp] theorem discard_step_state_cons (state:SymbolMoveControl)
    (a:SparseSymbol) (data:List SparseSymbol):
    TM2.step discardProgram (discardCfgState .loop state (a::data)) =
      some (discardCfg .loop data):=by
  simp [TM2.step,discardProgram,discardCfgState,discardCfg,discardStacks]
  congr 2
  funext k
  cases k
  rfl

@[simp] theorem discard_step_nil:
    TM2.step discardProgram (discardCfg .loop []) =
      some (discardCfg .done []):=by
  simp [TM2.step,discardProgram,discardCfg,discardStacks]

@[simp] theorem discard_step_cons (a:SparseSymbol)
    (data:List SparseSymbol):
    TM2.step discardProgram (discardCfg .loop (a::data)) =
      some (discardCfg .loop data):=by
  simp [TM2.step,discardProgram,discardCfg,discardStacks]
  congr 2
  funext k
  cases k
  rfl

theorem discard_iterate (data:List SparseSymbol):
    ((fun o:Option (TM2.Cfg (fun _:DiscardStack => SparseSymbol)
        DiscardLabel SymbolMoveControl) => o.bind (TM2.step discardProgram))^[data.length])
      (some (discardCfg .loop data)) =
        some (discardCfg .loop []):=by
  induction data with
  | nil => rfl
  | cons a data ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,discard_step_cons]
      exact ih

theorem discard_correct (data:List SparseSymbol):
    ((fun o:Option (TM2.Cfg (fun _:DiscardStack => SparseSymbol)
        DiscardLabel SymbolMoveControl) => o.bind (TM2.step discardProgram))^[data.length + 1])
      (some (discardCfg .loop data)) =
        some (discardCfg .done []):=by
  rw [Nat.add_comm,Function.iterate_add_apply,discard_iterate]
  simp only [Function.iterate_one,Option.bind_some,discard_step_nil]

theorem discard_correct_from (state:SymbolMoveControl)
    (data:List SparseSymbol):
    ((fun o:Option (TM2.Cfg (fun _:DiscardStack => SparseSymbol)
        DiscardLabel SymbolMoveControl) => o.bind (TM2.step discardProgram))^[data.length + 1])
      (some (discardCfgState .loop state data)) =
        some (discardCfg .done []):=by
  cases data with
  | nil => simpa using discard_step_state_nil state
  | cons a data =>
      rw [List.length_cons,show data.length + 1 + 1=(data.length + 1) + 1 by omega,
        Function.iterate_succ_apply]
      simp only [Option.bind_some,discard_step_state_cons]
      exact discard_correct data

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def operandBoundaryBase (w accumulator:ℕ) (m:SparseMemory)
    (base:CoreStack→ List SparseSymbol):CoreStack→ List SparseSymbol:=
  fun
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work0 | .work1 | .work2 | .work3
  | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def operandResultBase (w accumulator value:ℕ) (m:SparseMemory)
    (base:CoreStack→ List SparseSymbol):CoreStack→ List SparseSymbol:=
  fun
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work0 => (fixedBits w value).reverse.map SparseSymbol.bit
  | .work1 | .work2 | .work3 | .work4
  | .work5 | .work6 | .work7 => []
  | k => base k

@[simp] theorem operandBoundaryBase_coreStacks (w value:Nat)
    (s:SparseState):
    operandBoundaryBase w value s.mem (coreStacks w s) =
      coreStacks w { s with acc:=value }:=by
  funext k
  cases k <;> rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

theorem lookupExit_halts {R:Type} (label:LookupScanLabel)
    (h:(lookupExit (R:=R) label).isSome):
    lookupScanProgram label=.halt:=by
  cases label <;> simp [lookupExit,lookupScanProgram,lookupScanMachine] at h ⊢

theorem unifiedLookup_found_bridge {N:ℕ} {R:Type}
    (w accumulator query value:ℕ) (m:SparseMemory)
    (base:CoreStack→ List SparseSymbol)
    (state:FullInterpreterState N):
    multiPhaseReturnCfg lookupCoreRenaming FullInterpreterState.lookupLens
      (Sum.inl DiscardLabel.loop:UnifiedLookupTail R)
      (lookupRecordOutcome LookupScanLabel.found)
      (lookupScanMacroCfg .found true
        (encodeSparseMemory w m ++ [.memoryEnd]) []
        ((fixedBits w value).reverse.map SparseSymbol.bit) []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
      state (operandBoundaryBase w accumulator m base) =
    lensRenamedCfg (Λx:=R) (discardCoreRenaming .work1)
      FullInterpreterState.moveLens
      (discardCfgState .loop
        (FullInterpreterState.moveLens.get
          (lookupRecordOutcome .found
            (FullInterpreterState.lookupLens.put state
              ⟨none,true,none,none⟩)))
        ((fixedBits w query).reverse.map SparseSymbol.bit))
      (lookupRecordOutcome .found
        (FullInterpreterState.lookupLens.put state
          ⟨none,true,none,none⟩))
      (operandResultBase w accumulator value m base):=by
  simp [multiPhaseReturnCfg,lensRenamedCfg,lookupRecordOutcome,
    operandBoundaryBase,operandResultBase,renamedStacks,
    lookupCoreRenaming,lookupCoreDecode,lookupScanMacroCfg,
    lookupScanCfg,lookupScanStacks,discardCoreRenaming,
    discardCfgState,discardStacks]
  constructor
  · rw [FullInterpreterState.moveLens.put_get]
  · funext k
    cases k <;> simp [renamedStacks,lookupCoreRenaming,lookupCoreDecode,
      lookupScanMacroCfg,lookupScanCfg,lookupScanStacks,
      discardCoreRenaming,discardCfgState,discardStacks,
      operandBoundaryBase,operandResultBase,List.map_reverse]

theorem unifiedLookup_missing_bridge {N:ℕ} {R:Type}
    (w accumulator query:ℕ) (m:SparseMemory)
    (base:CoreStack→ List SparseSymbol)
    (state:FullInterpreterState N):
    multiPhaseReturnCfg lookupCoreRenaming FullInterpreterState.lookupLens
      (Sum.inl DiscardLabel.loop:UnifiedLookupTail R)
      (lookupRecordOutcome LookupScanLabel.missing)
      (lookupScanMacroCfg .missing (decide m.isEmpty)
        (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
      state (operandBoundaryBase w accumulator m base) =
    lensRenamedCfg (Λx:=R) (discardCoreRenaming .work1)
      FullInterpreterState.moveLens
      (discardCfgState .loop
        (FullInterpreterState.moveLens.get
          (lookupRecordOutcome .missing
            (FullInterpreterState.lookupLens.put state
              ⟨none,decide m.isEmpty,none,none⟩)))
        ((fixedBits w query).reverse.map SparseSymbol.bit))
      (lookupRecordOutcome .missing
        (FullInterpreterState.lookupLens.put state
          ⟨none,decide m.isEmpty,none,none⟩))
      (operandBoundaryBase w accumulator m base):=by
  simp [multiPhaseReturnCfg,lensRenamedCfg,lookupRecordOutcome,
    operandBoundaryBase,renamedStacks,lookupCoreRenaming,lookupCoreDecode,
    lookupScanMacroCfg,lookupScanCfg,lookupScanStacks,
    discardCoreRenaming,discardCfgState,discardStacks]
  constructor
  · rw [FullInterpreterState.moveLens.put_get]
  · funext k
    cases k <;> simp [renamedStacks,lookupCoreRenaming,lookupCoreDecode,
      lookupScanMacroCfg,lookupScanCfg,lookupScanStacks,
      discardCoreRenaming,discardCfgState,discardStacks,
      operandBoundaryBase,List.map_reverse]

theorem unifiedLookup_found {N:ℕ} {R:Type}
    (w accumulator query value:ℕ) (hq:query < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (hfind:m.find? query=some value)
    (right:UnifiedLookupTail R→
      TM2.Stmt (fun _:CoreStack => SparseSymbol)
        (UnifiedLookupTail R) (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ∃ steps≤ m.length * (12 * w + 22) + 11 * w + 23,
      ((fun o => o.bind (TM2.step (unifiedLookupProgram right)))^[steps])
        (some (lensRenamedCfg lookupCoreRenaming
          FullInterpreterState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          state (operandBoundaryBase w accumulator m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg (Λx:=R) (discardCoreRenaming .work1)
          FullInterpreterState.moveLens
          (discardCfgState .loop
            (FullInterpreterState.moveLens.get
              (lookupRecordOutcome .found
                (FullInterpreterState.lookupLens.put state
                  ⟨none,true,none,none⟩)))
            ((fixedBits w query).reverse.map SparseSymbol.bit))
          (lookupRecordOutcome .found
            (FullInterpreterState.lookupLens.put state
              ⟨none,true,none,none⟩))
          (operandResultBase w accumulator value m base))):=by
  rcases lookupScan_found w query value hq m hm hfind [] with
    ⟨steps,hbound,hrun⟩
  simp only [List.length_nil,Nat.add_zero] at hbound
  refine ⟨steps + 1,by omega, ?_⟩
  have h:=run_lensMultiPhase_to_right lookupCoreRenaming
    FullInterpreterState.lookupLens lookupScanProgram lookupExit
    lookupRecordOutcome lookupExit_halts right hrun rfl (by rfl)
    state (operandBoundaryBase w accumulator m base)
  simp only [List.reverse_nil,List.nil_append,lookupScanMacroCfg,
    lookupScanCfg] at h
  have hb:=unifiedLookup_found_bridge (R:=R) w accumulator query value m
    base state
  simp only [lookupScanMacroCfg,lookupScanCfg] at hb
  have hout:=congrArg (fun c => some (mapLabelCfg
    (fun l:UnifiedLookupTail R =>
      (Sum.inr l:UnifiedLookupLabel R)) c)) hb
  simpa [unifiedLookupProgram,lookupScanMacroCfg,lookupScanCfg] using!
    h.trans hout

theorem unifiedLookup_missing {N:ℕ} {R:Type}
    (w accumulator query:ℕ) (hq:query < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (hmissing:m.find? query=none)
    (right:UnifiedLookupTail R→
      TM2.Stmt (fun _:CoreStack => SparseSymbol)
        (UnifiedLookupTail R) (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ((fun o => o.bind (TM2.step (unifiedLookupProgram right)))^[
      m.length * (12 * w + 22) + 3])
      (some (lensRenamedCfg lookupCoreRenaming
        FullInterpreterState.lookupLens
        (lookupScanMacroCfg .scan true
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
        state (operandBoundaryBase w accumulator m base))) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg (Λx:=R) (discardCoreRenaming .work1)
        FullInterpreterState.moveLens
        (discardCfgState .loop
          (FullInterpreterState.moveLens.get
            (lookupRecordOutcome .missing
              (FullInterpreterState.lookupLens.put state
                ⟨none,decide m.isEmpty,none,none⟩)))
          ((fixedBits w query).reverse.map SparseSymbol.bit))
        (lookupRecordOutcome .missing
          (FullInterpreterState.lookupLens.put state
            ⟨none,decide m.isEmpty,none,none⟩))
        (operandBoundaryBase w accumulator m base))):=by
  have hrun:
      ((fun o:Option
          (TM2.Cfg (fun _:LookupScanStack => SparseSymbol)
            LookupScanLabel LookupCellControl) =>
        o.bind (TM2.step lookupScanProgram))^[
          m.length * (12 * w + 22) + 2])
        (some (lookupScanMacroCfg .scan true
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])) =
      some (lookupScanMacroCfg .missing (decide m.isEmpty)
        (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
        ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] []):=by
    simpa [lookupScanProgram,lookupScanMacroCfg,lookupScanCfg,
      lookupScanMachine] using!
      lookupScan_all_missing w query hq m hm hmissing true []
  have h:=run_lensMultiPhase_to_right lookupCoreRenaming
    FullInterpreterState.lookupLens lookupScanProgram lookupExit
    lookupRecordOutcome lookupExit_halts right hrun rfl (by rfl)
    state (operandBoundaryBase w accumulator m base)
  simp only [lookupScanMacroCfg,lookupScanCfg] at h
  have hb:=unifiedLookup_missing_bridge (R:=R) w accumulator query m
    base state
  simp only [lookupScanMacroCfg,lookupScanCfg] at hb
  have hout:=congrArg (fun c => some (mapLabelCfg
    (fun l:UnifiedLookupTail R =>
      (Sum.inr l:UnifiedLookupLabel R)) c)) hb
  simpa [unifiedLookupProgram,lookupScanMacroCfg,lookupScanCfg] using
    h.trans hout

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def cleanDecisionCfg {N:ℕ} {R:Type}
    (state:FullInterpreterState N)
    (tapes:CoreStack→ List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (UnifiedCleanAfter R) (FullInterpreterState N) where
  l:=some (.inl .decide)
  var:=state
  stk:=tapes

def cleanReturnCfg {N:ℕ} {R:Type} (returnLabel:R)
    (state:FullInterpreterState N)
    (tapes:CoreStack→ List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N) where
  l:=some returnLabel
  var:=state
  stk:=tapes

@[simp] theorem lookupDecision_found_step {N:ℕ} {R:Type}
    (returnLabel:R) (right:R→ TM2.Stmt
      (fun _:CoreStack => SparseSymbol) R (FullInterpreterState N))
    (state:FullInterpreterState N) (hfound:state.lookupFound=true)
    (tapes:CoreStack→ List SparseSymbol):
    TM2.step (unifiedCleanAfterProgram returnLabel right)
      (cleanDecisionCfg (R:=R) state tapes) =
    some (mapLabelCfg Sum.inr
      (mapLabelCfg Sum.inr (cleanReturnCfg returnLabel state tapes))):=by
  simp [unifiedCleanAfterProgram,lookupDecisionProgram,cleanDecisionCfg,
    cleanReturnCfg,liftRightProgram,mapLabelCfg,TM2.step,hfound]

theorem lookupDecision_missing_step {N:ℕ} {R:Type}
    (returnLabel:R) (right:R→ TM2.Stmt
      (fun _:CoreStack => SparseSymbol) R (FullInterpreterState N))
    (w accumulator:ℕ) (m:SparseMemory)
    (base:CoreStack→ List SparseSymbol)
    (state:FullInterpreterState N) (hmissing:state.lookupFound=false):
    TM2.step (unifiedCleanAfterProgram returnLabel right)
      (cleanDecisionCfg (R:=R) state
        (operandBoundaryBase w accumulator m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg (Λx:=R) zeroWordCoreRenaming
        FullInterpreterState.zeroLens
        (zeroWordCfgState .fill
          (FullInterpreterState.zeroLens.get state)
          ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
        state (operandBoundaryBase w accumulator m base))):=by
  simp [unifiedCleanAfterProgram,lookupDecisionProgram,cleanDecisionCfg,
    liftRightProgram,mapLabelCfg,TM2.step,hmissing,
    lensRenamedCfg,zeroWordCoreRenaming,zeroWordCoreDecode,
    zeroWordCfgState,zeroWordStacks,operandBoundaryBase,renamedStacks]
  constructor
  · rw [FullInterpreterState.zeroLens.put_get]
  · funext k
    cases k <;> rfl

theorem discard_decision_bridge {N:ℕ} {R:Type}
    (state:FullInterpreterState N)
    (tapes:CoreStack→ List SparseSymbol)
    (hwork:tapes .work1=[]):
    phaseReturnCfg (discardCoreRenaming .work1)
      FullInterpreterState.moveLens
      (Sum.inl LookupDecisionLabel.decide:UnifiedCleanAfter R)
      (discardCfg .done []) state tapes =
    cleanDecisionCfg (R:=R)
      (FullInterpreterState.moveLens.put state default) tapes:=by
  simp [phaseReturnCfg,cleanDecisionCfg,discardCoreRenaming,
    discardCfg,discardStacks,renamedStacks]
  funext k
  cases k <;> simp [renamedStacks,discardCoreRenaming,
    discardCfg,discardStacks,hwork]

theorem zero_return_bridge {N:ℕ} {R:Type}
    (returnLabel:R) (w accumulator:ℕ) (m:SparseMemory)
    (base:CoreStack→ List SparseSymbol)
    (state:FullInterpreterState N):
    phaseReturnCfg zeroWordCoreRenaming FullInterpreterState.zeroLens
      returnLabel
      (zeroWordCfg .done
        ((fixedBits w accumulator).map SparseSymbol.bit) []
        ((fixedBits w 0).reverse.map SparseSymbol.bit))
      state (operandBoundaryBase w accumulator m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.zeroLens.put state default)
      (operandResultBase w accumulator 0 m base):=by
  simp [phaseReturnCfg,cleanReturnCfg,lensRenamedCfg,
    zeroWordCoreRenaming,zeroWordCoreDecode,zeroWordCfg,
    zeroWordStacks,operandBoundaryBase,operandResultBase,
    renamedStacks,fixedBits_zero,List.map_reverse]
  funext k
  cases k <;> simp [renamedStacks,zeroWordCoreRenaming,
    zeroWordCoreDecode,zeroWordCfg,zeroWordStacks,
    operandBoundaryBase,operandResultBase,fixedBits_zero,
    List.map_reverse]

theorem unifiedCleanLookup_found {N:ℕ} {R:Type}
    (w accumulator query value:ℕ) (hq:query < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (hfind:m.find? query=some value)
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ∃ steps≤ m.length * (12 * w + 22) + 12 * w + 26,
      ((fun o => o.bind (TM2.step
        (unifiedCleanLookupProgram returnLabel right)))^[steps])
        (some (lensRenamedCfg lookupCoreRenaming
          FullInterpreterState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          state (operandBoundaryBase w accumulator m base))) =
      some (mapLabelCfg (fun l:UnifiedCleanTail R => Sum.inr l)
        (mapLabelCfg (fun l:UnifiedCleanAfter R => Sum.inr l)
          (mapLabelCfg (fun l:UnifiedCleanFinish R => Sum.inr l)
            (mapLabelCfg (fun l:R => Sum.inr l)
              (cleanReturnCfg returnLabel
                (FullInterpreterState.moveLens.put
                  (lookupRecordOutcome .found
                    (FullInterpreterState.lookupLens.put state
                      ⟨none,true,none,none⟩)) default)
                (operandResultBase w accumulator value m base)))))):=by
  let foundState:=lookupRecordOutcome LookupScanLabel.found
    (FullInterpreterState.lookupLens.put state
      ⟨none,true,none,none⟩)
  rcases unifiedLookup_found (R:=UnifiedCleanAfter R)
      w accumulator query value hq m hm hfind
      (unifiedCleanTailProgram returnLabel right) state base with
    ⟨lookupSteps,hbound,hlookup⟩
  have hdiscard:=run_lensPhase_to_right
    (discardCoreRenaming .work1) FullInterpreterState.moveLens
    discardProgram .done (by rfl)
    (Sum.inl LookupDecisionLabel.decide)
    (unifiedCleanAfterProgram returnLabel right)
    (discard_correct_from
      (FullInterpreterState.moveLens.get foundState)
      ((fixedBits w query).reverse.map SparseSymbol.bit)) rfl
    foundState (operandResultBase w accumulator value m base)
  simp only [List.length_map,List.length_reverse,fixedBits_length] at hdiscard
  rw [discard_decision_bridge (R:=R) foundState
    (operandResultBase w accumulator value m base) (by rfl)] at hdiscard
  have houtcome:=lookupDecision_found_step returnLabel right
    (FullInterpreterState.moveLens.put foundState default) (by rfl)
    (operandResultBase w accumulator value m base)
  have houtcome':
      ((fun o => o.bind (TM2.step
        (unifiedCleanAfterProgram returnLabel right)))^[1])
        (some (cleanDecisionCfg
          (FullInterpreterState.moveLens.put foundState default)
          (operandResultBase w accumulator value m base))) =
      some (mapLabelCfg Sum.inr
        (mapLabelCfg Sum.inr
          (cleanReturnCfg returnLabel
            (FullInterpreterState.moveLens.put foundState default)
            (operandResultBase w accumulator value m base)))):=by
    simpa using houtcome
  have htail:=chain_liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl LookupDecisionLabel.decide))
    (unifiedCleanAfterProgram returnLabel right) hdiscard houtcome'
  have hchain:=chain_liftRightProgram
    (lensMultiPhaseLeft lookupCoreRenaming FullInterpreterState.lookupLens
      lookupScanProgram lookupExit lookupRecordOutcome)
    (unifiedCleanTailProgram returnLabel right) hlookup htail
  refine ⟨lookupSteps + (w + 2 + 1), ?_, ?_⟩
  · omega
  · simpa [unifiedCleanLookupProgram,foundState] using! hchain

theorem unifiedCleanLookup_missing {N:ℕ} {R:Type}
    (w accumulator query:ℕ) (hq:query < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (hmissing:m.find? query=none)
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ((fun o => o.bind (TM2.step
      (unifiedCleanLookupProgram returnLabel right)))^[
        m.length * (12 * w + 22) + 3 * w + 9])
      (some (lensRenamedCfg lookupCoreRenaming
        FullInterpreterState.lookupLens
        (lookupScanMacroCfg .scan true
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
        state (operandBoundaryBase w accumulator m base))) =
    some (mapLabelCfg (fun l:UnifiedCleanTail R => Sum.inr l)
      (mapLabelCfg (fun l:UnifiedCleanAfter R => Sum.inr l)
        (mapLabelCfg (fun l:UnifiedCleanFinish R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (phaseReturnCfg zeroWordCoreRenaming
              FullInterpreterState.zeroLens returnLabel
              (zeroWordCfg .done
                ((fixedBits w accumulator).map SparseSymbol.bit) []
                ((fixedBits w 0).reverse.map SparseSymbol.bit))
              (FullInterpreterState.moveLens.put
                (lookupRecordOutcome .missing
                  (FullInterpreterState.lookupLens.put state
                    ⟨none,decide m.isEmpty,none,none⟩)) default)
              (operandBoundaryBase w accumulator m base)))))):=by
  let missingState:=lookupRecordOutcome LookupScanLabel.missing
    (FullInterpreterState.lookupLens.put state
      ⟨none,decide m.isEmpty,none,none⟩)
  have hlookup:=unifiedLookup_missing (R:=UnifiedCleanAfter R)
    w accumulator query hq m hm hmissing
    (unifiedCleanTailProgram returnLabel right) state base
  have hdiscard:=run_lensPhase_to_right
    (discardCoreRenaming .work1) FullInterpreterState.moveLens
    discardProgram .done (by rfl)
    (Sum.inl LookupDecisionLabel.decide)
    (unifiedCleanAfterProgram returnLabel right)
    (discard_correct_from
      (FullInterpreterState.moveLens.get missingState)
      ((fixedBits w query).reverse.map SparseSymbol.bit)) rfl
    missingState (operandBoundaryBase w accumulator m base)
  simp only [List.length_map,List.length_reverse,fixedBits_length] at hdiscard
  rw [discard_decision_bridge (R:=R) missingState
    (operandBoundaryBase w accumulator m base) (by rfl)] at hdiscard
  have houtcome:=lookupDecision_missing_step returnLabel right
    w accumulator m base
    (FullInterpreterState.moveLens.put missingState default) (by rfl)
  have houtcome':
      ((fun o => o.bind (TM2.step
        (unifiedCleanAfterProgram returnLabel right)))^[1])
        (some (cleanDecisionCfg
          (FullInterpreterState.moveLens.put missingState default)
          (operandBoundaryBase w accumulator m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg (Λx:=R) zeroWordCoreRenaming
          FullInterpreterState.zeroLens
          (zeroWordCfgState .fill
            (FullInterpreterState.zeroLens.get
              (FullInterpreterState.moveLens.put missingState default))
            ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
          (FullInterpreterState.moveLens.put missingState default)
          (operandBoundaryBase w accumulator m base))):=by
    simpa using houtcome
  have hzero:=run_lensPhase_to_right zeroWordCoreRenaming
    FullInterpreterState.zeroLens zeroWordProgram .done (by rfl)
    returnLabel right
    (zeroWord_correct_from
      (FullInterpreterState.zeroLens.get
        (FullInterpreterState.moveLens.put missingState default))
      ((fixedBits w accumulator).map SparseSymbol.bit) []) rfl
    (FullInterpreterState.moveLens.put missingState default)
    (operandBoundaryBase w accumulator m base)
  simp only [List.length_map,fixedBits_length,fixedBits_zero,
    List.map_replicate,List.reverse_replicate,List.append_nil] at hzero
  have hafter:=chain_liftRightProgram
    (lookupDecisionProgram returnLabel)
    (unifiedCleanFinishProgram returnLabel right) houtcome' hzero
  have htail:=chain_liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl LookupDecisionLabel.decide))
    (unifiedCleanAfterProgram returnLabel right) hdiscard hafter
  have hchain:=chain_liftRightProgram
    (lensMultiPhaseLeft lookupCoreRenaming FullInterpreterState.lookupLens
      lookupScanProgram lookupExit lookupRecordOutcome)
    (unifiedCleanTailProgram returnLabel right) hlookup htail
  have htime:m.length * (12 * w + 22) + 3 +
      (w + 2 + (1 + (2 * w + 3))) =
      m.length * (12 * w + 22) + 3 * w + 9:=by omega
  rw [htime] at hchain
  simpa [unifiedCleanLookupProgram,missingState] using! hchain

theorem unifiedCleanLookup_missing_clean {N:ℕ} {R:Type}
    (w accumulator query:ℕ) (hq:query < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (hmissing:m.find? query=none)
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ((fun o => o.bind (TM2.step
      (unifiedCleanLookupProgram returnLabel right)))^[
        m.length * (12 * w + 22) + 3 * w + 9])
      (some (lensRenamedCfg lookupCoreRenaming
        FullInterpreterState.lookupLens
        (lookupScanMacroCfg .scan true
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
        state (operandBoundaryBase w accumulator m base))) =
    some (mapLabelCfg (fun l:UnifiedCleanTail R => Sum.inr l)
      (mapLabelCfg (fun l:UnifiedCleanAfter R => Sum.inr l)
        (mapLabelCfg (fun l:UnifiedCleanFinish R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel
              (FullInterpreterState.zeroLens.put
                (FullInterpreterState.moveLens.put
                  (lookupRecordOutcome .missing
                    (FullInterpreterState.lookupLens.put state
                      ⟨none,decide m.isEmpty,none,none⟩)) default) default)
              (operandResultBase w accumulator 0 m base)))))):=by
  have h:=unifiedCleanLookup_missing w accumulator query hq m hm hmissing
    returnLabel right state base
  have hb:=zero_return_bridge returnLabel w accumulator m base
    (FullInterpreterState.moveLens.put
      (lookupRecordOutcome .missing
        (FullInterpreterState.lookupLens.put state
          ⟨none,decide m.isEmpty,none,none⟩)) default)
  have hout:=congrArg (fun c => some
    (mapLabelCfg (fun l:UnifiedCleanTail R =>
        (Sum.inr l:UnifiedCleanLookupLabel R))
      (mapLabelCfg (fun l:UnifiedCleanAfter R => Sum.inr l)
        (mapLabelCfg (fun l:UnifiedCleanFinish R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l) c))))) hb
  exact h.trans hout

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def lookupQueryBase (w accumulator query:ℕ) (m:SparseMemory)
    (base:CoreStack→ List SparseSymbol):CoreStack→ List SparseSymbol:=
  fun
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work1 => (fixedBits w query).reverse.map SparseSymbol.bit
  | .work0 | .work2 | .work3 | .work4
  | .work5 | .work6 | .work7 => []
  | k => base k

theorem queryTransfer_bridge {N:ℕ} {R:Type}
    (w accumulator query:ℕ) (m:SparseMemory)
    (base:CoreStack→ List SparseSymbol)
    (state:FullInterpreterState N):
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl SymbolMoveLabel.loop:QueryTransferTail R)
      (symbolMoveLocalCfg .done []
        ((fixedBits w query).map SparseSymbol.bit))
      state (operandResultBase w accumulator query m base) =
    lensRenamedCfg (Λx:=R)
      (symbolMoveCoreRenaming .work2 .work1 (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((fixedBits w query).map SparseSymbol.bit) [])
      (FullInterpreterState.moveLens.put state default)
      (lookupQueryBase w accumulator query m base):=by
  simp [phaseReturnCfg,lensRenamedCfg,operandResultBase,lookupQueryBase,
    renamedStacks,symbolMoveCoreRenaming,symbolMoveCoreDecode,
    symbolMoveLocalCfg,symbolMoveStacks,List.map_reverse]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks,symbolMoveCoreRenaming,
      symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks,
      operandResultBase,lookupQueryBase,List.map_reverse]

theorem queryTransfer_correct {N:ℕ} {R:Type}
    (w accumulator query:ℕ) (m:SparseMemory)
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ((fun o => o.bind (TM2.step
      (queryTransferProgram returnLabel right)))^[2 * w + 4])
      (some (lensRenamedCfg
        (symbolMoveCoreRenaming .work0 .work2 (by decide))
        FullInterpreterState.moveLens
        (symbolMoveLocalCfgState .loop
          (FullInterpreterState.moveLens.get state)
          ((fixedBits w query).reverse.map SparseSymbol.bit) [])
        state (operandResultBase w accumulator query m base))) =
    some (mapLabelCfg (fun l:QueryTransferTail R => Sum.inr l)
      (mapLabelCfg (fun l:R => Sum.inr l)
        (phaseReturnCfg
          (symbolMoveCoreRenaming .work2 .work1 (by decide))
          FullInterpreterState.moveLens returnLabel
          (symbolMoveLocalCfg .done []
            ((fixedBits w query).reverse.map SparseSymbol.bit))
          (FullInterpreterState.moveLens.put state default)
          (lookupQueryBase w accumulator query m base)))):=by
  have h₁:=run_lensPhase_to_right
    (symbolMoveCoreRenaming .work0 .work2 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop)
    (queryTransferTailProgram returnLabel right)
    (symbolMoveLocal_correct_from
      (FullInterpreterState.moveLens.get state)
      ((fixedBits w query).reverse.map SparseSymbol.bit) []) rfl
    state (operandResultBase w accumulator query m base)
  simp only [List.length_map,List.length_reverse,fixedBits_length,
    List.append_nil,List.map_reverse,List.reverse_reverse] at h₁
  rw [queryTransfer_bridge (R:=R) w accumulator query m base state] at h₁
  have h₂:=run_lensPhase_to_right
    (symbolMoveCoreRenaming .work2 .work1 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    returnLabel right
    (symbolMoveLocal_correct ((fixedBits w query).map SparseSymbol.bit) []) rfl
    (FullInterpreterState.moveLens.put state default)
    (lookupQueryBase w accumulator query m base)
  simp only [List.length_map,fixedBits_length,List.append_nil,
    List.map_reverse] at h₂
  have hchain:=chain_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (queryTransferTailProgram returnLabel right) h₁ h₂
  have htime:w + 2 + (w + 2)=2 * w + 4:=by omega
  rw [htime] at hchain
  simpa [queryTransferProgram] using hchain

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def lookupInitCfg {N:ℕ} {R:Type}
    (state:FullInterpreterState N)
    (tapes:CoreStack→ List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (DirectOperandTail R) (FullInterpreterState N) where
  l:=some (.inl .init)
  var:=state
  stk:=tapes

theorem literalQuery_init_bridge {N:ℕ} {R:Type}
    (n:ℕ) (hn:n≤ N) (w accumulator:ℕ)
    (m:SparseMemory) (base:CoreStack→ List SparseSymbol)
    (state:FullInterpreterState N):
    phaseReturnCfg literalQueryCoreRenaming
      FullInterpreterState.literalLens
      (Sum.inl LookupInitLabel.init:DirectOperandTail R)
      (boundedLiteralWordCfg N .done
        ⟨n / 2 ^ w,by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
        ((fixedBits w accumulator).map SparseSymbol.bit) []
        ((fixedBits w n).reverse.map SparseSymbol.bit))
      state (operandBoundaryBase w accumulator m base) =
    lookupInitCfg (R:=R)
      (FullInterpreterState.literalLens.put state
        ⟨none, ⟨n / 2 ^ w,by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
      (lookupQueryBase w accumulator (n % 2 ^ w) m base):=by
  simp [phaseReturnCfg,lookupInitCfg,lensRenamedCfg,
    literalQueryCoreRenaming,literalQueryCoreDecode,
    boundedLiteralWordCfg,literalWordStacks,
    operandBoundaryBase,lookupQueryBase,renamedStacks,
    fixedBits_mod_word]
  funext k
  cases k <;> simp [renamedStacks,literalQueryCoreRenaming,
    literalQueryCoreDecode,boundedLiteralWordCfg,literalWordStacks,
    operandBoundaryBase,lookupQueryBase,fixedBits_mod_word,
    List.map_reverse]

theorem lookupInit_step {N:ℕ} {R:Type}
    (w accumulator query:ℕ) (m:SparseMemory)
    (base:CoreStack→ List SparseSymbol)
    (state:FullInterpreterState N)
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)):
    TM2.step (directOperandTailProgram returnLabel right)
      (lookupInitCfg (R:=R) state
        (lookupQueryBase w accumulator query m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg lookupCoreRenaming
        FullInterpreterState.lookupLens
        (lookupScanMacroCfg .scan true
          (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
          ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
        state (operandBoundaryBase w accumulator m base))):=by
  simp [directOperandTailProgram,lookupInitProgram,lookupInitCfg,
    liftRightProgram,TM2.step,mapLabelCfg,lensRenamedCfg,
    lookupScanMacroCfg,lookupScanCfg,lookupScanStacks,
    lookupCoreRenaming,lookupCoreDecode,lookupInitialControl,
    lookupQueryBase,operandBoundaryBase,renamedStacks]
  funext k
  cases k <;> simp [lookupQueryBase,operandBoundaryBase,
    renamedStacks,lookupCoreRenaming,lookupCoreDecode,
    lookupScanMacroCfg,lookupScanCfg,lookupScanStacks,
    List.map_reverse]

theorem directOperand_found {N:ℕ} {R:Type}
    (address:ℕ) (haN:address≤ N)
    (w accumulator value:ℕ)
    (m:SparseMemory) (hm:m.Normalized w)
    (hfind:m.find? (address % 2 ^ w)=some value)
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ∃ steps≤ m.length * (12 * w + 22) + 14 * w + 30,
      ((fun o => o.bind (TM2.step
        (directOperandProgram returnLabel right)))^[steps])
        (some (lensRenamedCfg literalQueryCoreRenaming
          FullInterpreterState.literalLens
          (boundedLiteralWordCfg N .emit ⟨address,by omega⟩
            ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
          state (operandBoundaryBase w accumulator m base))) =
      some (mapLabelCfg (fun l:DirectOperandTail R => Sum.inr l)
        (mapLabelCfg (fun l:UnifiedCleanLookupLabel R => Sum.inr l)
          (mapLabelCfg (fun l:UnifiedCleanTail R => Sum.inr l)
            (mapLabelCfg (fun l:UnifiedCleanAfter R => Sum.inr l)
              (mapLabelCfg (fun l:UnifiedCleanFinish R => Sum.inr l)
                (mapLabelCfg (fun l:R => Sum.inr l)
                  (cleanReturnCfg returnLabel
                    (FullInterpreterState.moveLens.put
                      (lookupRecordOutcome .found
                        (FullInterpreterState.lookupLens.put
                          (FullInterpreterState.literalLens.put state
                            ⟨none, ⟨address / 2 ^ w,by
                              exact lt_of_le_of_lt
                                (Nat.div_le_self _ _) (by omega)⟩⟩)
                          ⟨none,true,none,none⟩)) default)
                    (operandResultBase w accumulator value m base)))))))):=by
  let literalState:=FullInterpreterState.literalLens.put state
    ⟨none, ⟨address / 2 ^ w,by
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
  let query:=address % 2 ^ w
  have hquery:query < 2 ^ w:=Nat.mod_lt _ (Nat.two_pow_pos w)
  have hliteral:=run_lensPhase_to_right literalQueryCoreRenaming
    FullInterpreterState.literalLens (boundedLiteralWordProgram N)
    .done (by rfl) (Sum.inl LookupInitLabel.init)
    (directOperandTailProgram returnLabel right)
    (boundedLiteralWord_correct_exact N address haN
      ((fixedBits w accumulator).map SparseSymbol.bit) []) rfl
    state (operandBoundaryBase w accumulator m base)
  simp only [List.length_map,fixedBits_length,List.append_nil] at hliteral
  rw [literalQuery_init_bridge (R:=R) address haN w accumulator m base
    state] at hliteral
  have hinitStep:=lookupInit_step (R:=R) w accumulator query m base
    literalState returnLabel right
  have hinit:
      ((fun o => o.bind (TM2.step
        (directOperandTailProgram returnLabel right)))^[1])
        (some (lookupInitCfg (R:=R) literalState
          (lookupQueryBase w accumulator query m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg lookupCoreRenaming
          FullInterpreterState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          literalState (operandBoundaryBase w accumulator m base))):=by
    simpa using hinitStep
  rcases unifiedCleanLookup_found w accumulator query value hquery m hm hfind
      returnLabel right literalState base with
    ⟨lookupSteps,hbound,hlookup⟩
  have htail:=chain_liftRightProgram lookupInitProgram
    (unifiedCleanLookupProgram returnLabel right) hinit hlookup
  have hchain:=chain_liftRightProgram
    (lensPhaseLeft literalQueryCoreRenaming
      FullInterpreterState.literalLens (boundedLiteralWordProgram N)
      .done (Sum.inl LookupInitLabel.init))
    (directOperandTailProgram returnLabel right) hliteral htail
  refine ⟨2 * w + 3 + (1 + lookupSteps), ?_, ?_⟩
  · omega
  · simpa [directOperandProgram,literalState,query] using hchain

theorem directOperand_missing {N:ℕ} {R:Type}
    (address:ℕ) (haN:address≤ N)
    (w accumulator:ℕ)
    (m:SparseMemory) (hm:m.Normalized w)
    (hmissing:m.find? (address % 2 ^ w)=none)
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ((fun o => o.bind (TM2.step
      (directOperandProgram returnLabel right)))^[
        m.length * (12 * w + 22) + 5 * w + 13])
      (some (lensRenamedCfg literalQueryCoreRenaming
        FullInterpreterState.literalLens
        (boundedLiteralWordCfg N .emit ⟨address,by omega⟩
          ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
        state (operandBoundaryBase w accumulator m base))) =
    some (mapLabelCfg (fun l:DirectOperandTail R => Sum.inr l)
      (mapLabelCfg (fun l:UnifiedCleanLookupLabel R => Sum.inr l)
        (mapLabelCfg (fun l:UnifiedCleanTail R => Sum.inr l)
          (mapLabelCfg (fun l:UnifiedCleanAfter R => Sum.inr l)
            (mapLabelCfg (fun l:UnifiedCleanFinish R => Sum.inr l)
              (mapLabelCfg (fun l:R => Sum.inr l)
                (phaseReturnCfg zeroWordCoreRenaming
                  FullInterpreterState.zeroLens returnLabel
                  (zeroWordCfg .done
                    ((fixedBits w accumulator).map SparseSymbol.bit) []
                    ((fixedBits w 0).reverse.map SparseSymbol.bit))
                  (FullInterpreterState.moveLens.put
                    (lookupRecordOutcome .missing
                      (FullInterpreterState.lookupLens.put
                        (FullInterpreterState.literalLens.put state
                          ⟨none, ⟨address / 2 ^ w,by
                            exact lt_of_le_of_lt
                              (Nat.div_le_self _ _) (by omega)⟩⟩)
                        ⟨none,decide m.isEmpty,none,none⟩)) default)
                  (operandBoundaryBase w accumulator m base)))))))):=by
  let literalState:=FullInterpreterState.literalLens.put state
    ⟨none, ⟨address / 2 ^ w,by
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
  let query:=address % 2 ^ w
  have hquery:query < 2 ^ w:=Nat.mod_lt _ (Nat.two_pow_pos w)
  have hliteral:=run_lensPhase_to_right literalQueryCoreRenaming
    FullInterpreterState.literalLens (boundedLiteralWordProgram N)
    .done (by rfl) (Sum.inl LookupInitLabel.init)
    (directOperandTailProgram returnLabel right)
    (boundedLiteralWord_correct_exact N address haN
      ((fixedBits w accumulator).map SparseSymbol.bit) []) rfl
    state (operandBoundaryBase w accumulator m base)
  simp only [List.length_map,fixedBits_length,List.append_nil] at hliteral
  rw [literalQuery_init_bridge (R:=R) address haN w accumulator m base
    state] at hliteral
  have hinitStep:=lookupInit_step (R:=R) w accumulator query m base
    literalState returnLabel right
  have hinit:
      ((fun o => o.bind (TM2.step
        (directOperandTailProgram returnLabel right)))^[1])
        (some (lookupInitCfg (R:=R) literalState
          (lookupQueryBase w accumulator query m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg lookupCoreRenaming
          FullInterpreterState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          literalState (operandBoundaryBase w accumulator m base))):=by
    simpa using hinitStep
  have hlookup:=unifiedCleanLookup_missing w accumulator query hquery
    m hm hmissing returnLabel right literalState base
  have htail:=chain_liftRightProgram lookupInitProgram
    (unifiedCleanLookupProgram returnLabel right) hinit hlookup
  have hchain:=chain_liftRightProgram
    (lensPhaseLeft literalQueryCoreRenaming
      FullInterpreterState.literalLens (boundedLiteralWordProgram N)
      .done (Sum.inl LookupInitLabel.init))
    (directOperandTailProgram returnLabel right) hliteral htail
  have htime:2 * w + 3 +
      (1 + (m.length * (12 * w + 22) + 3 * w + 9)) =
      m.length * (12 * w + 22) + 5 * w + 13:=by omega
  rw [htime] at hchain
  simpa [directOperandProgram,literalState,query] using hchain

def embedDirectReturnCfg {N:ℕ} {R:Type}
    (c:TM2.Cfg (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (DirectOperandLabel R) (FullInterpreterState N):=
  mapLabelCfg Sum.inr <| mapLabelCfg Sum.inr <|
    mapLabelCfg Sum.inr <| mapLabelCfg Sum.inr <|
      mapLabelCfg Sum.inr <| mapLabelCfg Sum.inr c

theorem transport_iterate_direct_right {N:ℕ} {R:Type}
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    {steps:ℕ}
    {c d:TM2.Cfg (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)}
    (hrun:((fun o => o.bind (TM2.step right))^[steps])
      (some c)=some d):
    ((fun o => o.bind (TM2.step
      (directOperandProgram returnLabel right)))^[steps])
      (some (embedDirectReturnCfg c)) =
    some (embedDirectReturnCfg d):=by
  have h₁:=transport_iterate_liftRightProgram
    (lensPhaseLeft zeroWordCoreRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done returnLabel) right hrun
  have h₂:=transport_iterate_liftRightProgram
    (lookupDecisionProgram returnLabel)
    (unifiedCleanFinishProgram returnLabel right) h₁
  have h₃:=transport_iterate_liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl LookupDecisionLabel.decide))
    (unifiedCleanAfterProgram returnLabel right) h₂
  have h₄:=transport_iterate_liftRightProgram
    (lensMultiPhaseLeft lookupCoreRenaming FullInterpreterState.lookupLens
      lookupScanProgram lookupExit lookupRecordOutcome)
    (unifiedCleanTailProgram returnLabel right) h₃
  have h₅:=transport_iterate_liftRightProgram lookupInitProgram
    (unifiedCleanLookupProgram returnLabel right) h₄
  have h₆:=transport_iterate_liftRightProgram
    (lensPhaseLeft literalQueryCoreRenaming
      FullInterpreterState.literalLens (boundedLiteralWordProgram N)
      .done (Sum.inl LookupInitLabel.init))
    (directOperandTailProgram returnLabel right) h₅
  simpa [directOperandProgram,directOperandTailProgram,
    unifiedCleanLookupProgram,unifiedLookupProgram,
    unifiedCleanTailProgram,unifiedCleanAfterProgram,
    unifiedCleanFinishProgram,embedDirectReturnCfg] using h₆

theorem directOperandTail_found {N:ℕ} {R:Type}
    (w accumulator query value:ℕ) (hq:query < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (hfind:m.find? query=some value)
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ∃ steps≤ m.length * (12 * w + 22) + 12 * w + 27,
      ((fun o => o.bind (TM2.step
        (directOperandTailProgram returnLabel right)))^[steps])
        (some (lookupInitCfg (R:=R) state
          (lookupQueryBase w accumulator query m base))) =
      some (mapLabelCfg (fun l:UnifiedCleanLookupLabel R => Sum.inr l)
        (mapLabelCfg (fun l:UnifiedCleanTail R => Sum.inr l)
          (mapLabelCfg (fun l:UnifiedCleanAfter R => Sum.inr l)
            (mapLabelCfg (fun l:UnifiedCleanFinish R => Sum.inr l)
              (mapLabelCfg (fun l:R => Sum.inr l)
                (cleanReturnCfg returnLabel
                  (FullInterpreterState.moveLens.put
                    (lookupRecordOutcome .found
                      (FullInterpreterState.lookupLens.put state
                        lookupInitialControl)) default)
                  (operandResultBase w accumulator value m base))))))):=by
  have hinitStep:=lookupInit_step (R:=R) w accumulator query m base
    state returnLabel right
  have hinit:
      ((fun o => o.bind (TM2.step
        (directOperandTailProgram returnLabel right)))^[1])
        (some (lookupInitCfg (R:=R) state
          (lookupQueryBase w accumulator query m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg lookupCoreRenaming FullInterpreterState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          state (operandBoundaryBase w accumulator m base))):=by
    simpa using hinitStep
  rcases unifiedCleanLookup_found w accumulator query value hq m hm hfind
      returnLabel right state base with ⟨steps,hbound,hlookup⟩
  have hchain:=chain_liftRightProgram lookupInitProgram
    (unifiedCleanLookupProgram returnLabel right) hinit hlookup
  refine ⟨1 + steps,by omega, ?_⟩
  simpa [directOperandTailProgram,lookupInitialControl] using hchain

theorem directOperandTail_missing {N:ℕ} {R:Type}
    (w accumulator query:ℕ) (hq:query < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (hmissing:m.find? query=none)
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ((fun o => o.bind (TM2.step
      (directOperandTailProgram returnLabel right)))^[
        m.length * (12 * w + 22) + 3 * w + 10])
      (some (lookupInitCfg (R:=R) state
        (lookupQueryBase w accumulator query m base))) =
    some (mapLabelCfg (fun l:UnifiedCleanLookupLabel R => Sum.inr l)
      (mapLabelCfg (fun l:UnifiedCleanTail R => Sum.inr l)
        (mapLabelCfg (fun l:UnifiedCleanAfter R => Sum.inr l)
          (mapLabelCfg (fun l:UnifiedCleanFinish R => Sum.inr l)
            (mapLabelCfg (fun l:R => Sum.inr l)
              (cleanReturnCfg returnLabel
                (FullInterpreterState.zeroLens.put
                  (FullInterpreterState.moveLens.put
                    (lookupRecordOutcome .missing
                      (FullInterpreterState.lookupLens.put state
                        ⟨none,decide m.isEmpty,none,none⟩)) default) default)
                (operandResultBase w accumulator 0 m base))))))):=by
  have hinitStep:=lookupInit_step (R:=R) w accumulator query m base
    state returnLabel right
  have hinit:
      ((fun o => o.bind (TM2.step
        (directOperandTailProgram returnLabel right)))^[1])
        (some (lookupInitCfg (R:=R) state
          (lookupQueryBase w accumulator query m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg lookupCoreRenaming FullInterpreterState.lookupLens
          (lookupScanMacroCfg .scan true
            (encodeSparseMemory w m ++ [.memoryEnd]) [] [] []
            ((fixedBits w query).reverse.map SparseSymbol.bit) [] [] [] [])
          state (operandBoundaryBase w accumulator m base))):=by
    simpa using hinitStep
  have hlookup:=unifiedCleanLookup_missing_clean w accumulator query hq
    m hm hmissing returnLabel right state base
  have hchain:=chain_liftRightProgram lookupInitProgram
    (unifiedCleanLookupProgram returnLabel right) hinit hlookup
  have htime:1 + (m.length * (12 * w + 22) + 3 * w + 9) =
      m.length * (12 * w + 22) + 3 * w + 10:=by omega
  rw [htime] at hchain
  simpa only [directOperandTailProgram,lookupInitialControl] using hchain

theorem directOperand_found_clean {N:ℕ} {R:Type}
    (address:ℕ) (haN:address≤ N)
    (w accumulator value:ℕ)
    (m:SparseMemory) (hm:m.Normalized w)
    (hfind:m.find? (address % 2 ^ w)=some value)
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ∃ steps≤ m.length * (12 * w + 22) + 14 * w + 30,
      ((fun o => o.bind (TM2.step
        (directOperandProgram returnLabel right)))^[steps])
        (some (lensRenamedCfg literalQueryCoreRenaming
          FullInterpreterState.literalLens
          (boundedLiteralWordCfg N .emit ⟨address,by omega⟩
            ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
          state (operandBoundaryBase w accumulator m base))) =
      some (embedDirectReturnCfg
        (cleanReturnCfg returnLabel
          (FullInterpreterState.moveLens.put
            (lookupRecordOutcome .found
              (FullInterpreterState.lookupLens.put
                (FullInterpreterState.literalLens.put state
                  ⟨none, ⟨address / 2 ^ w,by
                    exact lt_of_le_of_lt
                      (Nat.div_le_self _ _) (by omega)⟩⟩)
                ⟨none,true,none,none⟩)) default)
          (operandResultBase w accumulator value m base))):=by
  simpa [embedDirectReturnCfg] using directOperand_found address haN w
    accumulator value m hm hfind returnLabel right state base

theorem directOperand_missing_clean {N:ℕ} {R:Type}
    (address:ℕ) (haN:address≤ N)
    (w accumulator:ℕ)
    (m:SparseMemory) (hm:m.Normalized w)
    (hmissing:m.find? (address % 2 ^ w)=none)
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ((fun o => o.bind (TM2.step
      (directOperandProgram returnLabel right)))^[
        m.length * (12 * w + 22) + 5 * w + 13])
      (some (lensRenamedCfg literalQueryCoreRenaming
        FullInterpreterState.literalLens
        (boundedLiteralWordCfg N .emit ⟨address,by omega⟩
          ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
        state (operandBoundaryBase w accumulator m base))) =
    some (embedDirectReturnCfg
      (cleanReturnCfg returnLabel
        (FullInterpreterState.zeroLens.put
          (FullInterpreterState.moveLens.put
            (lookupRecordOutcome .missing
              (FullInterpreterState.lookupLens.put
                (FullInterpreterState.literalLens.put state
                  ⟨none, ⟨address / 2 ^ w,by
                    exact lt_of_le_of_lt
                      (Nat.div_le_self _ _) (by omega)⟩⟩)
                ⟨none,decide m.isEmpty,none,none⟩)) default) default)
        (operandResultBase w accumulator 0 m base))):=by
  have h:=directOperand_missing address haN w accumulator m hm hmissing
    returnLabel right state base
  have hb:=zero_return_bridge returnLabel w accumulator m base
    (FullInterpreterState.moveLens.put
      (lookupRecordOutcome .missing
        (FullInterpreterState.lookupLens.put
          (FullInterpreterState.literalLens.put state
            ⟨none, ⟨address / 2 ^ w,by
              exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
          ⟨none,decide m.isEmpty,none,none⟩)) default)
  have hout:=congrArg (fun c => some (embedDirectReturnCfg c)) hb
  simpa [embedDirectReturnCfg] using h.trans hout

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def literalOperandStartCfg {N:ℕ} {R:Type}
    (n:ℕ) (hn:n≤ N) (w accumulator:ℕ)
    (m:SparseMemory) (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (Sum LiteralWordLabel R) (FullInterpreterState N):=
  lensRenamedCfg literalWordCoreRenaming FullInterpreterState.literalLens
    (boundedLiteralWordCfg N .emit ⟨n,by omega⟩
      ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
    state (operandBoundaryBase w accumulator m base)

theorem literalOperand_return_bridge {N:ℕ} {R:Type}
    (n:ℕ) (hn:n≤ N) (w accumulator:ℕ)
    (m:SparseMemory) (returnLabel:R)
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    phaseReturnCfg literalWordCoreRenaming FullInterpreterState.literalLens
      returnLabel
      (boundedLiteralWordCfg N .done
        ⟨n / 2 ^ w,by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
        ((fixedBits w accumulator).map SparseSymbol.bit) []
        ((fixedBits w n).reverse.map SparseSymbol.bit))
      state (operandBoundaryBase w accumulator m base) =
    cleanReturnCfg returnLabel
        (FullInterpreterState.literalLens.put state
          ⟨none, ⟨n / 2 ^ w,by
            exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
        (operandResultBase w accumulator (n % 2 ^ w) m base):=by
  simp [phaseReturnCfg,cleanReturnCfg,lensRenamedCfg,
    literalWordCoreRenaming,literalWordCoreDecode,boundedLiteralWordCfg,
    literalWordStacks,operandBoundaryBase,operandResultBase,
    renamedStacks,fixedBits_mod_word]
  funext k
  cases k <;> simp [renamedStacks,literalWordCoreRenaming,
    literalWordCoreDecode,boundedLiteralWordCfg,literalWordStacks,
    operandBoundaryBase,operandResultBase,fixedBits_mod_word,
    List.map_reverse]

theorem literalOperand_correct {N:ℕ} {R:Type}
    (n:ℕ) (hn:n≤ N) (w accumulator:ℕ)
    (m:SparseMemory) (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ((fun o => o.bind (TM2.step
      (literalOperandProgram returnLabel right)))^[2 * w + 3])
      (some (literalOperandStartCfg (R:=R) n hn w accumulator m state base)) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel
        (FullInterpreterState.literalLens.put state
          ⟨none, ⟨n / 2 ^ w,by
            exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
        (operandResultBase w accumulator (operandWordValue w (.lit n) m)
          m base))):=by
  have h:=run_lensPhase_to_right literalWordCoreRenaming
    FullInterpreterState.literalLens (boundedLiteralWordProgram N)
    .done (by rfl) returnLabel right
    (boundedLiteralWord_correct_exact N n hn
      ((fixedBits w accumulator).map SparseSymbol.bit) []) rfl
    state (operandBoundaryBase w accumulator m base)
  simp only [List.length_map,fixedBits_length,List.append_nil] at h
  rw [literalOperand_return_bridge n hn w accumulator m returnLabel state base]
    at h
  simpa [literalOperandProgram,literalOperandStartCfg,operandWordValue] using! h

theorem transport_iterate_literal_right {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    {steps:Nat}
    {c d:TM2.Cfg (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)}
    (hrun:((fun o => o.bind (TM2.step right))^[steps])
      (some c)=some d):
    ((fun o => o.bind (TM2.step
      (literalOperandProgram returnLabel right)))^[steps])
      (some (mapLabelCfg Sum.inr c)) =
    some (mapLabelCfg Sum.inr d):=by
  exact transport_iterate_liftRightProgram
    (lensPhaseLeft literalWordCoreRenaming FullInterpreterState.literalLens
      (boundedLiteralWordProgram N) .done returnLabel)
    right hrun

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem closedAddPipelineProgram_done:
    closedAddPipelineProgram closedAddDone=.halt:=rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

theorem cleanReturn_queryTransfer_bridge {N:ℕ} {R:Type}
    (w accumulator query:ℕ) (m:SparseMemory)
    (base:CoreStack→ List SparseSymbol)
    (state:FullInterpreterState N):
    cleanReturnCfg (Sum.inl SymbolMoveLabel.loop:QueryTransferLabel R)
      state (operandResultBase w accumulator query m base) =
    lensRenamedCfg
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfgState .loop
        (FullInterpreterState.moveLens.get state)
        ((fixedBits w query).reverse.map SparseSymbol.bit) [])
      state (operandResultBase w accumulator query m base):=by
  simp [cleanReturnCfg,lensRenamedCfg,symbolMoveLocalCfgState,
    symbolMoveStacks,symbolMoveCoreRenaming,symbolMoveCoreDecode,
    operandResultBase,renamedStacks]
  constructor
  · rw [FullInterpreterState.moveLens.put_get]
  · funext k
    cases k <;> simp [renamedStacks,symbolMoveCoreRenaming,
      symbolMoveCoreDecode,symbolMoveLocalCfgState,symbolMoveStacks,
      operandResultBase,List.map_reverse]

theorem queryTransfer_init_bridge {N:ℕ} {R:Type}
    (w accumulator query:ℕ) (m:SparseMemory)
    (base:CoreStack→ List SparseSymbol)
    (state:FullInterpreterState N):
    phaseReturnCfg
      (symbolMoveCoreRenaming .work2 .work1 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl LookupInitLabel.init:DirectOperandTail R)
      (symbolMoveLocalCfg .done []
        ((fixedBits w query).reverse.map SparseSymbol.bit))
      state (lookupQueryBase w accumulator query m base) =
    lookupInitCfg (R:=R)
      (FullInterpreterState.moveLens.put state default)
      (lookupQueryBase w accumulator query m base):=by
  simp [phaseReturnCfg,lookupInitCfg,lensRenamedCfg,
    symbolMoveCoreRenaming,symbolMoveCoreDecode,
    symbolMoveLocalCfg,symbolMoveStacks,lookupQueryBase,
    renamedStacks,List.map_reverse]
  funext k
  cases k <;> simp [renamedStacks,symbolMoveCoreRenaming,
    symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks,
    lookupQueryBase,List.map_reverse]

theorem transport_iterate_indirectTransfer_right {N:ℕ} {R:Type}
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    {steps:ℕ}
    {c d:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (DirectOperandTail R) (FullInterpreterState N)}
    (hrun:((fun o => o.bind (TM2.step
      (directOperandTailProgram returnLabel right)))^[steps])
      (some c)=some d):
    ((fun o => o.bind (TM2.step
      (indirectTransferProgram returnLabel right)))^[steps])
      (some (mapLabelCfg Sum.inr (mapLabelCfg Sum.inr c))) =
    some (mapLabelCfg Sum.inr (mapLabelCfg Sum.inr d)):=by
  have h₁:=transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work2 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl LookupInitLabel.init))
    (directOperandTailProgram returnLabel right) hrun
  have h₂:=transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (queryTransferTailProgram (Sum.inl LookupInitLabel.init)
      (directOperandTailProgram returnLabel right)) h₁
  simpa [indirectTransferProgram,queryTransferProgram] using h₂

def embedDirectTailReturnCfg {N:ℕ} {R:Type}
    (c:TM2.Cfg (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (DirectOperandTail R) (FullInterpreterState N):=
  mapLabelCfg Sum.inr <| mapLabelCfg Sum.inr <|
    mapLabelCfg Sum.inr <| mapLabelCfg Sum.inr <|
      mapLabelCfg Sum.inr c

def embedIndirectTransferReturnCfg {N:ℕ} {R:Type}
    (c:TM2.Cfg (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (IndirectTransferLabel R) (FullInterpreterState N):=
  mapLabelCfg Sum.inr <| mapLabelCfg Sum.inr <|
    embedDirectTailReturnCfg c

def embedIndirectReturnCfg {N:ℕ} {R:Type}
    (c:TM2.Cfg (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (IndirectOperandLabel R) (FullInterpreterState N):=
  embedDirectReturnCfg (embedIndirectTransferReturnCfg c)

theorem transport_iterate_directTail_right {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    {steps:Nat}
    {c d:TM2.Cfg (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)}
    (hrun:((fun o => o.bind (TM2.step right))^[steps])
      (some c)=some d):
    ((fun o => o.bind (TM2.step
      (directOperandTailProgram returnLabel right)))^[steps])
      (some (embedDirectTailReturnCfg c)) =
    some (embedDirectTailReturnCfg d):=by
  have h1:=transport_iterate_liftRightProgram
    (lensPhaseLeft zeroWordCoreRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done returnLabel) right hrun
  have h2:=transport_iterate_liftRightProgram
    (lookupDecisionProgram returnLabel)
    (unifiedCleanFinishProgram returnLabel right) h1
  have h3:=transport_iterate_liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl LookupDecisionLabel.decide))
    (unifiedCleanAfterProgram returnLabel right) h2
  have h4:=transport_iterate_liftRightProgram
    (lensMultiPhaseLeft lookupCoreRenaming FullInterpreterState.lookupLens
      lookupScanProgram lookupExit lookupRecordOutcome)
    (unifiedCleanTailProgram returnLabel right) h3
  have h5:=transport_iterate_liftRightProgram lookupInitProgram
    (unifiedCleanLookupProgram returnLabel right) h4
  simpa [directOperandTailProgram,unifiedCleanLookupProgram,
    unifiedLookupProgram,unifiedCleanTailProgram,unifiedCleanAfterProgram,
    unifiedCleanFinishProgram,embedDirectTailReturnCfg] using h5

theorem transport_iterate_indirect_right {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    {steps:Nat}
    {c d:TM2.Cfg (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)}
    (hrun:((fun o => o.bind (TM2.step right))^[steps])
      (some c)=some d):
    ((fun o => o.bind (TM2.step
      (indirectOperandProgram returnLabel right)))^[steps])
      (some (embedIndirectReturnCfg c)) =
    some (embedIndirectReturnCfg d):=by
  have htail:=transport_iterate_directTail_right returnLabel right hrun
  have htransfer:=transport_iterate_indirectTransfer_right
    returnLabel right htail
  have hall:=transport_iterate_direct_right
    (Sum.inl SymbolMoveLabel.loop:IndirectTransferLabel R)
    (indirectTransferProgram returnLabel right) htransfer
  simpa [embedIndirectReturnCfg,embedIndirectTransferReturnCfg] using! hall

private theorem chain_iterations_2cf6f9f7 {X:Type} (step:X→ X)
    {a b c:X} {m n:ℕ}
    (h₁:(step^[m]) a=b) (h₂:(step^[n]) b=c):
    (step^[m + n]) a=c:=by
  rw [Nat.add_comm,Function.iterate_add_apply,h₁,h₂]

theorem indirectContinue_found {N:ℕ} {R:Type}
    (w accumulator pointer value:ℕ) (hp:pointer < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (hfind:m.find? pointer=some value)
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ∃ steps≤ m.length * (12 * w + 22) + 14 * w + 31,
      ((fun o => o.bind (TM2.step
        (indirectTransferProgram returnLabel right)))^[steps])
        (some (cleanReturnCfg
          (Sum.inl SymbolMoveLabel.loop:IndirectTransferLabel R)
          state (operandResultBase w accumulator pointer m base))) =
      some (embedIndirectTransferReturnCfg
        (cleanReturnCfg returnLabel
          (FullInterpreterState.moveLens.put
            (lookupRecordOutcome .found
              (FullInterpreterState.lookupLens.put
                (FullInterpreterState.moveLens.put state default)
                lookupInitialControl)) default)
          (operandResultBase w accumulator value m base))):=by
  have htransfer:=queryTransfer_correct (R:=DirectOperandTail R)
    w accumulator pointer m (Sum.inl LookupInitLabel.init)
    (directOperandTailProgram returnLabel right) state base
  have hb:=queryTransfer_init_bridge (R:=R) w accumulator pointer m base
    state
  have hb':=congrArg (fun c => some
    (mapLabelCfg (fun l:QueryTransferTail (DirectOperandTail R) =>
        (Sum.inr l:IndirectTransferLabel R))
      (mapLabelCfg (fun l:DirectOperandTail R => Sum.inr l) c))) hb
  have htransfer':=htransfer.trans hb'
  have htransfer'':
      ((fun o => o.bind (TM2.step
        (indirectTransferProgram returnLabel right)))^[2 * w + 4])
        (some (cleanReturnCfg
          (Sum.inl SymbolMoveLabel.loop:IndirectTransferLabel R)
          state (operandResultBase w accumulator pointer m base))) =
      some (mapLabelCfg Sum.inr (mapLabelCfg Sum.inr
        (lookupInitCfg (R:=R)
          (FullInterpreterState.moveLens.put state default)
          (lookupQueryBase w accumulator pointer m base)))):=by
    rw [cleanReturn_queryTransfer_bridge (R:=DirectOperandTail R)
      w accumulator pointer m base state]
    exact htransfer'
  rcases directOperandTail_found w accumulator pointer value hp m hm hfind
      returnLabel right (FullInterpreterState.moveLens.put state default) base with
    ⟨lookupSteps,hbound,hlookup⟩
  have hlift:=transport_iterate_indirectTransfer_right returnLabel right hlookup
  have hchain:=chain_iterations_2cf6f9f7
    (fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (IndirectTransferLabel R) (FullInterpreterState N)) =>
      o.bind (TM2.step (indirectTransferProgram returnLabel right)))
    htransfer'' hlift
  refine ⟨2 * w + 4 + lookupSteps,by omega, ?_⟩
  simpa [embedIndirectTransferReturnCfg,embedDirectTailReturnCfg,
    lookupInitialControl] using hchain

theorem indirectContinue_missing {N:ℕ} {R:Type}
    (w accumulator pointer:ℕ) (hp:pointer < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (hmissing:m.find? pointer=none)
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ((fun o => o.bind (TM2.step
      (indirectTransferProgram returnLabel right)))^[
        m.length * (12 * w + 22) + 5 * w + 14])
      (some (cleanReturnCfg
        (Sum.inl SymbolMoveLabel.loop:IndirectTransferLabel R)
        state (operandResultBase w accumulator pointer m base))) =
    some (embedIndirectTransferReturnCfg
      (cleanReturnCfg returnLabel
        (FullInterpreterState.zeroLens.put
          (FullInterpreterState.moveLens.put
            (lookupRecordOutcome .missing
              (FullInterpreterState.lookupLens.put
                (FullInterpreterState.moveLens.put state default)
                ⟨none,decide m.isEmpty,none,none⟩)) default) default)
        (operandResultBase w accumulator 0 m base))):=by
  have htransfer:=queryTransfer_correct (R:=DirectOperandTail R)
    w accumulator pointer m (Sum.inl LookupInitLabel.init)
    (directOperandTailProgram returnLabel right) state base
  have hb:=queryTransfer_init_bridge (R:=R) w accumulator pointer m base
    state
  have hb':=congrArg (fun c => some
    (mapLabelCfg (fun l:QueryTransferTail (DirectOperandTail R) =>
        (Sum.inr l:IndirectTransferLabel R))
      (mapLabelCfg (fun l:DirectOperandTail R => Sum.inr l) c))) hb
  have htransfer':=htransfer.trans hb'
  have htransfer'':
      ((fun o => o.bind (TM2.step
        (indirectTransferProgram returnLabel right)))^[2 * w + 4])
        (some (cleanReturnCfg
          (Sum.inl SymbolMoveLabel.loop:IndirectTransferLabel R)
          state (operandResultBase w accumulator pointer m base))) =
      some (mapLabelCfg Sum.inr (mapLabelCfg Sum.inr
        (lookupInitCfg (R:=R)
          (FullInterpreterState.moveLens.put state default)
          (lookupQueryBase w accumulator pointer m base)))):=by
    rw [cleanReturn_queryTransfer_bridge (R:=DirectOperandTail R)
      w accumulator pointer m base state]
    exact htransfer'
  have hlookup:=directOperandTail_missing w accumulator pointer hp m hm hmissing
    returnLabel right (FullInterpreterState.moveLens.put state default) base
  have hlift:=transport_iterate_indirectTransfer_right returnLabel right hlookup
  have hchain:=chain_iterations_2cf6f9f7
    (fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (IndirectTransferLabel R) (FullInterpreterState N)) =>
      o.bind (TM2.step (indirectTransferProgram returnLabel right)))
    htransfer'' hlift
  have htime:2 * w + 4 +
      (m.length * (12 * w + 22) + 3 * w + 10) =
      m.length * (12 * w + 22) + 5 * w + 14:=by omega
  rw [htime] at hchain
  simpa [embedIndirectTransferReturnCfg,embedDirectTailReturnCfg] using hchain

theorem indirectOperand_correct {N:ℕ} {R:Type}
    (address:ℕ) (haN:address≤ N)
    (w accumulator:ℕ) (m:SparseMemory) (hm:m.Normalized w)
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack→ List SparseSymbol):
    ∃ steps≤ 2 * (m.length * (12 * w + 22)) + 28 * w + 61,
      ∃ finalState:FullInterpreterState N,
      ((fun o => o.bind (TM2.step
        (indirectOperandProgram returnLabel right)))^[steps])
        (some (lensRenamedCfg literalQueryCoreRenaming
          FullInterpreterState.literalLens
          (boundedLiteralWordCfg N .emit ⟨address,by omega⟩
            ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
          state (operandBoundaryBase w accumulator m base))) =
      some (embedIndirectReturnCfg
        (cleanReturnCfg returnLabel finalState
          (operandResultBase w accumulator
            (m.read (m.read (address % 2 ^ w))) m base))):=by
  let query:=address % 2 ^ w
  have hquery:query < 2 ^ w:=Nat.mod_lt _ (Nat.two_pow_pos w)
  cases hfirst:m.find? query with
  | none =>
      have hreadFirst:m.read query=0:=by
        have h:=SparseMemory.find?_getD m query
        rw [hfirst] at h
        exact h.symm
      let state₁:=FullInterpreterState.zeroLens.put
        (FullInterpreterState.moveLens.put
          (lookupRecordOutcome LookupScanLabel.missing
            (FullInterpreterState.lookupLens.put
              (FullInterpreterState.literalLens.put state
                ⟨none, ⟨address / 2 ^ w,by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
              ⟨none,decide m.isEmpty,none,none⟩)) default) default
      have hrunFirst:=directOperand_missing_clean
        (R:=IndirectTransferLabel R) address haN w accumulator m hm hfirst
        (Sum.inl SymbolMoveLabel.loop)
        (indirectTransferProgram returnLabel right) state base
      cases hsecond:m.find? 0 with
      | none =>
          have hreadSecond:m.read 0=0:=by
            have h:=SparseMemory.find?_getD m 0
            rw [hsecond] at h
            exact h.symm
          have hcont:=indirectContinue_missing w accumulator 0
            (Nat.two_pow_pos w) m hm hsecond returnLabel right state₁ base
          have hlift:=transport_iterate_direct_right
            (Sum.inl SymbolMoveLabel.loop:IndirectTransferLabel R)
            (indirectTransferProgram returnLabel right) hcont
          have hchain:=chain_iterations_2cf6f9f7
            (fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
                (IndirectOperandLabel R) (FullInterpreterState N)) =>
              o.bind (TM2.step (indirectOperandProgram returnLabel right)))
            hrunFirst hlift
          let finalState:=FullInterpreterState.zeroLens.put
            (FullInterpreterState.moveLens.put
              (lookupRecordOutcome LookupScanLabel.missing
                (FullInterpreterState.lookupLens.put
                  (FullInterpreterState.moveLens.put state₁ default)
                  ⟨none,decide m.isEmpty,none,none⟩)) default) default
          refine ⟨m.length * (12 * w + 22) + 5 * w + 13 +
              (m.length * (12 * w + 22) + 5 * w + 14),by omega,
            finalState, ?_⟩
          simpa [indirectOperandProgram,embedIndirectReturnCfg,
            hreadFirst,hreadSecond,query,state₁,finalState] using hchain
      | some value =>
          have hreadSecond:m.read 0=value:=by
            have h:=SparseMemory.find?_getD m 0
            rw [hsecond] at h
            exact h.symm
          have hcont:=indirectContinue_found w accumulator 0 value
            (Nat.two_pow_pos w) m hm hsecond returnLabel right state₁ base
          rcases hcont with ⟨contSteps,hcontBound,hcontRun⟩
          have hlift:=transport_iterate_direct_right
            (Sum.inl SymbolMoveLabel.loop:IndirectTransferLabel R)
            (indirectTransferProgram returnLabel right) hcontRun
          have hchain:=chain_iterations_2cf6f9f7
            (fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
                (IndirectOperandLabel R) (FullInterpreterState N)) =>
              o.bind (TM2.step (indirectOperandProgram returnLabel right)))
            hrunFirst hlift
          let finalState:=FullInterpreterState.moveLens.put
            (lookupRecordOutcome LookupScanLabel.found
              (FullInterpreterState.lookupLens.put
                (FullInterpreterState.moveLens.put state₁ default)
                lookupInitialControl)) default
          refine ⟨m.length * (12 * w + 22) + 5 * w + 13 + contSteps,
            by omega,finalState, ?_⟩
          simpa [indirectOperandProgram,embedIndirectReturnCfg,
            hreadFirst,hreadSecond,query,state₁,finalState,
            lookupInitialControl] using hchain
  | some pointer =>
      have hreadFirst:m.read query=pointer:=by
        have h:=SparseMemory.find?_getD m query
        rw [hfirst] at h
        exact h.symm
      have hp:pointer < 2 ^ w:=by
        rw [← hreadFirst]
        exact SparseMemory.read_lt_of_normalized hm query
      let state₁:=FullInterpreterState.moveLens.put
        (lookupRecordOutcome LookupScanLabel.found
          (FullInterpreterState.lookupLens.put
            (FullInterpreterState.literalLens.put state
              ⟨none, ⟨address / 2 ^ w,by
                exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
            lookupInitialControl)) default
      rcases directOperand_found_clean
          (R:=IndirectTransferLabel R) address haN w accumulator pointer m hm
          hfirst (Sum.inl SymbolMoveLabel.loop)
          (indirectTransferProgram returnLabel right) state base with
        ⟨firstSteps,hfirstBound,hrunFirst⟩
      cases hsecond:m.find? pointer with
      | none =>
          have hreadSecond:m.read pointer=0:=by
            have h:=SparseMemory.find?_getD m pointer
            rw [hsecond] at h
            exact h.symm
          have hcont:=indirectContinue_missing w accumulator pointer hp
            m hm hsecond returnLabel right state₁ base
          have hlift:=transport_iterate_direct_right
            (Sum.inl SymbolMoveLabel.loop:IndirectTransferLabel R)
            (indirectTransferProgram returnLabel right) hcont
          have hchain:=chain_iterations_2cf6f9f7
            (fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
                (IndirectOperandLabel R) (FullInterpreterState N)) =>
              o.bind (TM2.step (indirectOperandProgram returnLabel right)))
            hrunFirst hlift
          let finalState:=FullInterpreterState.zeroLens.put
            (FullInterpreterState.moveLens.put
              (lookupRecordOutcome LookupScanLabel.missing
                (FullInterpreterState.lookupLens.put
                  (FullInterpreterState.moveLens.put state₁ default)
                  ⟨none,decide m.isEmpty,none,none⟩)) default) default
          refine ⟨firstSteps +
              (m.length * (12 * w + 22) + 5 * w + 14),by omega,
            finalState, ?_⟩
          simpa [indirectOperandProgram,embedIndirectReturnCfg,
            hreadFirst,hreadSecond,query,state₁,finalState,
            lookupInitialControl] using hchain
      | some value =>
          have hreadSecond:m.read pointer=value:=by
            have h:=SparseMemory.find?_getD m pointer
            rw [hsecond] at h
            exact h.symm
          rcases indirectContinue_found w accumulator pointer value hp
              m hm hsecond returnLabel right state₁ base with
            ⟨contSteps,hcontBound,hcontRun⟩
          have hlift:=transport_iterate_direct_right
            (Sum.inl SymbolMoveLabel.loop:IndirectTransferLabel R)
            (indirectTransferProgram returnLabel right) hcontRun
          have hchain:=chain_iterations_2cf6f9f7
            (fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
                (IndirectOperandLabel R) (FullInterpreterState N)) =>
              o.bind (TM2.step (indirectOperandProgram returnLabel right)))
            hrunFirst hlift
          let finalState:=FullInterpreterState.moveLens.put
            (lookupRecordOutcome LookupScanLabel.found
              (FullInterpreterState.lookupLens.put
                (FullInterpreterState.moveLens.put state₁ default)
                lookupInitialControl)) default
          refine ⟨firstSteps + contSteps,by omega,finalState, ?_⟩
          simpa [indirectOperandProgram,embedIndirectReturnCfg,
            hreadFirst,hreadSecond,query,state₁,finalState,
            lookupInitialControl] using hchain

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

def operandEvalStartCfg {N:Nat} {R:Type} (o:Op)
    (hN:operandArgument o <= N) (w accumulator:Nat)
    (m:SparseMemory) (state:FullInterpreterState N)
    (base:CoreStack -> List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (OperandEvalLabel o R) (FullInterpreterState N):=
  match o with
  | .lit n => literalOperandStartCfg n (by simpa [operandArgument] using hN)
      w accumulator m state base
  | .mem a => lensRenamedCfg literalQueryCoreRenaming
      FullInterpreterState.literalLens
      (boundedLiteralWordCfg N .emit
        ⟨a,by simpa [operandArgument] using hN⟩
        ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
      state (operandBoundaryBase w accumulator m base)
  | .ind a => lensRenamedCfg literalQueryCoreRenaming
      FullInterpreterState.literalLens
      (boundedLiteralWordCfg N .emit
        ⟨a,by simpa [operandArgument] using hN⟩
        ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
      state (operandBoundaryBase w accumulator m base)

def embedOperandReturnCfg {N:Nat} {R:Type} (o:Op)
    (c:TM2.Cfg (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (OperandEvalLabel o R) (FullInterpreterState N):=
  match o with
  | .lit _ => mapLabelCfg Sum.inr c
  | .mem _ => embedDirectReturnCfg c
  | .ind _ => embedIndirectReturnCfg c

theorem directOperand_correct_uniform {N:Nat} {R:Type}
    (address:Nat) (haN:address <= N)
    (w accumulator:Nat) (m:SparseMemory) (hm:m.Normalized w)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack -> List SparseSymbol):
    ∃ steps,steps <= operandEvalBound w m∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (directOperandProgram returnLabel right)))^[steps])
        (some (operandEvalStartCfg (R:=R) (.mem address) haN
          w accumulator m state base)) =
      some (embedDirectReturnCfg
        (cleanReturnCfg returnLabel finalState
          (operandResultBase w accumulator
            (operandWordValue w (.mem address) m) m base))):=by
  cases hfind:m.find? (address % 2 ^ w) with
  | none =>
      have hread:m.read (address % 2 ^ w)=0:=by
        have h:=SparseMemory.find?_getD m (address % 2 ^ w)
        rw [hfind] at h
        exact h.symm
      let finalState:=FullInterpreterState.zeroLens.put
        (FullInterpreterState.moveLens.put
          (lookupRecordOutcome .missing
            (FullInterpreterState.lookupLens.put
              (FullInterpreterState.literalLens.put state
                ⟨none, ⟨address / 2 ^ w,by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
              ⟨none,decide m.isEmpty,none,none⟩)) default) default
      refine ⟨m.length * (12 * w + 22) + 5 * w + 13,by
        simp [operandEvalBound]
        omega,finalState, ?_⟩
      simpa [operandEvalStartCfg,operandArgument,operandWordValue,
        sparseValue,Op.value,hread,finalState] using!
        directOperand_missing_clean address haN w accumulator m hm hfind
          returnLabel right state base
  | some value =>
      have hread:m.read (address % 2 ^ w)=value:=by
        have h:=SparseMemory.find?_getD m (address % 2 ^ w)
        rw [hfind] at h
        exact h.symm
      have hvalue:value < 2 ^ w:=by
        rw [← hread]
        exact SparseMemory.read_lt_of_normalized hm _
      rcases directOperand_found_clean address haN w accumulator value m hm
        hfind returnLabel right state base with ⟨steps,hsteps,hrun⟩
      let finalState:=FullInterpreterState.moveLens.put
        (lookupRecordOutcome .found
          (FullInterpreterState.lookupLens.put
            (FullInterpreterState.literalLens.put state
              ⟨none, ⟨address / 2 ^ w,by
                exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩)
            ⟨none,true,none,none⟩)) default
      refine ⟨steps, ?_,finalState, ?_⟩
      · simp [operandEvalBound]
        omega
      · simpa [operandEvalStartCfg,operandArgument,operandWordValue,
          sparseValue,Op.value,hread,
          Nat.mod_eq_of_lt hvalue,finalState]
          using! hrun

theorem operandEval_correct {N:Nat} {R:Type}
    (o:Op) (hN:operandArgument o <= N)
    (w accumulator:Nat) (m:SparseMemory) (hm:m.Normalized w)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N)
    (base:CoreStack -> List SparseSymbol):
    ∃ steps,steps <= operandEvalBound w m∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (operandEvalProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg (R:=R) o hN
          w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (cleanReturnCfg returnLabel finalState
          (operandResultBase w accumulator (operandWordValue w o m) m base))):=by
  cases o with
  | lit n =>
      change n <= N at hN
      let finalState:=FullInterpreterState.literalLens.put state
        ⟨none, ⟨n / 2 ^ w,by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
      refine ⟨2 * w + 3,by simp [operandEvalBound]; omega,
        finalState, ?_⟩
      simpa [operandEvalProgram,operandEvalStartCfg,operandArgument,
        embedOperandReturnCfg] using!
        literalOperand_correct n hN
          w accumulator m returnLabel right state base
  | mem a =>
      change a <= N at hN
      simpa [operandEvalProgram,embedOperandReturnCfg] using!
        directOperand_correct_uniform a hN w accumulator m hm
          returnLabel right state base
  | ind a =>
      change a <= N at hN
      have hp:m.read (a % 2 ^ w) < 2 ^ w:=
        SparseMemory.read_lt_of_normalized hm _
      have hv:m.read (m.read (a % 2 ^ w)) < 2 ^ w:=
        SparseMemory.read_lt_of_normalized hm _
      simpa [operandEvalProgram,operandEvalStartCfg,operandArgument,
        embedOperandReturnCfg,operandEvalBound,operandWordValue,
        sparseValue,Op.value,Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt hv] using!
        indirectOperand_correct a hN w accumulator m hm returnLabel right
          state base

theorem transport_iterate_operand_right {N:Nat} {R:Type}
    (o:Op) (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    {steps:Nat}
    {c d:TM2.Cfg (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)}
    (hrun:((fun x => x.bind (TM2.step right))^[steps])
      (some c)=some d):
    ((fun x => x.bind (TM2.step
      (operandEvalProgram o returnLabel right)))^[steps])
      (some (embedOperandReturnCfg o c)) =
    some (embedOperandReturnCfg o d):=by
  cases o with
  | lit n =>
      simpa [operandEvalProgram,embedOperandReturnCfg] using!
        transport_iterate_literal_right returnLabel right hrun
  | mem a =>
      simpa [operandEvalProgram,embedOperandReturnCfg] using!
        transport_iterate_direct_right returnLabel right hrun
  | ind a =>
      simpa [operandEvalProgram,embedOperandReturnCfg] using!
        transport_iterate_indirect_right returnLabel right hrun

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem closedAccInstallProgram_done:
    closedAccInstallProgram closedAccInstallDone=.halt:=rfl

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

theorem chain_loadInstruction_iterations {X:Type} (step:X -> X)
    {a b c:X} {m n:Nat}
    (h1:(step^[m]) a=b) (h2:(step^[n]) b=c):
    (step^[m + n]) a=c:=by
  rw [Nat.add_comm,Function.iterate_add_apply,h1,h2]

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem closedZipProgram_done (f:Bool -> Bool -> Bool):
    closedZipProgram f closedZipDone=.halt:=rfl

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

attribute [local instance] Lax759944Proofs.RamToTM.instDecidableEqClosedMulLabel

@[simp] theorem closedMulProgram_done:
    closedMulProgram closedMulDone=.halt:=rfl

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

def readTransferStacks (input value:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol
  | .input => input
  | .work1 => value
  | k => base k

def readTransferCfg {N:Nat} {R:Type} (state:FullInterpreterState N)
    (input value:List SparseSymbol) (base:CoreStack -> List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol) (ReadTailLabel R)
      (FullInterpreterState N):=
  ⟨some (Sum.inl .loop),state,readTransferStacks input value base⟩

theorem readTransfer_initialize {N:Nat} {R:Type}
    (exhaustedLabel returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator address:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    TM2.step (readTransferProgram exhaustedLabel returnLabel right)
      (cleanReturnCfg (Sum.inl ReadTransferLabel.initializeState) state
        (operandResultBase w accumulator address m base)) =
    some (readTransferCfg (FullInterpreterState.moveLens.put state default)
      (base .input) [] (operandResultBase w accumulator address m base)):=by
  simp [readTransferProgram,cleanReturnCfg,readTransferCfg,
    readTransferLeftProgram,readTransferStacks,operandResultBase,
    liftRightProgram,TM2.step]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem readTransfer_step_exhausted {N:Nat} {R:Type}
    (exhaustedLabel returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N) (value:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol):
    TM2.step (readTransferProgram exhaustedLabel returnLabel right)
      (readTransferCfg state [.inputEnd] value base) =
    some ⟨some (Sum.inr (Sum.inr exhaustedLabel)),
      FullInterpreterState.moveLens.put state default,
      readTransferStacks [] value base⟩:=by
  simp [readTransferProgram,readTransferCfg,readTransferStacks,
    readTransferLeftProgram,liftRightProgram,TM2.step,Function.update,
    FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  congr 2
  funext k
  cases k <;> rfl

theorem readInstruction_exhausted {N:Nat} {R:Type}
    (address:Nat) (hN:address <= N)
    (exhaustedLabel returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator:Nat) (m:SparseMemory) (hm:m.Normalized w)
    (base:CoreStack -> List SparseSymbol)
    (hinput:base .input=[.inputEnd])
    (state:FullInterpreterState N):
    ∃ steps,steps <= operandEvalBound w m + 2∧ ∃ finalState,
      ((fun o => o.bind (TM2.step
        (readInstructionProgram address exhaustedLabel returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=ReadTailLabel R) (.lit address) hN
          w accumulator m state base)) =
      some (embedOperandReturnCfg (.lit address)
        ⟨some (Sum.inr (Sum.inr exhaustedLabel)),finalState,
          readTransferStacks [] []
            (operandResultBase w accumulator
              (operandWordValue w (.lit address) m) m base)⟩):=by
  rcases operandEval_correct (.lit address) hN w accumulator m hm
      (Sum.inl ReadTransferLabel.initializeState)
      (readTransferProgram exhaustedLabel returnLabel right) state base with
    ⟨operandSteps,hoperandSteps,operandState,hoperand⟩
  have hinit:=readTransfer_initialize exhaustedLabel returnLabel right
    w accumulator (operandWordValue w (.lit address) m) m base operandState
  have hexhaust:=readTransfer_step_exhausted exhaustedLabel returnLabel right
    (FullInterpreterState.moveLens.put operandState default) []
    (operandResultBase w accumulator
      (operandWordValue w (.lit address) m) m base)
  simp only [hinput] at hinit
  have hinit':
      ((fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (ReadTailLabel R) (FullInterpreterState N)) =>
          o.bind (TM2.step
            (readTransferProgram exhaustedLabel returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl ReadTransferLabel.initializeState)
          operandState (operandResultBase w accumulator
            (operandWordValue w (.lit address) m) m base))) =
      some (readTransferCfg
        (FullInterpreterState.moveLens.put operandState default)
        [.inputEnd] [] (operandResultBase w accumulator
          (operandWordValue w (.lit address) m) m base)):=by
    simpa using hinit
  have hexhaust':
      ((fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (ReadTailLabel R) (FullInterpreterState N)) =>
          o.bind (TM2.step
            (readTransferProgram exhaustedLabel returnLabel right)))^[1])
        (some (readTransferCfg
          (FullInterpreterState.moveLens.put operandState default)
          [.inputEnd] [] (operandResultBase w accumulator
            (operandWordValue w (.lit address) m) m base))) =
      some ⟨some (Sum.inr (Sum.inr exhaustedLabel)),
        FullInterpreterState.moveLens.put
          (FullInterpreterState.moveLens.put operandState default) default,
        readTransferStacks [] [] (operandResultBase w accumulator
          (operandWordValue w (.lit address) m) m base)⟩:=by
    simpa using hexhaust
  have htail:=chain_loadInstruction_iterations
    (fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (ReadTailLabel R) (FullInterpreterState N)) =>
        o.bind (TM2.step
          (readTransferProgram exhaustedLabel returnLabel right)))
    hinit' hexhaust'
  have hlift:=transport_iterate_operand_right (.lit address)
    (Sum.inl ReadTransferLabel.initializeState)
    (readTransferProgram exhaustedLabel returnLabel right) htail
  have hchain:=chain_loadInstruction_iterations
    (fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (ReadInstructionLabel address R) (FullInterpreterState N)) =>
        o.bind (TM2.step
          (readInstructionProgram address exhaustedLabel returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + 2,by omega,
    FullInterpreterState.moveLens.put operandState default, ?_⟩
  simpa [readInstructionProgram] using! hchain

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

theorem chain_iterations {X:Type} (step:X -> X)
    {a b c:X} {m n:Nat}
    (h₁:(step^[m]) a=b) (h₂:(step^[n]) b=c):
    (step^[m + n]) a=c:=by
  rw [Nat.add_comm,Function.iterate_add_apply,h₁,h₂]

@[simp] theorem mapLabelStmt_id
    {K Λ σ:Type} {α:K→ Type} [DecidableEq K]
    (stmt:TM2.Stmt α Λ σ):
    mapLabelStmt id stmt=stmt:=by
  induction stmt <;> simp [mapLabelStmt, *]

theorem mapLabelStmt_comp
    {K Λ Λ' Λ'' σ:Type} {α:K→ Type} [DecidableEq K]
    (second:Λ' -> Λ'') (first:Λ -> Λ')
    (stmt:TM2.Stmt α Λ σ):
    mapLabelStmt second (mapLabelStmt first stmt) =
      mapLabelStmt (second ∘ first) stmt:=by
  induction stmt <;> simp [mapLabelStmt,Function.comp_def, *]

@[simp] theorem mapLabelCfg_id
    {K Λ σ:Type} {α:K→ Type} (cfg:TM2.Cfg α Λ σ):
    mapLabelCfg id cfg=cfg:=by
  cases cfg <;> simp [mapLabelCfg]

theorem step_mapLabelProgram_of_nonhalt
    {K Λ Λ' σ:Type} {α:K→ Type} [DecidableEq K]
    (source:Λ -> TM2.Stmt α Λ σ)
    (target:Λ' -> TM2.Stmt α Λ' σ)
    (encode:Λ -> Λ')
    (c:TM2.Cfg α Λ σ)
    (hnonhalt:∀ l,c.l=some l -> source l ≠ .halt)
    (hprogram:∀ l,source l ≠ .halt ->
      target (encode l)=mapLabelStmt encode (source l)):
    TM2.step target (mapLabelCfg encode c) =
      (TM2.step source c).map (mapLabelCfg encode):=by
  rcases c with ⟨label,state,tapes⟩
  cases label with
  | none => rfl
  | some label =>
      have hn:=hnonhalt label rfl
      simp only [TM2.step,mapLabelCfg,Option.map_some]
      rw [hprogram label hn]
      exact congrArg some
        (stepAux_mapLabelStmt encode (source label) state tapes)

theorem step_mapLabelProgram
    {K Λ Λ' σ:Type} {α:K→ Type} [DecidableEq K]
    (source:Λ -> TM2.Stmt α Λ σ)
    (target:Λ' -> TM2.Stmt α Λ' σ)
    (encode:Λ -> Λ')
    (hprogram:∀ l,target (encode l)=mapLabelStmt encode (source l))
    (c:TM2.Cfg α Λ σ):
    TM2.step target (mapLabelCfg encode c) =
      (TM2.step source c).map (mapLabelCfg encode):=by
  rcases c with ⟨label,state,tapes⟩
  cases label with
  | none => rfl
  | some label =>
      simp only [TM2.step,mapLabelCfg,Option.map_some]
      rw [hprogram label]
      exact congrArg some
        (stepAux_mapLabelStmt encode (source label) state tapes)

theorem iterate_mapLabelProgram
    {K Λ Λ' σ:Type} {α:K→ Type} [DecidableEq K]
    (source:Λ -> TM2.Stmt α Λ σ)
    (target:Λ' -> TM2.Stmt α Λ' σ)
    (encode:Λ -> Λ')
    (hprogram:∀ l,target (encode l)=mapLabelStmt encode (source l))
    (n:Nat) (c:TM2.Cfg α Λ σ):
    ((fun x => x.bind (TM2.step target))^[n])
        (some (mapLabelCfg encode c)) =
      (((fun x => x.bind (TM2.step source))^[n]) (some c)).map
        (mapLabelCfg encode):=by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
      simp only [Option.bind_some]
      rw [step_mapLabelProgram source target encode hprogram]
      cases hs:TM2.step source c with
      | none =>
          simp only [hs,Option.map_none]
          rw [iterate_optionBind_none,iterate_optionBind_none]
          rfl
      | some c' => simp only [hs,Option.map_some,Option.bind_some]; exact ih c'

theorem iterate_mapLabelProgram_until_exit
    {K Λ Λ' σ:Type} {α:K→ Type} [DecidableEq K]
    (source:Λ -> TM2.Stmt α Λ σ)
    (target:Λ' -> TM2.Stmt α Λ' σ)
    (encode:Λ -> Λ')
    (hprogram:∀ l,source l ≠ .halt ->
      target (encode l)=mapLabelStmt encode (source l))
    {n:Nat} {c d:TM2.Cfg α Λ σ}
    (hrun:((fun x => x.bind (TM2.step source))^[n]) (some c)=some d)
    (hd:d.l.isSome):
    ((fun x => x.bind (TM2.step target))^[n])
      (some (mapLabelCfg encode c)) =
    some (mapLabelCfg encode d):=by
  have hAvoid:=avoidsHalts_of_reaches_labeled source hrun hd
  induction n generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply] at hrun ⊢
      exact congrArg (fun q => q.map (mapLabelCfg encode)) hrun
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun
      rw [Function.iterate_succ_apply]
      simp only [Option.bind_some] at hrun ⊢
      rw [step_mapLabelProgram_of_nonhalt source target encode c hAvoid.1 hprogram]
      cases hs:TM2.step source c with
      | none =>
          simp only [hs,Option.map_none,Option.bind_none] at hrun ⊢
          rw [iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          simp only [hs,Option.map_some,Option.bind_some] at hrun ⊢
          have hAvoid':AvoidsHalts source n c':=by
            simpa [hs] using hAvoid.2
          exact ih hrun hAvoid'

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem subLens_get_moveLens_put {N:Nat}
    (state:FullInterpreterState N) (move:SymbolMoveControl):
    FullInterpreterState.subLens.get
      (FullInterpreterState.moveLens.put state move) =
    FullInterpreterState.subLens.get state:=by
  rfl

@[simp] theorem subtractInstallZero_moveLens_put {N:Nat}
    (state:FullInterpreterState N) (move:SymbolMoveControl):
    subtractInstallZero (FullInterpreterState.moveLens.put state move) =
      subtractInstallZero state:=by
  rfl

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

@[simp] theorem operandEvalStartCfg_label {N:Nat} {R:Type} (o:Op)
    (hN:operandArgument o <= N) (w accumulator:Nat)
    (m:SparseMemory) (state:FullInterpreterState N)
    (base:CoreStack -> List SparseSymbol):
    (operandEvalStartCfg (R:=R) o hN w accumulator m state base).l =
      some (operandEvalStartLabel o):=by
  cases o <;> rfl

theorem operandEvalStartCfg_coreStacks {N:Nat} {R:Type} (o:Op)
    (hN:operandArgument o <= N) (w:Nat) (s:SparseState)
    (state:FullInterpreterState N):
    operandEvalStartCfg (R:=R) o hN w s.acc s.mem state (coreStacks w s) =
      ⟨some (operandEvalStartLabel o),
        FullInterpreterState.literalLens.put state
          (BoundedLiteralControl.initial hN),
        coreStacks w s⟩:=by
  cases o <;>
    simp [operandEvalStartCfg,operandEvalStartLabel,literalOperandStartCfg,
      lensRenamedCfg,boundedLiteralWordCfg,literalWordStacks,
      renamedStacks,literalWordCoreRenaming,literalWordCoreDecode,
      literalQueryCoreRenaming,literalQueryCoreDecode,
      operandBoundaryBase_coreStacks,BoundedLiteralControl.initial,operandArgument]
  all_goals
    congr 2
    funext k
    cases k <;> simp [renamedStacks,literalWordCoreRenaming,
      literalWordCoreDecode,literalQueryCoreRenaming,
      literalQueryCoreDecode,operandBoundaryBase_coreStacks,
      operandBoundaryBase,coreStacks,literalWordStacks,
      encodeAccumulator]

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

noncomputable section

def instructionLabelType (p:Program) (pc:BoundedPC p):Type:=
  match pc.fetch with
  | some (.read a) => ReadInstructionLabel a (BoundedPC p)
  | some (.write o) => WriteInstructionLabel o (BoundedPC p)
  | some (.load o) => LoadInstructionLabel o (BoundedPC p)
  | some (.store a) => StoreInstructionLabel a (BoundedPC p)
  | some (.storeInd a) => StoreIndInstructionLabel a (BoundedPC p)
  | some (.add o) => AddInstructionLabel o (BoundedPC p)
  | some (.sub o) => SubtractInstructionLabel o (BoundedPC p)
  | some (.mul o) => MulInstructionLabel o (BoundedPC p)
  | some (.div o) => DivideInstructionTotalLabel o (BoundedPC p)
  | some (.and o) | some (.or o) | some (.xor o) | some (.compl o) =>
      ZipInstructionLabel o (BoundedPC p)
  | some (.shiftl o) | some (.shiftr o) =>
      ShiftInstructionLabel o (BoundedPC p)
  | _ => PUnit

noncomputable instance instructionLabelTypeFintype (p:Program)
    (pc:BoundedPC p):Fintype (instructionLabelType p pc):=by
  unfold instructionLabelType
  split <;> infer_instance

inductive InterpreterLabel (p:Program) (N:Nat)
  | fetch (pc:BoundedPC p)
  | data (pc:BoundedPC p)
      (code:Fin (Fintype.card (instructionLabelType p pc)))
  | control (label:ControlDispatchLabel p)
  deriving Fintype,Inhabited

theorem stmtIsHalt_eq_true_iff {α K Λ σ:Type}
    (stmt:TM2.Stmt (fun _:K => α) Λ σ):
    stmtIsHalt stmt=true↔ stmt=.halt:=by
  cases stmt <;> simp [stmtIsHalt]

end

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

noncomputable section

noncomputable instance (p:Program) (N:Nat):
    DecidableEq (FiniteInterpreterLabel p N):=Classical.decEq _

theorem finitePrepareEntry_of_fetch {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (pc:BoundedPC p)
    (i:Instr) (hfetch:pc.fetch=some i):
    finitePrepareEntry p N hbound pc =
      finitePrepareInstr p N hbound pc i hfetch:=by
  unfold finitePrepareEntry
  split
  · simp_all
  · rename_i j hj
    have hij:j=i:=Option.some.inj (hj.symm.trans hfetch)
    subst j
    rfl

def finiteEmbedCfg {p:Program} {N:Nat} {L:Type} [Fintype L]
    (encode:L -> FiniteInterpreterLabel p N)
    (c:TM2.Cfg (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N)):
    TM2.Cfg (fun _:CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N):=mapLabelCfg encode c

theorem wrapFiniteLocal_encode_nonhalt {p:Program} {N:Nat} {L:Type}
    [Fintype L] (encode:L -> FiniteInterpreterLabel p N)
    (next:BoundedPC p)
    (program:L -> TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N)) (label:L) (h:program label ≠ .halt):
    wrapFiniteLocal encode next program (localCodeEquiv L label) =
      mapLabelStmt encode (program label):=by
  simp [wrapFiniteLocal,stmtIsHalt_eq_true_iff,h]

theorem finite_step_fetch_data {p:Program} {N pc:Nat}
    (hbound:programArgumentBound p <= N) {i:Instr}
    (hfetch:p[pc]?=some i) (hdata:i ≠ .halt)
    (hnjump:match i with
      | .jump _ | .jzero _ | .jgtz _ => False
      | _ => True)
    (state:FullInterpreterState N)
    (tapes:CoreStack -> List SparseSymbol):
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.fetch (boundPC p pc)) state tapes) =
    some (finiteInterpreterCfg
      (.control (.data (boundPC p pc) (instrClass i))) state tapes):=by
  have hpc:pc < p.length:=fetch_some_pc_lt hfetch
  have hget:p[pc]=i:=by
    simpa [List.getElem?_eq_getElem hpc] using hfetch
  cases i <;>
    simp_all [finiteInterpreterProgram,finiteControlStmt,
      finiteInterpreterCfg,controlDispatchMachine,fetch_boundPC,
      mapLabelStmt,lensRenameStmt,coreIdentityRenaming,
      FullInterpreterState.dispatchLens,FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens,StateLens.comp,TM2.step,
      renamedStacks,finiteEmbedControlLabel,hget]
  all_goals contradiction

theorem finite_step_prepare_entry {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (pc:BoundedPC p)
    (i:Instr) (kind:InstrClass) (hfetch:pc.fetch=some i)
    (hclass:instrClass i=kind)
    (state:FullInterpreterState N) (tapes:CoreStack -> List SparseSymbol):
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data pc kind)) state tapes) =
    some (TM2.stepAux (finitePrepareInstr p N hbound pc i hfetch)
      state tapes):=by
  subst kind
  change some (TM2.stepAux (finitePrepareEntry p N hbound pc) state tapes)=_
  rw [finitePrepareEntry_of_fetch hbound pc i hfetch]

end

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

noncomputable section

def PreservesDispatch {N:Nat} {L:Type}
    (stmt:TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N)):Prop:=
  ∀ state tapes,FullInterpreterState.dispatchLens.get
    (TM2.stepAux stmt state tapes).var =
    FullInterpreterState.dispatchLens.get state

theorem PreservesDispatch.mapLabelStmt {N:Nat} {L L':Type}
    (encode:L→ L')
    {q:TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N)} (hq:PreservesDispatch q):
    PreservesDispatch (mapLabelStmt encode q):=by
  intro state tapes
  rw [stepAux_mapLabelStmt]
  exact hq state tapes

theorem PreservesDispatch.lensRenameStmt
    {N:Nat} {K L X σ:Type} [DecidableEq K]
    (stackMap:StackRenaming K CoreStack)
    (lens:StateLens σ (FullInterpreterState N))
    (hdisjoint:∀ s v, (lens.put s v).dispatch=s.dispatch)
    (q:TM2.Stmt (fun _:K => SparseSymbol) L σ):
    PreservesDispatch (lensRenameStmt (Λx:=X) stackMap lens q):=by
  intro state tapes
  induction q generalizing state tapes with
  | push k f q ih =>
      simpa only [lensRenameStmt,TM2.stepAux] using!
        ih state (Function.update tapes (stackMap.encode k)
          (f (lens.get state)::tapes (stackMap.encode k)))
  | peek k f q ih =>
      exact (ih (lens.put state (f (lens.get state)
        (tapes (stackMap.encode k)).head?)) tapes).trans
          (hdisjoint state _)
  | pop k f q ih =>
      exact (ih (lens.put state (f (lens.get state)
        (tapes (stackMap.encode k)).head?))
          (Function.update tapes (stackMap.encode k)
            (tapes (stackMap.encode k)).tail)).trans
          (hdisjoint state _)
  | load f q ih =>
      exact (ih (lens.put state (f (lens.get state))) tapes).trans
        (hdisjoint state _)
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases h:f (lens.get state)
      · simpa only [Lax759944Proofs.RamToTM.lensRenameStmt,TM2.stepAux,h] using!
          ih₂ state tapes
      · simpa only [Lax759944Proofs.RamToTM.lensRenameStmt,TM2.stepAux,h] using!
          ih₁ state tapes
  | goto f => rfl
  | halt => rfl

theorem finite_data_prefix {p:Program} {N pc n:Nat}
    (hbound:programArgumentBound p <= N) {i:Instr}
    (hfetch:p[pc]?=some i) (hdata:i ≠ .halt)
    (hnjump:match i with
      | .jump _ | .jzero _ | .jgtz _ => False
      | _ => True)
    (state:FullInterpreterState N) (tapes:CoreStack -> List SparseSymbol)
    (localCfg finalCfg:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N))
    (hentry:TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg
        (.control (.data (boundPC p pc) (instrClass i))) state tapes) =
      some localCfg)
    (hlocal:((fun x => x.bind
      (TM2.step (finiteInterpreterProgram p N hbound)))^[n])
      (some localCfg)=some finalCfg):
    ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[2 + n])
      (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state tapes)) =
    some finalCfg:=by
  have hfetchStep:=finite_step_fetch_data hbound hfetch hdata hnjump state tapes
  have hfetchIter:
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[1])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state tapes)) =
      some (finiteInterpreterCfg
        (.control (.data (boundPC p pc) (instrClass i))) state tapes):=by
    simpa using hfetchStep
  have hentryIter:
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[1])
        (some (finiteInterpreterCfg
          (.control (.data (boundPC p pc) (instrClass i))) state tapes)) =
      some localCfg:=by
    simpa using hentry
  have hprefix:=chain_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N)) =>
      x.bind (TM2.step (finiteInterpreterProgram p N hbound)))
    hfetchIter hentryIter
  exact chain_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N)) =>
      x.bind (TM2.step (finiteInterpreterProgram p N hbound)))
    hprefix hlocal

theorem finite_read_exhausted {p:Program} {N pc w address:Nat}
    (hbound:programArgumentBound p <= N)
    (hfetch:p[pc]?=some (.read address))
    (s:SparseState) (hinp:s.inp=[]) (hm:s.mem.Normalized w)
    (state:FullInterpreterState N):
    ∃ steps,steps <= operandEvalBound w s.mem + 4∧
      ∃ finalState finalTapes,
        finalTapes .output=(coreStacks w s) .output∧
        ((fun x => x.bind (TM2.step
          (finiteInterpreterProgram p N hbound)))^[steps])
          (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
            (coreStacks w s))) =
        some (finiteInterpreterCfg (.control .stopped) finalState finalTapes):=by
  let harg:address <= N:=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let ba:=boundedAddress address harg
  let R:=Sum (BoundedPC p) Unit
  let haltRight:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N):=fun _ => .halt
  let localCfg:=finiteEmbedCfg (encodeReadLabel (boundPC p pc) ba)
    (operandEvalStartCfg
      (R:=ReadTailLabel R) (.lit ba.val)
      (Nat.le_of_lt_succ ba.isLt) w s.acc s.mem state (coreStacks w s))
  have hprepare:=finite_step_prepare_entry hbound (boundPC p pc)
    (.read address) .read (by simpa [fetch_boundPC] using hfetch) rfl
    state (coreStacks w s)
  have hentry:TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .read))
        state (coreStacks w s))=some localCfg:=by
    rw [hprepare]
    simp [finitePrepareInstr,finiteInitializeEntry,instrArgument,
      localCfg,operandEvalStartCfg_coreStacks,finiteEmbedCfg,
      mapLabelCfg,finiteInterpreterCfg,ba,harg,boundedAddress] <;>
      constructor <;> congr
  have hinput:(coreStacks w s) .input=[.inputEnd]:=by
    simp [coreStacks,encodeInputStack,encodeWordList,hinp]
  rcases readInstruction_exhausted ba.val (by omega)
      (Sum.inr ()) (Sum.inl (nextPC p (boundPC p pc))) haltRight
      w s.acc s.mem hm (coreStacks w s) hinput state with
    ⟨localSteps,hlocalSteps,finalState,hlocal⟩
  let finalTapes:=readTransferStacks [] []
    (operandResultBase w s.acc
      (operandWordValue w (.lit ba.val) s.mem) s.mem (coreStacks w s))
  let finalLocal:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (ReadInstructionLabel ba.val R) (FullInterpreterState N):=
    embedOperandReturnCfg (.lit ba.val)
      ⟨some (Sum.inr (Sum.inr (.inr ()))),finalState,finalTapes⟩
  have hlocal':
      ((fun x => x.bind (TM2.step
        (readInstructionProgram ba.val (Sum.inr ())
          (Sum.inl (nextPC p (boundPC p pc))) haltRight)))^[localSteps])
        (some (operandEvalStartCfg
          (R:=ReadTailLabel R) (.lit ba.val) (Nat.le_of_lt_succ ba.isLt)
          w s.acc s.mem state (coreStacks w s)))=some finalLocal:=by
    simpa [finalLocal,finalTapes] using hlocal
  have hglobal:=iterate_mapLabelProgram_until_exit
    (readInstructionProgram ba.val (Sum.inr ())
      (Sum.inl (nextPC p (boundPC p pc))) haltRight)
    (finiteInterpreterProgram p N hbound)
    (encodeReadLabel (boundPC p pc) ba)
    (by
      intro label hnonhalt
      cases label with
      | inl l =>
          simpa [finiteInterpreterProgram,encodeReadLabel] using
            (wrapFiniteLocal_encode_nonhalt
              (encodeReadLabel (boundPC p pc) ba)
              (nextPC p (boundPC p pc))
              (readInstructionProgram ba.val (Sum.inr ())
                (Sum.inl (nextPC p (boundPC p pc))) haltRight)
              (Sum.inl l) hnonhalt)
      | inr l =>
          cases l with
          | inl l =>
              simpa [finiteInterpreterProgram,encodeReadLabel] using
                (wrapFiniteLocal_encode_nonhalt
                  (encodeReadLabel (boundPC p pc) ba)
                  (nextPC p (boundPC p pc))
                  (readInstructionProgram ba.val (Sum.inr ())
                    (Sum.inl (nextPC p (boundPC p pc))) haltRight)
                  (Sum.inr (Sum.inl l)) hnonhalt)
          | inr l =>
              cases l with
              | inl l =>
                  simpa [finiteInterpreterProgram,encodeReadLabel] using
                    (wrapFiniteLocal_encode_nonhalt
                      (encodeReadLabel (boundPC p pc) ba)
                      (nextPC p (boundPC p pc))
                      (readInstructionProgram ba.val (Sum.inr ())
                        (Sum.inl (nextPC p (boundPC p pc))) haltRight)
                      (Sum.inr (Sum.inr (Sum.inl l))) hnonhalt)
              | inr l =>
                  cases l with
                  | inl returnPC =>
                      simpa [finiteInterpreterProgram,encodeReadLabel] using
                        (wrapFiniteLocal_encode_nonhalt
                          (encodeReadLabel (boundPC p pc) ba)
                          (nextPC p (boundPC p pc))
                          (readInstructionProgram ba.val (Sum.inr ())
                            (Sum.inl (nextPC p (boundPC p pc))) haltRight)
                          (Sum.inr (Sum.inr (Sum.inr (Sum.inl returnPC)))) hnonhalt)
                  | inr u =>
                      cases u
                      exact False.elim (hnonhalt rfl))
    hlocal' (by rfl)
  have hglobal':
      ((fun x => x.bind (TM2.step
        (finiteInterpreterProgram p N hbound)))^[localSteps])
        (some localCfg) =
      some (finiteInterpreterCfg (.control .stopped) finalState finalTapes):=by
    simpa [localCfg,finalLocal,finalTapes,finiteEmbedCfg,mapLabelCfg,
      encodeReadLabel,finiteInterpreterCfg] using! hglobal
  have hall:=finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.control .stopped) finalState finalTapes)
    hentry hglobal'
  refine ⟨2 + localSteps,by omega,finalState,finalTapes, ?_, ?_⟩
  · simp [finalTapes,readTransferStacks,operandResultBase]
  · exact hall

theorem finite_halt_fetch {p:Program} {N pc:Nat}
    (hbound:programArgumentBound p <= N)
    (hfetch:p[pc]?=some .halt)
    (state:FullInterpreterState N) (tapes:CoreStack -> List SparseSymbol):
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.fetch (boundPC p pc)) state tapes) =
    some (finiteInterpreterCfg (.control .stopped) state tapes):=by
  have hpc:pc < p.length:=fetch_some_pc_lt hfetch
  have hget:p[pc]=.halt:=by
    simpa [List.getElem?_eq_getElem hpc] using hfetch
  simp [finiteInterpreterProgram,finiteControlStmt,finiteInterpreterCfg,
    controlDispatchMachine,fetch_boundPC,hfetch,hget,mapLabelStmt,
    lensRenameStmt,coreIdentityRenaming,FullInterpreterState.dispatchLens,
    FullInterpreterState.macroLens,InterpreterMacroState.dispatchLens,
    StateLens.comp,TM2.step,finiteEmbedControlLabel]

theorem finite_missing_fetch {p:Program} {N pc:Nat}
    (hbound:programArgumentBound p <= N)
    (hfetch:p[pc]?=none)
    (state:FullInterpreterState N) (tapes:CoreStack -> List SparseSymbol):
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.fetch (boundPC p pc)) state tapes) =
    some (finiteInterpreterCfg (.control .stopped) state tapes):=by
  simp [finiteInterpreterProgram,finiteControlStmt,finiteInterpreterCfg,
    controlDispatchMachine,fetch_boundPC,hfetch,mapLabelStmt,
    lensRenameStmt,coreIdentityRenaming,FullInterpreterState.dispatchLens,
    FullInterpreterState.macroLens,InterpreterMacroState.dispatchLens,
    StateLens.comp,TM2.step,finiteEmbedControlLabel]

theorem finite_sparseHalt_to_stopped {p:Program} {N w:Nat}
    (hbound:programArgumentBound p <= N) (s:SparseState)
    (hm:s.mem.Normalized w) (hstop:sparseStep w p s=none)
    (state:FullInterpreterState N):
    ∃ steps,steps <= operandEvalBound w s.mem + 4∧
      ∃ finalState finalTapes,
        finalTapes .output=(coreStacks w s) .output∧
        ((fun x => x.bind (TM2.step
          (finiteInterpreterProgram p N hbound)))^[steps])
          (some (finiteInterpreterCfg (.fetch (boundPC p s.pc)) state
            (coreStacks w s))) =
        some (finiteInterpreterCfg (.control .stopped) finalState finalTapes):=by
  unfold sparseStep at hstop
  cases hfetch:p[s.pc]? with
  | none =>
      refine ⟨1,by simp [operandEvalBound],state,coreStacks w s,rfl, ?_⟩
      simpa [Function.iterate_one] using
        finite_missing_fetch hbound hfetch state (coreStacks w s)
  | some i =>
      simp [hfetch] at hstop
      cases i with
      | read address =>
          cases hinp:s.inp with
          | nil =>
              exact finite_read_exhausted hbound hfetch s hinp hm state
          | cons value tail => simp [sparseEffect,hinp] at hstop
      | halt =>
          refine ⟨1,by simp [operandEvalBound],state,coreStacks w s,rfl, ?_⟩
          simpa [Function.iterate_one] using
            finite_halt_fetch hbound hfetch state (coreStacks w s)
      | write o => simp [sparseEffect] at hstop
      | load o => simp [sparseEffect] at hstop
      | store address => simp [sparseEffect] at hstop
      | storeInd address => simp [sparseEffect] at hstop
      | add o => simp [sparseEffect] at hstop
      | sub o => simp [sparseEffect] at hstop
      | mul o => simp [sparseEffect] at hstop
      | div o => simp [sparseEffect] at hstop
      | and o => simp [sparseEffect] at hstop
      | or o => simp [sparseEffect] at hstop
      | xor o => simp [sparseEffect] at hstop
      | compl o => simp [sparseEffect] at hstop
      | shiftl o => simp [sparseEffect] at hstop
      | shiftr o => simp [sparseEffect] at hstop
      | jump target => simp [sparseEffect] at hstop
      | jzero target => simp [sparseEffect] at hstop
      | jgtz target => simp [sparseEffect] at hstop

theorem sparseEffect_acc_lt {w:Nat} (hw:0 < w) {i:Instr}
    {s s':SparseState} (hacc:s.acc < 2 ^ w)
    (h:sparseEffect w i s=some s'):s'.acc < 2 ^ w:=by
  cases i <;> simp [sparseEffect] at h
  case read address =>
    cases hin:s.inp with
    | nil => simp [hin] at h
    | cons value tail =>
        simp [hin] at h
        subst s'
        exact hacc
  all_goals
    subst s'
    first
    | exact hacc
    | exact Nat.mod_lt _ (by positivity)

theorem sparseStep_acc_lt {w:Nat} (hw:0 < w) {p:Program}
    {s s':SparseState} (hacc:s.acc < 2 ^ w)
    (h:sparseStep w p s=some s'):s'.acc < 2 ^ w:=by
  unfold sparseStep at h
  cases hi:p[s.pc]? with
  | none => simp [hi] at h
  | some i =>
      simp [hi] at h
      exact sparseEffect_acc_lt hw hacc h

theorem finiteStepBound_mono_length {w:Nat} {m₁ m₂:SparseMemory}
    (h:m₁.length <= m₂.length):
    finiteStepBound w m₁ <= finiteStepBound w m₂:=by
  simp [finiteStepBound,finiteDataStepBound,readInstructionBound,
    writeInstructionBound,loadInstructionBound,storeInstructionBound,
    storeIndInstructionBound,addInstructionBound,subtractInstructionBound,
    mulInstructionBound,divideInstructionTotalBound,zipInstructionBound,
    shiftInstructionBound,operandEvalBound]
  nlinarith

def finiteRunUnitBound (w initialMemoryLength t:Nat):Nat:=
  finiteStepBound w (List.replicate (initialMemoryLength + t) (0,0))

set_option maxHeartbeats 3500000 in
theorem finite_sparseRun_correct {p:Program} {N w t:Nat}
    (hbound:programArgumentBound p <= N) (hw:0 < w)
    (s s':SparseState) (hacc:s.acc < 2 ^ w)
    (hm:s.mem.Normalized w) (hrun:sparseRun w p t s=some s')
    (state:FullInterpreterState N)
    (hdispatch:FullInterpreterState.dispatchLens.get state=default):
    ∃ steps,steps <= t * finiteRunUnitBound w s.mem.length t∧
      ∃ finalState,
        FullInterpreterState.dispatchLens.get finalState=default∧
        ((fun x => x.bind
          (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
          (some (finiteInterpreterCfg (.fetch (boundPC p s.pc)) state
            (coreStacks w s))) =
        some (finiteInterpreterCfg (.fetch (boundPC p s'.pc)) finalState
          (coreStacks w s')):=by
  induction t generalizing s state with
  | zero =>
      simp [sparseRun] at hrun
      subst s'
      exact ⟨0,by simp,state,hdispatch,rfl⟩
  | succ t ih =>
      simp only [sparseRun] at hrun
      cases hs:sparseStep w p s with
      | none => simp [hs] at hrun
      | some s₁ =>
          simp [hs] at hrun
          have hacc₁:=sparseStep_acc_lt hw hacc hs
          have hm₁:=sparseStep_mem_normalized hm hs
          rcases finite_sparseStep_correct hbound hw s s₁ hacc hm hs state
              hdispatch with
            ⟨firstSteps,hfirstBound,middleState,hmiddleDispatch,hfirst⟩
          have hmiddleDefault:
              FullInterpreterState.dispatchLens.get middleState=default:=
            hmiddleDispatch.trans hdispatch
          rcases ih s₁ hacc₁ hm₁ hrun middleState hmiddleDefault with
            ⟨restSteps,hrestBound,finalState,hfinalDispatch,hrest⟩
          let targetMemory:SparseMemory:=
            List.replicate (s.mem.length + (t + 1)) (0,0)
          have hlen₁:s₁.mem.length <= s.mem.length + 1:=
            sparseStep_mem_length_le hs
          have hfirstUnit:finiteStepBound w s.mem <=
              finiteStepBound w targetMemory:=by
            apply finiteStepBound_mono_length
            simp [targetMemory]
          have hrestUnit:finiteRunUnitBound w s₁.mem.length t <=
              finiteStepBound w targetMemory:=by
            unfold finiteRunUnitBound
            apply finiteStepBound_mono_length
            simp [targetMemory]
            omega
          have htotalBound:firstSteps + restSteps <=
              (t + 1) * finiteRunUnitBound w s.mem.length (t + 1):=by
            have hf:=hfirstBound.trans hfirstUnit
            have hr:=hrestBound.trans (Nat.mul_le_mul_left t hrestUnit)
            have hadd:=Nat.add_le_add hf hr
            simpa [finiteRunUnitBound,targetMemory,Nat.add_mul,
              Nat.add_comm] using hadd
          have hchain:=chain_iterations
            (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
              (FiniteInterpreterLabel p N) (FullInterpreterState N)) =>
              x.bind (TM2.step (finiteInterpreterProgram p N hbound)))
            hfirst hrest
          exact ⟨firstSteps + restSteps,htotalBound,finalState,
            hfinalDispatch,hchain⟩

theorem cappedShiftLoopBound_closed (w fuel:Nat):
    cappedShiftLoopBound w fuel=fuel * (6 * w + 14) + 3 * w + 7:=by
  induction fuel with
  | zero => simp [cappedShiftLoopBound]
  | succ fuel ih =>
      simp only [cappedShiftLoopBound]
      rw [ih]
      ring

theorem finiteStepBound_polynomial (w:Nat) (m:SparseMemory):
    finiteStepBound w m <= 1000 * (m.length + 1) * (w + 1) ^ 2:=by
  simp [finiteStepBound,finiteDataStepBound,readInstructionBound,
    writeInstructionBound,loadInstructionBound,storeInstructionBound,
    storeIndInstructionBound,addInstructionBound,subtractInstructionBound,
    mulInstructionBound,divideInstructionTotalBound,zipInstructionBound,
    shiftInstructionBound,operandEvalBound,divRunTimeBound,fullShiftBound,
    shiftCoreBound,shiftSetupBound,cappedShiftLoopBound_closed]
  ring_nf at *
  nlinarith

theorem finiteSparseRun_steps_polynomial {w t initialMemoryLength steps:Nat}
    (hsteps:steps <= t * finiteRunUnitBound w initialMemoryLength t):
    steps <= 1000 * t * (initialMemoryLength + t + 1) * (w + 1) ^ 2:=by
  apply hsteps.trans
  unfold finiteRunUnitBound
  have h:=finiteStepBound_polynomial w
    (List.replicate (initialMemoryLength + t) (0,0))
  simp only [List.length_replicate] at h
  nlinarith

@[simp] theorem coreSimulationPolynomial_eval
    (wordBound timeBound:Polynomial Nat) (n:Nat):
    (coreSimulationPolynomial wordBound timeBound).eval n =
      1000 * timeBound.eval n * (timeBound.eval n + 1) *
        (wordBound.eval n + 2) ^ 2:=by
  simp [coreSimulationPolynomial]

theorem finiteSparseRun_steps_le_corePolynomial
    (wordBound timeBound:Polynomial Nat) (n w t steps:Nat)
    (hw:w=wordBound.eval n + 1) (ht:t <= timeBound.eval n)
    (hsteps:steps <= t * finiteRunUnitBound w 0 t):
    steps <= (coreSimulationPolynomial wordBound timeBound).eval n:=by
  have hcore:=finiteSparseRun_steps_polynomial hsteps
  subst w
  rw [coreSimulationPolynomial_eval]
  calc
    steps <= 1000 * t * (0 + t + 1) *
        (wordBound.eval n + 1 + 1) ^ 2:=hcore
    _ <= 1000 * timeBound.eval n * (timeBound.eval n + 1) *
        (wordBound.eval n + 2) ^ 2:=by
      simp only [zero_add,Nat.add_assoc,Nat.add_left_cancel_iff]
      gcongr

set_option maxHeartbeats 2000000 in
theorem ramRunsTo_coreSimulation {p:Program} {w t:Nat}
    (hw:0 < w) {input output:List Nat}
    (hram:RunsTo w p input output t):
    ∃ (ss:SparseState) (steps:Nat),
      ss.out=output∧ sparseStep w p ss=none∧
      ss.mem.Normalized w∧ ss.mem.length <= t∧ ss.out.length <= t∧
      steps <= t * finiteRunUnitBound w 0 t∧
      ∃ finalState,
        FullInterpreterState.dispatchLens.get finalState=default∧
        ((fun x => x.bind (TM2.step
          (finiteInterpreterProgram p (programArgumentBound p) le_rfl)))^[steps])
          (some (finiteInterpreterCfg (.fetch (boundPC p 0))
            (default:FullInterpreterState (programArgumentBound p))
            (coreStacks w (sparseInitState input)))) =
        some (finiteInterpreterCfg (.fetch (boundPC p ss.pc)) finalState
          (coreStacks w ss)):=by
  rcases sparse_halts_of_runsTo hram with
    ⟨ss,hsrun,hhalt,hout,hmem⟩
  have hacc0:(sparseInitState input).acc < 2 ^ w:=by
    simp [sparseInitState]
  rcases finite_sparseRun_correct (p:=p) (N:=programArgumentBound p)
      le_rfl hw (sparseInitState input) ss hacc0
      (SparseMemory.normalized_nil w) hsrun default rfl with
    ⟨steps,hsteps,finalState,hdispatch,htm⟩
  refine ⟨ss,steps,hout,hhalt,
    sparseRun_init_mem_normalized hsrun,hmem,
    sparseRun_init_out_length_le hsrun,
    hsteps,finalState,hdispatch, ?_⟩
  simpa [sparseInitState] using htm

end

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2
open Lax759944.BinaryWordEncoding

noncomputable section

instance (k:WrapperStack):Fintype (WrapperAlphabet k):=by
  cases k <;> simp [WrapperAlphabet] <;> infer_instance

def wrapperCoreStacks (inner:CoreStack -> List SparseSymbol)
    (externalInput externalOutput:List Symbol):
    (k:WrapperStack) -> List (WrapperAlphabet k)
  | .input => externalInput
  | .output => externalOutput
  | .core k => inner k

theorem update_wrapperCoreStacks (inner:CoreStack→ List SparseSymbol)
    (externalInput externalOutput:List Symbol) (k:CoreStack)
    (xs:List SparseSymbol):
    Function.update (wrapperCoreStacks inner externalInput externalOutput)
        (.core k) xs =
      wrapperCoreStacks (Function.update inner k xs)
        externalInput externalOutput:=by
  funext stack
  cases stack with
  | input | output => simp [wrapperCoreStacks,Function.update]
  | core stack =>
      by_cases h:stack=k
      · subst stack
        simp [wrapperCoreStacks,Function.update]
      · simp [wrapperCoreStacks,Function.update,h]

def liftCoreCfg {N:Nat} {L X:Type}
    (c:TM2.Cfg (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (ambient:WrapperState N) (externalInput externalOutput:List Symbol):
    TM2.Cfg WrapperAlphabet (Sum L X) (WrapperState N) where
  l:=c.l.map Sum.inl
  var:=WrapperState.coreLens.put ambient c.var
  stk:=wrapperCoreStacks c.stk externalInput externalOutput

theorem stepAux_liftCoreStmt {N:Nat} {L X:Type}
    (stmt:TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (core:FullInterpreterState N) (inner:CoreStack -> List SparseSymbol)
    (ambient:WrapperState N) (externalInput externalOutput:List Symbol):
    TM2.stepAux (liftCoreStmt (X:=X) stmt)
        (WrapperState.coreLens.put ambient core)
        (wrapperCoreStacks inner externalInput externalOutput) =
      liftCoreCfg (X:=X) (TM2.stepAux stmt core inner)
        ambient externalInput externalOutput:=by
  induction stmt generalizing core inner with
  | push k f q ih =>
      simp only [liftCoreStmt,TM2.stepAux,WrapperState.coreLens]
      simpa only [update_wrapperCoreStacks] using! ih _ _
  | peek k f q ih =>
      simp only [liftCoreStmt,TM2.stepAux,WrapperState.coreLens]
      simpa only [wrapperCoreStacks] using! ih _ _
  | pop k f q ih =>
      simp only [liftCoreStmt,TM2.stepAux,WrapperState.coreLens]
      simpa only [wrapperCoreStacks,update_wrapperCoreStacks] using! ih _ _
  | load f q ih =>
      simp only [liftCoreStmt,TM2.stepAux,WrapperState.coreLens]
      exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [liftCoreStmt,TM2.stepAux,WrapperState.coreLens]
      cases h:f core <;> simp [h]
      · exact ih₂ _ _
      · exact ih₁ _ _
  | goto f =>
      simp [liftCoreStmt,TM2.stepAux,liftCoreCfg,WrapperState.coreLens]
  | halt =>
      simp [liftCoreStmt,TM2.stepAux,liftCoreCfg,WrapperState.coreLens]

def liftCoreProgram {N:Nat} {L X:Type}
    (coreProgram:L -> TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (adapterProgram:X -> TM2.Stmt WrapperAlphabet (Sum L X)
      (WrapperState N)):
    Sum L X -> TM2.Stmt WrapperAlphabet (Sum L X) (WrapperState N)
  | .inl label => liftCoreStmt (coreProgram label)
  | .inr label => adapterProgram label

theorem step_liftCoreProgram {N:Nat} {L X:Type}
    (coreProgram:L -> TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (adapterProgram:X -> TM2.Stmt WrapperAlphabet (Sum L X)
      (WrapperState N))
    (c:TM2.Cfg (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (ambient:WrapperState N) (externalInput externalOutput:List Symbol):
    TM2.step (liftCoreProgram coreProgram adapterProgram)
      (liftCoreCfg (X:=X) c ambient externalInput externalOutput) =
    (TM2.step coreProgram c).map
      (fun d => liftCoreCfg (X:=X) d ambient externalInput externalOutput):=by
  rcases c with ⟨label,core,inner⟩
  cases label with
  | none => rfl
  | some label =>
      simp only [liftCoreCfg,Option.map_some,TM2.step,liftCoreProgram]
      rw [stepAux_liftCoreStmt]
      rfl

theorem iterate_liftCoreProgram {N n:Nat} {L X:Type}
    (coreProgram:L -> TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (adapterProgram:X -> TM2.Stmt WrapperAlphabet (Sum L X)
      (WrapperState N))
    (c d:TM2.Cfg (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (ambient:WrapperState N) (externalInput externalOutput:List Symbol)
    (hrun:((fun x => x.bind (TM2.step coreProgram))^[n]) (some c)=some d):
    ((fun x => x.bind (TM2.step
      (liftCoreProgram coreProgram adapterProgram)))^[n])
      (some (liftCoreCfg (X:=X) c ambient externalInput externalOutput)) =
    some (liftCoreCfg (X:=X) d ambient externalInput externalOutput):=by
  induction n generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply,Option.some.injEq] at hrun ⊢
      subst d
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      simp only [Option.bind_some]
      rw [step_liftCoreProgram]
      cases hs:TM2.step coreProgram c with
      | none =>
          change ((fun x => x.bind (TM2.step coreProgram))^[n])
            (TM2.step coreProgram c)=some d at hrun
          rw [hs] at hrun
          rw [iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          simp only [hs,Option.map_some,Option.bind_some] at hrun ⊢
          exact ih c' hrun

end

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2
open Lax759944.BinaryWordEncoding

noncomputable section

theorem fixedBits_eq_bits_append_replicate {w n:Nat} (h:n < 2 ^ w):
    fixedBits w n=n.bits ++ List.replicate (w - n.bits.length) false:=by
  induction w generalizing n with
  | zero =>
      have hn:n=0:=by simpa using h
      subst n
      rfl
  | succ w ih =>
      by_cases hn:n=0
      · subst n
        simp [fixedBits,List.replicate_succ]
      · have hd:n.div2 < 2 ^ w:=by
          rw [← Nat.bit_bodd_div2 n] at h
          simp only [pow_succ] at h
          cases n.bodd <;> simp [Nat.bit_val] at h ⊢ <;> omega
        have htail:=ih hd
        have hbits:n.bits=n.bodd::n.div2.bits:=by
          rw [← Nat.bit_bodd_div2 n]
          simpa [Nat.bodd_bit,Nat.div2_bit] using
            (Nat.bits_append_bit n.div2 n.bodd (by
          intro hz
          have:n.bodd=true:=by
            have hbit:Nat.bit n.bodd 0=n:=by
              simpa [hz] using Nat.bit_bodd_div2 n
            cases hb:n.bodd
            · simp [Nat.bit,hb] at hbit
              exact False.elim (hn hbit.symm)
            · rfl
          exact this))
        have hlen:n.div2.bits.length <= w:=by
          have:=congrArg List.length htail
          simp only [fixedBits_length,List.length_append,
            List.length_replicate] at this
          omega
        rw [fixedBits,htail,hbits]
        simp only [List.cons_append,List.length_cons]
        congr 2
        simpa [Nat.add_comm] using congrArg
          (fun k => List.replicate k false)
          (Nat.succ_sub_succ_eq_sub w n.div2.bits.length).symm

def trimHighZeros (bitsMSB:List Bool):List Bool:=
  (bitsMSB.dropWhile (·=false)).reverse

theorem dropWhile_false_reverse_bits (n:Nat):
    (n.bits.reverse.dropWhile (·=false)).reverse=n.bits:=by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn:n=0
      · subst n
        simp
      · have hdiv:n.div2 < n:=by
          rw [Nat.div2_val]
          exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero hn) (by omega)
        have htail:=ih n.div2 hdiv
        have hbit:n.bits=n.bodd::n.div2.bits:=by
          calc
            n.bits=(Nat.bit n.bodd n.div2).bits:=
              congrArg Nat.bits (Nat.bit_bodd_div2 n).symm
            _=n.bodd::n.div2.bits:=Nat.bits_append_bit _ _ (by
              intro hz
              have heq:Nat.bit n.bodd 0=n:=by
                simpa [hz] using Nat.bit_bodd_div2 n
              cases hb:n.bodd
              · simp [Nat.bit,hb] at heq
                exact False.elim (hn heq.symm)
              · rfl)
        by_cases hz:n.div2=0
        · have hb:n.bodd=true:=by
            have heq:Nat.bit n.bodd 0=n:=by
              simpa [hz] using Nat.bit_bodd_div2 n
            cases hb:n.bodd
            · simp [Nat.bit,hb] at heq
              exact False.elim (hn heq.symm)
            · rfl
          simp [hbit,hz,hb]
        · rw [hbit,List.reverse_cons,List.dropWhile_append]
          have hnonempty:n.div2.bits.reverse.isEmpty=false:=by
            have hne:n.div2.bits ≠ []:=by
              have hmBits:n.div2.bits =
                  n.div2.bodd::n.div2.div2.bits:=by
                calc
                  n.div2.bits=(Nat.bit n.div2.bodd n.div2.div2).bits:=
                    congrArg Nat.bits (Nat.bit_bodd_div2 n.div2).symm
                  _=_:=Nat.bits_append_bit _ _ (by
                    intro hzero
                    have heq:Nat.bit n.div2.bodd 0=n.div2:=by
                      simpa [hzero] using Nat.bit_bodd_div2 n.div2
                    cases hb:n.div2.bodd
                    · simp [Nat.bit,hb] at heq
                      exact False.elim (hz heq.symm)
                    · rfl)
              rw [hmBits]
              simp
            simp [hne]
          rw [show n.div2.bits.reverse.dropWhile (·=false) =
              n.div2.bits.reverse by
            have:=congrArg List.reverse htail
            simpa using this]
          simp [hnonempty]

theorem trimHighZeros_fixedBits_reverse {w n:Nat} (h:n < 2 ^ w):
    trimHighZeros (fixedBits w n).reverse=n.bits:=by
  rw [fixedBits_eq_bits_append_replicate h]
  unfold trimHighZeros
  rw [List.reverse_append,List.reverse_replicate]
  rw [List.dropWhile_append_of_pos (by intro a ha; simp at ha ⊢; exact ha.2)]
  exact dropWhile_false_reverse_bits n

def outputAdapterCfg {N:Nat} {L:Type} (label:OutputAdapterLabel)
    (state:WrapperState N)
    (tapes:(k:WrapperStack) -> List (WrapperAlphabet k)):
    TM2.Cfg WrapperAlphabet (Sum L OutputAdapterLabel) (WrapperState N):=
  ⟨some (.inr label),state,tapes⟩

@[simp] theorem output_scan_step {N:Nat} {L:Type}
    (state:WrapperState N) (symbol:SparseSymbol)
    (tapes:(k:WrapperStack) -> List (WrapperAlphabet k)):
    TM2.step (liftCoreProgram (fun _:Empty => .halt)
      (outputAdapterProgram (N:=N) (L:=Empty)))
      (outputAdapterCfg (L:=Empty) .scan state
        (Function.update tapes (.core .output)
          (symbol::tapes (.core .output)))) =
    some (outputAdapterCfg (L:=Empty) .decide
      {state with heldSparse:=some symbol}
      (Function.update tapes (.core .output) (tapes (.core .output)))):=by
  simp [outputAdapterCfg,liftCoreProgram,outputAdapterProgram,TM2.step] <;> rfl

@[simp] theorem output_decide_bit_step {N:Nat}
    (state:WrapperState N) (bit:Bool)
    (tapes:(k:WrapperStack) -> List (WrapperAlphabet k)):
    TM2.step (liftCoreProgram (fun _:Empty => .halt)
      (outputAdapterProgram (N:=N) (L:=Empty)))
      (outputAdapterCfg (L:=Empty) .decide
        {state with heldSparse:=some (.bit bit)} tapes) =
    some (outputAdapterCfg (L:=Empty) .bit
      {state with heldSparse:=some (.bit bit)} tapes):=by
  simp [outputAdapterCfg,liftCoreProgram,outputAdapterProgram,TM2.step]

@[simp] theorem output_bit_true_step {N:Nat}
    (state:WrapperState N)
    (tapes:(k:WrapperStack) -> List (WrapperAlphabet k)):
    TM2.step (liftCoreProgram (fun _:Empty => .halt)
      (outputAdapterProgram (N:=N) (L:=Empty)))
      (outputAdapterCfg (L:=Empty) .bit
        {state with heldSparse:=some (.bit true)} tapes) =
    some (outputAdapterCfg (L:=Empty) .scan
      {state with heldSparse:=none,flag:=true}
      (Function.update tapes .output (.one::tapes .output))):=by
  simp [outputAdapterCfg,liftCoreProgram,outputAdapterProgram,TM2.step]

@[simp] theorem output_bit_false_seen_step {N:Nat}
    (state:WrapperState N) (hseen:state.flag=true)
    (tapes:(k:WrapperStack) -> List (WrapperAlphabet k)):
    TM2.step (liftCoreProgram (fun _:Empty => .halt)
      (outputAdapterProgram (N:=N) (L:=Empty)))
      (outputAdapterCfg (L:=Empty) .bit
        {state with heldSparse:=some (.bit false)} tapes) =
    some (outputAdapterCfg (L:=Empty) .scan
      {state with heldSparse:=none}
      (Function.update tapes .output (.zero::tapes .output))):=by
  simp [outputAdapterCfg,liftCoreProgram,outputAdapterProgram,TM2.step,hseen]

@[simp] theorem output_bit_false_unseen_step {N:Nat}
    (state:WrapperState N) (hseen:state.flag=false)
    (tapes:(k:WrapperStack) -> List (WrapperAlphabet k)):
    TM2.step (liftCoreProgram (fun _:Empty => .halt)
      (outputAdapterProgram (N:=N) (L:=Empty)))
      (outputAdapterCfg (L:=Empty) .bit
        {state with heldSparse:=some (.bit false)} tapes) =
    some (outputAdapterCfg (L:=Empty) .scan
      {state with heldSparse:=none} tapes):=by
  simp [outputAdapterCfg,liftCoreProgram,outputAdapterProgram,TM2.step,hseen]

def outputAdapterStacks (coreOutput:List SparseSymbol)
    (output:List Symbol)
    (base:(k:WrapperStack) -> List (WrapperAlphabet k)):
    (k:WrapperStack) -> List (WrapperAlphabet k):=
  Function.update (Function.update base (.core .output) coreOutput) .output output

theorem outputAdapterStacks_cons (symbol:SparseSymbol)
    (rest:List SparseSymbol) (output:List Symbol)
    (base:(k:WrapperStack)→ List (WrapperAlphabet k)):
    outputAdapterStacks (symbol::rest) output base =
      Function.update (outputAdapterStacks rest output base) (.core .output)
        (symbol::outputAdapterStacks rest output base (.core .output)):=by
  funext k
  cases k with
  | input => simp [outputAdapterStacks,Function.update]
  | output => simp [outputAdapterStacks,Function.update]
  | core k =>
      cases k <;> simp [outputAdapterStacks,Function.update] <;> rfl

theorem update_coreOutput_same
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    Function.update tapes (.core .output) (tapes (.core .output))=tapes:=by
  funext k
  cases k with
  | input | output => simp [Function.update]
  | core k => cases k <;> simp [Function.update] <;> rfl

def scanOutputBits:Bool -> List Bool -> List Symbol -> Bool × List Symbol
  | seen, [],output => (seen,output)
  | seen,bit::bits,output =>
      if bit then scanOutputBits true bits (.one::output)
      else if seen then scanOutputBits true bits (.zero::output)
      else scanOutputBits false bits output

@[simp] theorem scanOutputBits_nil (seen:Bool) (output:List Symbol):
    scanOutputBits seen [] output=(seen,output):=rfl

def canonicalBitSymbol (bit:Bool):Symbol:=
  if bit then .one else .zero

theorem scanOutputBits_true (bits:List Bool) (output:List Symbol):
    scanOutputBits true bits output =
      (true,bits.reverse.map canonicalBitSymbol ++ output):=by
  induction bits generalizing output with
  | nil => rfl
  | cons bit bits ih =>
      cases bit <;>
        simp [scanOutputBits,ih,canonicalBitSymbol,List.map_reverse,
          List.append_assoc]

theorem scanOutputBits_false (bits:List Bool) (output:List Symbol):
    (scanOutputBits false bits output).2 =
      (trimHighZeros bits).map canonicalBitSymbol ++ output:=by
  induction bits generalizing output with
  | nil => rfl
  | cons bit bits ih =>
      cases bit
      · simpa [scanOutputBits,trimHighZeros] using ih output
      · simp [scanOutputBits,scanOutputBits_true,trimHighZeros,
          canonicalBitSymbol,List.map_reverse,List.append_assoc]

theorem scanOutputBits_fst (seen:Bool) (bits:List Bool)
    (output₁ output₂:List Symbol):
    (scanOutputBits seen bits output₁).1 =
      (scanOutputBits seen bits output₂).1:=by
  induction bits generalizing seen output₁ output₂ with
  | nil => rfl
  | cons bit bits ih =>
      cases bit <;> cases seen <;> simp only [scanOutputBits, ↓reduceIte] <;>
        apply ih

def outputFinalSeen (w:Nat) (words:List Nat):Bool:=
  (scanOutputBits false
    (fixedBits w (words.getLast?.getD 0)).reverse []).1

theorem scanOutputBits_fixedBits {w n:Nat} (h:n < 2 ^ w)
    (output:List Symbol):
    (scanOutputBits false (fixedBits w n).reverse output).2 =
      n.bits.map canonicalBitSymbol ++ output:=by
  rw [scanOutputBits_false,trimHighZeros_fixedBits_reverse h]

theorem output_bits_run {N:Nat} (state:WrapperState N)
    (seen:Bool) (bits:List Bool) (rest:List SparseSymbol)
    (output:List Symbol)
    (base:(k:WrapperStack) -> List (WrapperAlphabet k)):
    let result:=scanOutputBits seen bits output
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _:Empty => .halt)
        (outputAdapterProgram (N:=N) (L:=Empty)))))^[3 * bits.length])
      (some (outputAdapterCfg (L:=Empty) .scan
        {state with heldSparse:=none,flag:=seen}
        (outputAdapterStacks (bits.map SparseSymbol.bit ++ rest) output base))) =
    some (outputAdapterCfg (L:=Empty) .scan
      {state with heldSparse:=none,flag:=result.1}
      (outputAdapterStacks rest result.2 base)):=by
  induction bits generalizing state seen output with
  | nil =>
      simp [scanOutputBits,outputAdapterStacks]
  | cons bit bits ih =>
      simp only [List.length_cons,List.map_cons,List.cons_append]
      rw [show 3 * (bits.length + 1)=3 * bits.length + 3 by omega,
        Function.iterate_add_apply]
      simp only [Function.iterate_succ_apply,Function.iterate_zero_apply,
        Option.bind_some]
      rw [outputAdapterStacks_cons]
      rw [output_scan_step]
      rw [update_coreOutput_same]
      simp only [Option.bind_some]
      rw [output_decide_bit_step (state:= {state with flag:=seen})]
      simp only [Option.bind_some]
      cases bit with
      | false =>
          cases seen with
          | false =>
              rw [output_bit_false_unseen_step
                (state:= {state with flag:=false}) rfl]
              simpa [scanOutputBits,outputAdapterStacks] using
                ih state false output
          | true =>
              rw [output_bit_false_seen_step
                (state:= {state with flag:=true}) rfl]
              simpa [scanOutputBits,outputAdapterStacks] using
                ih state true (.zero::output)
      | true =>
          cases seen with
          | false =>
              rw [output_bit_true_step (state:= {state with flag:=false})]
              simpa [scanOutputBits,outputAdapterStacks] using
                ih state true (.one::output)
          | true =>
              rw [output_bit_true_step (state:= {state with flag:=true})]
              simpa [scanOutputBits,outputAdapterStacks] using
                ih state true (.one::output)
      all_goals exact Symbol

theorem output_delimiter_run {N:Nat} (state:WrapperState N)
    (active:Bool) (rest:List SparseSymbol) (output:List Symbol)
    (base:(k:WrapperStack) -> List (WrapperAlphabet k)):
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _:Empty => .halt)
        (outputAdapterProgram (N:=N) (L:=Empty)))))^[3])
      (some (outputAdapterCfg (L:=Empty) .scan
        {state with heldSparse:=none,active:=active}
        (outputAdapterStacks (.wordEnd::rest) output base))) =
    some (outputAdapterCfg (L:=Empty) .scan
      {state with heldSparse:=none,flag:=false,active:=true}
      (outputAdapterStacks rest
        (if active then .separator::output else output) base)):=by
  simp only [show 3=Nat.succ (Nat.succ (Nat.succ 0)) by rfl,
    Function.iterate_succ_apply,Function.iterate_zero_apply,
    Option.bind_some]
  rw [outputAdapterStacks_cons]
  rw [output_scan_step]
  rw [update_coreOutput_same]
  simp [outputAdapterCfg,liftCoreProgram,outputAdapterProgram,
    outputAdapterStacks,TM2.step]
  cases active <;> rfl
  all_goals exact Symbol

theorem output_word_run {N w n:Nat} (h:n < 2 ^ w)
    (state:WrapperState N) (rest:List SparseSymbol)
    (output:List Symbol)
    (base:(k:WrapperStack) -> List (WrapperAlphabet k)):
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _:Empty => .halt)
        (outputAdapterProgram (N:=N) (L:=Empty)))))^[3 * w + 3])
      (some (outputAdapterCfg (L:=Empty) .scan
        {state with heldSparse:=none,flag:=false,active:=true}
        (outputAdapterStacks
          ((fixedBits w n).reverse.map SparseSymbol.bit ++ .wordEnd::rest)
          output base))) =
    some (outputAdapterCfg (L:=Empty) .scan
      {state with heldSparse:=none,flag:=false,active:=true}
      (outputAdapterStacks rest (encodeNat n ++ output) base)):=by
  have hbits:=output_bits_run {state with active:=true} false (fixedBits w n).reverse
    (.wordEnd::rest) output base
  have hscan:=scanOutputBits_fixedBits h output
  let middleState:WrapperState N:= {state with heldSparse:=none,flag:=(scanOutputBits false (fixedBits w n).reverse output).1,active:=true}
  have hdelimiter:=output_delimiter_run middleState true rest
    (scanOutputBits false (fixedBits w n).reverse output).2 base
  have hchain:=chain_iterations
    (fun x:Option (TM2.Cfg WrapperAlphabet (Sum Empty OutputAdapterLabel)
      (WrapperState N)) => x.bind (TM2.step
        (liftCoreProgram (fun _:Empty => .halt)
          (outputAdapterProgram (N:=N) (L:=Empty))))) hbits hdelimiter
  rw [show 3 * w + 3=3 * (fixedBits w n).reverse.length + 3 by simp]
  simpa [middleState,hscan,encodeNat,canonicalBitSymbol,
    List.map_map,Function.comp_def,List.append_assoc] using! hchain

theorem output_finish_run {N:Nat} (state:WrapperState N)
    (active:Bool) (output:List Symbol)
    (base:(k:WrapperStack) -> List (WrapperAlphabet k)):
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _:Empty => .halt)
        (outputAdapterProgram (N:=N) (L:=Empty)))))^[3])
      (some (outputAdapterCfg (L:=Empty) .scan
        {state with heldSparse:=none,active:=active}
        (outputAdapterStacks [.outputEnd] output base))) =
    some (outputAdapterCfg (L:=Empty) (.cleanupPeek .input)
      {state with heldSparse:=some .outputEnd,active:=active}
      (outputAdapterStacks []
        (if active then .separator::output else output) base)):=by
  simp only [show 3=Nat.succ (Nat.succ (Nat.succ 0)) by rfl,
    Function.iterate_succ_apply,Function.iterate_zero_apply,
    Option.bind_some]
  rw [outputAdapterStacks_cons]
  rw [output_scan_step]
  rw [update_coreOutput_same]
  simp [outputAdapterCfg,liftCoreProgram,outputAdapterProgram,
    outputAdapterStacks,TM2.step]
  cases active <;> rfl
  all_goals exact Symbol

theorem output_final_word_run {N w n:Nat} (h:n < 2 ^ w)
    (state:WrapperState N) (output:List Symbol)
    (base:(k:WrapperStack) -> List (WrapperAlphabet k)):
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _:Empty => .halt)
        (outputAdapterProgram (N:=N) (L:=Empty)))))^[3 * w + 3])
      (some (outputAdapterCfg (L:=Empty) .scan
        {state with heldSparse:=none,flag:=false,active:=true}
        (outputAdapterStacks
          ((fixedBits w n).reverse.map SparseSymbol.bit ++ [.outputEnd])
          output base))) =
    some (outputAdapterCfg (L:=Empty) (.cleanupPeek .input)
      {state with heldSparse:=some .outputEnd,flag:=(scanOutputBits false (fixedBits w n).reverse output).1,active:=true}
      (outputAdapterStacks [] (encodeNat n ++ output) base)):=by
  have hbits:=output_bits_run {state with active:=true} false (fixedBits w n).reverse
    [.outputEnd] output base
  let middleState:WrapperState N:= {state with heldSparse:=none,flag:=(scanOutputBits false (fixedBits w n).reverse output).1,active:=true}
  have hfinish:=output_finish_run middleState true
    (scanOutputBits false (fixedBits w n).reverse output).2 base
  have hchain:=chain_iterations
    (fun x:Option (TM2.Cfg WrapperAlphabet (Sum Empty OutputAdapterLabel)
      (WrapperState N)) => x.bind (TM2.step
        (liftCoreProgram (fun _:Empty => .halt)
          (outputAdapterProgram (N:=N) (L:=Empty))))) hbits hfinish
  have hscan:=scanOutputBits_fixedBits h output
  rw [show 3 * w + 3=3 * (fixedBits w n).reverse.length + 3 by simp]
  simpa [middleState,hscan,encodeNat,canonicalBitSymbol,
    List.map_map,Function.comp_def,List.append_assoc] using! hchain

def cleanupSuccessor (stack:CleanupStack):OutputAdapterLabel:=
  match nextCleanupStack stack with
  | some next => .cleanupPeek next
  | none => .halt

theorem cleanup_stack_run {N:Nat} (stack:CleanupStack)
    (state:WrapperState N) (xs:List (WrapperAlphabet (cleanupStack stack)))
    (base:(k:WrapperStack) -> List (WrapperAlphabet k)):
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _:Empty => .halt)
        (outputAdapterProgram (N:=N) (L:=Empty)))))^[2 * xs.length + 1])
      (some (outputAdapterCfg (L:=Empty) (.cleanupPeek stack) state
        (Function.update base (cleanupStack stack) xs))) =
    some (outputAdapterCfg (L:=Empty) (cleanupSuccessor stack)
      {state with flag:=false}
      (Function.update base (cleanupStack stack) [])):=by
  induction xs generalizing state with
  | nil =>
      simp [outputAdapterCfg,liftCoreProgram,outputAdapterProgram,
        cleanupSuccessor,TM2.step]
      cases h:nextCleanupStack stack <;> simp [h]
  | cons x xs ih =>
      have hpeek:
          ((fun z => z.bind (TM2.step
            (liftCoreProgram (fun _:Empty => .halt)
              (outputAdapterProgram (N:=N) (L:=Empty)))))^[1])
            (some (outputAdapterCfg (L:=Empty) (.cleanupPeek stack) state
              (Function.update base (cleanupStack stack) (x::xs)))) =
          some (outputAdapterCfg (L:=Empty) (.cleanupPop stack)
            {state with flag:=true}
            (Function.update base (cleanupStack stack) (x::xs))):=by
        simp [outputAdapterCfg,liftCoreProgram,outputAdapterProgram,TM2.step]
      have hpop:
          ((fun z => z.bind (TM2.step
            (liftCoreProgram (fun _:Empty => .halt)
              (outputAdapterProgram (N:=N) (L:=Empty)))))^[1])
            (some (outputAdapterCfg (L:=Empty) (.cleanupPop stack)
              {state with flag:=true}
              (Function.update base (cleanupStack stack) (x::xs)))) =
          some (outputAdapterCfg (L:=Empty) (.cleanupPeek stack)
            {state with flag:=true}
            (Function.update base (cleanupStack stack) xs)):=by
        simp [outputAdapterCfg,liftCoreProgram,outputAdapterProgram,TM2.step]
      have htwo:=chain_iterations
        (fun z:Option (TM2.Cfg WrapperAlphabet
          (Sum Empty OutputAdapterLabel) (WrapperState N)) =>
          z.bind (TM2.step (liftCoreProgram (fun _:Empty => .halt)
            (outputAdapterProgram (N:=N) (L:=Empty))))) hpeek hpop
      have hall:=chain_iterations _ htwo (ih {state with flag:=true})
      have hcost:2 + (2 * xs.length + 1)=2 * (xs.length + 1) + 1:=by
        omega
      simpa only [List.length_cons,hcost] using hall

def outputScanPayload (w:Nat):List Nat -> List SparseSymbol
  | [] => [.outputEnd]
  | n::ns =>
      (fixedBits w n).reverse.map SparseSymbol.bit ++
        match ns with
        | [] => [.outputEnd]
        | _::_ => .wordEnd::outputScanPayload w ns

theorem encodeOutputStack_eq_payload (w:Nat):∀ ys:List Nat,
    encodeOutputStack w ys =
      match ys.reverse with
      | [] => [.outputEnd]
      | _::_ => .wordEnd::outputScanPayload w ys.reverse:=by
  intro ys
  induction ys using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys y ih =>
      simp [encodeOutputStack,encodeWordList,encodeFixedWord,
        outputScanPayload,List.map_reverse,List.append_assoc]
      simpa [encodeWordList] using! ih

theorem output_words_run {N w:Nat} (state:WrapperState N)
    (words:List Nat) (hne:words ≠ [])
    (hfit:∀ n∈ words,n < 2 ^ w)
    (output:List Symbol)
    (base:(k:WrapperStack) -> List (WrapperAlphabet k)):
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _:Empty => .halt)
        (outputAdapterProgram (N:=N) (L:=Empty)))))^[
          words.length * (3 * w + 3)])
      (some (outputAdapterCfg (L:=Empty) .scan
        {state with heldSparse:=none,flag:=false,active:=true}
        (outputAdapterStacks (outputScanPayload w words) output base))) =
    some (outputAdapterCfg (L:=Empty) (.cleanupPeek .input)
      { core:=state.core,heldInput:=state.heldInput,
        heldSparse:=some SparseSymbol.outputEnd,
        flag:=outputFinalSeen w words,
        active:=true}
      (outputAdapterStacks [] (encode words.reverse ++ output) base)):=by
  induction words generalizing output state with
  | nil => contradiction
  | cons n words ih =>
      cases words with
      | nil =>
          have hfinal:=output_final_word_run (N:=N)
            (hfit n (by simp)) state output base
          have hflag:=scanOutputBits_fst false (fixedBits w n).reverse output []
          simpa [outputScanPayload,outputFinalSeen,hflag] using hfinal
      | cons m words =>
          have hn:n < 2 ^ w:=hfit n (by simp)
          have htail:∀ a∈ m::words,a < 2 ^ w:=by
            intro a ha
            exact hfit a (by simp [ha])
          have hfirst:=output_word_run hn state
            (outputScanPayload w (m::words)) output base
          have hrest:=ih
            {state with heldSparse:=none,flag:=false,active:=true}
            (by simp) htail (encodeNat n ++ output)
          have hchain:=chain_iterations
            (fun x:Option (TM2.Cfg WrapperAlphabet
              (Sum Empty OutputAdapterLabel) (WrapperState N)) =>
              x.bind (TM2.step
                (liftCoreProgram (fun _:Empty => .halt)
                  (outputAdapterProgram (N:=N) (L:=Empty))))) hfirst hrest
          have hcost:(n::m::words).length * (3 * w + 3) =
              (3 * w + 3) + (m::words).length * (3 * w + 3):=by
            simp
            ring
          rw [hcost]
          simpa [outputScanPayload,encode,List.append_assoc] using! hchain

theorem output_initialize_step {N:Nat} (state:WrapperState N)
    (tapes:(k:WrapperStack) -> List (WrapperAlphabet k)):
    TM2.step (liftCoreProgram (fun _:Empty => .halt)
      (outputAdapterProgram (N:=N) (L:=Empty)))
      (outputAdapterCfg (L:=Empty) .initializeState state tapes) =
    some (outputAdapterCfg (L:=Empty) .scan
      {state with heldSparse:=none,flag:=false,active:=false} tapes):=by
  simp [outputAdapterCfg,liftCoreProgram,outputAdapterProgram,TM2.step]

theorem output_decode_run {N w:Nat} (state:WrapperState N)
    (ys:List Nat) (hfit:∀ n∈ ys,n < 2 ^ w)
    (base:(k:WrapperStack) -> List (WrapperAlphabet k)):
    ∃ finalState,
      ((fun x => x.bind (TM2.step
        (liftCoreProgram (fun _:Empty => .halt)
          (outputAdapterProgram (N:=N) (L:=Empty)))))^[
            4 + ys.length * (3 * w + 3)])
        (some (outputAdapterCfg (L:=Empty) .initializeState state
          (outputAdapterStacks (encodeOutputStack w ys) [] base))) =
      some (outputAdapterCfg (L:=Empty) (.cleanupPeek .input) finalState
        (outputAdapterStacks [] (encode ys) base)):=by
  have hinit:
      ((fun x => x.bind (TM2.step
        (liftCoreProgram (fun _:Empty => .halt)
          (outputAdapterProgram (N:=N) (L:=Empty)))))^[1])
        (some (outputAdapterCfg (L:=Empty) .initializeState state
          (outputAdapterStacks (encodeOutputStack w ys) [] base))) =
      some (outputAdapterCfg (L:=Empty) .scan
        {state with heldSparse:=none,flag:=false,active:=false}
        (outputAdapterStacks (encodeOutputStack w ys) [] base)):=by
    simpa using output_initialize_step state
      (outputAdapterStacks (encodeOutputStack w ys) [] base)
  cases ys with
  | nil =>
      have hfinish:=output_finish_run
        {state with heldSparse:=none,flag:=false,active:=false}
        false [] base
      let finalState:WrapperState N:=
        {state with heldSparse:=some SparseSymbol.outputEnd,flag:=false,active:=false}
      refine ⟨finalState, ?_⟩
      have hchain:=chain_iterations
        (fun x:Option (TM2.Cfg WrapperAlphabet
          (Sum Empty OutputAdapterLabel) (WrapperState N)) =>
          x.bind (TM2.step
            (liftCoreProgram (fun _:Empty => .halt)
              (outputAdapterProgram (N:=N) (L:=Empty))))) hinit hfinish
      simpa [encodeOutputStack,encode,outputAdapterStacks] using hchain
  | cons y ys =>
      let words:=(y::ys).reverse
      have hwordsNe:words ≠ []:=by simp [words]
      have hwordsFit:∀ n∈ words,n < 2 ^ w:=by
        intro n hn
        exact hfit n (by simpa [words,or_comm] using hn)
      have hdelimiter:=output_delimiter_run
        {state with heldSparse:=none,flag:=false,active:=false}
        false (outputScanPayload w words) [] base
      have hstack:encodeOutputStack w (y::ys) =
          SparseSymbol.wordEnd::outputScanPayload w words:=by
        rw [encodeOutputStack_eq_payload]
        split <;> simp_all [words]
      have hinit':=hinit
      rw [hstack] at hinit'
      have hwords:=output_words_run
        {state with heldSparse:=none,flag:=false,active:=true}
        words hwordsNe hwordsFit [] base
      let finalState:WrapperState N:=
        { core:=state.core,heldInput:=state.heldInput,
          heldSparse:=some SparseSymbol.outputEnd,
          flag:=outputFinalSeen w words,active:=true}
      refine ⟨finalState, ?_⟩
      have hchain₁:=chain_iterations
        (fun x:Option (TM2.Cfg WrapperAlphabet
          (Sum Empty OutputAdapterLabel) (WrapperState N)) =>
          x.bind (TM2.step
            (liftCoreProgram (fun _:Empty => .halt)
              (outputAdapterProgram (N:=N) (L:=Empty))))) hinit' hdelimiter
      have hchain₂:=chain_iterations
        (fun x:Option (TM2.Cfg WrapperAlphabet
          (Sum Empty OutputAdapterLabel) (WrapperState N)) =>
          x.bind (TM2.step
            (liftCoreProgram (fun _:Empty => .halt)
              (outputAdapterProgram (N:=N) (L:=Empty))))) hchain₁ hwords
      rw [hstack]
      simpa [finalState,words,List.length_reverse,
        List.append_assoc] using hchain₂

def cleanupTotalCost
    (tapes:(k:WrapperStack) -> List (WrapperAlphabet k)):Nat:=
  2 * (tapes .input).length + 1 +
  2 * (tapes (.core .accumulator)).length + 1 +
  2 * (tapes (.core .memory)).length + 1 +
  2 * (tapes (.core .input)).length + 1 +
  2 * (tapes (.core .output)).length + 1 +
  2 * (tapes (.core .work0)).length + 1 +
  2 * (tapes (.core .work1)).length + 1 +
  2 * (tapes (.core .work2)).length + 1 +
  2 * (tapes (.core .work3)).length + 1 +
  2 * (tapes (.core .work4)).length + 1 +
  2 * (tapes (.core .work5)).length + 1 +
  2 * (tapes (.core .work6)).length + 1 +
  2 * (tapes (.core .work7)).length + 1

def cleanedStacks
    (tapes:(k:WrapperStack) -> List (WrapperAlphabet k)):
    (k:WrapperStack) -> List (WrapperAlphabet k)
  | .output => tapes .output
  | _ => []

theorem update_same_value {α:Type} {β:α→ Type} [DecidableEq α]
    (f:(a:α)→ β a) (i:α):
    Function.update f i (f i)=f:=by
  funext j
  by_cases h:j=i
  · subst j
    simp
  · simp [Function.update,h]

theorem output_halt_step {N:Nat} (state:WrapperState N)
    (tapes:(k:WrapperStack) -> List (WrapperAlphabet k)):
    TM2.step (liftCoreProgram (fun _:Empty => .halt)
      (outputAdapterProgram (N:=N) (L:=Empty)))
      (outputAdapterCfg (L:=Empty) .halt state tapes) =
    some ⟨none,default,tapes⟩:=by
  simp [outputAdapterCfg,liftCoreProgram,outputAdapterProgram,TM2.step]

theorem output_cleanup_run {N:Nat} (state:WrapperState N)
    (tapes:(k:WrapperStack) -> List (WrapperAlphabet k)):
    ((fun x => x.bind (TM2.step
      (liftCoreProgram (fun _:Empty => .halt)
        (outputAdapterProgram (N:=N) (L:=Empty)))))^[
          cleanupTotalCost tapes + 1])
      (some (outputAdapterCfg (L:=Empty) (.cleanupPeek .input) state tapes)) =
    some ⟨none,default,cleanedStacks tapes⟩:=by
  let s1:=Function.update tapes .input []
  let s2:=Function.update s1 (.core .accumulator) []
  let s3:=Function.update s2 (.core .memory) []
  let s4:=Function.update s3 (.core .input) []
  let s5:=Function.update s4 (.core .output) []
  let s6:=Function.update s5 (.core .work0) []
  let s7:=Function.update s6 (.core .work1) []
  let s8:=Function.update s7 (.core .work2) []
  let s9:=Function.update s8 (.core .work3) []
  let s10:=Function.update s9 (.core .work4) []
  let s11:=Function.update s10 (.core .work5) []
  let s12:=Function.update s11 (.core .work6) []
  let s13:=Function.update s12 (.core .work7) []
  have h1:=cleanup_stack_run (N:=N) .input state (tapes .input) tapes
  have h2:=cleanup_stack_run (N:=N) (.core .accumulator)
    {state with flag:=false} (s1 (.core .accumulator)) s1
  have h3:=cleanup_stack_run (N:=N) (.core .memory)
    {state with flag:=false} (s2 (.core .memory)) s2
  have h4:=cleanup_stack_run (N:=N) (.core .input)
    {state with flag:=false} (s3 (.core .input)) s3
  have h5:=cleanup_stack_run (N:=N) (.core .output)
    {state with flag:=false} (s4 (.core .output)) s4
  have h6:=cleanup_stack_run (N:=N) (.core .work0)
    {state with flag:=false} (s5 (.core .work0)) s5
  have h7:=cleanup_stack_run (N:=N) (.core .work1)
    {state with flag:=false} (s6 (.core .work1)) s6
  have h8:=cleanup_stack_run (N:=N) (.core .work2)
    {state with flag:=false} (s7 (.core .work2)) s7
  have h9:=cleanup_stack_run (N:=N) (.core .work3)
    {state with flag:=false} (s8 (.core .work3)) s8
  have h10:=cleanup_stack_run (N:=N) (.core .work4)
    {state with flag:=false} (s9 (.core .work4)) s9
  have h11:=cleanup_stack_run (N:=N) (.core .work5)
    {state with flag:=false} (s10 (.core .work5)) s10
  have h12:=cleanup_stack_run (N:=N) (.core .work6)
    {state with flag:=false} (s11 (.core .work6)) s11
  have h13:=cleanup_stack_run (N:=N) (.core .work7)
    {state with flag:=false} (s12 (.core .work7)) s12
  simp only [cleanupStack] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  rw [update_same_value] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp only [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13]
    at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  have hall:=chain_iterations
    (fun x:Option (TM2.Cfg WrapperAlphabet (Sum Empty OutputAdapterLabel)
      (WrapperState N)) => x.bind (TM2.step
        (liftCoreProgram (fun _:Empty => .halt)
          (outputAdapterProgram (N:=N) (L:=Empty))))) h1 h2
  have hall:=chain_iterations _ hall h3
  have hall:=chain_iterations _ hall h4
  have hall:=chain_iterations _ hall h5
  have hall:=chain_iterations _ hall h6
  have hall:=chain_iterations _ hall h7
  have hall:=chain_iterations _ hall h8
  have hall:=chain_iterations _ hall h9
  have hall:=chain_iterations _ hall h10
  have hall:=chain_iterations _ hall h11
  have hall:=chain_iterations _ hall h12
  have hall:=chain_iterations _ hall h13
  have hhalt:
      ((fun x => x.bind (TM2.step
        (liftCoreProgram (fun _:Empty => .halt)
          (outputAdapterProgram (N:=N) (L:=Empty)))))^[1])
        (some (outputAdapterCfg (L:=Empty) .halt
          {state with flag:=false} s13)) =
      some ⟨none,default,s13⟩:=by
    simpa using output_halt_step (N:=N) {state with flag:=false} s13
  have hall:=chain_iterations _ hall hhalt
  have hs13:s13=cleanedStacks tapes:=by
    funext k
    cases k with
    | input | output => simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,
        s11,s12,s13,cleanedStacks,Function.update]
    | core k =>
        cases k <;> simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,
          s11,s12,s13,cleanedStacks,Function.update]
  rw [hs13] at hall
  simpa [cleanupTotalCost,cleanupSuccessor,nextCleanupStack,s1,s2,s3,
    s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,cleanedStacks,
    Function.update_self,Function.update_of_ne,Nat.add_assoc] using hall

end

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944.BinaryWordEncoding Lax759944Proofs.Legacy.RamPolytime
open Polynomial

noncomputable section

def simulationWordWidth (wordBound:Polynomial Nat) (x:List Nat):Nat:=
  (polynomialSimpleMajorant wordBound).eval (bitSize x) + 1

inductive InputScanLabel
  | scan
  | decide
  | separator
  | zero
  | one
  | counted
  | done
  deriving DecidableEq,Fintype,Inhabited

def inputScanProgram {N:Nat} {L:Type}:InputScanLabel→
    Turing.TM2.Stmt WrapperAlphabet (Sum L InputScanLabel) (WrapperState N)
  | .scan =>
      .pop .input (fun s a => {s with heldInput:=a}) <|
      .goto fun _ => .inr .decide
  | .decide =>
      .branch (fun s => s.heldInput.isNone)
        (.goto fun _ => .inr .done) <|
      .branch (fun s => match s.heldInput with
        | some .separator => true
        | _ => false)
        (.goto fun _ => .inr .separator) <|
      .branch (fun s => match s.heldInput with
        | some .one => true
        | _ => false)
        (.goto fun _ => .inr .one) <|
      .goto fun _ => .inr .zero
  | .separator =>
      .push (.core .work0) (fun _ => .wordEnd) <|
      .push (.core .work2) (fun _ => .wordEnd) <|
      .goto fun _ => .inr .counted
  | .zero =>
      .push (.core .work0) (fun _ => .bit false) <|
      .goto fun _ => .inr .counted
  | .one =>
      .push (.core .work0) (fun _ => .bit true) <|
      .goto fun _ => .inr .counted
  | .counted =>
      .push (.core .work1) (fun _ => .wordEnd) <|
      .load (fun s => {s with heldInput:=none}) <|
      .goto fun _ => .inr .scan
  | .done => .halt

def sparseOfInputSymbol:Symbol→ SparseSymbol
  | .separator => .wordEnd
  | .zero => .bit false
  | .one => .bit true

def inputSeparatorCount:List Symbol→ Nat
  | [] => 0
  | .separator::xs => inputSeparatorCount xs + 1
  | _::xs => inputSeparatorCount xs

theorem inputSeparatorCount_append (xs ys:List Symbol):
    inputSeparatorCount (xs ++ ys) =
      inputSeparatorCount xs + inputSeparatorCount ys:=by
  induction xs with
  | nil => simp [inputSeparatorCount]
  | cons x xs ih => cases x <;> simp [inputSeparatorCount,ih] <;> omega

theorem inputSeparatorCount_bits (bits:List Bool):
    inputSeparatorCount
      (bits.map (fun b => if b then Symbol.one else Symbol.zero))=0:=by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [inputSeparatorCount,ih]

theorem inputSeparatorCount_encode (x:List Nat):
    inputSeparatorCount (encode x)=x.length:=by
  induction x with
  | nil => rfl
  | cons n x ih =>
      simp only [encode,List.flatMap_cons,encodeNat]
      change inputSeparatorCount
        (n.bits.map (fun b => if b then Symbol.one else Symbol.zero) ++ encode x) + 1 =
          x.length + 1
      rw [inputSeparatorCount_append,inputSeparatorCount_bits,ih]
      omega

def inputScanStacks (input:List Symbol) (seen:List Symbol)
    (base:(k:WrapperStack)→ List (WrapperAlphabet k)):
    (k:WrapperStack)→ List (WrapperAlphabet k):=
  Function.update
    (Function.update
      (Function.update
        (Function.update base .input input)
          (.core .work0) (seen.reverse.map sparseOfInputSymbol))
        (.core .work1) (List.replicate seen.length .wordEnd))
      (.core .work2) (List.replicate (inputSeparatorCount seen) .wordEnd)

@[simp] theorem inputScanStacks_input (input seen base):
    inputScanStacks input seen base .input=input:=by
  simp [inputScanStacks]

def inputScanStepStacks (symbol:Symbol) (tail seen:List Symbol)
    (base:(k:WrapperStack)→ List (WrapperAlphabet k)):
    (k:WrapperStack)→ List (WrapperAlphabet k):=
  let s₀:=Function.update (inputScanStacks (symbol::tail) seen base) .input tail
  let s₁:=Function.update s₀ (.core .work0)
    (sparseOfInputSymbol symbol::s₀ (.core .work0))
  let s₂:=match symbol with
    | .separator => Function.update s₁ (.core .work2)
        (.wordEnd::s₁ (.core .work2))
    | _ => s₁
  Function.update s₂ (.core .work1) (.wordEnd::s₂ (.core .work1))

theorem inputScanStepStacks_eq (symbol:Symbol) (tail seen:List Symbol)
    (base:(k:WrapperStack)→ List (WrapperAlphabet k)):
    inputScanStepStacks symbol tail seen base =
      inputScanStacks tail (seen ++ [symbol]) base:=by
  funext k
  cases symbol <;> cases k with
  | input => simp [inputScanStepStacks,inputScanStacks,Function.update]
  | output => simp [inputScanStepStacks,inputScanStacks,Function.update]
  | core k =>
      cases k <;> simp [inputScanStepStacks,inputScanStacks,
        sparseOfInputSymbol,inputSeparatorCount,List.reverse_append,
        inputSeparatorCount_append,Function.update,List.replicate_succ,
        Nat.add_assoc]

def inputScanMachine {N:Nat}:
    Sum Empty InputScanLabel→
      Turing.TM2.Stmt WrapperAlphabet (Sum Empty InputScanLabel)
        (WrapperState N):=
  liftCoreProgram (fun _:Empty => .halt)
    (inputScanProgram (N:=N) (L:=Empty))

def inputScanCfg {N:Nat} (label:InputScanLabel) (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    Turing.TM2.Cfg WrapperAlphabet (Sum Empty InputScanLabel) (WrapperState N):=
  ⟨some (.inr label),state,tapes⟩

theorem input_scan_symbol_run {N:Nat} (symbol:Symbol)
    (tail seen:List Symbol) (state:WrapperState N)
    (base:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun x => x.bind (Turing.TM2.step inputScanMachine))^[4])
      (some (inputScanCfg .scan {state with heldInput:=none}
        (inputScanStacks (symbol::tail) seen base))) =
    some (inputScanCfg .scan {state with heldInput:=none}
      (inputScanStacks tail (seen ++ [symbol]) base)):=by
  have hst:=inputScanStepStacks_eq symbol tail seen base
  rw [← hst]
  cases symbol <;>
    simp [inputScanMachine,inputScanCfg,inputScanProgram,
      liftCoreProgram,Turing.TM2.step,Turing.TM2.stepAux,
      inputScanStepStacks,inputScanStacks,sparseOfInputSymbol,inputSeparatorCount,
      List.reverse_append,Function.update_of_ne,List.head?,List.tail,
      Option.isNone,
      show decide (some Symbol.separator=some Symbol.separator)=true by decide,
      show decide (some Symbol.zero=some Symbol.separator)=false by decide,
      show decide (some Symbol.one=some Symbol.separator)=false by decide,
      show decide (some Symbol.separator=some Symbol.one)=false by decide,
      show decide (some Symbol.zero=some Symbol.one)=false by decide,
      show decide (some Symbol.one=some Symbol.one)=true by decide,
      show decide (some Symbol.zero=some Symbol.zero)=true by decide,
      show decide (some Symbol.one=some Symbol.zero)=false by decide]

theorem input_scan_run {N:Nat} (input seen:List Symbol)
    (state:WrapperState N)
    (base:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun x => x.bind (Turing.TM2.step inputScanMachine))^[
        4 * input.length])
      (some (inputScanCfg .scan {state with heldInput:=none}
        (inputScanStacks input seen base))) =
    some (inputScanCfg .scan {state with heldInput:=none}
      (inputScanStacks [] (seen ++ input) base)):=by
  induction input generalizing seen with
  | nil => simp
  | cons symbol tail ih =>
      rw [List.length_cons,show 4 * (tail.length + 1)=4 * tail.length + 4 by omega,
        Function.iterate_add_apply]
      rw [input_scan_symbol_run]
      simpa [List.append_assoc] using ih (seen ++ [symbol])

theorem input_scan_finish {N:Nat} (seen:List Symbol)
    (state:WrapperState N)
    (base:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun x => x.bind (Turing.TM2.step inputScanMachine))^[2])
      (some (inputScanCfg .scan {state with heldInput:=none}
        (inputScanStacks [] seen base))) =
    some (inputScanCfg .done {state with heldInput:=none}
      (inputScanStacks [] seen base)):=by
  simp [inputScanMachine,inputScanCfg,inputScanProgram,liftCoreProgram,
    Turing.TM2.step,Turing.TM2.stepAux,List.head?,List.tail,Option.isNone]

theorem input_scan_all {N:Nat} (input:List Symbol)
    (state:WrapperState N)
    (base:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun x => x.bind (Turing.TM2.step inputScanMachine))^[
        4 * input.length + 2])
      (some (inputScanCfg .scan {state with heldInput:=none}
        (inputScanStacks input [] base))) =
    some (inputScanCfg .done {state with heldInput:=none}
      (inputScanStacks [] input base)):=by
  exact chain_iterations _ (input_scan_run input [] state base)
    (input_scan_finish input state base)

end

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive UnaryMulStack | source | multiplier | destination | backup
  deriving DecidableEq,Fintype,Inhabited

inductive UnaryMulLabel | outer | copy | restore | done
  deriving DecidableEq,Fintype,Inhabited

def unaryMulProgram:UnaryMulLabel→
    TM2.Stmt (fun _:UnaryMulStack => SparseSymbol)
      UnaryMulLabel SymbolMoveControl
  | .outer =>
      .pop .source (fun _ a => ⟨a⟩) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .done)
        (.load (fun _ => default) <| .goto fun _ => .copy)
  | .copy =>
      .pop .multiplier (fun _ a => ⟨a⟩) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .restore)
        (.push .destination (fun s => s.held.getD default) <|
          .push .backup (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .copy)
  | .restore =>
      .pop .backup (fun _ a => ⟨a⟩) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .outer)
        (.push .multiplier (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .restore)
  | .done => .halt

def unaryMulStacks (source multiplier destination backup:List SparseSymbol):
    UnaryMulStack→ List SparseSymbol
  | .source => source
  | .multiplier => multiplier
  | .destination => destination
  | .backup => backup

def unaryMulCfg (label:UnaryMulLabel)
    (source multiplier destination backup:List SparseSymbol):
    TM2.Cfg (fun _:UnaryMulStack => SparseSymbol)
      UnaryMulLabel SymbolMoveControl:=
  ⟨some label,default,unaryMulStacks source multiplier destination backup⟩

@[simp] theorem unaryMul_outer_cons (a:SparseSymbol) (as bs out:List SparseSymbol):
    TM2.step unaryMulProgram (unaryMulCfg .outer (a::as) bs out []) =
      some (unaryMulCfg .copy as bs out []):=by
  simp [unaryMulProgram,unaryMulCfg,unaryMulStacks,TM2.step]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem unaryMul_outer_nil (bs out:List SparseSymbol):
    TM2.step unaryMulProgram (unaryMulCfg .outer [] bs out []) =
      some (unaryMulCfg .done [] bs out []):=by
  simp [unaryMulProgram,unaryMulCfg,unaryMulStacks,TM2.step]

@[simp] theorem unaryMul_copy_cons (a:SparseSymbol) (as bs out backup:List SparseSymbol):
    TM2.step unaryMulProgram (unaryMulCfg .copy as (a::bs) out backup) =
      some (unaryMulCfg .copy as bs (a::out) (a::backup)):=by
  simp [unaryMulProgram,unaryMulCfg,unaryMulStacks,TM2.step,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem unaryMul_copy_nil (as out backup:List SparseSymbol):
    TM2.step unaryMulProgram (unaryMulCfg .copy as [] out backup) =
      some (unaryMulCfg .restore as [] out backup):=by
  simp [unaryMulProgram,unaryMulCfg,unaryMulStacks,TM2.step]

@[simp] theorem unaryMul_restore_cons (a:SparseSymbol)
    (as bs out backup:List SparseSymbol):
    TM2.step unaryMulProgram (unaryMulCfg .restore as bs out (a::backup)) =
      some (unaryMulCfg .restore as (a::bs) out backup):=by
  simp [unaryMulProgram,unaryMulCfg,unaryMulStacks,TM2.step,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem unaryMul_restore_nil (as bs out:List SparseSymbol):
    TM2.step unaryMulProgram (unaryMulCfg .restore as bs out []) =
      some (unaryMulCfg .outer as bs out []):=by
  simp [unaryMulProgram,unaryMulCfg,unaryMulStacks,TM2.step]

theorem unaryMul_copy_iterate (as bs out backup:List SparseSymbol):
    ((fun o => o.bind (TM2.step unaryMulProgram))^[bs.length])
      (some (unaryMulCfg .copy as bs out backup)) =
    some (unaryMulCfg .copy as [] (bs.reverse ++ out)
      (bs.reverse ++ backup)):=by
  induction bs generalizing out backup with
  | nil => rfl
  | cons a bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,unaryMul_copy_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem unaryMul_restore_iterate (as bs out backup:List SparseSymbol):
    ((fun o => o.bind (TM2.step unaryMulProgram))^[backup.length])
      (some (unaryMulCfg .restore as bs out backup)) =
    some (unaryMulCfg .restore as (backup.reverse ++ bs) out []):=by
  induction backup generalizing bs with
  | nil => rfl
  | cons a backup ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,unaryMul_restore_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem unaryMul_copy_restore (as bs out:List SparseSymbol):
    ((fun o => o.bind (TM2.step unaryMulProgram))^[2 * bs.length + 2])
      (some (unaryMulCfg .copy as bs out [])) =
    some (unaryMulCfg .outer as bs (bs.reverse ++ out) []):=by
  have h₀:=unaryMul_copy_iterate as bs out []
  simp only [List.append_nil] at h₀
  have h₁:((fun o => o.bind (TM2.step unaryMulProgram))^[1])
      (some (unaryMulCfg .copy as [] (bs.reverse ++ out) bs.reverse)) =
      some (unaryMulCfg .restore as [] (bs.reverse ++ out) bs.reverse):=by
    simpa using unaryMul_copy_nil as (bs.reverse ++ out) bs.reverse
  have h₂:=unaryMul_restore_iterate as [] (bs.reverse ++ out) bs.reverse
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h₂
  have h₃:((fun o => o.bind (TM2.step unaryMulProgram))^[1])
      (some (unaryMulCfg .restore as bs (bs.reverse ++ out) [])) =
      some (unaryMulCfg .outer as bs (bs.reverse ++ out) []):=by
    simpa using unaryMul_restore_nil as bs (bs.reverse ++ out)
  have h:=chain_iterations _ (chain_iterations _
    (chain_iterations _ h₀ h₁) h₂) h₃
  have ht:2 * bs.length + 2=bs.length + 1 + bs.length + 1:=by omega
  rw [ht]
  exact h

def unaryMarkers (n:Nat):List SparseSymbol:=
  List.replicate n .wordEnd

theorem unaryMul_one_round (a b:Nat) (out:List SparseSymbol):
    ((fun o => o.bind (TM2.step unaryMulProgram))^[2 * b + 3])
      (some (unaryMulCfg .outer
        (.wordEnd::unaryMarkers a) (unaryMarkers b) out [])) =
    some (unaryMulCfg .outer (unaryMarkers a) (unaryMarkers b)
      (unaryMarkers b ++ out) []):=by
  have houter:((fun o => o.bind (TM2.step unaryMulProgram))^[1])
      (some (unaryMulCfg .outer (.wordEnd::unaryMarkers a)
        (unaryMarkers b) out [])) =
      some (unaryMulCfg .copy (unaryMarkers a) (unaryMarkers b) out []):=by
    simpa using unaryMul_outer_cons .wordEnd (unaryMarkers a)
      (unaryMarkers b) out
  have hcopy:=unaryMul_copy_restore (unaryMarkers a) (unaryMarkers b) out
  have h:=chain_iterations _ houter hcopy
  rw [show 2 * b + 3=1 + (2 * b + 2) by omega]
  simpa [unaryMarkers,List.reverse_replicate] using h

theorem unaryMul_iterate (a b:Nat) (out:List SparseSymbol):
    ((fun o => o.bind (TM2.step unaryMulProgram))^[a * (2 * b + 3)])
      (some (unaryMulCfg .outer (unaryMarkers a) (unaryMarkers b) out [])) =
    some (unaryMulCfg .outer [] (unaryMarkers b)
      (unaryMarkers (a * b) ++ out) []):=by
  induction a generalizing out with
  | zero => simp [unaryMarkers]
  | succ a ih =>
      have hs:unaryMarkers (a + 1)=.wordEnd::unaryMarkers a:=by
        rw [show a + 1=Nat.succ a by omega]
        rfl
      rw [hs]
      have hround:=unaryMul_one_round a b out
      have hrest:=ih (unaryMarkers b ++ out)
      have h:=chain_iterations _ hround hrest
      have hcost:(a + 1) * (2 * b + 3) =
          (2 * b + 3) + a * (2 * b + 3):=by ring
      rw [hcost]
      have hout:unaryMarkers (a * b) ++ (unaryMarkers b ++ out) =
          unaryMarkers ((a + 1) * b) ++ out:=by
        have hp:(a + 1) * b=a * b + b:=by ring
        rw [hp]
        simp only [unaryMarkers,List.replicate_add,List.append_assoc]
      rw [← hout]
      exact h

theorem unaryMul_correct (a b:Nat):
    ((fun o => o.bind (TM2.step unaryMulProgram))^[a * (2 * b + 3) + 1])
      (some (unaryMulCfg .outer (unaryMarkers a) (unaryMarkers b) [] [])) =
    some (unaryMulCfg .done [] (unaryMarkers b)
      (unaryMarkers (a * b)) []):=by
  have hrun:=unaryMul_iterate a b []
  have hdone:((fun o => o.bind (TM2.step unaryMulProgram))^[1])
      (some (unaryMulCfg .outer [] (unaryMarkers b)
        (unaryMarkers (a * b) ++ []) [])) =
      some (unaryMulCfg .done [] (unaryMarkers b)
        (unaryMarkers (a * b) ++ []) []):=by
    simpa using unaryMul_outer_nil (unaryMarkers b)
      (unaryMarkers (a * b) ++ [])
  simpa using chain_iterations _ hrun hdone

def unaryMulCoreRenaming:StackRenaming UnaryMulStack CoreStack where
  encode
    | .source => .work3
    | .multiplier => .work1
    | .destination => .work4
    | .backup => .work5
  decode
    | .work3 => some .source
    | .work1 => some .multiplier
    | .work4 => some .destination
    | .work5 => some .backup
    | _ => none
  decode_encode:=by intro k; cases k <;> rfl
  encode_decode:=by
    intro k' k h
    cases k <;> cases k' <;> simp_all

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive UnaryPowerLabel:Nat→ Type
  | done:UnaryPowerLabel 0
  | mul {d:Nat} (label:UnaryMulLabel):UnaryPowerLabel (d + 1)
  | move {d:Nat}:UnaryPowerLabel (d + 1)
  | next {d:Nat} (label:UnaryPowerLabel d):UnaryPowerLabel (d + 1)

deriving instance DecidableEq for UnaryPowerLabel

def unaryPowerLabelSuccEquiv (d:Nat):
    UnaryPowerLabel (d + 1) ≃ Option (UnaryMulLabel ⊕ UnaryPowerLabel d) where
  toFun
    | .mul l => some (.inl l)
    | .move => none
    | .next l => some (.inr l)
  invFun
    | some (.inl l) => .mul l
    | none => .move
    | some (.inr l) => .next l
  left_inv:=by intro l; cases l <;> rfl
  right_inv:=by
    intro l
    cases l with
    | none => rfl
    | some l => cases l <;> rfl

instance unaryPowerLabelFintype:(d:Nat)→ Fintype (UnaryPowerLabel d)
  | 0 => Fintype.ofEquiv Unit
      { toFun:=fun _ => .done
        invFun:=fun _ => ()
        left_inv:=by intro x; cases x; rfl
        right_inv:=by intro x; cases x; rfl }
  | d + 1 => by
      letI:=unaryPowerLabelFintype d
      exact Fintype.ofEquiv (Option (UnaryMulLabel ⊕ UnaryPowerLabel d))
        (unaryPowerLabelSuccEquiv d).symm

def unaryPowerStart:(d:Nat)→ UnaryPowerLabel d
  | 0 => .done
  | _ + 1 => .mul .outer

def unaryPowerFinish:(d:Nat)→ UnaryPowerLabel d
  | 0 => .done
  | d + 1 => .next (unaryPowerFinish d)

def unaryPowerProgram:(d:Nat)→ UnaryPowerLabel d→
    TM2.Stmt (fun _:UnaryMulStack => SparseSymbol)
      (UnaryPowerLabel d) SymbolMoveControl
  | 0, .done => .halt
  | d + 1, .mul .done => .goto fun _ => .move
  | d + 1, .mul label => mapLabelStmt .mul (unaryMulProgram label)
  | d + 1, .move =>
      .pop .destination (fun _ a => ⟨a⟩) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .next (unaryPowerStart d))
        (.push .source (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .move)
  | d + 1, .next label => mapLabelStmt .next (unaryPowerProgram d label)

def unaryPowerCfg {d:Nat} (label:UnaryPowerLabel d)
    (source multiplier destination backup:List SparseSymbol):
    TM2.Cfg (fun _:UnaryMulStack => SparseSymbol)
      (UnaryPowerLabel d) SymbolMoveControl:=
  ⟨some label,default,unaryMulStacks source multiplier destination backup⟩

def unaryPowerCost (a b:Nat):Nat→ Nat
  | 0 => 0
  | d + 1 =>
      a * (2 * b + 3) + 2 + a * b + 1 + unaryPowerCost (a * b) b d

theorem unaryPower_mul_phase {d a b:Nat}:
    ((fun o => o.bind (TM2.step (unaryPowerProgram (d + 1))))^[
        a * (2 * b + 3) + 2])
      (some (unaryPowerCfg (.mul .outer)
        (unaryMarkers a) (unaryMarkers b) [] [])) =
    some (unaryPowerCfg (.move:UnaryPowerLabel (d + 1)) []
      (unaryMarkers b) (unaryMarkers (a * b)) []):=by
  have h:=unaryMul_correct a b
  have hm:
      ((fun o => o.bind (TM2.step (unaryPowerProgram (d + 1))))^[
          a * (2 * b + 3) + 1])
        (some (unaryPowerCfg (.mul .outer)
          (unaryMarkers a) (unaryMarkers b) [] [])) =
      some (unaryPowerCfg (.mul .done)
        [] (unaryMarkers b) (unaryMarkers (a * b)) []):=by
    have hembed:=iterate_mapLabelProgram_until_exit unaryMulProgram
      (unaryPowerProgram (d + 1)) UnaryPowerLabel.mul
      (fun l hl => by
        cases l with
        | done => exact (hl rfl).elim
        | outer | copy | restore => rfl) h
      (by simp [unaryMulCfg])
    simpa [mapLabelCfg,unaryMulCfg,unaryPowerCfg] using hembed
  have hnext:
      ((fun o => o.bind (TM2.step (unaryPowerProgram (d + 1))))^[1])
        (some (unaryPowerCfg (.mul .done) [] (unaryMarkers b)
          (unaryMarkers (a * b)) [])) =
      some (unaryPowerCfg (.move:UnaryPowerLabel (d + 1)) []
        (unaryMarkers b) (unaryMarkers (a * b)) []):=by
    simp [unaryPowerProgram,unaryPowerCfg,TM2.step]
  simpa using chain_iterations _ hm hnext

theorem unaryPower_move_phase_aux {d a b:Nat} (acc:List SparseSymbol):
    ((fun o => o.bind (TM2.step (unaryPowerProgram (d + 1))))^[a + 1])
      (some (unaryPowerCfg (.move:UnaryPowerLabel (d + 1)) acc
        (unaryMarkers b) (unaryMarkers a) [])) =
    some (unaryPowerCfg (.next (unaryPowerStart d))
      (unaryMarkers a ++ acc) (unaryMarkers b) [] []):=by
  induction a generalizing acc with
  | zero =>
      simp [unaryMarkers,unaryPowerProgram,unaryPowerCfg,unaryMulStacks,
        TM2.step]
  | succ a ih =>
      have hs:unaryMarkers (a + 1)=.wordEnd::unaryMarkers a:=by
        rw [show a + 1=Nat.succ a by omega]
        rfl
      rw [hs]
      have hstep:
          ((fun o => o.bind (TM2.step (unaryPowerProgram (d + 1))))^[1])
            (some (unaryPowerCfg (.move:UnaryPowerLabel (d + 1)) acc
              (unaryMarkers b) (.wordEnd::unaryMarkers a) [])) =
          some (unaryPowerCfg (.move:UnaryPowerLabel (d + 1))
            (.wordEnd::acc) (unaryMarkers b) (unaryMarkers a) []):=by
        simp [unaryPowerProgram,unaryPowerCfg,unaryMulStacks,TM2.step,
          Function.update]
        congr 2
        funext k
        cases k <;> rfl
      have hrest:=ih (.wordEnd::acc)
      have h:=chain_iterations _ hstep hrest
      rw [show a + 1 + 1=1 + (a + 1) by omega]
      have hout:unaryMarkers a ++ (.wordEnd::acc) =
          .wordEnd::(unaryMarkers a ++ acc):=by
        change List.replicate a .wordEnd ++
            (List.replicate 1 .wordEnd ++ acc) =
          List.replicate 1 .wordEnd ++
            (List.replicate a .wordEnd ++ acc)
        rw [← List.append_assoc, ← List.replicate_add,
          ← List.append_assoc, ← List.replicate_add,Nat.add_comm a 1]
      simpa only [List.cons_append,hout] using h

theorem unaryPower_move_phase {d a b:Nat}:
    ((fun o => o.bind (TM2.step (unaryPowerProgram (d + 1))))^[a + 1])
      (some (unaryPowerCfg (.move:UnaryPowerLabel (d + 1)) []
        (unaryMarkers b) (unaryMarkers a) [])) =
    some (unaryPowerCfg (.next (unaryPowerStart d))
      (unaryMarkers a) (unaryMarkers b) [] []):=by
  simpa using unaryPower_move_phase_aux (d:=d) (a:=a) (b:=b) []

theorem unaryPower_correct (d a b:Nat):
    ((fun o => o.bind (TM2.step (unaryPowerProgram d)))^[
        unaryPowerCost a b d])
      (some (unaryPowerCfg (unaryPowerStart d)
        (unaryMarkers a) (unaryMarkers b) [] [])) =
    some (unaryPowerCfg (unaryPowerFinish d)
      (unaryMarkers (a * b ^ d)) (unaryMarkers b) [] []):=by
  induction d generalizing a with
  | zero => simp [unaryPowerCost,unaryPowerStart,unaryPowerFinish]
  | succ d ih =>
      rw [unaryPowerCost]
      have hmul:=unaryPower_mul_phase (d:=d) (a:=a) (b:=b)
      have hmove:=unaryPower_move_phase (d:=d) (a:=a * b) (b:=b)
      have htail:=ih (a * b)
      have htail':
          ((fun o => o.bind (TM2.step (unaryPowerProgram (d + 1))))^[
              unaryPowerCost (a * b) b d])
            (some (unaryPowerCfg (.next (unaryPowerStart d))
              (unaryMarkers (a * b)) (unaryMarkers b) [] [])) =
          some (unaryPowerCfg (.next (unaryPowerFinish d))
            (unaryMarkers ((a * b) * b ^ d)) (unaryMarkers b) [] []):=by
        have hembed:=iterate_mapLabelProgram (unaryPowerProgram d)
          (unaryPowerProgram (d + 1)) UnaryPowerLabel.next
          (fun l => by simp [unaryPowerProgram])
          (unaryPowerCost (a * b) b d)
          (unaryPowerCfg (unaryPowerStart d) (unaryMarkers (a * b))
            (unaryMarkers b) [] [])
        rw [htail] at hembed
        simpa [mapLabelCfg,unaryPowerCfg] using hembed
      have h:=chain_iterations _ (chain_iterations _ hmul hmove) htail'
      have hp:a * (b * b ^ d)=a * (b ^ d * b):=by ring
      rw [pow_succ]
      rw [← hp]
      simpa [unaryPowerStart,unaryPowerFinish,mul_assoc,
        Nat.add_assoc] using h

theorem unaryPowerProgram_finish_halt (d:Nat):
    unaryPowerProgram d (unaryPowerFinish d)=.halt:=by
  induction d with
  | zero => rfl
  | succ d ih => rw [unaryPowerFinish,unaryPowerProgram,ih]; rfl

@[simp] theorem unaryPowerCostPolynomial_eval
    (accumulator multiplier:Polynomial Nat) (d n:Nat):
    (unaryPowerCostPolynomial accumulator multiplier d).eval n =
      unaryPowerCost (accumulator.eval n) (multiplier.eval n) d:=by
  induction d generalizing accumulator with
  | zero => simp [unaryPowerCostPolynomial,unaryPowerCost]
  | succ d ih =>
      simp [unaryPowerCostPolynomial,unaryPowerCost,ih]

@[simp] theorem simpleMajorantEvalCostPolynomial_eval
    (p:Polynomial Nat) (n:Nat):
    (simpleMajorantEvalCostPolynomial p).eval n =
      unaryPowerCost (polyCoeffSum p) (n + 1) p.natDegree:=by
  simp [simpleMajorantEvalCostPolynomial]

theorem unaryPower_simpleMajorant_correct (p:Polynomial Nat) (n:Nat):
    ((fun o => o.bind (TM2.step (unaryPowerProgram p.natDegree)))^[
        (simpleMajorantEvalCostPolynomial p).eval n])
      (some (unaryPowerCfg (unaryPowerStart p.natDegree)
        (unaryMarkers (polyCoeffSum p)) (unaryMarkers (n + 1)) [] [])) =
    some (unaryPowerCfg (unaryPowerFinish p.natDegree)
      (unaryMarkers ((polynomialSimpleMajorant p).eval n))
      (unaryMarkers (n + 1)) [] []):=by
  simpa [polynomialSimpleMajorant_eval] using
    unaryPower_correct p.natDegree (polyCoeffSum p) (n + 1)

theorem unaryPower_core_simpleMajorant_correct {N:Nat} {R:Type}
    (p:Polynomial Nat) (n:Nat) (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol)
      (Sum (UnaryPowerLabel p.natDegree) R) (FullInterpreterState N))
    (ambientState:FullInterpreterState N)
    (ambientStacks:CoreStack→ List SparseSymbol):
    ((fun o => o.bind (TM2.step (lensSpliceProgram unaryMulCoreRenaming
      FullInterpreterState.moveLens (unaryPowerProgram p.natDegree)
      (unaryPowerFinish p.natDegree) returnLabel right)))^[
        (simpleMajorantEvalCostPolynomial p).eval n + 1])
      (some (lensRenamedCfg unaryMulCoreRenaming
        FullInterpreterState.moveLens
        (unaryPowerCfg (unaryPowerStart p.natDegree)
          (unaryMarkers (polyCoeffSum p)) (unaryMarkers (n + 1)) [] [])
        ambientState ambientStacks)) =
    some (lensReturnCfg unaryMulCoreRenaming FullInterpreterState.moveLens
      returnLabel
      (unaryPowerCfg (unaryPowerFinish p.natDegree)
        (unaryMarkers ((polynomialSimpleMajorant p).eval n))
        (unaryMarkers (n + 1)) [] [])
      ambientState ambientStacks):=by
  apply transport_lensHaltingMacro_and_return unaryMulCoreRenaming
    FullInterpreterState.moveLens (unaryPowerProgram p.natDegree)
    (unaryPowerFinish p.natDegree) (unaryPowerProgram_finish_halt _) returnLabel right
    (unaryPower_simpleMajorant_correct p n) rfl ambientState ambientStacks

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2
open Polynomial
open Lax759944.BinaryWordEncoding Lax759944Proofs.Legacy.RamPolytime

noncomputable section

def unaryPowerWrapperRenaming:StackRenaming UnaryMulStack WrapperStack where
  encode k:=.core (unaryMulCoreRenaming.encode k)
  decode
    | .core k => unaryMulCoreRenaming.decode k
    | _ => none
  decode_encode:=unaryMulCoreRenaming.decode_encode
  encode_decode:=by
    intro k' k h
    cases k' with
    | input => simp at h
    | output => simp at h
    | core k' =>
        simp only at h ⊢
        exact congrArg WrapperStack.core (unaryMulCoreRenaming.encode_decode h)

def unaryPowerWrapperLens {N:Nat}:
    StateLens SymbolMoveControl (WrapperState N):=
  StateLens.comp FullInterpreterState.moveLens WrapperState.coreLens

def pushUnaryMarkers {N:Nat} {L:Type} (stack:CoreStack):Nat→
    TM2.Stmt WrapperAlphabet L (WrapperState N)→
      TM2.Stmt WrapperAlphabet L (WrapperState N)
  | 0,q => q
  | n + 1,q => .push (.core stack) (fun _ => .wordEnd)
      (pushUnaryMarkers stack n q)

theorem stepAux_pushUnaryMarkers_work3 {N:Nat} {L:Type}
    (n:Nat) (q:TM2.Stmt WrapperAlphabet L (WrapperState N))
    (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    TM2.stepAux (pushUnaryMarkers .work3 n q) state tapes =
      TM2.stepAux q state (Function.update tapes (.core .work3)
        (List.replicate n SparseSymbol.wordEnd ++
          (show List SparseSymbol from tapes (.core .work3)))):=by
  induction n generalizing tapes with
  | zero => simp [pushUnaryMarkers,update_same_value]
  | succ n ih =>
      simp only [pushUnaryMarkers,TM2.stepAux]
      rw [ih]
      simp only [Function.update_self]
      have hlist:List.replicate n SparseSymbol.wordEnd ++
          (SparseSymbol.wordEnd::
            (show List SparseSymbol from tapes (.core .work3))) =
          List.replicate (n + 1) SparseSymbol.wordEnd ++
            (show List SparseSymbol from tapes (.core .work3)):=by
        change List.replicate n SparseSymbol.wordEnd ++
            (List.replicate 1 SparseSymbol.wordEnd ++
              (show List SparseSymbol from tapes (.core .work3)))=_
        rw [← List.append_assoc, ← List.replicate_add]
      have heq:
          Function.update
              (Function.update tapes (.core .work3)
                (.wordEnd::tapes (.core .work3)))
              (.core .work3)
              (List.replicate n .wordEnd ++
                (.wordEnd::tapes (.core .work3))) =
            Function.update tapes (.core .work3)
              (List.replicate (n + 1) .wordEnd ++ tapes (.core .work3)):=by
        funext k
        cases k with
        | input | output => simp [Function.update]
        | core k =>
            cases k <;> simp [Function.update]
            exact hlist
      exact congrArg (TM2.stepAux q state) heq

inductive WidthBoundaryLabel | addOne | ready
  deriving DecidableEq,Fintype,Inhabited

abbrev InputWidthLabel (p:Polynomial Nat):=
  Sum InputScanLabel (Sum (UnaryPowerLabel p.natDegree) WidthBoundaryLabel)

def widthBoundaryCoreProgram {N:Nat} {d:Nat}:WidthBoundaryLabel→
    TM2.Stmt (fun _:CoreStack => SparseSymbol)
      (Sum (UnaryPowerLabel d) WidthBoundaryLabel) (FullInterpreterState N)
  | .addOne =>
      .push .work3 (fun _ => .wordEnd) <|
      .goto fun _ => .inr .ready
  | .ready => .halt

def widthPowerCoreSpliceProgram {N:Nat} (p:Polynomial Nat):=
  lensSpliceProgram unaryMulCoreRenaming FullInterpreterState.moveLens
    (unaryPowerProgram p.natDegree) (unaryPowerFinish p.natDegree)
    WidthBoundaryLabel.addOne (widthBoundaryCoreProgram (N:=N))

def embedLiftedWidthPowerLabel {p:Polynomial Nat}:
    Sum (Sum (UnaryPowerLabel p.natDegree) WidthBoundaryLabel) Empty→
      InputWidthLabel p
  | .inl (.inl label) => .inr (.inl label)
  | .inl (.inr label) => .inr (.inr label)
  | .inr impossible => nomatch impossible

def inputWidthProgram {N:Nat} (p:Polynomial Nat):
    InputWidthLabel p→ TM2.Stmt WrapperAlphabet (InputWidthLabel p) (WrapperState N)
  | .inl .done =>
      .load (fun s => unaryPowerWrapperLens.put s default) <|
      .push (.core .work1) (fun _ => .wordEnd) <|
      pushUnaryMarkers .work3 (polyCoeffSum p) <|
      .goto fun _ => .inr (.inl (unaryPowerStart p.natDegree))
  | .inl label =>
      mapLabelStmt
        (fun label:Sum Empty InputScanLabel => match label with
          | Sum.inl impossible => nomatch impossible
          | Sum.inr next => Sum.inl next)
        (inputScanProgram (N:=N) (L:=Empty) label)
  | .inr label =>
      mapLabelStmt (embedLiftedWidthPowerLabel (p:=p)) <|
        liftCoreStmt (N:=N) (X:=Empty) (widthPowerCoreSpliceProgram p label)

def inputWidthCfg {N:Nat} {p:Polynomial Nat} (label:InputWidthLabel p)
    (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    TM2.Cfg WrapperAlphabet (InputWidthLabel p) (WrapperState N):=
  ⟨some label,state,tapes⟩

theorem inputWidth_scan_bridge {N:Nat} (p:Polynomial Nat)
    (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    TM2.step (inputWidthProgram p)
      (inputWidthCfg (.inl .done) state tapes) =
    some (inputWidthCfg (.inr (.inl (unaryPowerStart p.natDegree)))
      (unaryPowerWrapperLens.put state default)
      (Function.update
        (Function.update tapes (.core .work1)
          (.wordEnd::tapes (.core .work1)))
        (.core .work3)
          (unaryMarkers (polyCoeffSum p) ++
            (show List SparseSymbol from tapes (.core .work3))))):=by
  simp only [inputWidthCfg,TM2.step,inputWidthProgram,TM2.stepAux]
  rw [stepAux_pushUnaryMarkers_work3]
  simp [unaryMarkers]

theorem inputWidth_power_run {N:Nat} (p:Polynomial Nat) (n:Nat)
    (ambientState:WrapperState N)
    (ambientStacks:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun o => o.bind (TM2.step (inputWidthProgram p)))^[
        (simpleMajorantEvalCostPolynomial p).eval n + 1])
      (some (mapLabelCfg (embedLiftedWidthPowerLabel (p:=p))
        (liftCoreCfg (X:=Empty)
          (lensRenamedCfg unaryMulCoreRenaming FullInterpreterState.moveLens
            (unaryPowerCfg (unaryPowerStart p.natDegree)
              (unaryMarkers (polyCoeffSum p)) (unaryMarkers (n + 1)) [] [])
            ambientState.core (fun k => ambientStacks (.core k)))
          ambientState (ambientStacks .input) (ambientStacks .output)))) =
    some (mapLabelCfg (embedLiftedWidthPowerLabel (p:=p))
      (liftCoreCfg (X:=Empty)
        (lensReturnCfg unaryMulCoreRenaming FullInterpreterState.moveLens
          WidthBoundaryLabel.addOne
          (unaryPowerCfg (unaryPowerFinish p.natDegree)
            (unaryMarkers ((polynomialSimpleMajorant p).eval n))
            (unaryMarkers (n + 1)) [] [])
          ambientState.core (fun k => ambientStacks (.core k)))
        ambientState (ambientStacks .input) (ambientStacks .output))):=by
  have hcore:=unaryPower_core_simpleMajorant_correct (N:=N) p n
    WidthBoundaryLabel.addOne (widthBoundaryCoreProgram (N:=N))
    ambientState.core (fun k => ambientStacks (.core k))
  have hlift:=iterate_liftCoreProgram
    (widthPowerCoreSpliceProgram (N:=N) p)
    (fun impossible:Empty => nomatch impossible) _ _ ambientState
    (ambientStacks .input) (ambientStacks .output) hcore
  have hembed:=iterate_mapLabelProgram
    (liftCoreProgram (widthPowerCoreSpliceProgram (N:=N) p)
      (fun impossible:Empty => nomatch impossible))
    (inputWidthProgram p) (embedLiftedWidthPowerLabel (p:=p))
    (fun label => by cases label with
      | inl label => cases label <;> rfl
      | inr impossible => nomatch impossible)
    ((simpleMajorantEvalCostPolynomial p).eval n + 1)
    (liftCoreCfg (X:=Empty)
      (lensRenamedCfg unaryMulCoreRenaming FullInterpreterState.moveLens
        (unaryPowerCfg (unaryPowerStart p.natDegree)
          (unaryMarkers (polyCoeffSum p)) (unaryMarkers (n + 1)) [] [])
        ambientState.core (fun k => ambientStacks (.core k)))
      ambientState (ambientStacks .input) (ambientStacks .output))
  rw [hlift] at hembed
  exact hembed

def inputWidthInitialStacks (input:List Symbol):
    (k:WrapperStack)→ List (WrapperAlphabet k)
  | .input => input
  | .output => []
  | .core _ => []

def inputWidthScannedStacks (input:List Symbol):
    (k:WrapperStack)→ List (WrapperAlphabet k)
  | .input => []
  | .output => []
  | .core .work0 => input.reverse.map sparseOfInputSymbol
  | .core .work1 => List.replicate input.length .wordEnd
  | .core .work2 => List.replicate (inputSeparatorCount input) .wordEnd
  | .core _ => []

theorem inputScanStacks_initial (input:List Symbol):
    inputScanStacks input [] (inputWidthInitialStacks input) =
      inputWidthInitialStacks input:=by
  funext k
  cases k with
  | input => simp [inputScanStacks,inputWidthInitialStacks]
  | output => simp [inputScanStacks,inputWidthInitialStacks]
  | core k => cases k <;> simp [inputScanStacks,inputWidthInitialStacks]
    <;> rfl

theorem inputScanStacks_scanned (input:List Symbol):
    inputScanStacks [] input (inputWidthInitialStacks input) =
      inputWidthScannedStacks input:=by
  have hzero:inputSeparatorCount []=0:=rfl
  funext k
  cases k with
  | input => simp [inputScanStacks,inputWidthInitialStacks,
      inputWidthScannedStacks]
  | output => simp [inputScanStacks,inputWidthInitialStacks,
      inputWidthScannedStacks]
  | core k => cases k <;> simp [inputScanStacks,inputWidthInitialStacks,
      inputWidthScannedStacks,hzero]
    <;> rfl

theorem inputWidth_scan_bridge_powerStart {N:Nat} (p:Polynomial Nat)
    (input:List Symbol) (n:Nat) (hlen:input.length=n)
    (state:WrapperState N):
    TM2.step (inputWidthProgram p)
      (inputWidthCfg (.inl .done) state (inputWidthScannedStacks input)) =
    some (mapLabelCfg (embedLiftedWidthPowerLabel (p:=p))
      (liftCoreCfg (X:=Empty)
        (lensRenamedCfg unaryMulCoreRenaming FullInterpreterState.moveLens
          (unaryPowerCfg (unaryPowerStart p.natDegree)
            (unaryMarkers (polyCoeffSum p)) (unaryMarkers (n + 1)) [] [])
          state.core (fun k => inputWidthScannedStacks input (.core k)))
        state (inputWidthScannedStacks input .input)
          (inputWidthScannedStacks input .output))):=by
  have h:=inputWidth_scan_bridge (N:=N) p state
    (inputWidthScannedStacks input)
  convert h using 1 <;>
    simp [inputWidthCfg,mapLabelCfg,liftCoreCfg,lensRenamedCfg,
      unaryMulCoreRenaming,unaryMulStacks,unaryPowerWrapperLens,
      unaryPowerCfg,embedLiftedWidthPowerLabel,WrapperState.coreLens,
      StateLens.comp,inputWidthScannedStacks,unaryMarkers,hlen,
      List.replicate_succ]
  funext k
  cases k with
  | input | output => rfl
  | core k =>
      cases k <;> simp [renamedStacks,unaryMulCoreRenaming,
        unaryMulStacks,inputWidthScannedStacks,wrapperCoreStacks,
        Function.update,List.append_nil] <;>
        first | exact rfl | exact (List.append_nil _).symm

def embedInputScanLabel {p:Polynomial Nat}:
    Sum Empty InputScanLabel→ InputWidthLabel p
  | .inl impossible => nomatch impossible
  | .inr label => .inl label

theorem inputWidth_scan_run {N:Nat} (p:Polynomial Nat)
    (input:List Symbol) (state:WrapperState N):
    ((fun o => o.bind (TM2.step (inputWidthProgram p)))^[4 * input.length + 2])
      (some (inputWidthCfg (.inl .scan) {state with heldInput:=none}
        (inputWidthInitialStacks input))) =
    some (inputWidthCfg (.inl .done) {state with heldInput:=none}
      (inputWidthScannedStacks input)):=by
  have hrun:=input_scan_all (N:=N) input state
    (inputWidthInitialStacks input)
  rw [inputScanStacks_initial,inputScanStacks_scanned] at hrun
  apply iterate_mapLabelProgram_until_exit inputScanMachine
    (inputWidthProgram p) embedInputScanLabel
    (fun label hnonhalt => by
      cases label with
      | inl impossible => nomatch impossible
      | inr label =>
          cases label <;>
            simp [inputScanMachine,liftCoreProgram,inputScanProgram,
              embedInputScanLabel,inputWidthProgram,mapLabelStmt] at hnonhalt ⊢)
    hrun
  rfl

theorem inputWidth_addOne_step {N:Nat} (p:Polynomial Nat)
    (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    TM2.step (inputWidthProgram p)
      (inputWidthCfg (.inr (.inr .addOne)) state tapes) =
    some (inputWidthCfg (.inr (.inr .ready)) state
      (Function.update tapes (.core .work3)
        (.wordEnd::tapes (.core .work3)))):=by
  simp [inputWidthCfg,inputWidthProgram,widthPowerCoreSpliceProgram,
    lensSpliceProgram,widthBoundaryCoreProgram,liftCoreStmt,
    mapLabelStmt,embedLiftedWidthPowerLabel,TM2.step]

def inputWidthPowerFinalCfg {N:Nat} (p:Polynomial Nat) (n:Nat)
    (ambientState:WrapperState N)
    (ambientStacks:(k:WrapperStack)→ List (WrapperAlphabet k)):=
  mapLabelCfg (embedLiftedWidthPowerLabel (p:=p)) <|
    liftCoreCfg (X:=Empty)
      (lensReturnCfg unaryMulCoreRenaming FullInterpreterState.moveLens
        WidthBoundaryLabel.addOne
        (unaryPowerCfg (unaryPowerFinish p.natDegree)
          (unaryMarkers ((polynomialSimpleMajorant p).eval n))
          (unaryMarkers (n + 1)) [] [])
        ambientState.core (fun k => ambientStacks (.core k)))
      ambientState (ambientStacks .input) (ambientStacks .output)

def inputWidthReadyCfg {N:Nat} (p:Polynomial Nat) (n:Nat)
    (ambientState:WrapperState N)
    (ambientStacks:(k:WrapperStack)→ List (WrapperAlphabet k)):
    TM2.Cfg WrapperAlphabet (InputWidthLabel p) (WrapperState N):=
  let c:=inputWidthPowerFinalCfg p n ambientState ambientStacks
  { c with
    l:=some (.inr (.inr .ready))
    stk:=Function.update c.stk (.core .work3)
      (.wordEnd::c.stk (.core .work3)) }

theorem inputWidth_power_addOne {N:Nat} (p:Polynomial Nat) (n:Nat)
    (ambientState:WrapperState N)
    (ambientStacks:(k:WrapperStack)→ List (WrapperAlphabet k)):
    TM2.step (inputWidthProgram p)
      (inputWidthPowerFinalCfg p n ambientState ambientStacks) =
    some (inputWidthReadyCfg p n ambientState ambientStacks):=by
  let c:=inputWidthPowerFinalCfg p n ambientState ambientStacks
  have hc:c.l=some (.inr (.inr .addOne)):=by
    simp [c,inputWidthPowerFinalCfg,mapLabelCfg,liftCoreCfg,
      lensReturnCfg,embedLiftedWidthPowerLabel]
  have heq:c=inputWidthCfg (.inr (.inr .addOne)) c.var c.stk:=by
    cases hcfg:c with
    | mk l v s =>
        have hl:l=some (.inr (.inr .addOne)):=by
          simpa [hcfg] using hc
        subst l
        rfl
  have hadd:=inputWidth_addOne_step p c.var c.stk
  rw [← heq] at hadd
  change TM2.step (inputWidthProgram p) c=some
    { c with
      l:=some (.inr (.inr .ready))
      stk:=Function.update c.stk (.core .work3)
        (.wordEnd::c.stk (.core .work3)) }
  exact hadd

theorem inputWidth_complete_run {N:Nat} (p:Polynomial Nat)
    (x:List Nat) (state:WrapperState N):
    ((fun o => o.bind (TM2.step (inputWidthProgram p)))^[
        4 * bitSize x + (simpleMajorantEvalCostPolynomial p).eval (bitSize x) + 5])
      (some (inputWidthCfg (.inl .scan) {state with heldInput:=none}
        (inputWidthInitialStacks (encode x)))) =
    some (inputWidthReadyCfg p (bitSize x)
      {state with heldInput:=none} (inputWidthScannedStacks (encode x))):=by
  have hscan:=inputWidth_scan_run (N:=N) p (encode x) state
  have hbridge:=inputWidth_scan_bridge_powerStart (N:=N) p
    (encode x) (bitSize x) (by simp [bitSize]) {state with heldInput:=none}
  have hpower:=inputWidth_power_run (N:=N) p (bitSize x)
    {state with heldInput:=none} (inputWidthScannedStacks (encode x))
  have hadd:=inputWidth_power_addOne (N:=N) p (bitSize x)
    {state with heldInput:=none} (inputWidthScannedStacks (encode x))
  have liftStep {a b:TM2.Cfg WrapperAlphabet (InputWidthLabel p)
      (WrapperState N)} (hs:TM2.step (inputWidthProgram p) a=some b):
      ((fun o => o.bind (TM2.step (inputWidthProgram p)))^[1])
        (some a)=some b:=by
    simpa
  have hbridge':=liftStep hbridge
  have hadd':=liftStep hadd
  have hbridgePower:=chain_iterations _ hbridge' hpower
  have htail:=chain_iterations _ hbridgePower hadd'
  have h:=chain_iterations _ hscan htail
  rw [simpleMajorantEvalCostPolynomial_eval] at h
  rw [show (4 * (encode x).length + 2) +
      (1 + (unaryPowerCost (polyCoeffSum p) (bitSize x + 1)
        p.natDegree + 1) + 1) =
      4 * (encode x).length +
        unaryPowerCost (polyCoeffSum p) (bitSize x + 1)
          p.natDegree + 5 by omega] at h
  simpa only [bitSize,simpleMajorantEvalCostPolynomial_eval] using h

end

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def incrementBits:Bool→ List Bool→ List Bool
  | _, [] => []
  | carry,bit::bits =>
      Bool.xor bit carry::incrementBits (bit && carry) bits

theorem incrementBits_eq_addBits (carry:Bool) (bits:List Bool):
    incrementBits carry bits =
      addBits bits (List.replicate bits.length false) carry:=by
  induction bits generalizing carry with
  | nil => rfl
  | cons bit bits ih =>
      cases bit <;> cases carry <;>
        simp [incrementBits,addBits,fullAdder,ih,List.replicate_succ]

theorem incrementBits_fixedBits (w n:Nat):
    incrementBits true (fixedBits w n)=fixedBits w (n + 1):=by
  rw [incrementBits_eq_addBits]
  have hz:List.replicate (fixedBits w n).length false=fixedBits w 0:=by
    simp [fixedBits_zero]
  rw [hz, ← fixedBits_add_carry]
  simp

structure IncrementControl where
  carry:Bool:=true
  held:Option SparseSymbol:=none
  deriving DecidableEq,Fintype

instance:Inhabited IncrementControl:= ⟨⟨true,none⟩⟩

inductive IncrementStack | word | temp
  deriving DecidableEq,Fintype,Inhabited

inductive IncrementLabel | scan | restore | done
  deriving DecidableEq,Fintype,Inhabited

def incrementProgram:IncrementLabel→
    TM2.Stmt (fun _:IncrementStack => SparseSymbol)
      IncrementLabel IncrementControl
  | .scan =>
      .pop .word (fun s a => {s with held:=a}) <|
      .branch (fun s => s.held.isNone)
        (.goto fun _ => .restore) <|
      .push .temp (fun s => .bit
        (Bool.xor (s.held.getD (.bit false)).bitValue s.carry)) <|
      .load (fun s => {s with
        carry:=(s.held.getD (.bit false)).bitValue && s.carry,
        held:=none}) <|
      .goto fun _ => .scan
  | .restore =>
      .pop .temp (fun s a => {s with held:=a}) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .done) <|
      .push .word (fun s => s.held.getD default) <|
      .load (fun s => {s with held:=none}) <|
      .goto fun _ => .restore
  | .done => .halt

def incrementStacks (word temp:List SparseSymbol):
    IncrementStack→ List SparseSymbol
  | .word => word
  | .temp => temp

def incrementCfg (label:IncrementLabel) (carry:Bool)
    (word temp:List SparseSymbol):
    TM2.Cfg (fun _:IncrementStack => SparseSymbol)
      IncrementLabel IncrementControl:=
  ⟨some label, ⟨carry,none⟩,incrementStacks word temp⟩

theorem increment_scan_step (carry bit:Bool) (bits:List Bool)
    (temp:List SparseSymbol):
    TM2.step incrementProgram
      (incrementCfg .scan carry (.bit bit::bits.map SparseSymbol.bit) temp) =
    some (incrementCfg .scan (bit && carry) (bits.map SparseSymbol.bit)
      (.bit (Bool.xor bit carry)::temp)):=by
  simp [incrementProgram,incrementCfg,incrementStacks,TM2.step,
    Function.update]
  funext k
  cases k <;> rfl

theorem increment_scan_from (carry:Bool) (bits:List Bool)
    (temp:List SparseSymbol):
    ((fun o => o.bind (TM2.step incrementProgram))^[bits.length + 1])
      (some (incrementCfg .scan carry (bits.map SparseSymbol.bit) temp)) =
    some (incrementCfg .restore
      (addCarryOut bits (List.replicate bits.length false) carry) []
      ((incrementBits carry bits).reverse.map SparseSymbol.bit ++ temp)):=by
  induction bits generalizing carry temp with
  | nil => simp [incrementProgram,incrementCfg,incrementStacks,TM2.step,
      incrementBits,addCarryOut]
  | cons bit bits ih =>
      have hs:=increment_scan_step carry bit bits temp
      have hs':((fun o => o.bind (TM2.step incrementProgram))^[1])
          (some (incrementCfg .scan carry
            (.bit bit::bits.map SparseSymbol.bit) temp)) =
          some (incrementCfg .scan (bit && carry)
            (bits.map SparseSymbol.bit)
            (.bit (Bool.xor bit carry)::temp)):=by simpa using hs
      have hr:=ih (bit && carry)
        (.bit (Bool.xor bit carry)::temp)
      have h:=chain_iterations _ hs' hr
      rw [List.length_cons,
        show bits.length + 1 + 1=1 + (bits.length + 1) by omega]
      cases bit <;> cases carry <;>
        simpa [incrementBits,addCarryOut,fullAdder,
          List.reverse_cons,List.append_assoc,List.replicate_succ] using h

theorem increment_scan (carry:Bool) (bits:List Bool):
    ((fun o => o.bind (TM2.step incrementProgram))^[bits.length + 1])
      (some (incrementCfg .scan carry (bits.map SparseSymbol.bit) [])) =
    some (incrementCfg .restore
      (addCarryOut bits (List.replicate bits.length false) carry) []
      ((incrementBits carry bits).reverse.map SparseSymbol.bit)):=by
  simpa using increment_scan_from carry bits []

theorem increment_restore_from (carry:Bool) (source target:List SparseSymbol):
    ((fun o => o.bind (TM2.step incrementProgram))^[source.length + 1])
      (some (incrementCfg .restore carry target source)) =
    some (incrementCfg .done true (source.reverse ++ target) []):=by
  induction source generalizing carry target with
  | nil =>
      cases carry <;>
        simp [incrementProgram,incrementCfg,incrementStacks,TM2.step]
      all_goals change (default:IncrementControl)=⟨true,none⟩
      all_goals rfl
  | cons a source ih =>
      have hs:TM2.step incrementProgram
          (incrementCfg .restore carry target (a::source)) =
          some (incrementCfg .restore carry (a::target) source):=by
        simp [incrementProgram,incrementCfg,incrementStacks,TM2.step,
          Function.update]
        funext k
        cases k <;> rfl
      have hs':((fun o => o.bind (TM2.step incrementProgram))^[1])
          (some (incrementCfg .restore carry target (a::source))) =
          some (incrementCfg .restore carry (a::target) source):=by
        simpa using hs
      have h:=chain_iterations _ hs' (ih carry (a::target))
      rw [List.length_cons,
        show source.length + 1 + 1=1 + (source.length + 1) by omega]
      simpa [List.reverse_cons,List.append_assoc] using h

theorem increment_restore (carry:Bool) (bits:List Bool):
    ((fun o => o.bind (TM2.step incrementProgram))^[bits.length + 1])
      (some (incrementCfg .restore carry []
        (bits.reverse.map SparseSymbol.bit))) =
    some (incrementCfg .done true (bits.map SparseSymbol.bit) []):=by
  have h:=increment_restore_from carry
    (bits.reverse.map SparseSymbol.bit) []
  simpa [List.map_reverse] using h

theorem increment_correct (carry:Bool) (bits:List Bool):
    ((fun o => o.bind (TM2.step incrementProgram))^[2 * bits.length + 2])
      (some (incrementCfg .scan carry (bits.map SparseSymbol.bit) [])) =
    some (incrementCfg .done true
      ((incrementBits carry bits).map SparseSymbol.bit) []):=by
  have hs:=increment_scan carry bits
  have hr:=increment_restore
    (addCarryOut bits (List.replicate bits.length false) carry)
    (incrementBits carry bits)
  have h:=chain_iterations _ hs hr
  have hlen:(incrementBits carry bits).length=bits.length:=by
    simp [incrementBits_eq_addBits,addBits_length_of_eq]
  rw [hlen] at h
  rw [show (bits.length + 1) + (bits.length + 1) =
    2 * bits.length + 2 by omega] at h
  exact h

theorem increment_fixed_correct (w n:Nat):
    ((fun o => o.bind (TM2.step incrementProgram))^[2 * w + 2])
      (some (incrementCfg .scan true
        ((fixedBits w n).map SparseSymbol.bit) [])) =
    some (incrementCfg .done true
      ((fixedBits w (n + 1)).map SparseSymbol.bit) []):=by
  simpa [incrementBits_fixedBits] using
    increment_correct true (fixedBits w n)

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive CountIncrementStack | count | word | temp
  deriving DecidableEq,Fintype,Inhabited

inductive CountIncrementOuterLabel | loop | done
  deriving DecidableEq,Fintype,Inhabited

abbrev CountIncrementLabel:=Sum IncrementLabel CountIncrementOuterLabel

def incrementCountRenaming:StackRenaming IncrementStack CountIncrementStack where
  encode
    | .word => .word
    | .temp => .temp
  decode
    | .word => some .word
    | .temp => some .temp
    | .count => none
  decode_encode:=by intro k; cases k <;> rfl
  encode_decode:=by
    intro k' k h
    cases k' <;> cases k <;> simp_all

def incrementControlLens:StateLens IncrementControl IncrementControl where
  get:=id
  put:=fun _ inner => inner
  get_put:=by intros; rfl
  put_get:=by intros; rfl
  put_put:=by intros; rfl

def countIncrementOuterProgram:CountIncrementOuterLabel→
    TM2.Stmt (fun _:CountIncrementStack => SparseSymbol)
      CountIncrementLabel IncrementControl
  | .loop =>
      .pop .count (fun s a => {s with held:=a}) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .inr .done)
        (.load (fun _ => default) <| .goto fun _ => .inl .scan)
  | .done => .halt

def countIncrementProgram:CountIncrementLabel→
    TM2.Stmt (fun _:CountIncrementStack => SparseSymbol)
      CountIncrementLabel IncrementControl:=
  lensSpliceProgram incrementCountRenaming incrementControlLens
    incrementProgram .done CountIncrementOuterLabel.loop
    countIncrementOuterProgram

def countIncrementStacks (count word temp:List SparseSymbol):
    CountIncrementStack→ List SparseSymbol
  | .count => count
  | .word => word
  | .temp => temp

def countIncrementCfg (label:CountIncrementLabel)
    (count word temp:List SparseSymbol):
    TM2.Cfg (fun _:CountIncrementStack => SparseSymbol)
      CountIncrementLabel IncrementControl:=
  ⟨some label,default,countIncrementStacks count word temp⟩

def countIncrementCfgState (label:CountIncrementLabel) (control:IncrementControl)
    (count word temp:List SparseSymbol):
    TM2.Cfg (fun _:CountIncrementStack => SparseSymbol)
      CountIncrementLabel IncrementControl:=
  ⟨some label,control,countIncrementStacks count word temp⟩

@[simp] theorem countIncrement_outer_cons_from (control:IncrementControl)
    (count word:List SparseSymbol):
    TM2.step countIncrementProgram
      (countIncrementCfgState (.inr .loop) control (.wordEnd::count) word []) =
    some (countIncrementCfg (.inl .scan) count word []):=by
  simp [countIncrementProgram,lensSpliceProgram,countIncrementOuterProgram,
    countIncrementCfgState,countIncrementCfg,countIncrementStacks,TM2.step]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem countIncrement_outer_nil_from (control:IncrementControl)
    (word:List SparseSymbol):
    TM2.step countIncrementProgram
      (countIncrementCfgState (.inr .loop) control [] word []) =
    some (countIncrementCfg (.inr .done) [] word []):=by
  simp [countIncrementProgram,lensSpliceProgram,countIncrementOuterProgram,
    countIncrementCfgState,countIncrementCfg,countIncrementStacks,TM2.step]

@[simp] theorem countIncrement_outer_cons (count word:List SparseSymbol):
    TM2.step countIncrementProgram
      (countIncrementCfg (.inr .loop) (.wordEnd::count) word []) =
    some (countIncrementCfg (.inl .scan) count word []):=by
  simp [countIncrementProgram,lensSpliceProgram,countIncrementOuterProgram,
    countIncrementCfg,countIncrementStacks,TM2.step]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem countIncrement_outer_nil (word:List SparseSymbol):
    TM2.step countIncrementProgram
      (countIncrementCfg (.inr .loop) [] word []) =
    some (countIncrementCfg (.inr .done) [] word []):=by
  simp [countIncrementProgram,lensSpliceProgram,countIncrementOuterProgram,
    countIncrementCfg,countIncrementStacks,TM2.step]

theorem countIncrement_one {count:List SparseSymbol} (w n:Nat):
    ((fun o => o.bind (TM2.step countIncrementProgram))^[2 * w + 4])
      (some (countIncrementCfg (.inr .loop) (.wordEnd::count)
        ((fixedBits w n).map SparseSymbol.bit) [])) =
    some (countIncrementCfg (.inr .loop) count
      ((fixedBits w (n + 1)).map SparseSymbol.bit) []):=by
  have houter:
      ((fun o => o.bind (TM2.step countIncrementProgram))^[1])
        (some (countIncrementCfg (.inr .loop) (.wordEnd::count)
          ((fixedBits w n).map SparseSymbol.bit) [])) =
      some (countIncrementCfg (.inl .scan) count
        ((fixedBits w n).map SparseSymbol.bit) []):=by
    simpa using countIncrement_outer_cons count
      ((fixedBits w n).map SparseSymbol.bit)
  have hlocal:=transport_lensHaltingMacro_and_return
    incrementCountRenaming incrementControlLens incrementProgram .done (by rfl)
    CountIncrementOuterLabel.loop countIncrementOuterProgram
    (increment_fixed_correct w n) rfl default
    (countIncrementStacks count [] [])
  have hlocal':
      ((fun o => o.bind (TM2.step countIncrementProgram))^[2 * w + 3])
        (some (countIncrementCfg (.inl .scan) count
          ((fixedBits w n).map SparseSymbol.bit) [])) =
      some (countIncrementCfg (.inr .loop) count
        ((fixedBits w (n + 1)).map SparseSymbol.bit) []):=by
    convert hlocal using 1
    case e'_2 =>
      unfold countIncrementProgram
      rw [show 2 * w + 3=2 * w + 2 + 1 by omega]
      congr 2
      simp [countIncrementCfg,lensRenamedCfg,incrementCfg,
        incrementStacks,renamedStacks,incrementCountRenaming,
        incrementControlLens,countIncrementStacks]
      constructor
      · change (default:IncrementControl)=⟨true,none⟩
        rfl
      · funext k
        cases k <;> rfl
    case e'_3 =>
      congr 1
      simp [countIncrementCfg,lensReturnCfg,incrementCfg,
        incrementStacks,renamedStacks,incrementCountRenaming,
        incrementControlLens,countIncrementStacks]
      constructor
      · change (default:IncrementControl)=⟨true,none⟩
        rfl
      · funext k
        cases k <;> rfl
  have h:=chain_iterations _ houter hlocal'
  rw [show 1 + (2 * w + 3)=2 * w + 4 by omega] at h
  exact h

theorem countIncrement_iterate (count w n:Nat):
    ((fun o => o.bind (TM2.step countIncrementProgram))^[count * (2 * w + 4)])
      (some (countIncrementCfg (.inr .loop) (unaryMarkers count)
        ((fixedBits w n).map SparseSymbol.bit) [])) =
    some (countIncrementCfg (.inr .loop) []
      ((fixedBits w (n + count)).map SparseSymbol.bit) []):=by
  induction count generalizing n with
  | zero => simp [unaryMarkers]
  | succ count ih =>
      rw [Nat.add_mul count 1 (2 * w + 4),one_mul,
        Nat.add_comm (count * (2 * w + 4)) (2 * w + 4)]
      have hone:=countIncrement_one (count:=unaryMarkers count) w n
      have h:=chain_iterations _ hone (ih (n + 1))
      simpa only [unaryMarkers,List.replicate_succ,Nat.add_assoc,
        Nat.add_comm,Nat.add_left_comm] using h

theorem countIncrement_correct (count w:Nat):
    ((fun o => o.bind (TM2.step countIncrementProgram))^[
        count * (2 * w + 4) + 1])
      (some (countIncrementCfg (.inr .loop) (unaryMarkers count)
        ((fixedBits w 0).map SparseSymbol.bit) [])) =
    some (countIncrementCfg (.inr .done) []
      ((fixedBits w count).map SparseSymbol.bit) []):=by
  rw [Nat.add_comm,Function.iterate_add_apply,countIncrement_iterate]
  simp only [zero_add,Function.iterate_one,Option.bind_some,
    countIncrement_outer_nil]

theorem countIncrement_correct_from (control:IncrementControl)
    (count w:Nat):
    ((fun o => o.bind (TM2.step countIncrementProgram))^[
        count * (2 * w + 4) + 1])
      (some (countIncrementCfgState (.inr .loop) control (unaryMarkers count)
        ((fixedBits w 0).map SparseSymbol.bit) [])) =
    some (countIncrementCfg (.inr .done) []
      ((fixedBits w count).map SparseSymbol.bit) []):=by
  cases count with
  | zero =>
      simpa [unaryMarkers] using countIncrement_outer_nil_from control
        ((fixedBits w 0).map SparseSymbol.bit)
  | succ count =>
      have htail:=countIncrement_correct (count + 1) w
      have hcost:(count + 1) * (2 * w + 4) + 1 =
        1 + ((2 * w + 3) + count * (2 * w + 4) + 1):=by
          rw [Nat.add_mul count 1 (2 * w + 4),one_mul]
          omega
      rw [hcost,Function.iterate_add_apply] at htail ⊢
      simp only [Function.iterate_one,Option.bind_some,
        countIncrement_outer_cons_from,countIncrement_outer_cons] at htail ⊢
      simpa [unaryMarkers,List.replicate_succ] using htail

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive UnaryZeroStack | width | word | backup
  deriving DecidableEq,Fintype,Inhabited

inductive UnaryZeroLabel | copy | restore | done
  deriving DecidableEq,Fintype,Inhabited

def unaryZeroProgram:UnaryZeroLabel→
    TM2.Stmt (fun _:UnaryZeroStack => SparseSymbol)
      UnaryZeroLabel SymbolMoveControl
  | .copy =>
      .pop .width (fun _ a => ⟨a⟩) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .restore)
        (.push .word (fun _ => .bit false) <|
          .push .backup (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .copy)
  | .restore =>
      .pop .backup (fun _ a => ⟨a⟩) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .done)
        (.push .width (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .restore)
  | .done => .halt

def unaryZeroStacks (width word backup:List SparseSymbol):
    UnaryZeroStack→ List SparseSymbol
  | .width => width
  | .word => word
  | .backup => backup

def unaryZeroCfg (label:UnaryZeroLabel)
    (width word backup:List SparseSymbol):
    TM2.Cfg (fun _:UnaryZeroStack => SparseSymbol)
      UnaryZeroLabel SymbolMoveControl:=
  ⟨some label,default,unaryZeroStacks width word backup⟩

theorem unaryZero_copy_from (width word backup:List SparseSymbol):
    ((fun o => o.bind (TM2.step unaryZeroProgram))^[width.length + 1])
      (some (unaryZeroCfg .copy width word backup)) =
    some (unaryZeroCfg .restore []
      (List.replicate width.length (.bit false) ++ word)
      (width.reverse ++ backup)):=by
  induction width generalizing word backup with
  | nil => simp [unaryZeroProgram,unaryZeroCfg,unaryZeroStacks,TM2.step]
  | cons a width ih =>
      have hs:TM2.step unaryZeroProgram
          (unaryZeroCfg .copy (a::width) word backup) =
          some (unaryZeroCfg .copy width (.bit false::word)
            (a::backup)):=by
        simp [unaryZeroProgram,unaryZeroCfg,unaryZeroStacks,TM2.step,
          Function.update]
        funext k
        cases k <;> rfl
      have hs':((fun o => o.bind (TM2.step unaryZeroProgram))^[1])
          (some (unaryZeroCfg .copy (a::width) word backup)) =
          some (unaryZeroCfg .copy width (.bit false::word)
            (a::backup)):=by simpa using hs
      have h:=chain_iterations _ hs'
        (ih (.bit false::word) (a::backup))
      rw [show List.replicate width.length (.bit false) ++
          .bit false::word =
          List.replicate (width.length + 1) (.bit false) ++ word by
        simp [List.replicate_add,List.append_assoc]] at h
      rw [List.length_cons,
        show width.length + 1 + 1=1 + (width.length + 1) by omega]
      simpa [List.replicate_succ,List.reverse_cons,
        List.append_assoc] using h

theorem unaryZero_copy (width:List SparseSymbol):
    ((fun o => o.bind (TM2.step unaryZeroProgram))^[width.length + 1])
      (some (unaryZeroCfg .copy width [] [])) =
    some (unaryZeroCfg .restore []
      (List.replicate width.length (.bit false)) width.reverse):=by
  simpa using unaryZero_copy_from width [] []

theorem unaryZero_restore_from (source target word:List SparseSymbol):
    ((fun o => o.bind (TM2.step unaryZeroProgram))^[source.length + 1])
      (some (unaryZeroCfg .restore target word source)) =
    some (unaryZeroCfg .done (source.reverse ++ target) word []):=by
  induction source generalizing target with
  | nil => simp [unaryZeroProgram,unaryZeroCfg,unaryZeroStacks,TM2.step]
  | cons a source ih =>
      have hs:TM2.step unaryZeroProgram
          (unaryZeroCfg .restore target word (a::source)) =
          some (unaryZeroCfg .restore (a::target) word source):=by
        simp [unaryZeroProgram,unaryZeroCfg,unaryZeroStacks,TM2.step,
          Function.update]
        funext k
        cases k <;> rfl
      have hs':((fun o => o.bind (TM2.step unaryZeroProgram))^[1])
          (some (unaryZeroCfg .restore target word (a::source))) =
          some (unaryZeroCfg .restore (a::target) word source):=by
        simpa using hs
      have h:=chain_iterations _ hs' (ih (a::target))
      rw [List.length_cons,
        show source.length + 1 + 1=1 + (source.length + 1) by omega]
      simpa [List.reverse_cons,List.append_assoc] using h

theorem unaryZero_restore (width word:List SparseSymbol):
    ((fun o => o.bind (TM2.step unaryZeroProgram))^[width.length + 1])
      (some (unaryZeroCfg .restore [] word width.reverse)) =
    some (unaryZeroCfg .done width word []):=by
  simpa using unaryZero_restore_from width.reverse [] word

theorem unaryZero_correct (w:Nat):
    ((fun o => o.bind (TM2.step unaryZeroProgram))^[2 * w + 2])
      (some (unaryZeroCfg .copy (unaryMarkers w) [] [])) =
    some (unaryZeroCfg .done (unaryMarkers w)
      ((fixedBits w 0).map SparseSymbol.bit) []):=by
  have hc:=unaryZero_copy (unaryMarkers w)
  have hr:=unaryZero_restore (unaryMarkers w)
    (List.replicate w (.bit false))
  simp only [unaryMarkers,List.length_replicate] at hc hr
  have h:=chain_iterations _ hc hr
  rw [show (w + 1) + (w + 1)=2 * w + 2 by omega] at h
  simpa [unaryMarkers,fixedBits_zero] using h

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

noncomputable section

def unaryZeroWrapperRenaming:StackRenaming UnaryZeroStack CoreStack where
  encode
    | .width => .work3
    | .word => .work6
    | .backup => .work7
  decode
    | .work3 => some .width
    | .work6 => some .word
    | .work7 => some .backup
    | _ => none
  decode_encode:=by intro k; cases k <;> rfl
  encode_decode:=by
    intro k' k h
    cases k <;> cases k' <;> simp_all

def unaryZeroWrapperLens {N:Nat}:
    StateLens SymbolMoveControl (FullInterpreterState N):=
  FullInterpreterState.moveLens

def countIncrementWrapperRenaming:
    StackRenaming CountIncrementStack CoreStack where
  encode
    | .count => .work2
    | .word => .work6
    | .temp => .work7
  decode
    | .work2 => some .count
    | .work6 => some .word
    | .work7 => some .temp
    | _ => none
  decode_encode:=by intro k; cases k <;> rfl
  encode_decode:=by
    intro k' k h
    cases k <;> cases k' <;> simp_all

def incrementWrapperLens {N:Nat}:
    StateLens IncrementControl (FullInterpreterState N) where
  get s:= ⟨s.lookupFound, (FullInterpreterState.moveLens.get s).held⟩
  put s c:=FullInterpreterState.moveLens.put
    {s with lookupFound:=c.carry} ⟨c.held⟩
  get_put:=by intros; rfl
  put_get:=by intro s; cases s <;> rfl
  put_put:=by intros; rfl

abbrev LengthPrefixLabel:=
  Sum UnaryZeroLabel (Sum CountIncrementLabel Unit)

def zeroCoreSplice {N:Nat}:
    Sum UnaryZeroLabel Unit→
      TM2.Stmt (fun _:CoreStack => SparseSymbol)
        (Sum UnaryZeroLabel Unit) (FullInterpreterState N):=
  lensSpliceProgram unaryZeroWrapperRenaming unaryZeroWrapperLens
    unaryZeroProgram .done () (fun _ => .halt)

def countCoreSplice {N:Nat}:
    Sum CountIncrementLabel Unit→
      TM2.Stmt (fun _:CoreStack => SparseSymbol)
        (Sum CountIncrementLabel Unit) (FullInterpreterState N):=
  lensSpliceProgram countIncrementWrapperRenaming incrementWrapperLens
    countIncrementProgram (.inr .done) () (fun _ => .halt)

def embedLiftedZeroLengthLabel:Sum (Sum UnaryZeroLabel Unit) Empty→
    LengthPrefixLabel
  | .inl (.inl label) => .inl label
  | .inl (.inr ()) => .inr (.inl (.inr .loop))
  | .inr impossible => nomatch impossible

def embedLiftedCountLengthLabel:Sum (Sum CountIncrementLabel Unit) Empty→
    LengthPrefixLabel
  | .inl (.inl label) => .inr (.inl label)
  | .inl (.inr ()) => .inr (.inr ())
  | .inr impossible => nomatch impossible

def lengthPrefixProgram {N:Nat}:LengthPrefixLabel→
    TM2.Stmt WrapperAlphabet LengthPrefixLabel (WrapperState N)
  | .inl .done => .goto fun _ => .inr (.inl (.inr .loop))
  | .inl label =>
      mapLabelStmt embedLiftedZeroLengthLabel <|
        liftCoreStmt (N:=N) (X:=Empty)
          (zeroCoreSplice (.inl label))
  | .inr (.inl (.inr .done)) => .goto fun _ => .inr (.inr ())
  | .inr (.inl label) =>
      mapLabelStmt embedLiftedCountLengthLabel <|
        liftCoreStmt (N:=N) (X:=Empty)
          (countCoreSplice (.inl label))
  | .inr (.inr ()) => .halt

def lengthPrefixCfg {N:Nat} (label:LengthPrefixLabel)
    (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    TM2.Cfg WrapperAlphabet LengthPrefixLabel (WrapperState N):=
  ⟨some label,state,tapes⟩

def zeroWrapperSplice {N:Nat}:
    Sum (Sum UnaryZeroLabel Unit) Empty→
      TM2.Stmt WrapperAlphabet (Sum (Sum UnaryZeroLabel Unit) Empty)
        (WrapperState N):=
  liftCoreProgram (zeroCoreSplice (N:=N))
    (fun impossible:Empty => nomatch impossible)

theorem lengthPrefix_zero_run {N w:Nat} (state:WrapperState N)
    (ambient:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun o => o.bind (TM2.step lengthPrefixProgram))^[2 * w + 3])
      (some (mapLabelCfg embedLiftedZeroLengthLabel
        (liftCoreCfg (X:=Empty)
          (lensRenamedCfg unaryZeroWrapperRenaming unaryZeroWrapperLens
            (unaryZeroCfg .copy (unaryMarkers w) [] []) state.core
            (fun k => ambient (.core k))) state
          (ambient .input) (ambient .output)))) =
    some (mapLabelCfg embedLiftedZeroLengthLabel
      (liftCoreCfg (X:=Empty)
        (lensReturnCfg unaryZeroWrapperRenaming unaryZeroWrapperLens ()
        (unaryZeroCfg .done (unaryMarkers w)
          ((fixedBits w 0).map SparseSymbol.bit) []) state.core
          (fun k => ambient (.core k))) state
        (ambient .input) (ambient .output))):=by
  have hcore:=transport_lensHaltingMacro_and_return
    unaryZeroWrapperRenaming unaryZeroWrapperLens unaryZeroProgram .done (by rfl)
    () (fun _ => .halt) (unaryZero_correct w) rfl state.core
    (fun k => ambient (.core k))
  rw [show 2 * w + 2 + 1=2 * w + 3 by omega] at hcore
  have hlift:=iterate_liftCoreProgram (zeroCoreSplice (N:=N))
    (fun impossible:Empty => nomatch impossible) _ _ state
    (ambient .input) (ambient .output) hcore
  apply iterate_mapLabelProgram_until_exit (zeroWrapperSplice (N:=N))
    lengthPrefixProgram embedLiftedZeroLengthLabel ?_ hlift (by rfl)
  · intro label hnonhalt
    cases label with
    | inl label =>
        cases label with
        | inl label => cases label <;>
            simp [lengthPrefixProgram,zeroWrapperSplice,
              zeroCoreSplice,liftCoreProgram,lensSpliceProgram,
              liftCoreStmt,mapLabelStmt,lensRenameStmt,
              embedLiftedZeroLengthLabel] at hnonhalt ⊢
        | inr unit => cases unit
                      exact (hnonhalt rfl).elim
    | inr impossible => nomatch impossible

def countWrapperSplice {N:Nat}:
    Sum (Sum CountIncrementLabel Unit) Empty→
      TM2.Stmt WrapperAlphabet (Sum (Sum CountIncrementLabel Unit) Empty)
        (WrapperState N):=
  liftCoreProgram (countCoreSplice (N:=N))
    (fun impossible:Empty => nomatch impossible)

theorem lengthPrefix_count_run_from {N count w:Nat} (state:WrapperState N)
    (ambient:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun o => o.bind (TM2.step lengthPrefixProgram))^[
        count * (2 * w + 4) + 2])
      (some (mapLabelCfg embedLiftedCountLengthLabel
        (liftCoreCfg (X:=Empty)
          (lensRenamedCfg countIncrementWrapperRenaming incrementWrapperLens
          (countIncrementCfgState (.inr .loop)
            (incrementWrapperLens.get state.core) (unaryMarkers count)
            ((fixedBits w 0).map SparseSymbol.bit) []) state.core
            (fun k => ambient (.core k))) state
          (ambient .input) (ambient .output)))) =
    some (mapLabelCfg embedLiftedCountLengthLabel
      (liftCoreCfg (X:=Empty)
        (lensReturnCfg countIncrementWrapperRenaming incrementWrapperLens ()
        (countIncrementCfg (.inr .done) []
          ((fixedBits w count).map SparseSymbol.bit) []) state.core
          (fun k => ambient (.core k))) state
        (ambient .input) (ambient .output))):=by
  have hcore:=transport_lensHaltingMacro_and_return
    countIncrementWrapperRenaming incrementWrapperLens countIncrementProgram
    (.inr .done) (by rfl) () (fun _ => .halt)
    (countIncrement_correct_from (incrementWrapperLens.get state.core) count w)
    rfl state.core (fun k => ambient (.core k))
  rw [show count * (2 * w + 4) + 1 + 1 =
    count * (2 * w + 4) + 2 by omega] at hcore
  have hlift:=iterate_liftCoreProgram (countCoreSplice (N:=N))
    (fun impossible:Empty => nomatch impossible) _ _ state
    (ambient .input) (ambient .output) hcore
  apply iterate_mapLabelProgram_until_exit (countWrapperSplice (N:=N))
    lengthPrefixProgram embedLiftedCountLengthLabel ?_ hlift (by rfl)
  · intro label hnonhalt
    cases label with
    | inl label =>
        cases label with
        | inl label =>
            rcases label with label | label <;> cases label <;>
              simp [lengthPrefixProgram,countWrapperSplice,
                countCoreSplice,liftCoreProgram,lensSpliceProgram,
                liftCoreStmt,mapLabelStmt,lensRenameStmt,
                embedLiftedCountLengthLabel] at hnonhalt ⊢
        | inr unit => cases unit
                      exact (hnonhalt rfl).elim
    | inr impossible => nomatch impossible

def lengthPrefixInitialStacks (w count:Nat)
    (base:(k:WrapperStack)→ List (WrapperAlphabet k)):
    (k:WrapperStack)→ List (WrapperAlphabet k):=
  Function.update
    (Function.update
      (Function.update
        (Function.update base (.core .work2) (unaryMarkers count))
          (.core .work3) (unaryMarkers w))
        (.core .work6) [])
      (.core .work7) []

def lengthPrefixFinalStacks (w count:Nat)
    (base:(k:WrapperStack)→ List (WrapperAlphabet k)):
    (k:WrapperStack)→ List (WrapperAlphabet k):=
  Function.update
    (Function.update
      (Function.update
        (Function.update base (.core .work2) [])
          (.core .work3) (unaryMarkers w))
        (.core .work6) ((fixedBits w count).map SparseSymbol.bit))
      (.core .work7) []

def lengthPrefixFinalState {N:Nat} (state:WrapperState N):
    WrapperState N:=
  let afterZero:=unaryZeroWrapperLens.put state.core default
  {state with core:=incrementWrapperLens.put afterZero default}

theorem lengthPrefix_complete {N w count:Nat} (state:WrapperState N)
    (base:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun o => o.bind (TM2.step lengthPrefixProgram))^[
        2 * w + 3 + (count * (2 * w + 4) + 2)])
      (some (lengthPrefixCfg (.inl .copy)
        {state with core:=unaryZeroWrapperLens.put state.core default}
        (lengthPrefixInitialStacks w count base))) =
    some (lengthPrefixCfg (.inr (.inr ()))
      (lengthPrefixFinalState state)
      (lengthPrefixFinalStacks w count base)):=by
  let state₁:WrapperState N:=
    {state with core:=unaryZeroWrapperLens.put state.core default}
  have hzero:=lengthPrefix_zero_run (N:=N) (w:=w) state
    (lengthPrefixInitialStacks w count base)
  have hcount:=lengthPrefix_count_run_from (N:=N) (count:=count) (w:=w)
    state₁ (lengthPrefixInitialStacks w count base)
  have hmid:
      mapLabelCfg embedLiftedZeroLengthLabel
        (liftCoreCfg (X:=Empty)
          (lensReturnCfg unaryZeroWrapperRenaming unaryZeroWrapperLens ()
            (unaryZeroCfg .done (unaryMarkers w)
              ((fixedBits w 0).map SparseSymbol.bit) []) state.core
            (fun k => lengthPrefixInitialStacks w count base (.core k)))
          state (lengthPrefixInitialStacks w count base .input)
          (lengthPrefixInitialStacks w count base .output)) =
      mapLabelCfg embedLiftedCountLengthLabel
        (liftCoreCfg (X:=Empty)
          (lensRenamedCfg countIncrementWrapperRenaming incrementWrapperLens
            (countIncrementCfgState (.inr .loop)
              (incrementWrapperLens.get state₁.core) (unaryMarkers count)
              ((fixedBits w 0).map SparseSymbol.bit) []) state₁.core
            (fun k => lengthPrefixInitialStacks w count base (.core k)))
          state₁ (lengthPrefixInitialStacks w count base .input)
          (lengthPrefixInitialStacks w count base .output)):=by
    simp [state₁,mapLabelCfg,liftCoreCfg,lensReturnCfg,lensRenamedCfg,
      unaryZeroCfg,unaryZeroStacks,countIncrementCfgState,
      countIncrementStacks,renamedStacks,unaryZeroWrapperRenaming,
      countIncrementWrapperRenaming,lengthPrefixInitialStacks,
      wrapperCoreStacks,
      fixedBits_zero,Function.update]
    constructor
    · rfl
    constructor
    · rw [(incrementWrapperLens (N:=N)).put_get]
      rfl
    · funext k
      cases k with
      | input | output => rfl
      | core k =>
          cases k <;> simp [wrapperCoreStacks,renamedStacks,
            unaryZeroWrapperRenaming,countIncrementWrapperRenaming,
            unaryZeroStacks,countIncrementStacks,
            lengthPrefixInitialStacks,Function.update]
  rw [← hmid] at hcount
  have h:=chain_iterations _ hzero hcount
  convert h using 1
  case e'_2 =>
    congr 2
    simp [lengthPrefixCfg,mapLabelCfg,liftCoreCfg,lensRenamedCfg,
      unaryZeroCfg,unaryZeroStacks,renamedStacks,
      unaryZeroWrapperRenaming,lengthPrefixInitialStacks,
      wrapperCoreStacks,Function.update]
    constructor
    · rfl
    constructor
    · rfl
    · funext k
      cases k with
      | input | output => rfl
      | core k => cases k <;> simp [renamedStacks,unaryZeroStacks,
          lengthPrefixInitialStacks,wrapperCoreStacks,Function.update] <;> rfl
  case e'_3 =>
    congr 2
    simp [lengthPrefixCfg,lengthPrefixFinalState,lengthPrefixFinalStacks,
      mapLabelCfg,liftCoreCfg,lensReturnCfg,countIncrementCfg,
      countIncrementStacks,renamedStacks,countIncrementWrapperRenaming,
      state₁,wrapperCoreStacks,lengthPrefixInitialStacks,
      Function.update]
    funext k
    cases k with
    | input | output => rfl
    | core k => cases k <;> simp [renamedStacks,countIncrementStacks,
        countIncrementWrapperRenaming,lengthPrefixInitialStacks,
        lengthPrefixFinalStacks,wrapperCoreStacks,Function.update] <;> rfl

end

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2
open Lax759944.BinaryWordEncoding

structure PaddingControl where
  held:Option SparseSymbol:=none
  more:Bool:=false
  deriving DecidableEq,Fintype,Inhabited

inductive PaddingStack | raw | width | counter | backup | output
  deriving DecidableEq,Fintype,Inhabited

inductive PaddingLabel | start | copy | restore | scan | pad | finish | done
  deriving DecidableEq,Fintype,Inhabited

def paddingProgram:PaddingLabel→
    TM2.Stmt (fun _:PaddingStack => SparseSymbol)
      PaddingLabel PaddingControl
  | .start =>
      .pop .raw (fun s a => {s with held:=a}) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .done)
        (.load (fun _ => default) <| .goto fun _ => .copy)
  | .copy =>
      .pop .width (fun s a => {s with held:=a}) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .restore)
        (.push .counter (fun s => s.held.getD default) <|
          .push .backup (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .copy)
  | .restore =>
      .pop .backup (fun s a => {s with held:=a}) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .scan)
        (.push .width (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .restore)
  | .scan =>
      .pop .raw (fun s a => {s with held:=a}) <|
      .branch (fun s => s.held.isNone)
        (.load (fun s => {s with more:=false,held:=none}) <|
          .goto fun _ => .pad) <|
      .branch (fun s => s.held=some .wordEnd)
        (.load (fun s => {s with more:=true,held:=none}) <|
          .goto fun _ => .pad) <|
      .pop .counter (fun s _ => s) <|
      .push .output (fun s => s.held.getD (.bit false)) <|
      .load (fun s => {s with held:=none}) <|
      .goto fun _ => .scan
  | .pad =>
      .pop .counter (fun s a => {s with held:=a}) <|
      .branch (fun s => s.held.isNone)
        (.load (fun s => {s with held:=none}) <| .goto fun _ => .finish)
        (.push .output (fun _ => .bit false) <|
          .load (fun s => {s with held:=none}) <| .goto fun _ => .pad)
  | .finish =>
      .push .output (fun _ => .wordEnd) <|
      .branch (fun s => s.more)
        (.load (fun _ => default) <| .goto fun _ => .copy)
        (.load (fun _ => default) <| .goto fun _ => .done)
  | .done => .halt

def paddingStacks (raw width counter backup output:List SparseSymbol):
    PaddingStack→ List SparseSymbol
  | .raw => raw
  | .width => width
  | .counter => counter
  | .backup => backup
  | .output => output

def paddingCfg (label:PaddingLabel) (control:PaddingControl)
    (raw width counter backup output:List SparseSymbol):
    TM2.Cfg (fun _:PaddingStack => SparseSymbol)
      PaddingLabel PaddingControl:=
  ⟨some label,control,paddingStacks raw width counter backup output⟩

theorem padding_copy_from (control:PaddingControl)
    (source raw counter backup output:List SparseSymbol):
    ((fun o => o.bind (TM2.step paddingProgram))^[source.length + 1])
      (some (paddingCfg .copy control raw source counter backup output)) =
    some (paddingCfg .restore default raw []
      (source.reverse ++ counter) (source.reverse ++ backup) output):=by
  induction source generalizing control counter backup with
  | nil => simp [paddingProgram,paddingCfg,paddingStacks,TM2.step]
  | cons a source ih =>
      have hs:TM2.step paddingProgram
          (paddingCfg .copy control raw (a::source) counter backup output) =
          some (paddingCfg .copy default raw source (a::counter)
            (a::backup) output):=by
        simp [paddingProgram,paddingCfg,paddingStacks,TM2.step,
          Function.update]
        funext k
        cases k <;> rfl
      have hs':((fun o => o.bind (TM2.step paddingProgram))^[1])
          (some (paddingCfg .copy control raw (a::source) counter backup output)) =
          some (paddingCfg .copy default raw source (a::counter)
            (a::backup) output):=by simpa using hs
      have h:=chain_iterations _ hs' (ih default (a::counter) (a::backup))
      rw [List.length_cons,
        show source.length + 1 + 1=1 + (source.length + 1) by omega]
      simpa [List.reverse_cons,List.append_assoc] using h

theorem padding_restore_from (source target raw counter output:List SparseSymbol):
    ((fun o => o.bind (TM2.step paddingProgram))^[source.length + 1])
      (some (paddingCfg .restore default raw target counter source output)) =
    some (paddingCfg .scan default raw (source.reverse ++ target)
      counter [] output):=by
  induction source generalizing target with
  | nil => simp [paddingProgram,paddingCfg,paddingStacks,TM2.step]
  | cons a source ih =>
      have hs:TM2.step paddingProgram
          (paddingCfg .restore default raw target counter (a::source) output) =
          some (paddingCfg .restore default raw (a::target) counter source output):=by
        simp [paddingProgram,paddingCfg,paddingStacks,TM2.step,
          Function.update]
        funext k
        cases k <;> rfl
      have hs':((fun o => o.bind (TM2.step paddingProgram))^[1])
          (some (paddingCfg .restore default raw target counter (a::source) output)) =
          some (paddingCfg .restore default raw (a::target) counter source output):=by
        simpa using hs
      have h:=chain_iterations _ hs' (ih (a::target))
      rw [List.length_cons,
        show source.length + 1 + 1=1 + (source.length + 1) by omega]
      simpa [List.reverse_cons,List.append_assoc] using h

theorem padding_copy_width (w:Nat) (control:PaddingControl)
    (raw output:List SparseSymbol):
    ((fun o => o.bind (TM2.step paddingProgram))^[2 * w + 2])
      (some (paddingCfg .copy control raw (unaryMarkers w) [] [] output)) =
    some (paddingCfg .scan default raw (unaryMarkers w)
      (unaryMarkers w) [] output):=by
  have hc:=padding_copy_from control (unaryMarkers w) raw [] [] output
  have hr:=padding_restore_from (unaryMarkers w).reverse [] raw
    (unaryMarkers w) output
  simp only [unaryMarkers,List.reverse_replicate,List.append_nil,
    List.length_replicate,List.reverse_reverse] at hc hr
  have h:=chain_iterations _ hc hr
  rw [show (w + 1) + (w + 1)=2 * w + 2 by omega] at h
  simpa [unaryMarkers] using h

theorem padding_scan_bits_from (bits:List Bool) (rest width:List SparseSymbol)
    (remaining:Nat) (hlen:bits.length≤ remaining)
    (output:List SparseSymbol):
    ((fun o => o.bind (TM2.step paddingProgram))^[bits.length])
      (some (paddingCfg .scan default
        (bits.map SparseSymbol.bit ++ rest) width
        (unaryMarkers remaining) [] output)) =
    some (paddingCfg .scan default rest width
      (unaryMarkers (remaining - bits.length)) []
      (bits.reverse.map SparseSymbol.bit ++ output)):=by
  induction bits generalizing remaining output with
  | nil => simp
  | cons bit bits ih =>
      simp only [List.length_cons] at hlen
      cases remaining with
      | zero => omega
      | succ remaining =>
          have ht:bits.length≤ remaining:=by omega
          have hs:TM2.step paddingProgram
              (paddingCfg .scan default
                (.bit bit::bits.map SparseSymbol.bit ++ rest)
                width (unaryMarkers (remaining + 1)) [] output) =
              some (paddingCfg .scan default
                (bits.map SparseSymbol.bit ++ rest) width
                (unaryMarkers remaining) [] (.bit bit::output)):=by
            simp [unaryMarkers,List.replicate_succ,paddingProgram,
              paddingCfg,paddingStacks,TM2.step,Function.update]
            constructor
            · rfl
            · funext k
              cases k <;> rfl
          have hs':((fun o => o.bind (TM2.step paddingProgram))^[1])
              (some (paddingCfg .scan default
                (.bit bit::bits.map SparseSymbol.bit ++ rest)
                width (unaryMarkers (remaining + 1)) [] output)) =
              some (paddingCfg .scan default
                (bits.map SparseSymbol.bit ++ rest) width
                (unaryMarkers remaining) [] (.bit bit::output)):=by simpa using hs
          have hr:=ih remaining ht (.bit bit::output)
          have h:=chain_iterations _ hs' hr
          rw [List.length_cons,
            show bits.length + 1=1 + bits.length by omega]
          rw [show remaining + 1 - (1 + bits.length) =
            remaining - bits.length by omega]
          simpa [List.reverse_cons,List.append_assoc] using h

theorem padding_scan_bits (bits:List Bool) (rest:List SparseSymbol)
    (w:Nat) (hlen:bits.length≤ w) (output:List SparseSymbol):
    ((fun o => o.bind (TM2.step paddingProgram))^[bits.length])
      (some (paddingCfg .scan default
        (bits.map SparseSymbol.bit ++ rest) (unaryMarkers w)
        (unaryMarkers w) [] output)) =
    some (paddingCfg .scan default rest (unaryMarkers w)
      (unaryMarkers (w - bits.length)) []
      (bits.reverse.map SparseSymbol.bit ++ output)):=
  padding_scan_bits_from bits rest (unaryMarkers w) w hlen output

theorem padding_pad (remaining:Nat) (more:Bool)
    (raw width output:List SparseSymbol):
    ((fun o => o.bind (TM2.step paddingProgram))^[remaining + 1])
      (some (paddingCfg .pad ⟨none,more⟩ raw width
        (unaryMarkers remaining) [] output)) =
    some (paddingCfg .finish ⟨none,more⟩ raw width [] []
      (List.replicate remaining (.bit false) ++ output)):=by
  induction remaining generalizing output with
  | zero => simp [unaryMarkers,paddingProgram,paddingCfg,paddingStacks,
      TM2.step]
  | succ remaining ih =>
      have hs:TM2.step paddingProgram
          (paddingCfg .pad ⟨none,more⟩ raw width
            (unaryMarkers (remaining + 1)) [] output) =
          some (paddingCfg .pad ⟨none,more⟩ raw width
            (unaryMarkers remaining) [] (.bit false::output)):=by
        simp [unaryMarkers,List.replicate_succ,paddingProgram,paddingCfg,
          paddingStacks,TM2.step,Function.update]
        funext k
        cases k <;> rfl
      have hs':((fun o => o.bind (TM2.step paddingProgram))^[1])
          (some (paddingCfg .pad ⟨none,more⟩ raw width
            (unaryMarkers (remaining + 1)) [] output)) =
          some (paddingCfg .pad ⟨none,more⟩ raw width
            (unaryMarkers remaining) [] (.bit false::output)):=by
        simpa using hs
      have h:=chain_iterations _ hs' (ih (.bit false::output))
      rw [show remaining + 1 + 1=1 + (remaining + 1) by omega]
      rw [show List.replicate remaining (.bit false) ++ .bit false::output =
          List.replicate (remaining + 1) (.bit false) ++ output by
        simp [List.replicate_add,List.append_assoc]] at h
      exact h

theorem padding_boundary_more (raw width counter output:List SparseSymbol):
    TM2.step paddingProgram
      (paddingCfg .scan default (.wordEnd::raw) width counter [] output) =
    some (paddingCfg .pad ⟨none,true⟩ raw width counter [] output):=by
  simp [paddingProgram,paddingCfg,paddingStacks,TM2.step,Function.update]
  funext k
  cases k <;> rfl

theorem padding_boundary_end (width counter output:List SparseSymbol):
    TM2.step paddingProgram
      (paddingCfg .scan default [] width counter [] output) =
    some (paddingCfg .pad ⟨none,false⟩ [] width counter [] output):=by
  simp [paddingProgram,paddingCfg,paddingStacks,TM2.step]

theorem padding_finish_more (raw width output:List SparseSymbol):
    TM2.step paddingProgram
      (paddingCfg .finish ⟨none,true⟩ raw width [] [] output) =
    some (paddingCfg .copy default raw width [] [] (.wordEnd::output)):=by
  simp [paddingProgram,paddingCfg,paddingStacks,TM2.step,Function.update]
  funext k
  cases k <;> rfl

theorem padding_finish_end (width output:List SparseSymbol):
    TM2.step paddingProgram
      (paddingCfg .finish ⟨none,false⟩ [] width [] [] output) =
    some (paddingCfg .done default [] width [] [] (.wordEnd::output)):=by
  simp [paddingProgram,paddingCfg,paddingStacks,TM2.step,Function.update]
  funext k
  cases k <;> rfl

theorem padding_word_more (w:Nat) (bits:List Bool)
    (hlen:bits.length≤ w) (rest output:List SparseSymbol):
    ((fun o => o.bind (TM2.step paddingProgram))^[3 * w + 5])
      (some (paddingCfg .copy default
        (bits.map SparseSymbol.bit ++ .wordEnd::rest)
        (unaryMarkers w) [] [] output)) =
    some (paddingCfg .copy default rest (unaryMarkers w) [] []
      (.wordEnd::List.replicate (w - bits.length) (.bit false) ++
        bits.reverse.map SparseSymbol.bit ++ output)):=by
  have hc:=padding_copy_width w default
    (bits.map SparseSymbol.bit ++ .wordEnd::rest) output
  have hs:=padding_scan_bits bits (.wordEnd::rest) w hlen output
  have hb:
      ((fun o => o.bind (TM2.step paddingProgram))^[1])
        (some (paddingCfg .scan default (.wordEnd::rest) (unaryMarkers w)
          (unaryMarkers (w - bits.length)) []
          (bits.reverse.map SparseSymbol.bit ++ output))) =
      some (paddingCfg .pad ⟨none,true⟩ rest (unaryMarkers w)
        (unaryMarkers (w - bits.length)) []
        (bits.reverse.map SparseSymbol.bit ++ output)):=by
    simpa using padding_boundary_more rest (unaryMarkers w)
      (unaryMarkers (w - bits.length))
      (bits.reverse.map SparseSymbol.bit ++ output)
  have hp:=padding_pad (w - bits.length) true rest (unaryMarkers w)
    (bits.reverse.map SparseSymbol.bit ++ output)
  have hf:
      ((fun o => o.bind (TM2.step paddingProgram))^[1])
        (some (paddingCfg .finish ⟨none,true⟩ rest (unaryMarkers w)
          [] [] (List.replicate (w - bits.length) (.bit false) ++
            (bits.reverse.map SparseSymbol.bit ++ output)))) =
      some (paddingCfg .copy default rest (unaryMarkers w) [] []
        (.wordEnd::(List.replicate (w - bits.length) (.bit false) ++
          (bits.reverse.map SparseSymbol.bit ++ output)))):=by
    simpa using padding_finish_more rest (unaryMarkers w)
      (List.replicate (w - bits.length) (.bit false) ++
        (bits.reverse.map SparseSymbol.bit ++ output))
  have h:=chain_iterations _ (chain_iterations _
    (chain_iterations _ (chain_iterations _ hc hs) hb) hp) hf
  have htime:3 * w + 5 =
      (2 * w + 2) + bits.length + 1 + (w - bits.length + 1) + 1:=by omega
  rw [htime]
  simpa [List.append_assoc] using h

theorem padding_word_end (w:Nat) (bits:List Bool)
    (hlen:bits.length≤ w) (output:List SparseSymbol):
    ((fun o => o.bind (TM2.step paddingProgram))^[3 * w + 5])
      (some (paddingCfg .copy default (bits.map SparseSymbol.bit)
        (unaryMarkers w) [] [] output)) =
    some (paddingCfg .done default [] (unaryMarkers w) [] []
      (.wordEnd::List.replicate (w - bits.length) (.bit false) ++
        bits.reverse.map SparseSymbol.bit ++ output)):=by
  have hc:=padding_copy_width w default (bits.map SparseSymbol.bit) output
  have hs:=padding_scan_bits bits [] w hlen output
  simp only [List.append_nil] at hs
  have hb:
      ((fun o => o.bind (TM2.step paddingProgram))^[1])
        (some (paddingCfg .scan default [] (unaryMarkers w)
          (unaryMarkers (w - bits.length)) []
          (bits.reverse.map SparseSymbol.bit ++ output))) =
      some (paddingCfg .pad ⟨none,false⟩ [] (unaryMarkers w)
        (unaryMarkers (w - bits.length)) []
        (bits.reverse.map SparseSymbol.bit ++ output)):=by
    simpa using padding_boundary_end (unaryMarkers w)
      (unaryMarkers (w - bits.length))
      (bits.reverse.map SparseSymbol.bit ++ output)
  have hp:=padding_pad (w - bits.length) false [] (unaryMarkers w)
    (bits.reverse.map SparseSymbol.bit ++ output)
  have hf:
      ((fun o => o.bind (TM2.step paddingProgram))^[1])
        (some (paddingCfg .finish ⟨none,false⟩ [] (unaryMarkers w)
          [] [] (List.replicate (w - bits.length) (.bit false) ++
            (bits.reverse.map SparseSymbol.bit ++ output)))) =
      some (paddingCfg .done default [] (unaryMarkers w) [] []
        (.wordEnd::(List.replicate (w - bits.length) (.bit false) ++
          (bits.reverse.map SparseSymbol.bit ++ output)))):=by
    simpa using padding_finish_end (unaryMarkers w)
      (List.replicate (w - bits.length) (.bit false) ++
        (bits.reverse.map SparseSymbol.bit ++ output))
  have h:=chain_iterations _ (chain_iterations _
    (chain_iterations _ (chain_iterations _ hc hs) hb) hp) hf
  have htime:3 * w + 5 =
      (2 * w + 2) + bits.length + 1 + (w - bits.length + 1) + 1:=by omega
  rw [htime]
  simpa [List.append_assoc] using h

def canonicalPaddingRaw:List Nat→ List SparseSymbol
  | [] => []
  | n::ns => .wordEnd::n.bits.map SparseSymbol.bit ++ canonicalPaddingRaw ns

theorem canonicalPaddingRaw_eq (x:List Nat):
    canonicalPaddingRaw x=(encode x).map sparseOfInputSymbol:=by
  induction x with
  | nil => rfl
  | cons n x ih =>
      simp [canonicalPaddingRaw,encode,encodeNat,sparseOfInputSymbol,ih,
        List.map_append,List.map_map,Function.comp_def]

theorem padding_words_run (w:Nat) (x:List Nat)
    (hfit:∀ n∈ x,n < 2 ^ w) (output:List SparseSymbol):
    ((fun o => o.bind (TM2.step paddingProgram))^[x.length * (3 * w + 5)])
      (some (paddingCfg .copy default
        (match x with
          | [] => []
          | _::_ => (canonicalPaddingRaw x).tail)
        (unaryMarkers w) [] [] output)) =
    some (paddingCfg (if x=[] then .copy else .done) default []
      (unaryMarkers w) [] [] ((encodeWordList w x).reverse ++ output)):=by
  induction x generalizing output with
  | nil => simp [canonicalPaddingRaw,encodeWordList]
  | cons n x ih =>
      have hn:=hfit n (by simp)
      have hlen:n.bits.length≤ w:=by
        have hlt:n.bits.length≤ w:=by
          rw [Nat.size_eq_bits_len]
          exact (Nat.size_le.mpr hn)
        exact hlt
      cases x with
      | nil =>
          simpa [canonicalPaddingRaw,encodeWordList,encodeFixedWord,
            fixedBits_eq_bits_append_replicate hn,List.reverse_append,
            List.map_append,List.map_reverse,List.append_assoc] using
            padding_word_end w n.bits hlen output
      | cons m x =>
          have hfirst:=padding_word_more w n.bits hlen
            (m.bits.map SparseSymbol.bit ++ canonicalPaddingRaw x) output
          have hout:
              ((.wordEnd::List.replicate (w - n.bits.length) (.bit false)) ++
                n.bits.reverse.map SparseSymbol.bit) ++ output =
              (encodeFixedWord w n).reverse ++ output:=by
            simp [encodeFixedWord,fixedBits_eq_bits_append_replicate hn,
              List.reverse_append,List.map_append,List.map_reverse,
              List.append_assoc]
          rw [hout] at hfirst
          have htail:=ih (fun a ha => hfit a (by simp [ha]))
            ((encodeFixedWord w n).reverse ++ output)
          simp [canonicalPaddingRaw] at htail
          have h:=chain_iterations _ hfirst htail
          rw [show (3 * w + 5) +
              (x.length + 1) * (3 * w + 5) =
              (x.length + 2) * (3 * w + 5) by ring] at h
          simpa [canonicalPaddingRaw,encodeWordList,encodeFixedWord,
            fixedBits_eq_bits_append_replicate hn,List.reverse_append,
            List.map_append,List.map_reverse,List.append_assoc,Nat.add_mul,
            Nat.add_assoc,two_mul]
            using h

def physicalPaddingRaw (w:Nat) (x:List Nat):List SparseSymbol:=
  .wordEnd::(fixedBits w x.length).map SparseSymbol.bit ++
    canonicalPaddingRaw x

theorem padding_physical_input (w:Nat) (x:List Nat)
    (hlen:x.length < 2 ^ w) (hfit:∀ n∈ x,n < 2 ^ w):
    ((fun o => o.bind (TM2.step paddingProgram))^[
        1 + (x.length + 1) * (3 * w + 5)])
      (some (paddingCfg .start default (physicalPaddingRaw w x)
        (unaryMarkers w) [] [] [])) =
    some (paddingCfg .done default [] (unaryMarkers w) [] []
      (encodeWordList w (x.length::x)).reverse):=by
  have hstart:
      TM2.step paddingProgram
        (paddingCfg .start default (physicalPaddingRaw w x)
          (unaryMarkers w) [] [] []) =
      some (paddingCfg .copy default
        ((fixedBits w x.length).map SparseSymbol.bit ++ canonicalPaddingRaw x)
        (unaryMarkers w) [] [] []):=by
    simp [physicalPaddingRaw,paddingProgram,paddingCfg,paddingStacks,
      TM2.step,Function.update]
    funext k
    cases k <;> rfl
  have hstart':((fun o => o.bind (TM2.step paddingProgram))^[1])
      (some (paddingCfg .start default (physicalPaddingRaw w x)
        (unaryMarkers w) [] [] [])) =
      some (paddingCfg .copy default
        ((fixedBits w x.length).map SparseSymbol.bit ++ canonicalPaddingRaw x)
        (unaryMarkers w) [] [] []):=by simpa using hstart
  cases x with
  | nil =>
      have hword:=padding_word_end w (fixedBits w 0) (by simp) []
      have hstartNil:
          ((fun o => o.bind (TM2.step paddingProgram))^[1])
            (some (paddingCfg .start default (physicalPaddingRaw w [])
              (unaryMarkers w) [] [] [])) =
          some (paddingCfg .copy default
            ((fixedBits w 0).map SparseSymbol.bit)
            (unaryMarkers w) [] [] []):=by
        simpa [canonicalPaddingRaw] using hstart'
      have h:=chain_iterations _ hstartNil hword
      simpa [encodeWordList,encodeFixedWord,physicalPaddingRaw] using h
  | cons n x =>
      have hfirst:=padding_word_more w (fixedBits w (n::x).length)
        (by simp) (n.bits.map SparseSymbol.bit ++ canonicalPaddingRaw x) []
      have hout:
          ((.wordEnd::
              List.replicate (w - (fixedBits w (n::x).length).length)
                (.bit false)) ++
              (fixedBits w (n::x).length).reverse.map SparseSymbol.bit) ++ [] =
            (encodeFixedWord w (n::x).length).reverse:=by
        simp [encodeFixedWord,List.reverse_append,List.map_reverse]
      rw [hout] at hfirst
      have htail:=padding_words_run w (n::x) hfit
        ((encodeFixedWord w (n::x).length).reverse)
      simp [canonicalPaddingRaw] at htail
      have hwords:=chain_iterations _ hfirst htail
      have h:=chain_iterations _ hstart' hwords
      rw [show 1 + ((3 * w + 5) +
          (x.length + 1) * (3 * w + 5)) =
          1 + (x.length + 2) * (3 * w + 5) by ring] at h
      simpa [encodeWordList,encodeFixedWord,physicalPaddingRaw,
        canonicalPaddingRaw,List.reverse_append,List.append_assoc,
        Nat.add_mul,Nat.add_assoc,two_mul] using h

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2
open Lax759944.BinaryWordEncoding Lax759944Proofs.Legacy.RamPolytime

inductive PhysicalRawStack | saved | raw | length | temp
  deriving DecidableEq,Fintype,Inhabited

inductive PhysicalRawLabel | reverseSaved | reverseLength | prependLength | finish | done
  deriving DecidableEq,Fintype,Inhabited

def physicalRawProgram:PhysicalRawLabel→
    TM2.Stmt (fun _:PhysicalRawStack => SparseSymbol)
      PhysicalRawLabel SymbolMoveControl
  | .reverseSaved => symbolMoveIteration .saved .raw .reverseSaved .reverseLength
  | .reverseLength => symbolMoveIteration .length .temp .reverseLength .prependLength
  | .prependLength => symbolMoveIteration .temp .raw .prependLength .finish
  | .finish =>
      .push .raw (fun _ => .wordEnd) <|
      .goto fun _ => .done
  | .done => .halt

def physicalRawStacks (saved raw length temp:List SparseSymbol):
    PhysicalRawStack→ List SparseSymbol
  | .saved => saved
  | .raw => raw
  | .length => length
  | .temp => temp

def physicalRawCfg (label:PhysicalRawLabel)
    (saved raw length temp:List SparseSymbol):
    TM2.Cfg (fun _:PhysicalRawStack => SparseSymbol)
      PhysicalRawLabel SymbolMoveControl:=
  ⟨some label,default,physicalRawStacks saved raw length temp⟩

theorem physicalRaw_reverseSaved (saved raw length:List SparseSymbol):
    ((fun o => o.bind (TM2.step physicalRawProgram))^[saved.length + 1])
      (some (physicalRawCfg .reverseSaved saved raw length [])) =
    some (physicalRawCfg .reverseLength [] (saved.reverse ++ raw) length []):=by
  induction saved generalizing raw with
  | nil =>
      simp [physicalRawProgram,physicalRawCfg,physicalRawStacks,
        symbolMoveIteration,TM2.step]
      decide
  | cons a saved ih =>
      have hs:TM2.step physicalRawProgram
          (physicalRawCfg .reverseSaved (a::saved) raw length []) =
          some (physicalRawCfg .reverseSaved saved (a::raw) length []):=by
        simp [physicalRawProgram,physicalRawCfg,physicalRawStacks,
          symbolMoveIteration,TM2.step,Function.update]
        funext k
        cases k <;> rfl
      have hs':((fun o => o.bind (TM2.step physicalRawProgram))^[1])
          (some (physicalRawCfg .reverseSaved (a::saved) raw length [])) =
          some (physicalRawCfg .reverseSaved saved (a::raw) length []):=by simpa using hs
      have h:=chain_iterations _ hs' (ih (a::raw))
      rw [List.length_cons,
        show saved.length + 1 + 1=1 + (saved.length + 1) by omega]
      simpa [List.reverse_cons,List.append_assoc] using h

theorem physicalRaw_reverseLength_from (raw length temp:List SparseSymbol):
    ((fun o => o.bind (TM2.step physicalRawProgram))^[length.length + 1])
      (some (physicalRawCfg .reverseLength [] raw length temp)) =
    some (physicalRawCfg .prependLength [] raw [] (length.reverse ++ temp)):=by
  induction length generalizing temp with
  | nil =>
      simp [physicalRawProgram,physicalRawCfg,physicalRawStacks,
        symbolMoveIteration,TM2.step]
      decide
  | cons a length ih =>
      have hs:TM2.step physicalRawProgram
          (physicalRawCfg .reverseLength [] raw (a::length) temp) =
          some (physicalRawCfg .reverseLength [] raw length (a::temp)):=by
        simp [physicalRawProgram,physicalRawCfg,physicalRawStacks,
          symbolMoveIteration,TM2.step,Function.update]
        funext k
        cases k <;> rfl
      have hs':((fun o => o.bind (TM2.step physicalRawProgram))^[1])
          (some (physicalRawCfg .reverseLength [] raw (a::length) temp)) =
          some (physicalRawCfg .reverseLength [] raw length (a::temp)):=by simpa using hs
      have h:=chain_iterations _ hs' (ih (a::temp))
      rw [List.length_cons,
        show length.length + 1 + 1=1 + (length.length + 1) by omega]
      simpa [List.reverse_cons,List.append_assoc] using h

theorem physicalRaw_reverseLength (raw length:List SparseSymbol):
    ((fun o => o.bind (TM2.step physicalRawProgram))^[length.length + 1])
      (some (physicalRawCfg .reverseLength [] raw length [])) =
    some (physicalRawCfg .prependLength [] raw [] length.reverse):=by
  simpa using physicalRaw_reverseLength_from raw length []

theorem physicalRaw_prependLength (raw temp:List SparseSymbol):
    ((fun o => o.bind (TM2.step physicalRawProgram))^[temp.length + 1])
      (some (physicalRawCfg .prependLength [] raw [] temp)) =
    some (physicalRawCfg .finish [] (temp.reverse ++ raw) [] []):=by
  induction temp generalizing raw with
  | nil =>
      simp [physicalRawProgram,physicalRawCfg,physicalRawStacks,
        symbolMoveIteration,TM2.step]
      decide
  | cons a temp ih =>
      have hs:TM2.step physicalRawProgram
          (physicalRawCfg .prependLength [] raw [] (a::temp)) =
          some (physicalRawCfg .prependLength [] (a::raw) [] temp):=by
        simp [physicalRawProgram,physicalRawCfg,physicalRawStacks,
          symbolMoveIteration,TM2.step,Function.update]
        funext k
        cases k <;> rfl
      have hs':((fun o => o.bind (TM2.step physicalRawProgram))^[1])
          (some (physicalRawCfg .prependLength [] raw [] (a::temp))) =
          some (physicalRawCfg .prependLength [] (a::raw) [] temp):=by simpa using hs
      have h:=chain_iterations _ hs' (ih (a::raw))
      rw [List.length_cons,
        show temp.length + 1 + 1=1 + (temp.length + 1) by omega]
      simpa [List.reverse_cons,List.append_assoc] using h

theorem physicalRaw_finish (raw:List SparseSymbol):
    TM2.step physicalRawProgram (physicalRawCfg .finish [] raw [] []) =
      some (physicalRawCfg .done [] (.wordEnd::raw) [] []):=by
  simp [physicalRawProgram,physicalRawCfg,physicalRawStacks,TM2.step,
    Function.update]
  funext k
  cases k <;> rfl

theorem physicalRaw_correct (saved length:List SparseSymbol):
    ((fun o => o.bind (TM2.step physicalRawProgram))^[
        saved.length + 2 * length.length + 4])
      (some (physicalRawCfg .reverseSaved saved [] length [])) =
    some (physicalRawCfg .done []
      (.wordEnd::length ++ saved.reverse) [] []):=by
  have h₁:=physicalRaw_reverseSaved saved [] length
  rw [List.append_nil] at h₁
  have h₂:=physicalRaw_reverseLength saved.reverse length
  have h₃:=physicalRaw_prependLength saved.reverse length.reverse
  rw [List.reverse_reverse] at h₃
  have h₄:
      ((fun o => o.bind (TM2.step physicalRawProgram))^[1])
        (some (physicalRawCfg .finish [] (length ++ saved.reverse) [] [])) =
      some (physicalRawCfg .done []
        (.wordEnd::length ++ saved.reverse) [] []):=by
    simpa using physicalRaw_finish (length ++ saved.reverse)
  have h:=chain_iterations _ (chain_iterations _
    (chain_iterations _ h₁ h₂) h₃) h₄
  rw [List.length_reverse] at h
  have hsteps:
      saved.length + 1 + (length.length + 1) + (length.length + 1) + 1 =
        saved.length + 2 * length.length + 4:=by omega
  rw [hsteps] at h
  exact h

theorem physicalRaw_input_correct (w:Nat) (x:List Nat):
    ((fun o => o.bind (TM2.step physicalRawProgram))^[
        bitSize x + 2 * w + 4])
      (some (physicalRawCfg .reverseSaved
        ((encode x).reverse.map sparseOfInputSymbol) []
        ((fixedBits w x.length).map SparseSymbol.bit) [])) =
    some (physicalRawCfg .done [] (physicalPaddingRaw w x) [] []):=by
  simpa [physicalPaddingRaw,canonicalPaddingRaw_eq,bitSize,
    List.length_map,List.length_reverse,List.map_reverse] using
    physicalRaw_correct ((encode x).reverse.map sparseOfInputSymbol)
      ((fixedBits w x.length).map SparseSymbol.bit)

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive FinalizeInputStack | source | input
  deriving DecidableEq,Fintype,Inhabited

inductive FinalizeInputLabel | mark | move | done
  deriving DecidableEq,Fintype,Inhabited

def finalizeInputProgram:FinalizeInputLabel→
    TM2.Stmt (fun _:FinalizeInputStack => SparseSymbol)
      FinalizeInputLabel SymbolMoveControl
  | .mark =>
      .push .source (fun _ => .inputEnd) <|
      .goto fun _ => .move
  | .move => symbolMoveIteration .source .input .move .done
  | .done => .halt

def finalizeInputStacks (source input:List SparseSymbol):
    FinalizeInputStack→ List SparseSymbol
  | .source => source
  | .input => input

def finalizeInputCfg (label:FinalizeInputLabel)
    (source input:List SparseSymbol):
    TM2.Cfg (fun _:FinalizeInputStack => SparseSymbol)
      FinalizeInputLabel SymbolMoveControl:=
  ⟨some label,default,finalizeInputStacks source input⟩

theorem finalizeInput_move (source input:List SparseSymbol):
    ((fun o => o.bind (TM2.step finalizeInputProgram))^[source.length + 1])
      (some (finalizeInputCfg .move source input)) =
    some (finalizeInputCfg .done [] (source.reverse ++ input)):=by
  induction source generalizing input with
  | nil =>
      simp [finalizeInputProgram,finalizeInputCfg,finalizeInputStacks,
        symbolMoveIteration,TM2.step]
      decide
  | cons a source ih =>
      have hs:TM2.step finalizeInputProgram
          (finalizeInputCfg .move (a::source) input) =
          some (finalizeInputCfg .move source (a::input)):=by
        simp [finalizeInputProgram,finalizeInputCfg,finalizeInputStacks,
          symbolMoveIteration,TM2.step,Function.update]
        funext k
        cases k <;> rfl
      have hs':((fun o => o.bind (TM2.step finalizeInputProgram))^[1])
          (some (finalizeInputCfg .move (a::source) input)) =
          some (finalizeInputCfg .move source (a::input)):=by simpa using hs
      have h:=chain_iterations _ hs' (ih (a::input))
      rw [List.length_cons,
        show source.length + 1 + 1=1 + (source.length + 1) by omega]
      simpa [List.reverse_cons,List.append_assoc] using h

theorem finalizeInput_correct (payload:List SparseSymbol):
    ((fun o => o.bind (TM2.step finalizeInputProgram))^[payload.length + 3])
      (some (finalizeInputCfg .mark payload [])) =
    some (finalizeInputCfg .done [] (payload.reverse ++ [.inputEnd])):=by
  have hmark:
      TM2.step finalizeInputProgram (finalizeInputCfg .mark payload []) =
        some (finalizeInputCfg .move (.inputEnd::payload) []):=by
    simp [finalizeInputProgram,finalizeInputCfg,finalizeInputStacks,TM2.step]
    funext k
    cases k <;> rfl
  have hmark':((fun o => o.bind (TM2.step finalizeInputProgram))^[1])
      (some (finalizeInputCfg .mark payload [])) =
      some (finalizeInputCfg .move (.inputEnd::payload) []):=by
    simpa using hmark
  have hmove:=finalizeInput_move (.inputEnd::payload) []
  have h:=chain_iterations _ hmark' hmove
  have hsteps:1 + ((.inputEnd::payload).length + 1) =
      payload.length + 3:=by simp; omega
  rw [hsteps] at h
  simpa [List.reverse_cons,List.append_assoc] using h

theorem finalizeInput_encoded (w:Nat) (xs:List Nat):
    ((fun o => o.bind (TM2.step finalizeInputProgram))^[
        (encodeWordList w xs).length + 3])
      (some (finalizeInputCfg .mark (encodeWordList w xs).reverse [])) =
    some (finalizeInputCfg .done [] (encodeInputStack w xs)):=by
  simpa [encodeInputStack] using finalizeInput_correct (encodeWordList w xs).reverse

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2
open Lax759944.BinaryWordEncoding Lax759944Proofs.Legacy.RamPolytime

noncomputable section

def physicalRawWrapperRenaming:StackRenaming PhysicalRawStack CoreStack where
  encode
    | .saved => .work0
    | .raw => .work4
    | .length => .work6
    | .temp => .work2
  decode
    | .work0 => some .saved
    | .work4 => some .raw
    | .work6 => some .length
    | .work2 => some .temp
    | _ => none
  decode_encode:=by intro k; cases k <;> rfl
  encode_decode:=by
    intro k' k h
    cases k <;> cases k' <;> simp_all

def moveWrapperLens {N:Nat}:
    StateLens SymbolMoveControl (FullInterpreterState N):=
  FullInterpreterState.moveLens

def paddingWrapperRenaming:StackRenaming PaddingStack CoreStack where
  encode
    | .raw => .work4
    | .width => .work3
    | .counter => .work2
    | .backup => .work7
    | .output => .work5
  decode
    | .work4 => some .raw
    | .work3 => some .width
    | .work2 => some .counter
    | .work7 => some .backup
    | .work5 => some .output
    | _ => none
  decode_encode:=by intro k; cases k <;> rfl
  encode_decode:=by
    intro k' k h
    cases k <;> cases k' <;> simp_all

def paddingWrapperLens {N:Nat}:
    StateLens PaddingControl (FullInterpreterState N) where
  get s:= ⟨(FullInterpreterState.moveLens.get s).held, !s.lookupFound⟩
  put s c:=FullInterpreterState.moveLens.put
    {s with lookupFound:= !c.more} ⟨c.held⟩
  get_put:=by
    intro s c
    rcases c with ⟨held,more⟩
    cases more <;> rfl
  put_get:=by
    intro s
    cases s with
    | mk macros dispatch literal lookupFound subtractForceZero countdown =>
        cases lookupFound <;> rfl
  put_put:=by
    intros
    simp [FullInterpreterState.moveLens,InterpreterMacroState.moveLens,
      FullInterpreterState.macroLens,StateLens.comp]

def finalizeInputWrapperRenaming:
    StackRenaming FinalizeInputStack CoreStack where
  encode
    | .source => .work5
    | .input => .input
  decode
    | .work5 => some .source
    | .input => some .input
    | _ => none
  decode_encode:=by intro k; cases k <;> rfl
  encode_decode:=by
    intro k' k h
    cases k <;> cases k' <;> simp_all

def physicalRawCoreProgram {N:Nat}:Sum PhysicalRawLabel Unit→
    TM2.Stmt (fun _:CoreStack => SparseSymbol) (Sum PhysicalRawLabel Unit)
      (FullInterpreterState N):=
  lensSpliceProgram physicalRawWrapperRenaming moveWrapperLens
    physicalRawProgram .done () (fun _ => .halt)

def paddingCoreProgram {N:Nat}:Sum PaddingLabel Unit→
    TM2.Stmt (fun _:CoreStack => SparseSymbol) (Sum PaddingLabel Unit)
      (FullInterpreterState N):=
  lensSpliceProgram paddingWrapperRenaming paddingWrapperLens
    paddingProgram .done () (fun _ => .halt)

def finalizeInputCoreProgram {N:Nat}:Sum FinalizeInputLabel Unit→
    TM2.Stmt (fun _:CoreStack => SparseSymbol) (Sum FinalizeInputLabel Unit)
      (FullInterpreterState N):=
  lensSpliceProgram finalizeInputWrapperRenaming moveWrapperLens
    finalizeInputProgram .done () (fun _ => .halt)

def collapseEmptyLabel {L:Type}:Sum L Empty→ L
  | .inl label => label
  | .inr impossible => nomatch impossible

def liftCoreProgramSame {N:Nat} {L:Type}
    (program:L→ TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N)):
    L→ TM2.Stmt WrapperAlphabet L (WrapperState N):=
  fun label => mapLabelStmt collapseEmptyLabel
    (liftCoreStmt (X:=Empty) (program label))

def liftCoreCfgSame {N:Nat} {L:Type}
    (cfg:TM2.Cfg (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (ambient:WrapperState N) (input output:List Symbol):
    TM2.Cfg WrapperAlphabet L (WrapperState N):=
  mapLabelCfg collapseEmptyLabel
    (liftCoreCfg (X:=Empty) cfg ambient input output)

theorem iterate_liftCoreProgramSame {N n:Nat} {L:Type}
    (program:L→ TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (c d:TM2.Cfg (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (ambient:WrapperState N) (input output:List Symbol)
    (hrun:((fun o => o.bind (TM2.step program))^[n]) (some c)=some d):
    ((fun o => o.bind (TM2.step (liftCoreProgramSame program)))^[n])
      (some (liftCoreCfgSame c ambient input output)) =
    some (liftCoreCfgSame d ambient input output):=by
  have hlift:=iterate_liftCoreProgram program
    (fun impossible:Empty => nomatch impossible) c d ambient input output hrun
  have hmap:=iterate_mapLabelProgram
    (liftCoreProgram program (fun impossible:Empty => nomatch impossible))
    (liftCoreProgramSame program) collapseEmptyLabel (by
      intro label
      cases label with
      | inl label => rfl
      | inr impossible => nomatch impossible)
    n (liftCoreCfg (X:=Empty) c ambient input output)
  rw [hlift] at hmap
  exact hmap

def physicalRawWrapperProgram {N:Nat}:=
  liftCoreProgramSame (physicalRawCoreProgram (N:=N))

def paddingWrapperProgram {N:Nat}:=
  liftCoreProgramSame (paddingCoreProgram (N:=N))

def finalizeInputWrapperProgram {N:Nat}:=
  liftCoreProgramSame (finalizeInputCoreProgram (N:=N))

theorem physicalRaw_wrapper_correct {N:Nat} (w:Nat) (x:List Nat)
    (state:WrapperState N)
    (ambient:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun o => o.bind (TM2.step physicalRawWrapperProgram))^[
        bitSize x + 2 * w + 5])
      (some (liftCoreCfgSame
        (lensRenamedCfg physicalRawWrapperRenaming moveWrapperLens
        (physicalRawCfg .reverseSaved
          ((encode x).reverse.map sparseOfInputSymbol) []
          ((fixedBits w x.length).map SparseSymbol.bit) []) state.core
          (fun k => ambient (.core k))) state (ambient .input) (ambient .output))) =
    some (liftCoreCfgSame
      (lensReturnCfg physicalRawWrapperRenaming moveWrapperLens ()
        (physicalRawCfg .done [] (physicalPaddingRaw w x) [] []) state.core
        (fun k => ambient (.core k))) state (ambient .input) (ambient .output)):=by
  have hcore:=transport_lensHaltingMacro_and_return physicalRawWrapperRenaming
    moveWrapperLens physicalRawProgram .done (by rfl) () (fun _ => .halt)
    (physicalRaw_input_correct w x) rfl state.core (fun k => ambient (.core k))
  exact iterate_liftCoreProgramSame physicalRawCoreProgram _ _ state
    (ambient .input) (ambient .output) hcore

theorem padding_wrapper_correct {N:Nat} (w:Nat) (x:List Nat)
    (hlen:x.length < 2 ^ w) (hfit:∀ n∈ x,n < 2 ^ w)
    (state:WrapperState N)
    (ambient:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun o => o.bind (TM2.step paddingWrapperProgram))^[
        1 + (x.length + 1) * (3 * w + 5) + 1])
      (some (liftCoreCfgSame
        (lensRenamedCfg paddingWrapperRenaming paddingWrapperLens
        (paddingCfg .start default (physicalPaddingRaw w x)
          (unaryMarkers w) [] [] []) state.core (fun k => ambient (.core k)))
          state (ambient .input) (ambient .output))) =
    some (liftCoreCfgSame
      (lensReturnCfg paddingWrapperRenaming paddingWrapperLens ()
      (paddingCfg .done default [] (unaryMarkers w) [] []
        (encodeWordList w (x.length::x)).reverse) state.core
        (fun k => ambient (.core k))) state (ambient .input) (ambient .output)):=by
  have hcore:=transport_lensHaltingMacro_and_return paddingWrapperRenaming
    paddingWrapperLens paddingProgram .done (by rfl) () (fun _ => .halt)
    (padding_physical_input w x hlen hfit) rfl state.core
    (fun k => ambient (.core k))
  exact iterate_liftCoreProgramSame paddingCoreProgram _ _ state
    (ambient .input) (ambient .output) hcore

theorem finalizeInput_wrapper_correct {N:Nat} (w:Nat) (xs:List Nat)
    (state:WrapperState N)
    (ambient:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun o => o.bind (TM2.step finalizeInputWrapperProgram))^[
        (encodeWordList w xs).length + 4])
      (some (liftCoreCfgSame
        (lensRenamedCfg finalizeInputWrapperRenaming moveWrapperLens
          (finalizeInputCfg .mark (encodeWordList w xs).reverse []) state.core
          (fun k => ambient (.core k))) state (ambient .input) (ambient .output))) =
    some (liftCoreCfgSame
      (lensReturnCfg finalizeInputWrapperRenaming moveWrapperLens ()
        (finalizeInputCfg .done [] (encodeInputStack w xs)) state.core
        (fun k => ambient (.core k))) state (ambient .input) (ambient .output)):=by
  have hcore:=transport_lensHaltingMacro_and_return finalizeInputWrapperRenaming
    moveWrapperLens finalizeInputProgram .done (by rfl) () (fun _ => .halt)
    (finalizeInput_encoded w xs) rfl state.core (fun k => ambient (.core k))
  exact iterate_liftCoreProgramSame finalizeInputCoreProgram _ _ state
    (ambient .input) (ambient .output) hcore

end

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive CoreInitLabel | zeroCopy | zeroRestore | clearMultiplier | clearWidth | finish | done
  deriving DecidableEq,Fintype,Inhabited

def coreInitProgram {N:Nat}:CoreInitLabel→
    TM2.Stmt WrapperAlphabet CoreInitLabel (WrapperState N)
  | .zeroCopy =>
      .pop (.core .work3) (fun s a => {s with heldSparse:=a}) <|
      .branch (fun s => s.heldSparse.isNone)
        (.load (fun s => {s with heldSparse:=none}) <|
          .goto fun _ => .zeroRestore)
        (.push (.core .accumulator) (fun _ => .bit false) <|
          .push (.core .work7) (fun s => s.heldSparse.getD default) <|
          .load (fun s => {s with heldSparse:=none}) <|
          .goto fun _ => .zeroCopy)
  | .zeroRestore =>
      .pop (.core .work7) (fun s a => {s with heldSparse:=a}) <|
      .branch (fun s => s.heldSparse.isNone)
        (.load (fun s => {s with heldSparse:=none}) <|
          .goto fun _ => .clearMultiplier)
        (.push (.core .work3) (fun s => s.heldSparse.getD default) <|
          .load (fun s => {s with heldSparse:=none}) <|
          .goto fun _ => .zeroRestore)
  | .clearMultiplier =>
      .pop (.core .work1) (fun s a => {s with heldSparse:=a}) <|
      .branch (fun s => s.heldSparse.isNone)
        (.load (fun s => {s with heldSparse:=none}) <|
          .goto fun _ => .clearWidth)
        (.load (fun s => {s with heldSparse:=none}) <|
          .goto fun _ => .clearMultiplier)
  | .clearWidth =>
      .pop (.core .work3) (fun s a => {s with heldSparse:=a}) <|
      .branch (fun s => s.heldSparse.isNone)
        (.load (fun s => {s with heldSparse:=none}) <|
          .goto fun _ => .finish)
        (.load (fun s => {s with heldSparse:=none}) <|
          .goto fun _ => .clearWidth)
  | .finish =>
      .push (.core .memory) (fun _ => .memoryEnd) <|
      .push (.core .output) (fun _ => .outputEnd) <|
      .load (fun _ => default) <|
      .goto fun _ => .done
  | .done => .halt

def coreInitCfg {N:Nat} (label:CoreInitLabel) (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    TM2.Cfg WrapperAlphabet CoreInitLabel (WrapperState N):=
  ⟨some label,state,tapes⟩

theorem coreInit_zero_copy_from {N:Nat} (markers acc backup:List SparseSymbol)
    (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun o => o.bind (TM2.step coreInitProgram))^[markers.length + 1])
      (some (coreInitCfg .zeroCopy state
        (Function.update
          (Function.update
            (Function.update tapes (.core .work3) markers)
            (.core .accumulator) acc)
          (.core .work7) backup))) =
    some (coreInitCfg .zeroRestore {state with heldSparse:=none}
      (Function.update
        (Function.update
          (Function.update tapes (.core .work3) [])
          (.core .accumulator)
            (List.replicate markers.length (.bit false) ++ acc))
        (.core .work7) (markers.reverse ++ backup))):=by
  induction markers generalizing state acc backup with
  | nil =>
      simp [coreInitProgram,coreInitCfg,TM2.step,List.head?,List.tail,
        Option.isNone,Function.update]
  | cons marker markers ih =>
      have hs:TM2.step coreInitProgram
          (coreInitCfg .zeroCopy state
            (Function.update
              (Function.update
                (Function.update tapes (.core .work3) (marker::markers))
                (.core .accumulator) acc)
              (.core .work7) backup)) =
          some (coreInitCfg .zeroCopy {state with heldSparse:=none}
            (Function.update
              (Function.update
                (Function.update tapes (.core .work3) markers)
                (.core .accumulator) (.bit false::acc))
              (.core .work7) (marker::backup))):=by
        simp [coreInitProgram,coreInitCfg,TM2.step,Option.isNone,
          Option.getD,Function.update]
        funext k
        cases k with
        | input | output => rfl
        | core k => cases k <;> simp [Function.update]
      have hs':((fun o => o.bind (TM2.step coreInitProgram))^[1])
          (some (coreInitCfg .zeroCopy state
            (Function.update
              (Function.update
                (Function.update tapes (.core .work3) (marker::markers))
                (.core .accumulator) acc)
              (.core .work7) backup))) =
          some (coreInitCfg .zeroCopy {state with heldSparse:=none}
            (Function.update
              (Function.update
                (Function.update tapes (.core .work3) markers)
                (.core .accumulator) (.bit false::acc))
              (.core .work7) (marker::backup))):=by simpa using hs
      have hi:=ih (.bit false::acc) (marker::backup)
        {state with heldSparse:=none}
      have h:=chain_iterations _ hs' hi
      rw [show 1 + (markers.length + 1)=markers.length + 1 + 1 by omega] at h
      have hout:
          coreInitCfg .zeroRestore {state with heldSparse:=none}
            (Function.update
              (Function.update
                (Function.update tapes (.core .work3) [])
                (.core .accumulator)
                  (List.replicate markers.length (.bit false) ++
                    .bit false::acc))
              (.core .work7) (markers.reverse ++ marker::backup)) =
          coreInitCfg .zeroRestore {state with heldSparse:=none}
            (Function.update
              (Function.update
                (Function.update tapes (.core .work3) [])
              (.core .accumulator)
                  (List.replicate (marker::markers).length (.bit false) ++ acc))
              (.core .work7) ((marker::markers).reverse ++ backup)):=by
        have hrep:
            List.replicate markers.length (.bit false) ++ .bit false::acc =
              List.replicate (marker::markers).length (.bit false) ++ acc:=by
          change List.replicate markers.length (.bit false) ++
              ([.bit false] ++ acc) =
            List.replicate (markers.length + 1) (.bit false) ++ acc
          calc
            _=(List.replicate markers.length (.bit false) ++
                [.bit false]) ++ acc:=(List.append_assoc _ _ _).symm
            _=_:=by
              rw [show [SparseSymbol.bit false] =
                List.replicate 1 (SparseSymbol.bit false) by rfl,
                List.replicate_append_replicate]
        apply congrArg (fun updated =>
          coreInitCfg .zeroRestore {state with heldSparse:=none} updated)
        funext k
        cases k with
        | input | output => rfl
        | core k =>
            cases k <;>
              simp [List.reverse_cons,List.append_assoc,Function.update]
            case accumulator => simpa only [List.length_cons] using hrep
      rw [hout] at h
      exact h

theorem coreInit_zero_copy {N w:Nat} (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k))
    (hacc:tapes (.core .accumulator)=[])
    (hbackup:tapes (.core .work7)=[]):
    ((fun o => o.bind (TM2.step coreInitProgram))^[w + 1])
      (some (coreInitCfg .zeroCopy state
        (Function.update tapes (.core .work3) (unaryMarkers w)))) =
    some (coreInitCfg .zeroRestore {state with heldSparse:=none}
      (Function.update
        (Function.update
          (Function.update tapes (.core .work3) [])
          (.core .accumulator) ((fixedBits w 0).map SparseSymbol.bit).reverse)
        (.core .work7) (unaryMarkers w).reverse)):=by
  have h:=coreInit_zero_copy_from (N:=N) (unaryMarkers w) [] [] state tapes
  rw [show (unaryMarkers w).length=w by simp [unaryMarkers]] at h
  have hstart:
      coreInitCfg .zeroCopy state
          (Function.update
            (Function.update
              (Function.update tapes (.core .work3) (unaryMarkers w))
              (.core .accumulator) [])
            (.core .work7) []) =
        coreInitCfg .zeroCopy state
          (Function.update tapes (.core .work3) (unaryMarkers w)):=by
    apply congrArg (fun updated => coreInitCfg .zeroCopy state updated)
    funext k
    cases k with
    | input | output => rfl
    | core k => cases k <;> simp [hacc,hbackup,Function.update]
  have hfinal:
      coreInitCfg .zeroRestore {state with heldSparse:=none}
          (Function.update
            (Function.update
              (Function.update tapes (.core .work3) [])
              (.core .accumulator)
                (List.replicate w (.bit false) ++ []))
            (.core .work7) ((unaryMarkers w).reverse ++ [])) =
        coreInitCfg .zeroRestore {state with heldSparse:=none}
          (Function.update
            (Function.update
              (Function.update tapes (.core .work3) [])
              (.core .accumulator)
                ((fixedBits w 0).map SparseSymbol.bit).reverse)
            (.core .work7) (unaryMarkers w).reverse):=by
    apply congrArg (fun updated =>
      coreInitCfg .zeroRestore {state with heldSparse:=none} updated)
    funext k
    cases k with
    | input | output => rfl
    | core k =>
        cases k <;>
          simp [fixedBits_zero,List.reverse_replicate,Function.update]
  have hin:=congrArg
    (fun cfg => ((fun o => o.bind (TM2.step coreInitProgram))^[w + 1]) cfg)
    (congrArg some hstart).symm
  exact hin.trans (h.trans (congrArg some hfinal))

theorem coreInit_zero_restore_from {N:Nat}
    (saved width:List SparseSymbol) (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun o => o.bind (TM2.step coreInitProgram))^[saved.length + 1])
      (some (coreInitCfg .zeroRestore state
        (Function.update
          (Function.update tapes (.core .work3) width)
          (.core .work7) saved))) =
    some (coreInitCfg .clearMultiplier {state with heldSparse:=none}
      (Function.update
        (Function.update tapes (.core .work3) (saved.reverse ++ width))
        (.core .work7) [])):=by
  induction saved generalizing state width with
  | nil =>
      simp [coreInitProgram,coreInitCfg,TM2.step,List.head?,List.tail,
        Option.isNone,Function.update]
  | cons marker saved ih =>
      have hs:TM2.step coreInitProgram
          (coreInitCfg .zeroRestore state
            (Function.update
              (Function.update tapes (.core .work3) width)
              (.core .work7) (marker::saved))) =
          some (coreInitCfg .zeroRestore {state with heldSparse:=none}
            (Function.update
              (Function.update tapes (.core .work3) (marker::width))
              (.core .work7) saved)):=by
        simp [coreInitProgram,coreInitCfg,TM2.step,Option.isNone,
          Option.getD,Function.update]
        funext k
        cases k with
        | input | output => rfl
        | core k => cases k <;> simp [Function.update]
      have hs':((fun o => o.bind (TM2.step coreInitProgram))^[1])
          (some (coreInitCfg .zeroRestore state
            (Function.update
              (Function.update tapes (.core .work3) width)
              (.core .work7) (marker::saved)))) =
          some (coreInitCfg .zeroRestore {state with heldSparse:=none}
            (Function.update
              (Function.update tapes (.core .work3) (marker::width))
              (.core .work7) saved)):=by simpa using hs
      have hi:=ih (marker::width) {state with heldSparse:=none}
      have h:=chain_iterations _ hs' hi
      rw [show 1 + (saved.length + 1)=saved.length + 1 + 1 by omega] at h
      simpa [List.reverse_cons,List.append_assoc] using h

theorem coreInit_zero_restore {N w:Nat} (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun o => o.bind (TM2.step coreInitProgram))^[w + 1])
      (some (coreInitCfg .zeroRestore state
        (Function.update
          (Function.update tapes (.core .work3) [])
          (.core .work7) (unaryMarkers w).reverse))) =
    some (coreInitCfg .clearMultiplier {state with heldSparse:=none}
      (Function.update
        (Function.update tapes (.core .work3) (unaryMarkers w))
        (.core .work7) [])):=by
  have h:=coreInit_zero_restore_from (N:=N)
    (unaryMarkers w).reverse [] state tapes
  rw [show (unaryMarkers w).reverse.length=w by simp [unaryMarkers]] at h
  simpa using h

theorem coreInit_clearMultiplier {N:Nat} (state:WrapperState N)
    (xs:List SparseSymbol)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun o => o.bind (TM2.step coreInitProgram))^[xs.length + 1])
      (some (coreInitCfg .clearMultiplier state
        (Function.update tapes (.core .work1) xs))) =
    some (coreInitCfg .clearWidth {state with heldSparse:=none}
      (Function.update tapes (.core .work1) [])):=by
  induction xs generalizing state with
  | nil =>
      simp [coreInitProgram,coreInitCfg,TM2.step,List.head?,List.tail,
        Option.isNone,Function.update]
  | cons x xs ih =>
      have hs:TM2.step coreInitProgram
          (coreInitCfg .clearMultiplier state
            (Function.update tapes (.core .work1) (x::xs))) =
          some (coreInitCfg .clearMultiplier {state with heldSparse:=none}
            (Function.update tapes (.core .work1) xs)):=by
        simp [coreInitProgram,coreInitCfg,TM2.step,Option.isNone,
          Function.update]
      have hs':((fun o => o.bind (TM2.step coreInitProgram))^[1])
          (some (coreInitCfg .clearMultiplier state
            (Function.update tapes (.core .work1) (x::xs)))) =
          some (coreInitCfg .clearMultiplier {state with heldSparse:=none}
            (Function.update tapes (.core .work1) xs)):=by simpa using hs
      have h:=chain_iterations _ hs' (ih {state with heldSparse:=none})
      rw [show 1 + (xs.length + 1)=xs.length + 1 + 1 by omega] at h
      exact h

theorem coreInit_clearWidth {N w:Nat} (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun o => o.bind (TM2.step coreInitProgram))^[w + 1])
      (some (coreInitCfg .clearWidth state
        (Function.update tapes (.core .work3) (unaryMarkers w)))) =
    some (coreInitCfg .finish {state with heldSparse:=none}
      (Function.update tapes (.core .work3) [])):=by
  induction w generalizing state with
  | zero =>
      simp [unaryMarkers,coreInitProgram,coreInitCfg,TM2.step,List.head?,
        List.tail,Option.isNone,Function.update]
  | succ w ih =>
      have hs:TM2.step coreInitProgram
          (coreInitCfg .clearWidth state
            (Function.update tapes (.core .work3) (unaryMarkers (w + 1)))) =
          some (coreInitCfg .clearWidth {state with heldSparse:=none}
            (Function.update tapes (.core .work3) (unaryMarkers w))):=by
        simp [unaryMarkers,List.replicate_succ,coreInitProgram,coreInitCfg,
          TM2.step,List.head?,List.tail,Option.isNone,Function.update]
      have hs':((fun o => o.bind (TM2.step coreInitProgram))^[1])
          (some (coreInitCfg .clearWidth state
            (Function.update tapes (.core .work3) (unaryMarkers (w + 1))))) =
          some (coreInitCfg .clearWidth {state with heldSparse:=none}
            (Function.update tapes (.core .work3) (unaryMarkers w))):=by
        simpa using hs
      have h:=chain_iterations _ hs' (ih {state with heldSparse:=none})
      rw [show 1 + (w + 1)=w + 1 + 1 by omega] at h
      exact h

theorem coreInit_finish {N:Nat} (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    TM2.step coreInitProgram (coreInitCfg .finish state tapes) =
    some (coreInitCfg .done default
      (Function.update
        (Function.update tapes (.core .memory)
          (.memoryEnd::tapes (.core .memory)))
        (.core .output) (.outputEnd::tapes (.core .output)))):=by
  simp [coreInitProgram,coreInitCfg,TM2.step]

def coreInitFinalStacks (w:Nat)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    (k:WrapperStack)→ List (WrapperAlphabet k):=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update tapes (.core .accumulator)
              ((fixedBits w 0).map SparseSymbol.bit))
            (.core .work1) [])
          (.core .work3) [])
        (.core .work7) [])
      (.core .memory) [.memoryEnd])
    (.core .output) [.outputEnd]

theorem coreInit_correct {N w:Nat} (state:WrapperState N)
    (multiplier:List SparseSymbol)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k))
    (hacc:tapes (.core .accumulator)=[])
    (hbackup:tapes (.core .work7)=[])
    (hmemory:tapes (.core .memory)=[])
    (houtput:tapes (.core .output)=[]):
    ((fun o => o.bind (TM2.step coreInitProgram))^[
        3 * w + multiplier.length + 5])
      (some (coreInitCfg .zeroCopy state
        (Function.update
          (Function.update tapes (.core .work1) multiplier)
          (.core .work3) (unaryMarkers w)))) =
    some (coreInitCfg .done default (coreInitFinalStacks w tapes)):=by
  let startStacks:=Function.update tapes (.core .work1) multiplier
  have hcopy:=coreInit_zero_copy (N:=N) (w:=w) state startStacks
    (by simp [startStacks,hacc]) (by simp [startStacks,hbackup])
  have hrestore:=coreInit_zero_restore (N:=N) (w:=w)
    {state with heldSparse:=none}
    (Function.update startStacks (.core .accumulator)
      ((fixedBits w 0).map SparseSymbol.bit).reverse)
  have hclear1:=coreInit_clearMultiplier (N:=N)
    {state with heldSparse:=none} multiplier
    (Function.update
      (Function.update startStacks (.core .accumulator)
        ((fixedBits w 0).map SparseSymbol.bit).reverse)
      (.core .work3) (unaryMarkers w))
  have hclear3:=coreInit_clearWidth (N:=N) (w:=w)
    {state with heldSparse:=none}
    (Function.update
      (Function.update
        (Function.update startStacks (.core .accumulator)
          ((fixedBits w 0).map SparseSymbol.bit).reverse)
        (.core .work1) [])
      (.core .work7) [])
  have hfinish:=coreInit_finish (N:=N)
    {state with heldSparse:=none}
    (Function.update
      (Function.update
        (Function.update
          (Function.update startStacks (.core .accumulator)
            ((fixedBits w 0).map SparseSymbol.bit).reverse)
          (.core .work1) [])
        (.core .work7) [])
      (.core .work3) [])
  have htapes₁:
      Function.update
          (Function.update
            (Function.update startStacks (.core .work3) [])
            (.core .accumulator) ((fixedBits w 0).map SparseSymbol.bit).reverse)
          (.core .work7) (unaryMarkers w).reverse =
        Function.update
          (Function.update
            (Function.update startStacks (.core .accumulator)
              ((fixedBits w 0).map SparseSymbol.bit).reverse)
            (.core .work3) [])
          (.core .work7) (unaryMarkers w).reverse:=by
    funext k
    cases k with
    | input | output => rfl
    | core k => cases k <;> simp [Function.update]
  rw [← htapes₁] at hrestore
  have htapes₂:
      Function.update
          (Function.update
            (Function.update startStacks (.core .accumulator)
              ((fixedBits w 0).map SparseSymbol.bit).reverse)
            (.core .work3) (unaryMarkers w))
          (.core .work7) [] =
        Function.update
          (Function.update
            (Function.update startStacks (.core .accumulator)
              ((fixedBits w 0).map SparseSymbol.bit).reverse)
            (.core .work3) (unaryMarkers w))
          (.core .work1) multiplier:=by
    funext k
    cases k with
    | input | output => rfl
    | core k => cases k <;> simp [startStacks,hbackup,Function.update]
  rw [← htapes₂] at hclear1
  have htapes₃:
      Function.update
          (Function.update
            (Function.update startStacks (.core .accumulator)
              ((fixedBits w 0).map SparseSymbol.bit).reverse)
            (.core .work3) (unaryMarkers w))
          (.core .work1) [] =
        Function.update
          (Function.update
            (Function.update
              (Function.update startStacks (.core .accumulator)
                ((fixedBits w 0).map SparseSymbol.bit).reverse)
              (.core .work1) [])
            (.core .work7) [])
          (.core .work3) (unaryMarkers w):=by
    funext k
    cases k with
    | input | output => rfl
    | core k => cases k <;> simp [startStacks,hbackup,Function.update]
  rw [← htapes₃] at hclear3
  have hfinish':
      ((fun o => o.bind (TM2.step coreInitProgram))^[1])
        (some (coreInitCfg .finish {state with heldSparse:=none}
          (Function.update
            (Function.update
              (Function.update
                (Function.update startStacks (.core .accumulator)
                  ((fixedBits w 0).map SparseSymbol.bit).reverse)
                (.core .work1) [])
              (.core .work7) [])
            (.core .work3) []))) =
      some (coreInitCfg .done default
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update startStacks (.core .accumulator)
                    ((fixedBits w 0).map SparseSymbol.bit).reverse)
                  (.core .work1) [])
                (.core .work7) [])
              (.core .work3) [])
            (.core .memory) (.memoryEnd::
              (Function.update
                (Function.update
                  (Function.update
                    (Function.update startStacks (.core .accumulator)
                      ((fixedBits w 0).map SparseSymbol.bit).reverse)
                    (.core .work1) [])
                  (.core .work7) [])
                (.core .work3) []) (.core .memory)))
          (.core .output) (.outputEnd::
            (Function.update
              (Function.update
                (Function.update
                  (Function.update startStacks (.core .accumulator)
                    ((fixedBits w 0).map SparseSymbol.bit).reverse)
                  (.core .work1) [])
                (.core .work7) [])
              (.core .work3) []) (.core .output)))):=by
    simpa using hfinish
  have h:=chain_iterations _ (chain_iterations _ (chain_iterations _
    (chain_iterations _ hcopy hrestore) hclear1) hclear3) hfinish'
  simp [startStacks,coreInitFinalStacks,fixedBits_zero,
    List.reverse_replicate,hmemory,houtput,Nat.add_assoc] at h
  have hsteps:
      w + (1 + (w + (1 + (multiplier.length + (1 + (w + 2)))))) =
        3 * w + multiplier.length + 5:=by omega
  rw [hsteps] at h
  have htapesFinal:
      Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update
                    (Function.update tapes (.core .work1) multiplier)
                    (.core .accumulator)
                      (List.replicate w (.bit false)))
                  (.core .work1) [])
                (.core .work7) [])
              (.core .work3) [])
            (.core .memory) [.memoryEnd])
          (.core .output) [.outputEnd] =
        coreInitFinalStacks w tapes:=by
    funext k
    cases k with
    | input | output => rfl
    | core k => cases k <;>
        simp [coreInitFinalStacks,fixedBits_zero,List.reverse_replicate,
          hacc,hbackup,hmemory,houtput,Function.update]
  exact h.trans (congrArg some
    (congrArg (fun updated => coreInitCfg .done default updated) htapesFinal))

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2
open Polynomial
open Lax759944.BinaryWordEncoding Lax759944Proofs.Legacy.RamPolytime

noncomputable section

abbrev FullInputLabel (p:Polynomial Nat):=
  Sum (InputWidthLabel p)
    (Sum LengthPrefixLabel
      (Sum PhysicalRawLabel
        (Sum PaddingLabel (Sum FinalizeInputLabel (Sum CoreInitLabel Unit)))))

def fullInputProgram {N:Nat} (p:Polynomial Nat):FullInputLabel p→
    TM2.Stmt WrapperAlphabet (FullInputLabel p) (WrapperState N)
  | .inl (.inr (.inr .ready)) =>
      .load (fun s => {s with core:=unaryZeroWrapperLens.put s.core default}) <|
      .goto fun _ => .inr (.inl (.inl .copy))
  | .inl label => mapLabelStmt Sum.inl (inputWidthProgram p label)
  | .inr (.inl (.inr (.inr ()))) =>
      .goto fun _ => .inr (.inr (.inl .reverseSaved))
  | .inr (.inl label) =>
      mapLabelStmt (fun next => .inr (.inl next)) (lengthPrefixProgram label)
  | .inr (.inr (.inl .done)) =>
      .goto fun _ => .inr (.inr (.inr (.inl .start)))
  | .inr (.inr (.inl label)) =>
      mapLabelStmt (fun next => match next with
        | .inl phaseLabel => .inr (.inr (.inl phaseLabel))
        | .inr () => .inr (.inr (.inr (.inl .start))))
        ((physicalRawWrapperProgram (N:=N)) (.inl label))
  | .inr (.inr (.inr (.inl .done))) =>
      .goto fun _ => .inr (.inr (.inr (.inr (.inl .mark))))
  | .inr (.inr (.inr (.inl label))) =>
      mapLabelStmt (fun next => match next with
        | .inl phaseLabel => .inr (.inr (.inr (.inl phaseLabel)))
        | .inr () => .inr (.inr (.inr (.inr (.inl .mark)))))
        ((paddingWrapperProgram (N:=N)) (.inl label))
  | .inr (.inr (.inr (.inr (.inl .done)))) =>
      .goto fun _ => .inr (.inr (.inr (.inr (.inr (.inl .zeroCopy)))))
  | .inr (.inr (.inr (.inr (.inl label)))) =>
      mapLabelStmt (fun next => match next with
        | .inl phaseLabel => .inr (.inr (.inr (.inr (.inl phaseLabel))))
        | .inr () => .inr (.inr (.inr (.inr (.inr (.inl .zeroCopy))))))
        ((finalizeInputWrapperProgram (N:=N)) (.inl label))
  | .inr (.inr (.inr (.inr (.inr (.inl .done))))) =>
      .goto fun _ => .inr (.inr (.inr (.inr (.inr (.inr ())))))
  | .inr (.inr (.inr (.inr (.inr (.inl label))))) =>
      mapLabelStmt
        (fun next => .inr (.inr (.inr (.inr (.inr (.inl next))))))
        (coreInitProgram label)
  | .inr (.inr (.inr (.inr (.inr (.inr ()))))) => .halt

def fullInputCfg {N:Nat} {p:Polynomial Nat} (label:FullInputLabel p)
    (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N):=
  ⟨some label,state,tapes⟩

def embedWidthFull {p:Polynomial Nat}:InputWidthLabel p→ FullInputLabel p:=
  Sum.inl

def embedLengthFull {p:Polynomial Nat}:LengthPrefixLabel→ FullInputLabel p:=
  fun label => .inr (.inl label)

theorem fullInput_lift_width {N:Nat} (p:Polynomial Nat)
    {steps:Nat}
    {c d:TM2.Cfg WrapperAlphabet (InputWidthLabel p) (WrapperState N)}
    (hrun:((fun o => o.bind (TM2.step (inputWidthProgram p)))^[steps])
      (some c)=some d) (hd:d.l.isSome):
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[steps])
      (some (mapLabelCfg embedWidthFull c)) =
    some (mapLabelCfg embedWidthFull d):=by
  apply iterate_mapLabelProgram_until_exit (inputWidthProgram p)
    (fullInputProgram p) embedWidthFull ?_ hrun hd
  intro label hnonhalt
  rcases label with scan | power
  · cases scan <;>
      simp [embedWidthFull,fullInputProgram,inputWidthProgram,mapLabelStmt]
        at hnonhalt ⊢
  · rcases power with power | boundary
    · simp [embedWidthFull,fullInputProgram,inputWidthProgram,mapLabelStmt,
        mapLabelStmt_comp,Function.comp_def]
    · cases boundary <;>
        simp [embedWidthFull,fullInputProgram,inputWidthProgram,mapLabelStmt,
          mapLabelStmt_comp,Function.comp_def,widthPowerCoreSpliceProgram,
          widthBoundaryCoreProgram,lensSpliceProgram,liftCoreStmt,
          lensRenameStmt] at hnonhalt ⊢

theorem fullInput_lift_length {N:Nat} (p:Polynomial Nat)
    {steps:Nat}
    {c d:TM2.Cfg WrapperAlphabet LengthPrefixLabel (WrapperState N)}
    (hrun:((fun o => o.bind (TM2.step lengthPrefixProgram))^[steps])
      (some c)=some d) (hd:d.l.isSome):
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[steps])
      (some (mapLabelCfg embedLengthFull c)) =
    some (mapLabelCfg embedLengthFull d):=by
  apply iterate_mapLabelProgram_until_exit lengthPrefixProgram
    (fullInputProgram p) embedLengthFull ?_ hrun hd
  intro label hnonhalt
  rcases label with zero | tail
  · cases zero <;>
      simp [embedLengthFull,fullInputProgram,lengthPrefixProgram,mapLabelStmt,
        mapLabelStmt_comp,Function.comp_def,lensRenameStmt] at hnonhalt ⊢
  · rcases tail with count | unit
    · rcases count with inc | outer
      · cases inc <;>
          simp [embedLengthFull,fullInputProgram,lengthPrefixProgram,
            mapLabelStmt,mapLabelStmt_comp,Function.comp_def,
            lensRenameStmt] at hnonhalt ⊢
      · cases outer <;>
          simp [embedLengthFull,fullInputProgram,lengthPrefixProgram,
            mapLabelStmt,mapLabelStmt_comp,Function.comp_def,
            lensRenameStmt] at hnonhalt ⊢
    · cases unit
      simp [embedLengthFull,fullInputProgram,lengthPrefixProgram] at hnonhalt

def embedRawFull {p:Polynomial Nat}:
    Sum PhysicalRawLabel Unit→ FullInputLabel p
  | .inl label => .inr (.inr (.inl label))
  | .inr () => .inr (.inr (.inr (.inl .start)))

def embedPaddingFull {p:Polynomial Nat}:
    Sum PaddingLabel Unit→ FullInputLabel p
  | .inl label => .inr (.inr (.inr (.inl label)))
  | .inr () => .inr (.inr (.inr (.inr (.inl .mark))))

def embedFinalizeFull {p:Polynomial Nat}:
    Sum FinalizeInputLabel Unit→ FullInputLabel p
  | .inl label => .inr (.inr (.inr (.inr (.inl label))))
  | .inr () => .inr (.inr (.inr (.inr (.inr (.inl .zeroCopy)))))

def embedCoreInitFull {p:Polynomial Nat}:CoreInitLabel→ FullInputLabel p:=
  fun label => .inr (.inr (.inr (.inr (.inr (.inl label)))))

theorem fullInput_lift_raw {N:Nat} (p:Polynomial Nat)
    {steps:Nat}
    {c d:TM2.Cfg WrapperAlphabet (Sum PhysicalRawLabel Unit) (WrapperState N)}
    (hrun:((fun o => o.bind (TM2.step physicalRawWrapperProgram))^[steps])
      (some c)=some d) (hd:d.l.isSome):
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[steps])
      (some (mapLabelCfg embedRawFull c)) =
    some (mapLabelCfg embedRawFull d):=by
  apply iterate_mapLabelProgram_until_exit physicalRawWrapperProgram
    (fullInputProgram p) embedRawFull ?_ hrun hd
  intro label hnonhalt
  rcases label with phaseLabel | unit
  · cases phaseLabel <;>
      simp [physicalRawWrapperProgram,physicalRawCoreProgram,
        liftCoreProgramSame,liftCoreStmt,collapseEmptyLabel,
        lensSpliceProgram,embedRawFull,fullInputProgram,mapLabelStmt,
        mapLabelStmt_comp,Function.comp_def,lensRenameStmt] at hnonhalt ⊢
  · cases unit
    exact (hnonhalt (by simp [physicalRawWrapperProgram,physicalRawCoreProgram,
      liftCoreProgramSame,liftCoreStmt,collapseEmptyLabel,
      lensSpliceProgram,mapLabelStmt])).elim

theorem fullInput_lift_padding {N:Nat} (p:Polynomial Nat)
    {steps:Nat}
    {c d:TM2.Cfg WrapperAlphabet (Sum PaddingLabel Unit) (WrapperState N)}
    (hrun:((fun o => o.bind (TM2.step paddingWrapperProgram))^[steps])
      (some c)=some d) (hd:d.l.isSome):
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[steps])
      (some (mapLabelCfg embedPaddingFull c)) =
    some (mapLabelCfg embedPaddingFull d):=by
  apply iterate_mapLabelProgram_until_exit paddingWrapperProgram
    (fullInputProgram p) embedPaddingFull ?_ hrun hd
  intro label hnonhalt
  rcases label with phaseLabel | unit
  · cases phaseLabel <;>
      simp [paddingWrapperProgram,paddingCoreProgram,liftCoreProgramSame,
        liftCoreStmt,collapseEmptyLabel,lensSpliceProgram,embedPaddingFull,
        fullInputProgram,mapLabelStmt,mapLabelStmt_comp,Function.comp_def,
        lensRenameStmt] at hnonhalt ⊢
  · cases unit
    exact (hnonhalt (by simp [paddingWrapperProgram,paddingCoreProgram,
      liftCoreProgramSame,liftCoreStmt,collapseEmptyLabel,
      lensSpliceProgram,mapLabelStmt])).elim

theorem fullInput_lift_finalize {N:Nat} (p:Polynomial Nat)
    {steps:Nat}
    {c d:TM2.Cfg WrapperAlphabet (Sum FinalizeInputLabel Unit)
      (WrapperState N)}
    (hrun:((fun o => o.bind (TM2.step finalizeInputWrapperProgram))^[steps])
      (some c)=some d) (hd:d.l.isSome):
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[steps])
      (some (mapLabelCfg embedFinalizeFull c)) =
    some (mapLabelCfg embedFinalizeFull d):=by
  apply iterate_mapLabelProgram_until_exit finalizeInputWrapperProgram
    (fullInputProgram p) embedFinalizeFull ?_ hrun hd
  intro label hnonhalt
  rcases label with phaseLabel | unit
  · cases phaseLabel <;>
      simp [finalizeInputWrapperProgram,finalizeInputCoreProgram,
        liftCoreProgramSame,liftCoreStmt,collapseEmptyLabel,
        lensSpliceProgram,embedFinalizeFull,fullInputProgram,mapLabelStmt,
        mapLabelStmt_comp,Function.comp_def,lensRenameStmt] at hnonhalt ⊢
  · cases unit
    exact (hnonhalt (by simp [finalizeInputWrapperProgram,
      finalizeInputCoreProgram,liftCoreProgramSame,liftCoreStmt,
      collapseEmptyLabel,lensSpliceProgram,mapLabelStmt])).elim

theorem fullInput_lift_coreInit {N:Nat} (p:Polynomial Nat)
    {steps:Nat}
    {c d:TM2.Cfg WrapperAlphabet CoreInitLabel (WrapperState N)}
    (hrun:((fun o => o.bind (TM2.step coreInitProgram))^[steps])
      (some c)=some d) (hd:d.l.isSome):
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[steps])
      (some (mapLabelCfg embedCoreInitFull c)) =
    some (mapLabelCfg embedCoreInitFull d):=by
  apply iterate_mapLabelProgram_until_exit coreInitProgram
    (fullInputProgram p) embedCoreInitFull ?_ hrun hd
  intro label hnonhalt
  cases label <;>
    simp [embedCoreInitFull,fullInputProgram,coreInitProgram,mapLabelStmt]
      at hnonhalt ⊢

def fullInputWidthFinal {N:Nat} (p:Polynomial Nat) (x:List Nat)
    (state:WrapperState N):
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N):=
  mapLabelCfg embedWidthFull
    (inputWidthReadyCfg p (bitSize x) {state with heldInput:=none}
      (inputWidthScannedStacks (encode x)))

def resetLengthPrefixState {N:Nat} (state:WrapperState N):
    WrapperState N:=
  {state with core:=unaryZeroWrapperLens.put state.core default}

def fullInputLengthStart {N:Nat} (p:Polynomial Nat) (x:List Nat)
    (state:WrapperState N):
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N):=
  let c:=fullInputWidthFinal p x state
  mapLabelCfg embedLengthFull
    (lengthPrefixCfg (.inl .copy) (resetLengthPrefixState c.var)
      (lengthPrefixInitialStacks (simulationWordWidth p x) x.length c.stk))

theorem fullInput_width_complete {N:Nat} (p:Polynomial Nat)
    (x:List Nat) (state:WrapperState N):
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
        4 * bitSize x + (simpleMajorantEvalCostPolynomial p).eval (bitSize x) + 5])
      (some (fullInputCfg (.inl (.inl .scan)) {state with heldInput:=none}
        (inputWidthInitialStacks (encode x)))) =
    some (fullInputWidthFinal p x state):=by
  apply fullInput_lift_width p
    (inputWidth_complete_run (N:=N) p x state) rfl

theorem fullInput_width_bridge {N:Nat} (p:Polynomial Nat)
    (x:List Nat) (state:WrapperState N):
    TM2.step (fullInputProgram p) (fullInputWidthFinal p x state) =
    some (fullInputCfg (.inr (.inl (.inl .copy)))
      (resetLengthPrefixState (fullInputWidthFinal p x state).var)
      (fullInputWidthFinal p x state).stk):=by
  rfl

theorem fullInput_width_bridge_start {N:Nat} (p:Polynomial Nat)
    (x:List Nat) (state:WrapperState N):
    TM2.step (fullInputProgram p) (fullInputWidthFinal p x state) =
    some (fullInputLengthStart p x state):=by
  rw [fullInput_width_bridge]
  apply congrArg some
  simp only [fullInputLengthStart,fullInputCfg,mapLabelCfg,
    lengthPrefixCfg,resetLengthPrefixState]
  congr 1
  funext k
  cases k with
  | input | output => rfl
  | core k =>
      cases k <;>
        simp [lengthPrefixInitialStacks,fullInputWidthFinal,
          inputWidthReadyCfg,inputWidthPowerFinalCfg,liftCoreCfg,
          wrapperCoreStacks,lensReturnCfg,lensRenamedCfg,renamedStacks,
          unaryPowerWrapperRenaming,unaryMulCoreRenaming,unaryMulStacks,
          unaryPowerCfg,inputWidthScannedStacks,inputSeparatorCount_encode,
          unaryMarkers,simulationWordWidth,List.replicate_succ,
          Function.update] <;> rfl

def fullInputLengthFinal {N:Nat} (p:Polynomial Nat) (x:List Nat)
    (state:WrapperState N):
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N):=
  let c:=fullInputWidthFinal p x state
  mapLabelCfg embedLengthFull
    (lengthPrefixCfg (.inr (.inr ()))
      (lengthPrefixFinalState c.var)
      (lengthPrefixFinalStacks (simulationWordWidth p x) x.length c.stk))

theorem fullInput_length_complete {N:Nat} (p:Polynomial Nat)
    (x:List Nat) (state:WrapperState N):
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
        2 * simulationWordWidth p x + 3 +
          (x.length * (2 * simulationWordWidth p x + 4) + 2)])
      (some (fullInputLengthStart p x state)) =
    some (fullInputLengthFinal p x state):=by
  let c:=fullInputWidthFinal p x state
  have hlocal:=lengthPrefix_complete
    (N:=N) (w:=simulationWordWidth p x) (count:=x.length)
    c.var c.stk
  have hlift:=fullInput_lift_length p hlocal rfl
  exact hlift

theorem fullInput_length_bridge {N:Nat} (p:Polynomial Nat)
    (x:List Nat) (state:WrapperState N):
    TM2.step (fullInputProgram p) (fullInputLengthFinal p x state) =
    some (fullInputCfg (.inr (.inr (.inl .reverseSaved)))
      (fullInputLengthFinal p x state).var
      (fullInputLengthFinal p x state).stk):=by
  rfl

def fullInputRawStart {N:Nat} (p:Polynomial Nat) (x:List Nat)
    (state:WrapperState N):
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N):=
  let c:=fullInputLengthFinal p x state
  mapLabelCfg embedRawFull
    (liftCoreCfgSame
      (lensRenamedCfg physicalRawWrapperRenaming moveWrapperLens
        (physicalRawCfg .reverseSaved
          ((encode x).reverse.map sparseOfInputSymbol) []
          ((fixedBits (simulationWordWidth p x) x.length).map
            SparseSymbol.bit) [])
        c.var.core (fun k => c.stk (.core k)))
      c.var (c.stk .input) (c.stk .output))

theorem fullInput_length_bridge_start {N:Nat} (p:Polynomial Nat)
    (x:List Nat) (state:WrapperState N):
    TM2.step (fullInputProgram p) (fullInputLengthFinal p x state) =
    some (fullInputRawStart p x state):=by
  rw [fullInput_length_bridge]
  apply congrArg some
  simp only [fullInputRawStart,fullInputCfg,mapLabelCfg,liftCoreCfgSame,
    liftCoreCfg,lensRenamedCfg,physicalRawCfg]
  congr 1
  funext k
  cases k with
  | input | output => rfl
  | core k =>
      cases k <;>
        simp [wrapperCoreStacks,renamedStacks,physicalRawWrapperRenaming,
          physicalRawStacks,fullInputLengthFinal,lengthPrefixCfg,
          lengthPrefixFinalStacks,fullInputWidthFinal,inputWidthReadyCfg,
          inputWidthPowerFinalCfg,liftCoreCfg,lensReturnCfg,
          lensRenamedCfg,unaryMulCoreRenaming,unaryPowerCfg,
          unaryMulStacks,inputWidthScannedStacks,simulationWordWidth,
          Function.update] <;> rfl

def fullInputRawFinal {N:Nat} (p:Polynomial Nat) (x:List Nat)
    (state:WrapperState N):
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N):=
  let c:=fullInputLengthFinal p x state
  mapLabelCfg embedRawFull
    (liftCoreCfgSame
      (lensReturnCfg physicalRawWrapperRenaming moveWrapperLens ()
        (physicalRawCfg .done []
          (physicalPaddingRaw (simulationWordWidth p x) x) [] [])
        c.var.core (fun k => c.stk (.core k)))
      c.var (c.stk .input) (c.stk .output))

theorem fullInput_raw_complete {N:Nat} (p:Polynomial Nat)
    (x:List Nat) (state:WrapperState N):
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
        bitSize x + 2 * simulationWordWidth p x + 5])
      (some (fullInputRawStart p x state)) =
    some (fullInputRawFinal p x state):=by
  let c:=fullInputLengthFinal p x state
  have hlocal:=physicalRaw_wrapper_correct
    (N:=N) (simulationWordWidth p x) x c.var c.stk
  have hlift:=fullInput_lift_raw p hlocal rfl
  exact hlift

def fullInputPaddingFinal {N:Nat} (p:Polynomial Nat) (x:List Nat)
    (state:WrapperState N):
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N):=
  let c:=fullInputRawFinal p x state
  let w:=simulationWordWidth p x
  mapLabelCfg embedPaddingFull
    (liftCoreCfgSame
      (lensReturnCfg paddingWrapperRenaming paddingWrapperLens ()
        (paddingCfg .done default [] (unaryMarkers w) [] []
          (encodeWordList w (x.length::x)).reverse)
        c.var.core (fun k => c.stk (.core k)))
      c.var (c.stk .input) (c.stk .output))

def fullInputPaddingStart {N:Nat} (p:Polynomial Nat) (x:List Nat)
    (state:WrapperState N):
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N):=
  let c:=fullInputRawFinal p x state
  let w:=simulationWordWidth p x
  mapLabelCfg embedPaddingFull
    (liftCoreCfgSame
      (lensRenamedCfg paddingWrapperRenaming paddingWrapperLens
        (paddingCfg .start default (physicalPaddingRaw w x)
          (unaryMarkers w) [] [] [])
        c.var.core (fun k => c.stk (.core k)))
      c.var (c.stk .input) (c.stk .output))

theorem fullInputRawFinal_eq_paddingStart {N:Nat} (p:Polynomial Nat)
    (x:List Nat) (state:WrapperState N):
    fullInputRawFinal p x state=fullInputPaddingStart p x state:=by
  simp only [fullInputPaddingStart,fullInputRawFinal,mapLabelCfg,
    liftCoreCfgSame,liftCoreCfg,lensReturnCfg,lensRenamedCfg,
    physicalRawCfg,paddingCfg]
  congr 1
  funext k
  cases k with
  | input | output => rfl
  | core k => cases k <;>
      simp [wrapperCoreStacks,renamedStacks,physicalRawWrapperRenaming,
        paddingWrapperRenaming,physicalRawStacks,paddingStacks,
        Function.update] <;> rfl

theorem fullInput_padding_complete {N:Nat} (p:Polynomial Nat)
    (x:List Nat) (state:WrapperState N)
    (hlen:x.length < 2 ^ simulationWordWidth p x)
    (hfit:∀ n∈ x,n < 2 ^ simulationWordWidth p x):
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
        1 + (x.length + 1) * (3 * simulationWordWidth p x + 5) + 1])
      (some (fullInputPaddingStart p x state)) =
    some (fullInputPaddingFinal p x state):=by
  let c:=fullInputRawFinal p x state
  let w:=simulationWordWidth p x
  have hlocal:=padding_wrapper_correct
    (N:=N) w x hlen hfit c.var c.stk
  have hlift:=fullInput_lift_padding p hlocal rfl
  exact hlift

def fullInputFinalizeFinal {N:Nat} (p:Polynomial Nat) (x:List Nat)
    (state:WrapperState N):
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N):=
  let c:=fullInputPaddingFinal p x state
  let w:=simulationWordWidth p x
  mapLabelCfg embedFinalizeFull
    (liftCoreCfgSame
      (lensReturnCfg finalizeInputWrapperRenaming moveWrapperLens ()
        (finalizeInputCfg .done [] (encodeInputStack w (x.length::x)))
        c.var.core (fun k => c.stk (.core k)))
      c.var (c.stk .input) (c.stk .output))

def fullInputFinalizeStart {N:Nat} (p:Polynomial Nat) (x:List Nat)
    (state:WrapperState N):
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N):=
  let c:=fullInputPaddingFinal p x state
  let w:=simulationWordWidth p x
  mapLabelCfg embedFinalizeFull
    (liftCoreCfgSame
      (lensRenamedCfg finalizeInputWrapperRenaming moveWrapperLens
        (finalizeInputCfg .mark (encodeWordList w (x.length::x)).reverse [])
        c.var.core (fun k => c.stk (.core k)))
      c.var (c.stk .input) (c.stk .output))

theorem fullInputPaddingFinal_eq_finalizeStart {N:Nat}
    (p:Polynomial Nat) (x:List Nat) (state:WrapperState N):
    fullInputPaddingFinal p x state=fullInputFinalizeStart p x state:=by
  simp only [fullInputFinalizeStart,fullInputPaddingFinal,mapLabelCfg,
    liftCoreCfgSame,liftCoreCfg,lensReturnCfg,lensRenamedCfg,
    paddingCfg,finalizeInputCfg]
  congr 1
  funext k
  cases k with
  | input | output => rfl
  | core k => cases k <;>
      simp [wrapperCoreStacks,renamedStacks,paddingWrapperRenaming,
        finalizeInputWrapperRenaming,paddingStacks,finalizeInputStacks,
        encodeInputStack,Function.update] <;> rfl

theorem fullInput_finalize_complete {N:Nat} (p:Polynomial Nat)
    (x:List Nat) (state:WrapperState N):
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
        (encodeWordList (simulationWordWidth p x) (x.length::x)).length + 4])
      (some (fullInputFinalizeStart p x state)) =
    some (fullInputFinalizeFinal p x state):=by
  let c:=fullInputPaddingFinal p x state
  let w:=simulationWordWidth p x
  have hlocal:=finalizeInput_wrapper_correct
    (N:=N) w (x.length::x) c.var c.stk
  have hlift:=fullInput_lift_finalize p hlocal rfl
  exact hlift

def fullInputCoreFinal {N:Nat} (p:Polynomial Nat) (x:List Nat)
    (state:WrapperState N):
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N):=
  let c:=fullInputFinalizeFinal p x state
  mapLabelCfg embedCoreInitFull
    (coreInitCfg .done default
      (coreInitFinalStacks (simulationWordWidth p x) c.stk))

def fullInputCoreStart {N:Nat} (p:Polynomial Nat) (x:List Nat)
    (state:WrapperState N):
    TM2.Cfg WrapperAlphabet (FullInputLabel p) (WrapperState N):=
  let c:=fullInputFinalizeFinal p x state
  mapLabelCfg embedCoreInitFull
    (coreInitCfg .zeroCopy c.var
      (Function.update
        (Function.update c.stk (.core .work1)
          (unaryMarkers (bitSize x + 1)))
        (.core .work3) (unaryMarkers (simulationWordWidth p x))))

theorem fullInputFinalizeFinal_eq_coreStart {N:Nat}
    (p:Polynomial Nat) (x:List Nat) (state:WrapperState N):
    fullInputFinalizeFinal p x state=fullInputCoreStart p x state:=by
  simp only [fullInputCoreStart,fullInputFinalizeFinal,mapLabelCfg,
    liftCoreCfgSame,liftCoreCfg,lensReturnCfg,finalizeInputCfg,coreInitCfg]
  congr 1
  funext k
  cases k with
  | input | output => rfl
  | core k => cases k <;>
      simp [wrapperCoreStacks,renamedStacks,finalizeInputWrapperRenaming,
        finalizeInputStacks,fullInputPaddingFinal,fullInputRawFinal,
        fullInputLengthFinal,fullInputWidthFinal,lensReturnCfg,
        lensRenamedCfg,liftCoreCfgSame,liftCoreCfg,
        paddingWrapperRenaming,physicalRawWrapperRenaming,
        paddingCfg,paddingStacks,physicalRawCfg,physicalRawStacks,
        lengthPrefixCfg,lengthPrefixFinalStacks,inputWidthReadyCfg,
        inputWidthPowerFinalCfg,unaryMulCoreRenaming,unaryPowerCfg,
        unaryMulStacks,inputWidthScannedStacks,unaryMarkers,
        bitSize,Function.update] <;> rfl

theorem fullInput_core_complete {N:Nat} (p:Polynomial Nat)
    (x:List Nat) (state:WrapperState N):
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
        3 * simulationWordWidth p x + (bitSize x + 1) + 5])
      (some (fullInputCoreStart p x state)) =
    some (fullInputCoreFinal p x state):=by
  let c:=fullInputFinalizeFinal p x state
  let w:=simulationWordWidth p x
  have hlocal:=coreInit_correct (N:=N) (w:=w) c.var
    (unaryMarkers (bitSize x + 1)) c.stk
    (by simp [c,fullInputFinalizeFinal,fullInputPaddingFinal,
      fullInputRawFinal,fullInputLengthFinal,fullInputWidthFinal,
      mapLabelCfg,liftCoreCfgSame,liftCoreCfg,wrapperCoreStacks,
      collapseEmptyLabel,lensReturnCfg,lensRenamedCfg,renamedStacks,
      finalizeInputWrapperRenaming,paddingWrapperRenaming,
      physicalRawWrapperRenaming,unaryPowerWrapperRenaming,
      unaryMulCoreRenaming,finalizeInputCfg,finalizeInputStacks,
      paddingCfg,paddingStacks,physicalRawCfg,physicalRawStacks,
      inputWidthReadyCfg,inputWidthPowerFinalCfg,unaryMulStacks,
      lengthPrefixCfg,lengthPrefixFinalStacks,inputWidthScannedStacks,
      Function.update] <;> rfl)
    (by simp [c,fullInputFinalizeFinal,fullInputPaddingFinal,
      mapLabelCfg,liftCoreCfgSame,liftCoreCfg,wrapperCoreStacks,
      collapseEmptyLabel,lensReturnCfg,lensRenamedCfg,renamedStacks,
      finalizeInputWrapperRenaming,paddingWrapperRenaming,
      finalizeInputCfg,finalizeInputStacks,paddingCfg,paddingStacks,
      lengthPrefixCfg,lengthPrefixFinalStacks,Function.update] <;> rfl)
    (by simp [c,fullInputFinalizeFinal,fullInputPaddingFinal,
      fullInputRawFinal,fullInputLengthFinal,fullInputWidthFinal,
      mapLabelCfg,liftCoreCfgSame,liftCoreCfg,wrapperCoreStacks,
      collapseEmptyLabel,lensReturnCfg,lensRenamedCfg,renamedStacks,
      finalizeInputWrapperRenaming,paddingWrapperRenaming,
      physicalRawWrapperRenaming,unaryPowerWrapperRenaming,
      finalizeInputCfg,finalizeInputStacks,paddingCfg,paddingStacks,
      physicalRawCfg,physicalRawStacks,inputWidthReadyCfg,
      inputWidthPowerFinalCfg,lengthPrefixCfg,lengthPrefixFinalStacks,
      inputWidthScannedStacks,Function.update] <;> rfl)
    (by simp [c,fullInputFinalizeFinal,fullInputPaddingFinal,
      fullInputRawFinal,fullInputLengthFinal,fullInputWidthFinal,
      mapLabelCfg,liftCoreCfgSame,liftCoreCfg,wrapperCoreStacks,
      collapseEmptyLabel,lensReturnCfg,lensRenamedCfg,renamedStacks,
      finalizeInputWrapperRenaming,paddingWrapperRenaming,
      physicalRawWrapperRenaming,unaryPowerWrapperRenaming,
      finalizeInputCfg,finalizeInputStacks,paddingCfg,paddingStacks,
      physicalRawCfg,physicalRawStacks,inputWidthReadyCfg,
      inputWidthPowerFinalCfg,lengthPrefixCfg,lengthPrefixFinalStacks,
      inputWidthScannedStacks,Function.update] <;> rfl)
  have hlift:=fullInput_lift_coreInit p hlocal rfl
  simpa [c,w,fullInputCoreStart,fullInputCoreFinal,unaryMarkers] using hlift

def fullInputCost (p:Polynomial Nat) (x:List Nat):Nat:=
  (4 * bitSize x +
      (simpleMajorantEvalCostPolynomial p).eval (bitSize x) + 5) + 1 +
  (2 * simulationWordWidth p x + 3 +
      (x.length * (2 * simulationWordWidth p x + 4) + 2)) + 1 +
  (bitSize x + 2 * simulationWordWidth p x + 5) +
  (1 + (x.length + 1) * (3 * simulationWordWidth p x + 5) + 1) +
  ((encodeWordList (simulationWordWidth p x) (x.length::x)).length + 4) +
  (3 * simulationWordWidth p x + (bitSize x + 1) + 5)

theorem fullInput_complete {N:Nat} (p:Polynomial Nat)
    (x:List Nat) (state:WrapperState N)
    (hlen:x.length < 2 ^ simulationWordWidth p x)
    (hfit:∀ n∈ x,n < 2 ^ simulationWordWidth p x):
    ((fun o => o.bind (TM2.step (fullInputProgram p)))^[fullInputCost p x])
      (some (fullInputCfg (.inl (.inl .scan)) {state with heldInput:=none}
        (inputWidthInitialStacks (encode x)))) =
    some (fullInputCoreFinal p x state):=by
  have h₁:=fullInput_width_complete (N:=N) p x state
  have h₂step:=fullInput_width_bridge_start (N:=N) p x state
  have h₂:
      ((fun o => o.bind (TM2.step (fullInputProgram p)))^[1])
        (some (fullInputWidthFinal p x state)) =
      some (fullInputLengthStart p x state):=by simpa using h₂step
  have h₃:=fullInput_length_complete (N:=N) p x state
  have h₄step:=fullInput_length_bridge_start (N:=N) p x state
  have h₄:
      ((fun o => o.bind (TM2.step (fullInputProgram p)))^[1])
        (some (fullInputLengthFinal p x state)) =
      some (fullInputRawStart p x state):=by simpa using h₄step
  have h₅:=fullInput_raw_complete (N:=N) p x state
  have h₆:=fullInput_padding_complete (N:=N) p x state hlen hfit
  have h₇:=fullInput_finalize_complete (N:=N) p x state
  have h₈:=fullInput_core_complete (N:=N) p x state
  have h₆':=(congrArg
    (fun cfg => ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
      1 + (x.length + 1) * (3 * simulationWordWidth p x + 5) + 1]) cfg)
    (congrArg some (fullInputRawFinal_eq_paddingStart (N:=N) p x state))).trans h₆
  have h₇':=(congrArg
    (fun cfg => ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
      (encodeWordList (simulationWordWidth p x) (x.length::x)).length + 4]) cfg)
    (congrArg some
      (fullInputPaddingFinal_eq_finalizeStart (N:=N) p x state))).trans h₇
  have h₈':=(congrArg
    (fun cfg => ((fun o => o.bind (TM2.step (fullInputProgram p)))^[
      3 * simulationWordWidth p x + (bitSize x + 1) + 5]) cfg)
    (congrArg some
      (fullInputFinalizeFinal_eq_coreStart (N:=N) p x state))).trans h₈
  have h:=chain_iterations _ (chain_iterations _ (chain_iterations _
    (chain_iterations _ (chain_iterations _ (chain_iterations _
      (chain_iterations _ h₁ h₂) h₃) h₄) h₅) h₆') h₇') h₈'
  simpa [fullInputCost,Nat.add_assoc] using h

theorem fullInputCoreFinal_eq_canonical {N:Nat} (p:Polynomial Nat)
    (x:List Nat) (state:WrapperState N):
    fullInputCoreFinal p x state =
      fullInputCfg
        (.inr (.inr (.inr (.inr (.inr (.inl .done)))))) default
        (wrapperCoreStacks
          (coreStacks (simulationWordWidth p x) (sparseInitState (x.length::x)))
          [] []):=by
  simp only [fullInputCoreFinal,mapLabelCfg,coreInitCfg,fullInputCfg]
  congr 1
  funext k
  cases k with
    | input =>
        simp [fullInputCoreFinal,coreInitFinalStacks,fullInputFinalizeFinal,
          fullInputPaddingFinal,fullInputRawFinal,fullInputLengthFinal,
          fullInputWidthFinal,wrapperCoreStacks,inputWidthInitialStacks,
          inputWidthScannedStacks,mapLabelCfg,liftCoreCfgSame,liftCoreCfg,
          collapseEmptyLabel,lensReturnCfg,
          lensRenamedCfg,renamedStacks,finalizeInputWrapperRenaming,
          paddingWrapperRenaming,physicalRawWrapperRenaming,
          unaryPowerWrapperRenaming,unaryMulCoreRenaming,coreStacks,
          sparseInitState,Function.update] <;> rfl
    | output =>
        simp [fullInputCoreFinal,coreInitFinalStacks,fullInputFinalizeFinal,
          fullInputPaddingFinal,fullInputRawFinal,fullInputLengthFinal,
          fullInputWidthFinal,wrapperCoreStacks,inputWidthInitialStacks,
          inputWidthScannedStacks,mapLabelCfg,liftCoreCfgSame,liftCoreCfg,
          collapseEmptyLabel,lensReturnCfg,
          lensRenamedCfg,renamedStacks,finalizeInputWrapperRenaming,
          paddingWrapperRenaming,physicalRawWrapperRenaming,
          unaryPowerWrapperRenaming,unaryMulCoreRenaming,
          Function.update] <;> rfl
    | core k =>
        cases k <;>
          simp [fullInputCoreFinal,coreInitFinalStacks,
            fullInputFinalizeFinal,fullInputPaddingFinal,fullInputRawFinal,
            fullInputLengthFinal,fullInputWidthFinal,wrapperCoreStacks,
            inputWidthInitialStacks,inputWidthScannedStacks,mapLabelCfg,
            liftCoreCfgSame,liftCoreCfg,collapseEmptyLabel,
            lensReturnCfg,lensRenamedCfg,renamedStacks,
            finalizeInputWrapperRenaming,paddingWrapperRenaming,
            physicalRawWrapperRenaming,unaryPowerWrapperRenaming,
            unaryMulCoreRenaming,unaryMulStacks,finalizeInputCfg,
            finalizeInputStacks,paddingCfg,paddingStacks,physicalRawCfg,
            physicalRawStacks,lengthPrefixCfg,lengthPrefixFinalStacks,
            inputWidthReadyCfg,inputWidthPowerFinalCfg,coreStacks,
            sparseInitState,encodeAccumulator,encodeMemoryStack,
            encodeOutputStack,encodeInputStack,Function.update] <;> rfl

@[simp] theorem fullInputCostPolynomial_eval (p:Polynomial Nat) (n:Nat):
    (fullInputCostPolynomial p).eval n =
      let w:=(polynomialSimpleMajorant p).eval n + 1
      (4 * n + (simpleMajorantEvalCostPolynomial p).eval n + 5) + 1 +
      (2 * w + 3 + (n * (2 * w + 4) + 2)) + 1 +
      (n + 2 * w + 5) +
      (1 + (n + 1) * (3 * w + 5) + 1) +
      ((n + 1) * (w + 1) + 4) +
      (3 * w + (n + 1) + 5):=by
  simp [fullInputCostPolynomial,simulationWidthPolynomial]

theorem fullInputCost_le_polynomial (p:Polynomial Nat) (x:List Nat):
    fullInputCost p x≤ (fullInputCostPolynomial p).eval (bitSize x):=by
  rw [fullInputCostPolynomial_eval]
  have hx:=Lax759944Proofs.Encoding.length_le_bitSize x
  simp only [fullInputCost,simulationWordWidth]
  simp only [encodeWordList_length,List.length_cons]
  gcongr

end

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

theorem stepAux_stack_length_le {K Λ σ:Type} {Γ:K→ Type}
    [DecidableEq K] (q:TM2.Stmt Γ Λ σ) (state:σ)
    (tapes:∀ k,List (Γ k)) (stack:K):
    ((TM2.stepAux q state tapes).stk stack).length≤
      (tapes stack).length + stmtPushCount q:=by
  induction q generalizing state tapes with
  | push k f q ih =>
      simp only [TM2.stepAux,stmtPushCount]
      have h:=ih state (Function.update tapes k (f state::tapes k))
      by_cases hk:stack=k
      · subst k
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
      · simp [hk] at h
        exact h.trans (by omega)
  | peek k f q ih =>
      simpa [stmtPushCount] using ih (f state (tapes k).head?) tapes
  | pop k f q ih =>
      simp only [TM2.stepAux,stmtPushCount]
      have h:=ih (f state (tapes k).head?)
        (Function.update tapes k (tapes k).tail)
      by_cases hk:stack=k
      · subst k
        simp at h
        exact h.trans (by simp)
      · simpa [hk] using h
  | load f q ih => simpa [stmtPushCount] using ih (f state) tapes
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [TM2.stepAux,stmtPushCount]
      cases h:f state
      · exact (ih₂ state tapes).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
      · exact (ih₁ state tapes).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  | goto f => simp [stmtPushCount]
  | halt => simp [stmtPushCount]

theorem stmtPushCount_le_programPushBound {K Λ σ:Type} {Γ:K→ Type}
    [Fintype Λ] [DecidableEq Λ]
    (program:Λ→ TM2.Stmt Γ Λ σ) (label:Λ):
    stmtPushCount (program label)≤ programPushBound program:=by
  unfold programPushBound
  exact Finset.single_le_sum
    (f:=fun label => stmtPushCount (program label))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ label)

theorem step_stack_length_le {K Λ σ:Type} {Γ:K→ Type}
    [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
    (program:Λ→ TM2.Stmt Γ Λ σ) (c d:TM2.Cfg Γ Λ σ)
    (hstep:TM2.step program c=some d) (stack:K):
    (d.stk stack).length≤
      (c.stk stack).length + programPushBound program:=by
  rcases c with ⟨label,state,tapes⟩
  cases label with
  | none => simp [TM2.step] at hstep
  | some label =>
      simp only [TM2.step,Option.some.injEq] at hstep
      subst d
      exact (stepAux_stack_length_le (program label) state tapes stack).trans
        (Nat.add_le_add_left
          (stmtPushCount_le_programPushBound program label) _)

theorem iterate_stack_length_le {K Λ σ:Type} {Γ:K→ Type}
    [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
    (program:Λ→ TM2.Stmt Γ Λ σ) (n:Nat)
    (c d:TM2.Cfg Γ Λ σ)
    (hrun:((fun o => o.bind (TM2.step program))^[n]) (some c)=some d)
    (stack:K):
    (d.stk stack).length≤
      (c.stk stack).length + n * programPushBound program:=by
  induction n generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply,Option.some.injEq] at hrun
      subst d
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun
      simp only [Option.bind_some] at hrun
      cases hs:TM2.step program c with
      | none =>
          simp only [hs,Option.bind_none] at hrun
          rw [iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          simp only [hs,Option.bind_some] at hrun
          have hfirst:=step_stack_length_le program c c' hs stack
          have hrest:=ih c' hrun
          calc
            (d.stk stack).length
                ≤ (c'.stk stack).length + n * programPushBound program:=hrest
            _≤ ((c.stk stack).length + programPushBound program) +
                n * programPushBound program:=
              Nat.add_le_add_right hfirst _
            _=(c.stk stack).length + Nat.succ n * programPushBound program:=by
              simp [Nat.succ_eq_add_one,Nat.add_mul,Nat.add_assoc,
                Nat.add_comm,Nat.add_left_comm]

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode
open Lax759944.BinaryWordEncoding Lax759944Proofs.Legacy.RamPolytime

noncomputable section

abbrev CombinedLabel (p:Program) (N:Nat)
    (wordBound:Polynomial Nat):=
  Sum (FullInputLabel wordBound) (MiddleLabel p N)

def combinedProgram (p:Program) (N:Nat)
    (hbound:programArgumentBound p <= N) (wordBound:Polynomial Nat):
    CombinedLabel p N wordBound→
      TM2.Stmt WrapperAlphabet (CombinedLabel p N wordBound) (WrapperState N)
  | .inl (.inr (.inr (.inr (.inr (.inr (.inr terminal)))))) =>
      .goto fun _ => .inr (.inl (.fetch (boundPC p 0)))
  | .inl label => mapLabelStmt Sum.inl (fullInputProgram wordBound label)
  | .inr label => mapLabelStmt Sum.inr (middleProgram p N hbound label)

def embedInputCombined {p:Program} {N:Nat} {wordBound:Polynomial Nat}:
    FullInputLabel wordBound→ CombinedLabel p N wordBound:=Sum.inl

def embedMiddleCombined {p:Program} {N:Nat} {wordBound:Polynomial Nat}:
    MiddleLabel p N→ CombinedLabel p N wordBound:=Sum.inr

def embedOutputMiddle {p:Program} {N:Nat}:
    Sum Empty OutputAdapterLabel→ MiddleLabel p N
  | .inl impossible => nomatch impossible
  | .inr label => .inr label

abbrev fullInputTerminal {wordBound:Polynomial Nat}:
    FullInputLabel wordBound:=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))))

theorem combined_lift_input {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (wordBound:Polynomial Nat)
    {steps:Nat}
    {c d:TM2.Cfg WrapperAlphabet (FullInputLabel wordBound) (WrapperState N)}
    (hrun:((fun o => o.bind (TM2.step (fullInputProgram wordBound)))^[steps])
      (some c)=some d) (hd:d.l.isSome):
    ((fun o => o.bind (TM2.step (combinedProgram p N hbound wordBound)))^[steps])
      (some (mapLabelCfg embedInputCombined c)) =
    some (mapLabelCfg embedInputCombined d):=by
  apply iterate_mapLabelProgram_until_exit
    (fullInputProgram wordBound) (combinedProgram p N hbound wordBound)
    embedInputCombined ?_ hrun hd
  intro label hnonhalt
  rcases label with width | rest
  · simp [combinedProgram,embedInputCombined,fullInputProgram,mapLabelStmt]
  · rcases rest with length | rest
    · simp [combinedProgram,embedInputCombined,fullInputProgram,mapLabelStmt]
    · rcases rest with raw | rest
      · simp [combinedProgram,embedInputCombined,fullInputProgram,mapLabelStmt]
      · rcases rest with padding | rest
        · simp [combinedProgram,embedInputCombined,fullInputProgram,mapLabelStmt]
        · rcases rest with finalize | rest
          · simp [combinedProgram,embedInputCombined,fullInputProgram,mapLabelStmt]
          · rcases rest with core | unit
            · cases core <;>
                simp [combinedProgram,embedInputCombined,fullInputProgram,
                  mapLabelStmt] at hnonhalt ⊢
            · cases unit
              simp [fullInputProgram] at hnonhalt

theorem middle_lift_core {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) {steps:Nat}
    {c d:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N)}
    (ambient:WrapperState N) (externalInput externalOutput:List Symbol)
    (hrun:((fun o => o.bind
      (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
      (some c)=some d) (hd:d.l.isSome):
    ((fun o => o.bind (TM2.step (middleProgram p N hbound)))^[steps])
      (some (liftCoreCfg (X:=OutputAdapterLabel) c ambient
        externalInput externalOutput)) =
    some (liftCoreCfg (X:=OutputAdapterLabel) d ambient
      externalInput externalOutput):=by
  let lifted:=liftCoreProgram (finiteInterpreterProgram p N hbound)
    (outputAdapterProgram (N:=N) (L:=FiniteInterpreterLabel p N))
  have hlift:=iterate_liftCoreProgram
    (finiteInterpreterProgram p N hbound)
    (outputAdapterProgram (N:=N) (L:=FiniteInterpreterLabel p N))
    c d ambient externalInput externalOutput hrun
  have hmapped:=iterate_mapLabelProgram_until_exit lifted
    (middleProgram p N hbound) id (by
      intro label hnonhalt
      cases label with
      | inl label =>
          cases label <;>
            simp [lifted,liftCoreProgram,middleProgram] at hnonhalt ⊢ <;>
            (rename_i control; cases control <;>
              simp [lifted,liftCoreProgram,middleProgram,
                finiteInterpreterProgram,finiteControlStmt,
                controlDispatchMachine,lensRenameStmt,liftCoreStmt,
                mapLabelStmt] at hnonhalt ⊢)
      | inr label => simp [lifted,liftCoreProgram,middleProgram]) hlift (by
        simpa [liftCoreCfg] using hd)
  simpa using hmapped

theorem middle_lift_output {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (steps:Nat)
    (c:TM2.Cfg WrapperAlphabet (Sum Empty OutputAdapterLabel)
      (WrapperState N)):
    ((fun o => o.bind (TM2.step (middleProgram p N hbound)))^[steps])
        (some (mapLabelCfg embedOutputMiddle c)) =
      (((fun o => o.bind (TM2.step
        (liftCoreProgram (fun _:Empty => .halt)
          (outputAdapterProgram (N:=N) (L:=Empty)))))^[steps])
          (some c)).map (mapLabelCfg embedOutputMiddle):=by
  apply iterate_mapLabelProgram
  intro label
  rcases label with impossible | output
  · exact nomatch impossible
  · cases output <;> simp [middleProgram,embedOutputMiddle,liftCoreProgram,
      outputAdapterProgram,mapLabelStmt_comp,Function.comp_def,
      mapLabelStmt] <;> try (congr 1 <;> funext x <;> rfl)
    split <;> simp_all [mapLabelStmt] <;> congr 1 <;> funext x <;> rfl

theorem combined_lift_middle {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (wordBound:Polynomial Nat)
    (steps:Nat)
    (c:TM2.Cfg WrapperAlphabet (MiddleLabel p N) (WrapperState N)):
    ((fun o => o.bind
      (TM2.step (combinedProgram p N hbound wordBound)))^[steps])
        (some (mapLabelCfg embedMiddleCombined c)) =
      (((fun o => o.bind (TM2.step (middleProgram p N hbound)))^[steps])
          (some c)).map (mapLabelCfg embedMiddleCombined):=by
  apply iterate_mapLabelProgram
  intro label
  simp [combinedProgram,embedMiddleCombined]

theorem combined_input_bridge {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (wordBound:Polynomial Nat)
    (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    TM2.step (combinedProgram p N hbound wordBound)
      (mapLabelCfg embedInputCombined
        (fullInputCfg
          fullInputTerminal state tapes)) =
    some ⟨some (.inr (.inl (.fetch (boundPC p 0)))),state,tapes⟩:=by
  rfl

theorem combined_input_finish {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (wordBound:Polynomial Nat)
    (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    ((fun o:Option (TM2.Cfg WrapperAlphabet (CombinedLabel p N wordBound)
      (WrapperState N)) => o.bind (TM2.step
        (combinedProgram p N hbound wordBound)))^[1])
      (some (mapLabelCfg embedInputCombined
        (fullInputCfg
          (.inr (.inr (.inr (.inr (.inr (.inl .done)))))) state tapes))) =
    some (mapLabelCfg embedInputCombined
      (fullInputCfg fullInputTerminal state tapes)):=by
  rfl

theorem middle_stopped_bridge {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N)
    (state:WrapperState N)
    (tapes:(k:WrapperStack)→ List (WrapperAlphabet k)):
    TM2.step (middleProgram p N hbound)
      ⟨some (.inl (.control .stopped)),state,tapes⟩ =
    some ⟨some (.inr .initializeState),state,tapes⟩:=by
  simp [middleProgram,TM2.step]

set_option maxHeartbeats 2000000 in
theorem middle_ram_to_output {p:Program} {w t:Nat}
    (hw:0 < w) {input output:List Nat}
    (hram:RunsTo w p input output t):
    ∃ ss coreSteps stopSteps finalState finalTapes,
      ss.out=output∧ sparseStep w p ss=none∧
      ss.mem.Normalized w∧ ss.mem.length≤ t∧ ss.out.length≤ t∧
      coreSteps≤ t * finiteRunUnitBound w 0 t∧
      stopSteps≤ operandEvalBound w ss.mem + 4∧
      finalTapes .output=(coreStacks w ss) .output∧
      ((fun o => o.bind (TM2.step
        (middleProgram p (programArgumentBound p) le_rfl)))^[
          coreSteps + stopSteps + 1])
        (some (liftCoreCfg (X:=OutputAdapterLabel)
          (finiteInterpreterCfg (.fetch (boundPC p 0)) default
            (coreStacks w (sparseInitState input))) default [] [])) =
      some ⟨some (.inr .initializeState),
        WrapperState.coreLens.put default finalState,
        wrapperCoreStacks finalTapes [] []⟩:=by
  rcases ramRunsTo_coreSimulation hw hram with
    ⟨ss,coreSteps,hout,hstop,hm,hmem,houtLength,hcoreBound,
      coreState,hdispatch,hcore⟩
  rcases finite_sparseHalt_to_stopped le_rfl ss hm hstop coreState with
    ⟨stopSteps,hstopBound,finalState,finalTapes,houtTapes,hterminal⟩
  have hcoreLift:=middle_lift_core le_rfl default [] [] hcore rfl
  have hterminalLift:=middle_lift_core le_rfl default [] [] hterminal rfl
  have hbeforeBridge:=chain_iterations
    (fun o:Option (TM2.Cfg WrapperAlphabet
      (MiddleLabel p (programArgumentBound p))
      (WrapperState (programArgumentBound p))) =>
      o.bind (TM2.step (middleProgram p (programArgumentBound p) le_rfl)))
    hcoreLift hterminalLift
  have hbridgeStep:=middle_stopped_bridge (p:=p) le_rfl
    (WrapperState.coreLens.put default finalState)
    (wrapperCoreStacks finalTapes [] [])
  have hbridge:((fun o:Option (TM2.Cfg WrapperAlphabet
      (MiddleLabel p (programArgumentBound p))
      (WrapperState (programArgumentBound p))) =>
      o.bind (TM2.step (middleProgram p (programArgumentBound p) le_rfl)))^[1])
      (some (liftCoreCfg (X:=OutputAdapterLabel)
        (finiteInterpreterCfg (.control .stopped) finalState finalTapes)
        default [] [])) =
      some ⟨some (.inr .initializeState),
        WrapperState.coreLens.put default finalState,
        wrapperCoreStacks finalTapes [] []⟩:=by
    simpa [liftCoreCfg,finiteInterpreterCfg,mapLabelCfg] using hbridgeStep
  have hall:=chain_iterations _ hbeforeBridge hbridge
  refine ⟨ss,coreSteps,stopSteps,finalState,finalTapes,
    hout,hstop,hm,hmem,houtLength,
    hcoreBound,hstopBound,houtTapes, ?_⟩
  simpa [liftCoreCfg,finiteInterpreterCfg,mapLabelCfg,
    WrapperState.coreLens,Nat.add_assoc] using hall

theorem middle_output_complete {p:Program} {N w:Nat}
    (hbound:programArgumentBound p <= N) (state:WrapperState N)
    (tapes:CoreStack→ List SparseSymbol) (output:List Nat)
    (hout:tapes .output=encodeOutputStack w output)
    (hfit:∀ n∈ output,n < 2 ^ w):
    let base:=wrapperCoreStacks tapes [] []
    let decoded:=outputAdapterStacks [] (encode output) base
    let steps:=4 + output.length * (3 * w + 3) +
      (cleanupTotalCost decoded + 1)
    ((fun o => o.bind (TM2.step (middleProgram p N hbound)))^[steps])
      (some ⟨some (.inr .initializeState),state,base⟩) =
    some ⟨none,default,cleanedStacks decoded⟩:=by
  dsimp only
  let base:=wrapperCoreStacks tapes [] []
  have hbase:outputAdapterStacks (encodeOutputStack w output) [] base=base:=by
    funext k
    cases k with
    | input => simp [outputAdapterStacks,base,wrapperCoreStacks]
    | output => simp [outputAdapterStacks,base,wrapperCoreStacks]
    | core k =>
        cases k <;> simp [outputAdapterStacks,base,wrapperCoreStacks,hout]
  rcases output_decode_run state output hfit base with
    ⟨decodedState,hdecode⟩
  rw [hbase] at hdecode
  let decoded:=outputAdapterStacks [] (encode output) base
  have hcleanup:=output_cleanup_run decodedState decoded
  have hdecodeLift:=middle_lift_output (p:=p) hbound
    (4 + output.length * (3 * w + 3))
    (outputAdapterCfg (L:=Empty) .initializeState state base)
  rw [hdecode] at hdecodeLift
  have hcleanupLift:=middle_lift_output (p:=p) hbound
    (cleanupTotalCost decoded + 1)
    (outputAdapterCfg (L:=Empty) (.cleanupPeek .input) decodedState decoded)
  rw [hcleanup] at hcleanupLift
  have hall:=chain_iterations
    (fun o:Option (TM2.Cfg WrapperAlphabet (MiddleLabel p N)
      (WrapperState N)) => o.bind (TM2.step (middleProgram p N hbound)))
    hdecodeLift hcleanupLift
  simpa [outputAdapterCfg,embedOutputMiddle,mapLabelCfg,decoded,
    Nat.add_assoc] using hall

set_option maxHeartbeats 2000000 in
theorem middle_cleanupCost_le {p:Program} {N w steps:Nat}
    (hbound:programArgumentBound p <= N) (input:List Nat)
    (finalState:FullInterpreterState N)
    (finalTapes:CoreStack→ List SparseSymbol)
    (hrun:((fun o => o.bind (TM2.step (middleProgram p N hbound)))^[steps])
      (some (liftCoreCfg (X:=OutputAdapterLabel)
        (finiteInterpreterCfg (.fetch (boundPC p 0)) default
          (coreStacks w (sparseInitState input))) default [] [])) =
      some ⟨some (.inr .initializeState),
        WrapperState.coreLens.put default finalState,
        wrapperCoreStacks finalTapes [] []⟩)
    (output:List Nat):
    cleanupTotalCost
        (outputAdapterStacks [] (encode output)
          (wrapperCoreStacks finalTapes [] []))≤
      2 * (13 * (coreSize w (sparseInitState input) +
        steps * programPushBound (middleProgram p N hbound))) + 13:=by
  let startCfg:TM2.Cfg WrapperAlphabet (MiddleLabel p N) (WrapperState N):=
    liftCoreCfg (X:=OutputAdapterLabel)
    (finiteInterpreterCfg (.fetch (boundPC p 0)) default
      (coreStacks w (sparseInitState input))) default [] []
  let finalCfg:TM2.Cfg WrapperAlphabet (MiddleLabel p N) (WrapperState N):=
    ⟨some (.inr .initializeState),WrapperState.coreLens.put default finalState,
      wrapperCoreStacks finalTapes [] []⟩
  have hb (k:CoreStack):=iterate_stack_length_le
    (middleProgram p N hbound) steps startCfg finalCfg hrun (.core k)
  have hinitial (k:CoreStack):
      (startCfg.stk (.core k)).length≤ coreSize w (sparseInitState input):=by
    dsimp only [startCfg,liftCoreCfg,finiteInterpreterCfg,
      wrapperCoreStacks,coreSize]
    cases k with
    | accumulator =>
        exact Nat.le_add_right_of_le (Nat.le_add_right_of_le
          (Nat.le_add_right _ _))
    | memory =>
        exact Nat.le_add_right_of_le (Nat.le_add_right_of_le
          (Nat.le_add_left _ _))
    | input =>
        exact Nat.le_add_right_of_le (Nat.le_add_left _ _)
    | output => exact Nat.le_add_left _ _
    | work0 | work1 | work2 | work3 | work4 | work5 | work6 | work7 =>
        exact Nat.zero_le _
  have hfinal (k:CoreStack):(finalTapes k).length≤
      coreSize w (sparseInitState input) +
        steps * programPushBound (middleProgram p N hbound):=by
    have hk:=hb k
    dsimp [startCfg,finalCfg,liftCoreCfg,finiteInterpreterCfg,
      wrapperCoreStacks] at hk
    apply hk.trans
    exact Nat.add_le_add_right (hinitial k) _
  have hacc:=hfinal .accumulator
  have hmem:=hfinal .memory
  have hinp:=hfinal .input
  have hw0:=hfinal .work0
  have hw1:=hfinal .work1
  have hw2:=hfinal .work2
  have hw3:=hfinal .work3
  have hw4:=hfinal .work4
  have hw5:=hfinal .work5
  have hw6:=hfinal .work6
  have hw7:=hfinal .work7
  let actualCost:=cleanupTotalCost
    (outputAdapterStacks [] (encode output)
      (wrapperCoreStacks finalTapes [] []))
  have hcost:cleanupTotalCost
      (outputAdapterStacks [] (encode output)
        (wrapperCoreStacks finalTapes [] []))=actualCost:=by
    rfl
  rw [hcost]
  let decodedTapes:=outputAdapterStacks [] (encode output)
    (wrapperCoreStacks finalTapes [] [])
  let bound:=coreSize w (sparseInitState input) +
    steps * programPushBound (middleProgram p N hbound)
  have hdecodedInput:(decodedTapes .input).length≤ bound:=by
    dsimp [decodedTapes,outputAdapterStacks,wrapperCoreStacks]
    exact Nat.zero_le _
  have hdecodedCore (k:CoreStack):(decodedTapes (.core k)).length≤ bound:=by
    cases k with
    | accumulator => simpa [decodedTapes,outputAdapterStacks,wrapperCoreStacks,bound] using! hacc
    | memory => simpa [decodedTapes,outputAdapterStacks,wrapperCoreStacks,bound] using! hmem
    | input => simpa [decodedTapes,outputAdapterStacks,wrapperCoreStacks,bound] using! hinp
    | output =>
        dsimp [decodedTapes,outputAdapterStacks,wrapperCoreStacks]
        exact Nat.zero_le _
    | work0 => simpa [decodedTapes,outputAdapterStacks,wrapperCoreStacks,bound] using! hw0
    | work1 => simpa [decodedTapes,outputAdapterStacks,wrapperCoreStacks,bound] using! hw1
    | work2 => simpa [decodedTapes,outputAdapterStacks,wrapperCoreStacks,bound] using! hw2
    | work3 => simpa [decodedTapes,outputAdapterStacks,wrapperCoreStacks,bound] using! hw3
    | work4 => simpa [decodedTapes,outputAdapterStacks,wrapperCoreStacks,bound] using! hw4
    | work5 => simpa [decodedTapes,outputAdapterStacks,wrapperCoreStacks,bound] using! hw5
    | work6 => simpa [decodedTapes,outputAdapterStacks,wrapperCoreStacks,bound] using! hw6
    | work7 => simpa [decodedTapes,outputAdapterStacks,wrapperCoreStacks,bound] using! hw7
  dsimp only [actualCost]
  change 2 * (decodedTapes .input).length + 1 +
    2 * (decodedTapes (.core .accumulator)).length + 1 +
    2 * (decodedTapes (.core .memory)).length + 1 +
    2 * (decodedTapes (.core .input)).length + 1 +
    2 * (decodedTapes (.core .output)).length + 1 +
    2 * (decodedTapes (.core .work0)).length + 1 +
    2 * (decodedTapes (.core .work1)).length + 1 +
    2 * (decodedTapes (.core .work2)).length + 1 +
    2 * (decodedTapes (.core .work3)).length + 1 +
    2 * (decodedTapes (.core .work4)).length + 1 +
    2 * (decodedTapes (.core .work5)).length + 1 +
    2 * (decodedTapes (.core .work6)).length + 1 +
    2 * (decodedTapes (.core .work7)).length + 1≤
      2 * (13 * bound) + 13
  have ha:=hdecodedCore .accumulator
  have hm:=hdecodedCore .memory
  have hi:=hdecodedCore .input
  have ho:=hdecodedCore .output
  have h0:=hdecodedCore .work0
  have h1:=hdecodedCore .work1
  have h2:=hdecodedCore .work2
  have h3:=hdecodedCore .work3
  have h4:=hdecodedCore .work4
  have h5:=hdecodedCore .work5
  have h6:=hdecodedCore .work6
  have h7:=hdecodedCore .work7
  omega

set_option maxHeartbeats 3000000 in
theorem combined_runsTo_complete (p:Program) (wordBound:Polynomial Nat)
    (x output:List Nat) (t:Nat)
    (hfits:Lax759944Proofs.Legacy.RamPolytime.FitsInWords
      (wordBound.eval (bitSize x)) ((x.length::x) ++ output))
    (hram:RunsTo (simulationWordWidth wordBound x) p
      (x.length::x) output t):
    ∃ ss:SparseState, ∃ coreSteps stopSteps:Nat,
      ∃ finalState:FullInterpreterState (programArgumentBound p),
      ∃ finalTapes:CoreStack→ List SparseSymbol,
      let w:=simulationWordWidth wordBound x
      let base:=wrapperCoreStacks finalTapes [] []
      let decoded:=outputAdapterStacks [] (encode output) base
      let totalSteps:=fullInputCost wordBound x + 2 +
        (coreSteps + stopSteps + 1) +
        (4 + output.length * (3 * w + 3) +
          (cleanupTotalCost decoded + 1))
      ss.mem.length≤ t∧ output.length≤ t∧
      coreSteps≤ t * finiteRunUnitBound w 0 t∧
      stopSteps≤ operandEvalBound w ss.mem + 4∧
      cleanupTotalCost decoded≤
        2 * (13 * (coreSize w (sparseInitState (x.length::x)) +
          (coreSteps + stopSteps + 1) *
            programPushBound (middleProgram p (programArgumentBound p) le_rfl))) + 13∧
      ((fun o => o.bind (TM2.step
        (combinedProgram p (programArgumentBound p) le_rfl wordBound)))^[
          totalSteps])
        (some (mapLabelCfg embedInputCombined
          (fullInputCfg (.inl (.inl .scan))
            (default:WrapperState (programArgumentBound p))
            (inputWidthInitialStacks (encode x))))) =
      some ⟨none,default,cleanedStacks decoded⟩:=by
  let w:=simulationWordWidth wordBound x
  have hw:0 < w:=by simp [w,simulationWordWidth]
  have hwidth:wordBound.eval (bitSize x)≤ w:=
    (polynomial_eval_le_simpleMajorant wordBound (bitSize x)).trans
      (by simp [w,simulationWordWidth])
  have hpow:2 ^ wordBound.eval (bitSize x)≤ 2 ^ w:=
    Nat.pow_le_pow_right (by omega) hwidth
  have hlen:x.length < 2 ^ w:=
    (hfits x.length (by simp)).trans_le hpow
  have hxfit:∀ n∈ x,n < 2 ^ w:=by
    intro n hn
    exact (hfits n (by simp [hn])).trans_le hpow
  have houtfit:∀ n∈ output,n < 2 ^ w:=by
    intro n hn
    exact (hfits n (by simp [hn])).trans_le hpow
  have hinput:=fullInput_complete
    (N:=programArgumentBound p) wordBound x default hlen hxfit
  have hinputLift:=combined_lift_input (p:=p) le_rfl wordBound
    hinput (by rfl)
  rw [fullInputCoreFinal_eq_canonical] at hinputLift
  have hinputFinish:=combined_input_finish (p:=p) le_rfl wordBound
    (default:WrapperState (programArgumentBound p))
    (wrapperCoreStacks
      (coreStacks w (sparseInitState (x.length::x))) [] [])
  have hpreFinish:=chain_iterations
    (fun o:Option (TM2.Cfg WrapperAlphabet
      (CombinedLabel p (programArgumentBound p) wordBound)
      (WrapperState (programArgumentBound p))) =>
      o.bind (TM2.step
        (combinedProgram p (programArgumentBound p) le_rfl wordBound)))
    hinputLift hinputFinish
  have hinputBridgeStep:=combined_input_bridge (p:=p) le_rfl wordBound
    (default:WrapperState (programArgumentBound p))
    (wrapperCoreStacks
      (coreStacks w (sparseInitState (x.length::x))) [] [])
  have hinputBridge:((fun o:Option (TM2.Cfg WrapperAlphabet
      (CombinedLabel p (programArgumentBound p) wordBound)
      (WrapperState (programArgumentBound p))) =>
      o.bind (TM2.step
        (combinedProgram p (programArgumentBound p) le_rfl wordBound)))^[1])
      (some (mapLabelCfg embedInputCombined
        (fullInputCfg
          fullInputTerminal default
          (wrapperCoreStacks
            (coreStacks w (sparseInitState (x.length::x))) [] [])))) =
      some ⟨some (.inr (.inl (.fetch (boundPC p 0)))),default,
        wrapperCoreStacks
          (coreStacks w (sparseInitState (x.length::x))) [] []⟩:=by
    simpa using hinputBridgeStep
  have hpre:=chain_iterations _ hpreFinish hinputBridge
  rcases middle_ram_to_output hw hram with
    ⟨ss,coreSteps,stopSteps,finalState,finalTapes,
      hout,hstop,hm,hmem,houtLength,
      hcoreBound,hstopBound,houtTapes,hmiddle⟩
  have houtEncoded:finalTapes .output=encodeOutputStack w output:=by
    rw [houtTapes]
    simp [coreStacks,hout]
  have houtput:=middle_output_complete le_rfl
    (WrapperState.coreLens.put default finalState) finalTapes output
    houtEncoded houtfit
  have hcleanupBound:=middle_cleanupCost_le le_rfl
    (x.length::x) finalState finalTapes hmiddle output
  have hmiddleAll:=chain_iterations
    (fun o:Option (TM2.Cfg WrapperAlphabet
      (MiddleLabel p (programArgumentBound p))
      (WrapperState (programArgumentBound p))) =>
      o.bind (TM2.step (middleProgram p (programArgumentBound p) le_rfl)))
    hmiddle houtput
  let middleStart:TM2.Cfg WrapperAlphabet
      (MiddleLabel p (programArgumentBound p))
      (WrapperState (programArgumentBound p)):=
    liftCoreCfg (X:=OutputAdapterLabel)
      (finiteInterpreterCfg (.fetch (boundPC p 0)) default
        (coreStacks w (sparseInitState (x.length::x)))) default [] []
  have hmiddleLift:=combined_lift_middle (p:=p) le_rfl wordBound
    ((coreSteps + stopSteps + 1) +
      (4 + output.length * (3 * w + 3) +
        (cleanupTotalCost
          (outputAdapterStacks [] (encode output)
            (wrapperCoreStacks finalTapes [] [])) + 1))) middleStart
  rw [hmiddleAll] at hmiddleLift
  have hall:=chain_iterations _ hpre hmiddleLift
  refine ⟨ss,coreSteps,stopSteps,finalState,finalTapes, ?_⟩
  dsimp only
  refine ⟨hmem,by simpa [hout] using houtLength,
    hcoreBound,hstopBound,hcleanupBound, ?_⟩
  simpa [w,middleStart,liftCoreCfg,finiteInterpreterCfg,mapLabelCfg,
    embedMiddleCombined,Nat.add_assoc] using! hall

end

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.CellToMicrocode

@[simp] theorem block_length (i:Lax759944Proofs.Legacy.Ram.Instr):(block i).length=3:=rfl

@[simp] theorem compile_length (p:Lax759944Proofs.Legacy.Ram.Program):
    (compile p).length=3 * p.length:=by
  induction p with
  | nil => rfl
  | cons i p ih =>
      change (block i ++ compile p).length=_
      simp only [List.length_append,block_length,ih,List.length_cons,Nat.mul_succ]
      omega

theorem compile_get (p:Lax759944Proofs.Legacy.Ram.Program) (pc offset:Nat) (hoff:offset < 3):
    (compile p)[3 * pc + offset]?=p[pc]?.bind (fun i => (block i)[offset]?):=by
  induction p generalizing pc with
  | nil => simp [compile]
  | cons i p ih =>
      cases pc with
      | zero => simp [compile,List.getElem?_append,hoff]
      | succ pc =>
          have hlarge:¬3 * (pc + 1) + offset < 3:=by omega
          change (block i ++ compile p)[3 * (pc + 1) + offset]?=_
          simp only [List.getElem?_append,block_length,hlarge,if_false,
            List.getElem?_cons_succ]
          have heq:3 * (pc + 1) + offset - 3=3 * pc + offset:=by omega
          rw [heq]
          exact ih pc

def embed (s:Lax759944Proofs.Legacy.Ram.State) (accumulator:Nat):Microcode.State:=
  { pc:=3 * s.pc,acc:=accumulator,mem:=s.mem,inp:=s.inp,out:=s.out }

def Normalized (w:Nat) (s:Lax759944Proofs.Legacy.Ram.State):Prop:=
  ∀ a,s.mem a < 2 ^ w

theorem normalized_init (w:Nat) (input:List Nat):
    Normalized w (Lax759944Proofs.Legacy.Ram.initState input):=by
  intro a
  exact Nat.two_pow_pos w

theorem normalized_effect {w:Nat} {s s':Lax759944Proofs.Legacy.Ram.State}
    {i:Lax759944Proofs.Legacy.Ram.Instr} (hs:Normalized w s)
    (heffect:i.effect w s=some s'):Normalized w s':=by
  have hwrite (a v:Nat):∀ b,Lax759944Proofs.Legacy.Ram.setCell w s.mem a v b < 2 ^ w:=by
    intro b
    simp only [Lax759944Proofs.Legacy.Ram.setCell]
    split
    · exact Nat.mod_lt _ (Nat.two_pow_pos w)
    · exact hs b
  cases i <;> simp [Lax759944Proofs.Legacy.Ram.Instr.effect] at heffect
  case read a =>
    cases hin:s.inp with
    | nil => simp [hin] at heffect
    | cons v vs =>
        simp [hin] at heffect
        subst s'
        exact hwrite a v
  all_goals
    subst s'
    first | exact hs | exact hwrite _ _

theorem effect_three {w:Nat} {p:Lax759944Proofs.Legacy.Ram.Program}
    {s s':Lax759944Proofs.Legacy.Ram.State} {i:Lax759944Proofs.Legacy.Ram.Instr}
    (hfetch:p[s.pc]?=some i) (hs:Normalized w s)
    (heffect:i.effect w s=some s') (accumulator:Nat):
    ∃ finalAccumulator,
      Microcode.run w (compile p) 3 (embed s accumulator) =
        some (embed s' finalAccumulator):=by
  have h0:(compile p)[3 * s.pc]?=some (lower i).1:=by
    simpa [hfetch,block] using compile_get p s.pc 0 (by omega)
  have h1:(compile p)[3 * s.pc + 1]?=some (lower i).2.1:=by
    simpa [hfetch,block] using compile_get p s.pc 1 (by omega)
  have h2:(compile p)[3 * s.pc + 2]?=some (lower i).2.2:=by
    simpa [hfetch,block] using compile_get p s.pc 2 (by omega)
  have hmod (a:Nat):s.mem a % 2 ^ w=s.mem a:=Nat.mod_eq_of_lt (hs a)
  cases i <;> simp [Lax759944Proofs.Legacy.Ram.Instr.effect] at heffect
  case read a =>
    cases hin:s.inp with
    | nil => simp [hin] at heffect
    | cons v vs =>
        simp [hin] at heffect
        subst s'
        exact ⟨0,by
          simp [Microcode.run,Microcode.step,embed,h0,h1,h2,
            lower,Microcode.Instr.effect,Microcode.Op.value,hin,
            Nat.add_assoc,Nat.mul_add]
          rfl⟩
  all_goals
    subst s'
    simp [Microcode.run,Microcode.step,embed,h0,h1,h2,
      lower,Microcode.Instr.effect,Microcode.Op.value,hmod,
      Nat.add_assoc,Nat.mul_add,
      Microcode.State.mk.injEq] <;>
      (funext address; simp [Microcode.setCell,Lax759944Proofs.Legacy.Ram.setCell])

theorem microcode_run_add (w:Nat) (p:Microcode.Program) (m n:Nat)
    (s:Microcode.State):
    Microcode.run w p (m + n) s =
      (Microcode.run w p m s).bind (Microcode.run w p n):=by
  induction m generalizing s with
  | zero => simp [Microcode.run]
  | succ m ih => simp [Nat.succ_add,Microcode.run,ih,Option.bind_assoc]

theorem run_translation {w t:Nat} {p:Lax759944Proofs.Legacy.Ram.Program}
    {s s':Lax759944Proofs.Legacy.Ram.State} (hs:Normalized w s)
    (hrun:Lax759944Proofs.Legacy.Ram.run w p t s=some s') (accumulator:Nat):
    ∃ finalAccumulator,Microcode.run w (compile p) (3 * t) (embed s accumulator) =
      some (embed s' finalAccumulator):=by
  induction t generalizing s accumulator with
  | zero =>
      simp [Lax759944Proofs.Legacy.Ram.run] at hrun
      subst s'
      exact ⟨accumulator,rfl⟩
  | succ t ih =>
      simp only [Lax759944Proofs.Legacy.Ram.run] at hrun
      cases hstep:Lax759944Proofs.Legacy.Ram.step w p s with
      | none => simp [hstep] at hrun
      | some middle =>
          simp only [hstep,Option.bind_some] at hrun
          cases hfetch:p[s.pc]? with
          | none => simp [Lax759944Proofs.Legacy.Ram.step,hfetch] at hstep
          | some i =>
              have heffect:i.effect w s=some middle:=by
                simpa [Lax759944Proofs.Legacy.Ram.step,hfetch] using hstep
              obtain ⟨middleAccumulator,hthree⟩:=effect_three hfetch hs heffect accumulator
              obtain ⟨finalAccumulator,hrest⟩:=ih (normalized_effect hs heffect)
                hrun middleAccumulator
              refine ⟨finalAccumulator, ?_⟩
              rw [show 3 * (t + 1)=3 + 3 * t by omega,microcode_run_add,hthree]
              exact hrest

theorem halt_translation {w:Nat} {p:Lax759944Proofs.Legacy.Ram.Program} {s:Lax759944Proofs.Legacy.Ram.State}
    (hhalt:Lax759944Proofs.Legacy.Ram.step w p s=none) (accumulator:Nat):
    Microcode.step w (compile p) (embed s accumulator)=none:=by
  have h0:=compile_get p s.pc 0 (by omega)
  cases hfetch:p[s.pc]? with
  | none =>
      have hfirst:(compile p)[3 * s.pc]?=none:=by simpa [hfetch] using h0
      simp [Microcode.step,embed,hfirst]
  | some i =>
      have heffect:i.effect w s=none:=by
        simpa [Lax759944Proofs.Legacy.Ram.step,hfetch] using hhalt
      have hfirst:(compile p)[3 * s.pc]?=some (lower i).1:=by
        simpa [hfetch,block] using h0
      cases i <;> simp [Lax759944Proofs.Legacy.Ram.Instr.effect] at heffect
      case halt => simp [Microcode.step,embed,hfirst,lower,Microcode.Instr.effect]
      case read a =>
        cases hin:s.inp with
        | nil => simp [Microcode.step,embed,hfirst,lower,Microcode.Instr.effect,hin]
        | cons v vs => simp [hin] at heffect

theorem runsTo {w t:Nat} {p:Lax759944Proofs.Legacy.Ram.Program} {input output:List Nat}
    (hrun:Lax759944Proofs.Legacy.Ram.RunsTo w p input output t):
    Microcode.RunsTo w (compile p) input output (3 * t):=by
  obtain ⟨s,hrun,hhalt,hout⟩:=hrun
  obtain ⟨accumulator,hmicro⟩:=run_translation (normalized_init w input) hrun 0
  exact ⟨embed s accumulator,hmicro,halt_translation hhalt accumulator,hout⟩

end Lax759944Proofs.CellToMicrocode

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Polynomial Lax759944Proofs.Microcode
open Lax759944.BinaryWordEncoding Lax759944Proofs.Legacy.RamPolytime

noncomputable section

def ramSimulationTM (p:Program) (wordBound:Polynomial Nat):FinTM2 where
  K:=WrapperStack
  k₀:=.input
  k₁:=.output
  Γ:=WrapperAlphabet
  Λ:=CombinedLabel p (programArgumentBound p) wordBound
  main:=.inl (.inl (.inl .scan))
  σ:=WrapperState (programArgumentBound p)
  initialState:=default
  m:=combinedProgram p (programArgumentBound p) le_rfl wordBound

@[simp] theorem terminalCostPolynomial_eval
    (wordBound timeBound:Polynomial Nat) (n:Nat):
    (terminalCostPolynomial wordBound timeBound).eval n =
      2 * timeBound.eval n *
          (12 * ((polynomialSimpleMajorant wordBound).eval n + 1) + 22) +
        28 * ((polynomialSimpleMajorant wordBound).eval n + 1) + 65:=by
  simp [terminalCostPolynomial]

@[simp] theorem middleCostPolynomial_eval
    (wordBound timeBound:Polynomial Nat) (n:Nat):
    (middleCostPolynomial wordBound timeBound).eval n =
      (coreSimulationPolynomial (polynomialSimpleMajorant wordBound) timeBound).eval n +
        (terminalCostPolynomial wordBound timeBound).eval n + 1:=by
  simp [middleCostPolynomial]

@[simp] theorem initialCoreSizePolynomial_eval
    (wordBound:Polynomial Nat) (n:Nat):
    (initialCoreSizePolynomial wordBound).eval n =
      ((polynomialSimpleMajorant wordBound).eval n + 1) +
        (n + 1) * ((polynomialSimpleMajorant wordBound).eval n + 2) + 3:=by
  simp [initialCoreSizePolynomial]

@[simp] theorem cleanupCostPolynomial_eval (p:Program)
    (wordBound timeBound:Polynomial Nat) (n:Nat):
    (cleanupCostPolynomial p wordBound timeBound).eval n =
      let pushes:=programPushBound
        (middleProgram p (programArgumentBound p) le_rfl)
      2 * (13 * ((initialCoreSizePolynomial wordBound).eval n +
        pushes * (middleCostPolynomial wordBound timeBound).eval n)) + 13:=by
  simp [cleanupCostPolynomial]

@[simp] theorem outputCostPolynomial_eval
    (wordBound timeBound:Polynomial Nat) (n:Nat):
    (outputCostPolynomial wordBound timeBound).eval n =
      4 + timeBound.eval n *
        (3 * ((polynomialSimpleMajorant wordBound).eval n + 1) + 3):=by
  simp [outputCostPolynomial]

@[simp] theorem ramToTMTimePolynomial_eval (p:Program)
    (wordBound timeBound:Polynomial Nat) (n:Nat):
    (ramToTMTimePolynomial p wordBound timeBound).eval n =
      (fullInputCostPolynomial wordBound).eval n + 2 +
      (middleCostPolynomial wordBound timeBound).eval n +
      (outputCostPolynomial wordBound timeBound).eval n +
      (cleanupCostPolynomial p wordBound timeBound).eval n + 1:=by
  simp [ramToTMTimePolynomial]

theorem cleaned_output_stacks (tapes:CoreStack→ List SparseSymbol)
    (output:List Nat):
    cleanedStacks
        (outputAdapterStacks [] (encode output)
          (wrapperCoreStacks tapes [] [])) =
      wrapperCoreStacks (fun _ => []) [] (encode output):=by
  funext k
  cases k with
  | input => simp [cleanedStacks,outputAdapterStacks,wrapperCoreStacks] <;> rfl
  | output => simp [cleanedStacks,outputAdapterStacks,wrapperCoreStacks]
  | core k =>
      cases k <;>
        simp [cleanedStacks,outputAdapterStacks,wrapperCoreStacks] <;> rfl

set_option maxHeartbeats 3000000 in
theorem combined_runsTo_bounded (p:Program)
    (wordBound timeBound:Polynomial Nat) (x output:List Nat) (t:Nat)
    (hfits:FitsInWords (wordBound.eval (bitSize x))
      ((x.length::x) ++ output))
    (ht:t≤ timeBound.eval (bitSize x))
    (hram:RunsTo (simulationWordWidth wordBound x) p
      (x.length::x) output t):
    ∃ steps≤ (ramToTMTimePolynomial p wordBound timeBound).eval (bitSize x),
      ((fun o => o.bind (TM2.step
        (combinedProgram p (programArgumentBound p) le_rfl wordBound)))^[steps])
        (some (mapLabelCfg embedInputCombined
          (fullInputCfg (.inl (.inl .scan))
            (default:WrapperState (programArgumentBound p))
            (inputWidthInitialStacks (encode x))))) =
      some ⟨none,default,
        wrapperCoreStacks (fun _ => []) [] (encode output)⟩:=by
  rcases combined_runsTo_complete p wordBound x output t hfits hram with
    ⟨ss,coreSteps,stopSteps,finalState,finalTapes,
      hmem,houtLength,hcore,hstop,hcleanup,hrun⟩
  let n:=bitSize x
  let w:=simulationWordWidth wordBound x
  let pushes:=programPushBound
    (middleProgram p (programArgumentBound p) le_rfl)
  let middleBound:=(middleCostPolynomial wordBound timeBound).eval n
  have hcorePoly:coreSteps≤
      (coreSimulationPolynomial (polynomialSimpleMajorant wordBound) timeBound).eval n:=by
    apply finiteSparseRun_steps_le_corePolynomial
      (polynomialSimpleMajorant wordBound) timeBound n w t coreSteps
    · simp [w,n,simulationWordWidth]
    · exact ht
    · exact hcore
  have hstopPoly:stopSteps≤
      (terminalCostPolynomial wordBound timeBound).eval n:=by
    apply hstop.trans
    have hw:w=(polynomialSimpleMajorant wordBound).eval n + 1:=by
      simp [w,n,simulationWordWidth]
    let widthCost:=12 * w + 22
    have hmemTime:=hmem.trans ht
    have hprod:=Nat.mul_le_mul_right widthCost hmemTime
    simp only [operandEvalBound,terminalCostPolynomial_eval]
    rw [← hw]
    dsimp [widthCost] at hprod
    nlinarith
  have hmiddle:coreSteps + stopSteps + 1≤ middleBound:=by
    dsimp [middleBound]
    rw [middleCostPolynomial_eval]
    exact Nat.add_le_add_right (Nat.add_le_add hcorePoly hstopPoly) 1
  have hx:=Lax759944Proofs.Encoding.length_le_bitSize x
  have hinitial:coreSize w (sparseInitState (x.length::x))≤
      (initialCoreSizePolynomial wordBound).eval n:=by
    simp [coreSize_eq,sparseInitState,initialCoreSizePolynomial_eval,
      w,n,simulationWordWidth]
    nlinarith
  have hcleanupPoly:cleanupTotalCost
        (outputAdapterStacks [] (encode output)
          (wrapperCoreStacks finalTapes [] []))≤
      (cleanupCostPolynomial p wordBound timeBound).eval n:=by
    apply hcleanup.trans
    rw [cleanupCostPolynomial_eval]
    dsimp only [pushes]
    have hmul:(coreSteps + stopSteps + 1) * pushes≤
        pushes * middleBound:=by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left pushes hmiddle
    have hins:=Nat.add_le_add hinitial hmul
    have hscaled:=Nat.mul_le_mul_left 13 hins
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hscaled) 13
  have houtputPoly:
      4 + output.length * (3 * w + 3)≤
        (outputCostPolynomial wordBound timeBound).eval n:=by
    rw [outputCostPolynomial_eval]
    have hw:w=(polynomialSimpleMajorant wordBound).eval n + 1:=by
      simp [w,n,simulationWordWidth]
    rw [hw]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right
        (3 * ((polynomialSimpleMajorant wordBound).eval n + 1) + 3)
        (houtLength.trans ht)) 4
  let decoded:=outputAdapterStacks [] (encode output)
    (wrapperCoreStacks finalTapes [] [])
  let steps:=fullInputCost wordBound x + 2 +
    (coreSteps + stopSteps + 1) +
    (4 + output.length * (3 * w + 3) +
      (cleanupTotalCost decoded + 1))
  refine ⟨steps, ?_, ?_⟩
  · rw [ramToTMTimePolynomial_eval]
    have hinput:=fullInputCost_le_polynomial wordBound x
    dsimp only [steps,decoded]
    calc
      fullInputCost wordBound x + 2 + (coreSteps + stopSteps + 1) +
          (4 + output.length * (3 * w + 3) +
            (cleanupTotalCost
              (outputAdapterStacks [] (encode output)
                (wrapperCoreStacks finalTapes [] [])) + 1))≤
        (fullInputCostPolynomial wordBound).eval (bitSize x) + 2 +
          middleBound +
          ((outputCostPolynomial wordBound timeBound).eval n +
            ((cleanupCostPolynomial p wordBound timeBound).eval n + 1)):=by
              gcongr
      _=(fullInputCostPolynomial wordBound).eval (bitSize x) + 2 +
          middleBound + (outputCostPolynomial wordBound timeBound).eval n +
          (cleanupCostPolynomial p wordBound timeBound).eval n + 1:=by omega
  · dsimp only [steps,decoded]
    rw [cleaned_output_stacks] at hrun
    simpa [w,Nat.add_assoc] using hrun

theorem ramSimulation_initList (p:Program) (wordBound:Polynomial Nat)
    (input:List Symbol):
    Turing.initList (ramSimulationTM p wordBound) input =
      mapLabelCfg embedInputCombined
        (fullInputCfg (.inl (.inl .scan))
          (default:WrapperState (programArgumentBound p))
          (inputWidthInitialStacks input)):=by
  simp only [Turing.initList,ramSimulationTM,mapLabelCfg,fullInputCfg]
  congr 1
  funext k
  cases k with
  | input => simp [inputWidthInitialStacks]
  | output => simp [inputWidthInitialStacks]
  | core k => simp [inputWidthInitialStacks]

theorem ramSimulation_haltList (p:Program) (wordBound:Polynomial Nat)
    (output:List Symbol):
    Turing.haltList (ramSimulationTM p wordBound) output =
      ⟨none,default,
        wrapperCoreStacks (fun _ => []) [] output⟩:=by
  simp only [Turing.haltList,ramSimulationTM]
  congr 1
  funext k
  cases k with
  | input => simp [wrapperCoreStacks] <;> rfl
  | output => simp [wrapperCoreStacks]
  | core k => simp [wrapperCoreStacks] <;> rfl

end

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Polynomial Lax759944Proofs.Microcode
open Lax759944.BinaryWordEncoding Lax759944Proofs.Legacy.RamPolytime

noncomputable section

theorem ramInTime_to_turingExplicitOverhead (p:Program)
    (wordBound:Polynomial ℕ):
      ∀ (x output:List ℕ) (t:ℕ),
        FitsInWords (wordBound.eval (bitSize x)) ((x.length::x) ++ output)→
        RunsTo (simulationWordWidth wordBound x) p (x.length::x) output t→
        Nonempty (TM2OutputsInTime (ramSimulationTM p wordBound) (encode x)
          (some (encode output))
          ((ramToTMTimePolynomial p wordBound X).eval (bitSize x + t))):=by
  let timeOverhead:=ramToTMTimePolynomial p wordBound X
  intro x output t hfits hram
  let n:=bitSize x
  let q:=n + t
  obtain ⟨steps,hsteps,htm⟩:=combined_runsTo_bounded
    p wordBound (C t) x output t hfits (by simp) hram
  have hnq:n≤ q:=by simp [q]
  have htq:t≤ q:=by simp [q]
  have hword:
      (polynomialSimpleMajorant wordBound).eval n≤
        (polynomialSimpleMajorant wordBound).eval q:=
    polynomial_eval_mono _ hnq
  have hcore:
      (coreSimulationPolynomial (polynomialSimpleMajorant wordBound) (C t)).eval n≤
        (coreSimulationPolynomial (polynomialSimpleMajorant wordBound) X).eval q:=by
    simp only [coreSimulationPolynomial_eval,eval_C,eval_X]
    gcongr
  have hterminal:
      (terminalCostPolynomial wordBound (C t)).eval n≤
        (terminalCostPolynomial wordBound X).eval q:=by
    simp only [terminalCostPolynomial_eval,eval_C,eval_X]
    gcongr
  have hmiddle:
      (middleCostPolynomial wordBound (C t)).eval n≤
        (middleCostPolynomial wordBound X).eval q:=by
    simp only [middleCostPolynomial_eval]
    gcongr
  have houtput:
      (outputCostPolynomial wordBound (C t)).eval n≤
        (outputCostPolynomial wordBound X).eval q:=by
    simp only [outputCostPolynomial_eval,eval_C,eval_X]
    gcongr
  have hcleanup:
      (cleanupCostPolynomial p wordBound (C t)).eval n≤
        (cleanupCostPolynomial p wordBound X).eval q:=by
    simp only [cleanupCostPolynomial_eval]
    gcongr
    · exact polynomial_eval_mono _ hnq
  have htime:
      (ramToTMTimePolynomial p wordBound (C t)).eval n≤
        timeOverhead.eval q:=by
    simp only [ramToTMTimePolynomial_eval]
    dsimp [timeOverhead]
    rw [ramToTMTimePolynomial_eval]
    gcongr
    · exact polynomial_eval_mono _ hnq
  refine ⟨{
    steps:=steps
    evals_in_steps:= ?_
    steps_le_m:=hsteps.trans (by simpa only [n,q,timeOverhead] using htime) }⟩
  rw [ramSimulation_initList]
  simp only [Option.map_some]
  rw [ramSimulation_haltList]
  simpa using! htm

end

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.TapeRamGenericTime

open Lax759944.BinaryWordEncoding Polynomial Turing
open Lax759944Proofs.RamToTM

private theorem map_refl_invFun (xs:List Symbol):
    List.map (Equiv.refl Symbol).invFun xs=xs:=by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      change a::List.map (Equiv.refl Symbol).invFun xs=a::xs
      rw [ih]

theorem genericTime_of_lowering_finite_explicit
    (lower:Lax808846.Ram.Program→ Legacy.Ram.Program)
    (hlower:∀ (p:Lax808846.Ram.Program) (v:ℕ)
        (x output:List ℕ) (t:ℕ),
      (∀ a∈ x.length::x,a < 2 ^ v)→
      x.length + 33 < 2 ^ v→
      Lax808846.Ram.RunsTo v p (x.length::x) output t→
      ∃ u≤ 18 * t + 6 * (x.length + 1) + 26,
        Legacy.Ram.RunsTo (v + 1) (lower p) (x.length::x) output u)
    (hlength:∀ x:List ℕ,x.length≤ bitSize x)
    (p:Lax808846.Ram.Program) (wordBound:Polynomial ℕ):
    ∃ (H:TM2ComputableAux Symbol Symbol)
        (widthOverhead:Polynomial ℕ),
      (∀ k,Finite (H.tm.Γ k))∧
      (∀ n,wordBound.eval n≤ widthOverhead.eval n)∧
        ∀ (x output:List ℕ) (t:ℕ),
          Lax759944.RamPolytime.FitsInWords (wordBound.eval (bitSize x))
              ((x.length::x) ++ output)→
            Lax808846.Ram.RunsTo (widthOverhead.eval (bitSize x)) p
                (x.length::x) output t→
              Nonempty (TM2OutputsInTime H.tm
                (List.map H.inputAlphabet.invFun (encode x))
                (some (List.map H.outputAlphabet.invFun (encode output)))
                (((ramToTMTimePolynomial (CellToMicrocode.compile (lower p))
                  (wordBound+Polynomial.X+Polynomial.C 7) Polynomial.X).comp
                    (Polynomial.C 100*(Polynomial.X+1))).eval (bitSize x+t))):=by
  let enlarged:=wordBound + Polynomial.X + Polynomial.C 7
  let widthOverhead:=polynomialSimpleMajorant enlarged
  let timeOverhead:=ramToTMTimePolynomial (CellToMicrocode.compile (lower p)) enlarged Polynomial.X
  have hsim:=Lax759944Proofs.RamToTM.ramInTime_to_turingExplicitOverhead
      (CellToMicrocode.compile (lower p)) enlarged
  let H:TM2ComputableAux Symbol Symbol:= {
    tm:=ramSimulationTM (CellToMicrocode.compile (lower p)) enlarged
    inputAlphabet:=Equiv.refl Symbol
    outputAlphabet:=Equiv.refl Symbol }
  have hwidth (n:ℕ):wordBound.eval n + 7≤ widthOverhead.eval n:=by
    have h:enlarged.eval n≤ widthOverhead.eval n:=
      polynomial_eval_le_simpleMajorant enlarged n
    apply le_trans (b:=enlarged.eval n) ?_ h
    simp only [enlarged,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
    omega
  refine ⟨H,widthOverhead, ?_, ?_, ?_⟩
  · intro k
    change Finite (WrapperAlphabet k)
    cases k <;> simp only [WrapperAlphabet] <;> infer_instance
  · intro n
    have:=hwidth n
    omega
  · intro x output t hfits hrun
    let v:=widthOverhead.eval (bitSize x)
    have hqv:wordBound.eval (bitSize x) + 6≤ v:=by
      have:=hwidth (bitSize x)
      dsimp [v]
      omega
    have hq:wordBound.eval (bitSize x)≤ v:=by omega
    have hinput:∀ a∈ x.length::x,a < 2 ^ v:=by
      intro a ha
      exact (hfits a (List.mem_append_left _ ha)).trans_le
        (Nat.pow_le_pow_right (by decide) hq)
    have hn:x.length < 2 ^ wordBound.eval (bitSize x):=
      hfits x.length (by simp)
    have hpow:2 ^ wordBound.eval (bitSize x) * 64≤ 2 ^ v:=by
      simpa [Nat.pow_add] using
        (Nat.pow_le_pow_right (by decide:1≤ 2) hqv)
    have hspace:x.length + 33 < 2 ^ v:=by
      have:=Nat.two_pow_pos (wordBound.eval (bitSize x))
      omega
    obtain ⟨u,hu,hr⟩:=hlower p v x output t hinput hspace hrun
    have hr':Legacy.Ram.RunsTo (simulationWordWidth enlarged x)
        (lower p) (x.length::x) output u:=by
      simpa [simulationWordWidth,v,widthOverhead] using hr
    have hfits':Legacy.RamPolytime.FitsInWords (enlarged.eval (bitSize x))
        ((x.length::x) ++ output):=by
      intro a ha
      apply (hfits a ha).trans_le
      apply Nat.pow_le_pow_right (by decide)
      simp only [enlarged,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
      omega
    obtain ⟨htm⟩:=hsim x output (3 * u) hfits' (CellToMicrocode.runsTo hr')
    have hinputMap:List.map H.inputAlphabet.invFun (encode x)=encode x:=by
      dsimp [H]
      exact map_refl_invFun (encode x)
    have houtputMap:List.map H.outputAlphabet.invFun (encode output)=encode output:=by
      dsimp [H]
      exact map_refl_invFun (encode output)
    rw [hinputMap,houtputMap]
    refine ⟨{ htm with steps_le_m:=htm.steps_le_m.trans ?_ }⟩
    simp only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    apply polynomial_eval_mono timeOverhead
    have hnbit:=hlength x
    omega

end Lax759944Proofs.TapeRamGenericTime

end

theorem solution:∀ (lower:Lax808846.Ram.Program→ Lax759944Proofs.Legacy.Ram.Program),
  (∀ (p:Lax808846.Ram.Program) (v:ℕ) (x output:List ℕ) (t:ℕ),
      (∀ a∈ x.length::x,a < 2 ^ v)→
        x.length + 33 < 2 ^ v→
          Lax808846.Ram.RunsTo v p (x.length::x) output t→
            ∃ u≤ 18 * t + 6 * (x.length + 1) + 26,
              Lax759944Proofs.Legacy.Ram.RunsTo (v + 1) (lower p) (x.length::x) output u)→
    (∀ (x:List ℕ),x.length≤ Lax759944.BinaryWordEncoding.bitSize x)→
      ∀ (p:Lax808846.Ram.Program) (wordBound:Polynomial ℕ),
        ∃ (H:Turing.TM2ComputableAux Lax759944.BinaryWordEncoding.Symbol Lax759944.BinaryWordEncoding.Symbol)
          (widthOverhead:Polynomial ℕ),
          (∀ (k:H.tm.K),Finite (H.tm.Γ k))∧
            (∀ (n:ℕ),Polynomial.eval n wordBound≤ Polynomial.eval n widthOverhead)∧
              ∀ (x output:List ℕ) (t:ℕ),
                Lax759944.RamPolytime.FitsInWords (Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize x) wordBound)
                    (x.length::x ++ output)→
                  Lax808846.Ram.RunsTo (Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize x) widthOverhead) p
                      (x.length::x) output t→
                    Nonempty
                      (Turing.TM2OutputsInTime H.tm
                        (List.map H.inputAlphabet.invFun (Lax759944.BinaryWordEncoding.encode x))
                        (Option.some (List.map H.outputAlphabet.invFun (Lax759944.BinaryWordEncoding.encode output)))
                        (Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize x + t)
                          ((Lax759944Proofs.RamToTM.ramToTMTimePolynomial
                                (Lax759944Proofs.CellToMicrocode.compile (lower p))
                                (wordBound + Polynomial.X + Polynomial.C 7) Polynomial.X).comp
                            (Polynomial.C 100 * (Polynomial.X + 1))))):= @Lax759944Proofs.TapeRamGenericTime.genericTime_of_lowering_finite_explicit
