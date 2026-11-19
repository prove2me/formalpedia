-- Prove2me | solution 1 for Lax759944Proofs.RamToTM.finite_div_instruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:02:34.132912+00:00
-- url     : https://prove2.me/submissions/e24b4e28-d98b-492b-afb0-7c21cd4910da

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

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

def initState (x:List ℕ):State where
  pc:=0
  acc:=0
  mem:=fun _ => 0
  inp:=x
  out:= []

end Lax759944Proofs.Microcode

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

@[simp] theorem SparseMemory.read_nil (a:ℕ):SparseMemory.read [] a=0:=rfl

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

theorem fullSubtractor_value (a b borrow:Bool):
    a.toNat + 2 * (fullSubtractor a b borrow).2.toNat =
      b.toNat + borrow.toNat + (fullSubtractor a b borrow).1.toNat:=by
  cases a <;> cases b <;> cases borrow <;> decide

def subBits:List Bool→ List Bool→ Bool→ List Bool
  | a::as,b::bs,borrow =>
      let q:=fullSubtractor a b borrow
      q.1::subBits as bs q.2
  | _,_,_ => []

def subBorrowOut:List Bool→ List Bool→ Bool→ Bool
  | a::as,b::bs,borrow =>
      subBorrowOut as bs (fullSubtractor a b borrow).2
  | _,_,borrow => borrow

theorem subBits_length_of_eq {as bs:List Bool} (borrow:Bool)
    (h:as.length=bs.length):(subBits as bs borrow).length=as.length:=by
  induction as generalizing bs borrow with
  | nil =>
      cases bs <;> simp [subBits] at h ⊢
  | cons a as ih =>
      cases bs with
      | nil => simp at h
      | cons b bs =>
          simp at h
          simp [subBits,ih _ h]

theorem subBits_value_identity {as bs:List Bool} (borrow:Bool)
    (h:as.length=bs.length):
    bitsValue as + 2 ^ as.length * (subBorrowOut as bs borrow).toNat =
      bitsValue bs + borrow.toNat + bitsValue (subBits as bs borrow):=by
  induction as generalizing bs borrow with
  | nil =>
      cases bs with
      | nil => simp [bitsValue,subBits,subBorrowOut]
      | cons _ _ => simp at h
  | cons a as ih =>
      cases bs with
      | nil => simp at h
      | cons b bs =>
          simp at h
          have ht:=ih (borrow:=(fullSubtractor a b borrow).2)
            (bs:=bs) h
          have hf:=fullSubtractor_value a b borrow
          simp only [bitsValue,subBits,subBorrowOut,List.length_cons,pow_succ]
          simp only [bitsValue,Nat.bit_val] at ht ⊢
          nlinarith

theorem sub_borrow_head_tail (a b:ℕ) (borrow:Bool)
    (h:b + borrow.toNat≤ a):
    let d:=a - (b + borrow.toNat)
    d.bodd=(fullSubtractor a.bodd b.bodd borrow).1∧
      d.div2=a.div2 -
        (b.div2 + (fullSubtractor a.bodd b.bodd borrow).2.toNat)∧
      b.div2 + (fullSubtractor a.bodd b.bodd borrow).2.toNat≤ a.div2:=by
  let d:=a - (b + borrow.toNat)
  have hd:b + borrow.toNat + d=a:=by
    dsimp [d]
    omega
  have ha:=Nat.bodd_add_div2 a
  have hb:=Nat.bodd_add_div2 b
  have hd':=Nat.bodd_add_div2 d
  have hf:=fullSubtractor_value a.bodd b.bodd borrow
  have hhead:d.bodd=(fullSubtractor a.bodd b.bodd borrow).1:=by
    cases hba:a.bodd <;> cases hbb:b.bodd <;> cases hbd:d.bodd <;>
      cases borrow <;> simp_all [fullSubtractor] <;> omega
  have hquot:
      a.div2=b.div2 +
        (fullSubtractor a.bodd b.bodd borrow).2.toNat + d.div2:=by
    cases hba:a.bodd <;> cases hbb:b.bodd <;> cases hbd:d.bodd <;>
      cases borrow <;> simp_all [fullSubtractor] <;> omega
  refine ⟨hhead, ?_, ?_⟩
  · rw [hquot,Nat.add_sub_cancel_left]
  · rw [hquot]
    omega

theorem fixedBits_sub_borrow (w a b:ℕ) (borrow:Bool)
    (h:b + borrow.toNat≤ a):
    fixedBits w (a - (b + borrow.toNat)) =
      subBits (fixedBits w a) (fixedBits w b) borrow:=by
  induction w generalizing a b borrow with
  | zero => rfl
  | succ w ih =>
      obtain ⟨hhead,htail,hnext⟩:=sub_borrow_head_tail a b borrow h
      simp only [fixedBits,subBits]
      rw [hhead,htail]
      apply congrArg ((fullSubtractor a.bodd b.bodd borrow).1::·)
      exact ih _ _ _ hnext

theorem fixedBits_sub_of_le (w:ℕ) {a b:ℕ} (h:b≤ a):
    fixedBits w (a - b)=subBits (fixedBits w a) (fixedBits w b) false:=by
  simpa using fixedBits_sub_borrow w a b false (by simpa using h)

theorem subBorrowOut_fixed_false (w:ℕ) {a b:ℕ} (borrow:Bool)
    (ha:a < 2 ^ w) (hb:b < 2 ^ w) (hba:b + borrow.toNat≤ a):
    subBorrowOut (fixedBits w a) (fixedBits w b) borrow=false:=by
  induction w generalizing a b borrow with
  | zero =>
      simp at ha hb
      subst a
      subst b
      cases borrow <;> simp_all [subBorrowOut,fixedBits]
  | succ w ih =>
      obtain ⟨_,_,hnext⟩:=sub_borrow_head_tail a b borrow hba
      have ha':a.div2 < 2 ^ w:=by
        change a / 2 < 2 ^ w
        rw [pow_succ] at ha
        omega
      have hb':b.div2 < 2 ^ w:=by
        change b / 2 < 2 ^ w
        rw [pow_succ] at hb
        omega
      simp only [fixedBits,subBorrowOut]
      exact ih _ ha' hb' hnext

theorem subBorrowOut_fixed_false_of_le (w:ℕ) {a b:ℕ}
    (ha:a < 2 ^ w) (hb:b < 2 ^ w) (hba:b≤ a):
    subBorrowOut (fixedBits w a) (fixedBits w b) false=false:=by
  exact subBorrowOut_fixed_false w false ha hb (by simpa using hba)

theorem subBorrowOut_fixed_eq_decide_lt (w a b:ℕ)
    (ha:a < 2 ^ w) (hb:b < 2 ^ w):
    subBorrowOut (fixedBits w a) (fixedBits w b) false=decide (a < b):=by
  by_cases hlt:a < b
  · have hi:=subBits_value_identity false
      (show (fixedBits w a).length=(fixedBits w b).length by simp)
    rw [bitsValue_fixedBits_of_lt ha,bitsValue_fixedBits_of_lt hb] at hi
    cases hout:subBorrowOut (fixedBits w a) (fixedBits w b) false
    · simp [hout] at hi
      omega
    · simp [hlt]
  · have hout:=subBorrowOut_fixed_false_of_le w ha hb (Nat.le_of_not_gt hlt)
    simp [hlt,hout]

theorem fixedBits_bitsValue (xs:List Bool):
    fixedBits xs.length (bitsValue xs)=xs:=by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      simp [fixedBits,bitsValue,ih]

theorem fixedBits_take (k w n:ℕ):
    (fixedBits w n).take k=fixedBits (min k w) n:=by
  induction k generalizing w n with
  | zero => simp [fixedBits]
  | succ k ih =>
      cases w with
      | zero => simp [fixedBits]
      | succ w => simp [fixedBits,ih,Nat.succ_min_succ]

def shiftInBit (bit:Bool):List Bool→ List Bool
  | [] => []
  | x::xs => bit::(x::xs).take xs.length

@[simp] theorem shiftInBit_length (bit:Bool) (bits:List Bool):
    (shiftInBit bit bits).length=bits.length:=by
  cases bits <;> simp [shiftInBit]

theorem shiftInBit_fixed (w r:ℕ) (bit:Bool):
    shiftInBit bit (fixedBits (w + 1) r) =
      fixedBits (w + 1) (2 * r + bit.toNat):=by
  simp only [fixedBits,shiftInBit,fixedBits_length]
  rw [show r.bodd::fixedBits w r.div2=fixedBits (w + 1) r by rfl,
    fixedBits_take]
  cases bit <;> simp [Nat.div2_val]

@[simp] theorem fixedBits_zero (w:ℕ):
    fixedBits w 0=List.replicate w false:=by
  induction w <;> simp [fixedBits,List.replicate_succ, *]

def msbValueFrom:ℕ→ List Bool→ ℕ
  | acc, [] => acc
  | acc,b::bs => msbValueFrom (2 * acc + b.toNat) bs

def msbValue (bits:List Bool):ℕ:=msbValueFrom 0 bits

theorem msbValueFrom_append (acc:ℕ) (xs ys:List Bool):
    msbValueFrom acc (xs ++ ys)=msbValueFrom (msbValueFrom acc xs) ys:=by
  induction xs generalizing acc <;> simp [msbValueFrom, *]

@[simp] theorem msbValue_reverse (xs:List Bool):
    msbValue xs.reverse=bitsValue xs:=by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      change msbValueFrom 0 bs.reverse=bitsValue bs at ih
      simp [msbValue,msbValueFrom_append,msbValueFrom,bitsValue,ih,
        Nat.bit_val]

structure DivisionScan where
  quotient:List Bool
  remainder:ℕ

def divisionScanStep (divisor:ℕ) (s:DivisionScan) (bit:Bool):
    DivisionScan:=
  let candidate:=2 * s.remainder + bit.toNat
  let quotientBit:=decide (divisor≤ candidate)
  { quotient:=quotientBit::s.quotient,
    remainder:=if quotientBit then candidate - divisor else candidate }

def divisionScan (divisor:ℕ):DivisionScan→ List Bool→ DivisionScan
  | s, [] => s
  | s,b::bs => divisionScan divisor (divisionScanStep divisor s b) bs

theorem divisionScanStep_invariant {d:ℕ} (hd:0 < d)
    (s:DivisionScan) (b:Bool) (hr:s.remainder < d):
    let s':=divisionScanStep d s b
    bitsValue s'.quotient * d + s'.remainder =
      2 * (bitsValue s.quotient * d + s.remainder) + b.toNat∧
    s'.remainder < d:=by
  simp only [divisionScanStep]
  have hb:b.toNat≤ 1:=by cases b <;> simp
  have hcand:2 * s.remainder + b.toNat < 2 * d:=by omega
  by_cases hle:d≤ 2 * s.remainder + b.toNat
  · simp [hle,bitsValue,Nat.bit_val]
    constructor
    · have hsub:=Nat.sub_add_cancel hle
      ring_nf at hsub ⊢
      omega
    · omega
  · simp [hle,bitsValue,Nat.bit_val]
    constructor
    · ring
    · omega

theorem divisionScan_candidate_lt_extra_bit {w d r:ℕ} (b:Bool)
    (hd:d < 2 ^ w) (hr:r < d):
    2 * r + b.toNat < 2 ^ (w + 1):=by
  have hb:b.toNat≤ 1:=by cases b <;> simp
  rw [pow_succ]
  omega

theorem divisionScan_invariant {d:ℕ} (hd:0 < d)
    (bits:List Bool) (s:DivisionScan) (hr:s.remainder < d):
    let s':=divisionScan d s bits
    bitsValue s'.quotient * d + s'.remainder =
      msbValueFrom (bitsValue s.quotient * d + s.remainder) bits∧
    s'.remainder < d:=by
  induction bits generalizing s with
  | nil => simp [divisionScan,msbValueFrom,hr]
  | cons b bits ih =>
      obtain ⟨hstep,hr'⟩:=divisionScanStep_invariant hd s b hr
      obtain ⟨htail,hr''⟩:=ih (divisionScanStep d s b) hr'
      simp only [divisionScan,msbValueFrom]
      rw [hstep] at htail
      exact ⟨htail,hr''⟩

theorem divisionScan_zero_correct {d:ℕ} (hd:0 < d) (bits:List Bool):
    let s:=divisionScan d ⟨[],0⟩ bits
    bitsValue s.quotient=msbValue bits / d∧
      s.remainder=msbValue bits % d:=by
  have hi:
      bitsValue (divisionScan d ⟨[],0⟩ bits).quotient * d +
          (divisionScan d ⟨[],0⟩ bits).remainder=msbValue bits∧
        (divisionScan d ⟨[],0⟩ bits).remainder < d:=by
    simpa [msbValue,bitsValue] using
      (divisionScan_invariant hd bits (⟨[],0⟩:DivisionScan) hd)
  let s:=divisionScan d ⟨[],0⟩ bits
  have hdiv:msbValue bits / d=bitsValue s.quotient:=by
    apply Nat.div_eq_of_lt_le
    · dsimp [s] at hi ⊢
      nlinarith [hi.1,hi.2]
    · dsimp [s] at hi ⊢
      nlinarith [hi.1,hi.2]
  have hmod:s.remainder=msbValue bits % d:=by
    have hcanonical:=Nat.div_add_mod (msbValue bits) d
    dsimp [s] at hi ⊢
    rw [hdiv] at hcanonical
    nlinarith [hi.1,hcanonical]
  exact ⟨hdiv.symm,hmod⟩

theorem divisionScan_fixed_correct (w n d:ℕ)
    (hn:n < 2 ^ w) (hd:0 < d):
    let s:=divisionScan d ⟨[],0⟩ (fixedBits w n).reverse
    bitsValue s.quotient=n / d∧ s.remainder=n % d:=by
  simpa [bitsValue_fixedBits_of_lt hn] using
    divisionScan_zero_correct hd (fixedBits w n).reverse

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

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

@[simp] theorem bitsValue_append_false (bits:List Bool):
    bitsValue (bits ++ [false])=bitsValue bits:=by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [bitsValue,ih]

theorem divisionScan_quotient_length (d:ℕ) (s:DivisionScan)
    (bits:List Bool):
    (divisionScan d s bits).quotient.length=s.quotient.length + bits.length:=by
  induction bits generalizing s with
  | nil => simp [divisionScan]
  | cons b bits ih =>
      simp only [divisionScan]
      rw [ih]
      simp [divisionScanStep]
      omega

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

def zeroWordTypedCfg (label:ZeroWordLabel)
    (query backup result:List SparseSymbol):
    TM2.Cfg (fun _:ZeroWordStack => SparseSymbol)
      ZeroWordLabel ZeroWordControl where
  l:=some label
  var:=default
  stk:=zeroWordStacks query backup result

theorem zeroWordTyped_correct (query result:List SparseSymbol):
    ((fun o:Option (TM2.Cfg (fun _:ZeroWordStack => SparseSymbol)
      ZeroWordLabel ZeroWordControl) => o.bind (TM2.step zeroWordProgram))^[
        2 * query.length + 2])
      (some (zeroWordTypedCfg .fill query [] result)) =
    some (zeroWordTypedCfg .done query []
      (List.replicate query.length (.bit false) ++ result)):=by
  simpa [zeroWordProgram,zeroWordTypedCfg,zeroWordCfg] using!
    zeroWord_correct query result

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

theorem literalWord_remaining_eq_zero_iff (n w:ℕ):
    n / 2 ^ w=0↔ n < 2 ^ w:=by
  exact Nat.div_eq_zero_iff_lt (by positivity)

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

theorem sparseValue_mem_lt {w:ℕ} {m:SparseMemory}
    (hm:m.Normalized w) (a:ℕ):sparseValue w (.mem a) m < 2 ^ w:=by
  exact SparseMemory.read_lt_of_normalized hm _

theorem sparseValue_ind_lt {w:ℕ} {m:SparseMemory}
    (hm:m.Normalized w) (a:ℕ):sparseValue w (.ind a) m < 2 ^ w:=by
  exact SparseMemory.read_lt_of_normalized hm _

theorem operandWordValue_lt (w:ℕ) (o:Op) (m:SparseMemory):
    operandWordValue w o m < 2 ^ w:=by
  exact Nat.mod_lt _ (by positivity)

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

def mapAlphabetStacks {α β K:Type} (encode:α→ β)
    (stk:K→ List α):K→ List β:=
  fun k => (stk k).map encode

def mapAlphabetCfg {α β K Λ σ:Type} (encode:α→ β)
    (c:TM2.Cfg (fun _:K => α) Λ σ):
    TM2.Cfg (fun _:K => β) Λ σ where
  l:=c.l
  var:=c.var
  stk:=mapAlphabetStacks encode c.stk

theorem update_mapAlphabetStacks {α β K:Type} [DecidableEq K]
    (encode:α→ β) (stk:K→ List α) (k:K) (xs:List α):
    Function.update (mapAlphabetStacks encode stk) k (xs.map encode) =
      mapAlphabetStacks encode (Function.update stk k xs):=by
  funext j
  by_cases h:j=k
  · subst j; simp [mapAlphabetStacks]
  · simp [mapAlphabetStacks,h]

theorem stepAux_mapAlphabetStmt {α β K Λ σ:Type} [DecidableEq K]
    (encode:α→ β) (decode:β→ α)
    (hleft:∀ a,decode (encode a)=a)
    (q:TM2.Stmt (fun _:K => α) Λ σ) (v:σ)
    (stk:K→ List α):
    TM2.stepAux (mapAlphabetStmt encode decode q) v
        (mapAlphabetStacks encode stk) =
      mapAlphabetCfg encode (TM2.stepAux q v stk):=by
  induction q generalizing v stk with
  | push k f q ih =>
      simp only [mapAlphabetStmt,TM2.stepAux]
      change TM2.stepAux (mapAlphabetStmt encode decode q) v
          (Function.update (mapAlphabetStacks encode stk) k
            ((f v::stk k).map encode))=_
      rw [update_mapAlphabetStacks]
      exact ih v (Function.update stk k (f v::stk k))
  | peek k f q ih =>
      simp only [mapAlphabetStmt,TM2.stepAux,mapAlphabetStacks]
      rw [List.head?_map]
      simp only [Option.map_map]
      have hmap:(stk k).head?.map (decode ∘ encode)=(stk k).head?:=by
        cases (stk k).head? <;> simp [hleft]
      rw [hmap]
      exact ih (f v (stk k).head?) stk
  | pop k f q ih =>
      simp only [mapAlphabetStmt,TM2.stepAux,mapAlphabetStacks]
      rw [List.head?_map]
      simp only [Option.map_map]
      have hmap:(stk k).head?.map (decode ∘ encode)=(stk k).head?:=by
        cases (stk k).head? <;> simp [hleft]
      rw [hmap]
      rw [show ((stk k).map encode).tail=(stk k).tail.map encode by
        cases stk k <;> rfl]
      rw [update_mapAlphabetStacks]
      exact ih (f v (stk k).head?)
        (Function.update stk k (stk k).tail)
  | load f q ih =>
      simp only [mapAlphabetStmt,TM2.stepAux]
      exact ih (f v) stk
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [mapAlphabetStmt,TM2.stepAux]
      cases h:f v <;> simp
      · exact ih₂ v stk
      · exact ih₁ v stk
  | goto f => rfl
  | halt => rfl

theorem step_mapAlphabetProgram {α β K Λ σ:Type} [DecidableEq K]
    (encode:α→ β) (decode:β→ α)
    (hleft:∀ a,decode (encode a)=a)
    (program:Λ→ TM2.Stmt (fun _:K => α) Λ σ)
    (c:TM2.Cfg (fun _:K => α) Λ σ):
    TM2.step (mapAlphabetProgram encode decode program) (mapAlphabetCfg encode c) =
      (TM2.step program c).map (mapAlphabetCfg encode):=by
  cases c with
  | mk label v stk =>
      cases label with
      | none => rfl
      | some label =>
          simp only [mapAlphabetCfg,TM2.step,mapAlphabetProgram,Option.map_some]
          rw [stepAux_mapAlphabetStmt encode decode hleft]
          rfl

theorem iterate_mapAlphabetProgram {α β K Λ σ:Type} [DecidableEq K]
    (encode:α→ β) (decode:β→ α)
    (hleft:∀ a,decode (encode a)=a)
    (program:Λ→ TM2.Stmt (fun _:K => α) Λ σ)
    (n:ℕ) (c:TM2.Cfg (fun _:K => α) Λ σ):
    ((fun o => o.bind (TM2.step (mapAlphabetProgram encode decode program)))^[n])
        (some (mapAlphabetCfg encode c)) =
      (((fun o => o.bind (TM2.step program))^[n]) (some c)).map
        (mapAlphabetCfg encode):=by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
      simp only [Option.bind_some,step_mapAlphabetProgram encode decode hleft]
      cases h:TM2.step program c with
      | none =>
          simp only [Option.map_none]
          rw [iterate_optionBind_none,iterate_optionBind_none]
          rfl
      | some c' =>
          simp only [Option.map_some,Option.bind_some]
          exact ih c'

theorem transport_iterate_mapAlphabetProgram {α β K Λ σ:Type} [DecidableEq K]
    (encode:α→ β) (decode:β→ α)
    (hleft:∀ a,decode (encode a)=a)
    (program:Λ→ TM2.Stmt (fun _:K => α) Λ σ)
    {n:ℕ} {c d:TM2.Cfg (fun _:K => α) Λ σ}
    (h:((fun o => o.bind (TM2.step program))^[n]) (some c)=some d):
    ((fun o => o.bind (TM2.step (mapAlphabetProgram encode decode program)))^[n])
        (some (mapAlphabetCfg encode c)) =
      some (mapAlphabetCfg encode d):=by
  rw [iterate_mapAlphabetProgram encode decode hleft]
  simp [h]

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

def divInitialCfg (dividend divisor remainder:List Bool):divMachine.Cfg:=
  divCfg .inspectDivisor default dividend divisor remainder [] [] [] [] []

def divCleanCfg (label:DivLabel) (divisorNonzero:Bool)
    (dividend divisor remainder quotient divisorBackup:List Bool):
    divMachine.Cfg:=
  divCfg label { (default:DivControl) with divisorNonzero:=divisorNonzero }
    dividend divisor remainder quotient divisorBackup [] [] []

def divDoneCfg (divisorNonzero:Bool) (divisor remainder quotient:List Bool):
    divMachine.Cfg:=
  divCfg .done { (default:DivControl) with divisorNonzero:=divisorNonzero }
    [] divisor remainder quotient [] [] [] []

def divPhaseCfg (label:DivLabel) (selected borrow:Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp:List Bool):divMachine.Cfg:=
  divCfg label
    { (default:DivControl) with
      selected:=selected,borrow:=borrow,
      divisorNonzero:=true }
    dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp

def divSubCfg (selected borrow:Bool) (left right:Option Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse:List Bool):divMachine.Cfg:=
  divCfg .subtract
    { (default:DivControl) with
      selected:=selected,borrow:=borrow,left:=left,right:=right,
      divisorNonzero:=true }
    dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse []

def containsTrue:List Bool→ Bool
  | [] => false
  | b::bs => b || containsTrue bs

theorem containsTrue_false_bitsValue_zero {bits:List Bool}
    (h:containsTrue bits=false):bitsValue bits=0:=by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      simp [containsTrue] at h
      simp [bitsValue,h.1,ih h.2]

@[simp] theorem div_step_inspect_cons (nz b:Bool)
    (dividend divisor remainder backup:List Bool):
    divMachine.step
        (divCleanCfg .inspectDivisor nz dividend (b::divisor) remainder [] backup) =
      some (divCleanCfg .inspectDivisor (nz || b) dividend divisor remainder []
        (b::backup)):=by
  simp [divMachine,divCleanCfg,divCfg,divStacks,DivControl.clearHeld,
    Function.update]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]
  funext k
  cases k <;> rfl

@[simp] theorem div_step_inspect_nil (nz:Bool)
    (dividend remainder backup:List Bool):
    divMachine.step
        (divCleanCfg .inspectDivisor nz dividend [] remainder [] backup) =
      some (divCleanCfg .restoreInspectedDivisor nz dividend [] remainder [] backup):=by
  simp [divMachine,divCleanCfg,divCfg,divStacks,DivControl.clearHeld]
  congr 2

theorem div_inspect_iterate (nz:Bool)
    (dividend divisor remainder backup:List Bool):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[divisor.length])
        (some (divCleanCfg .inspectDivisor nz dividend divisor remainder [] backup)) =
      some (divCleanCfg .inspectDivisor (nz || containsTrue divisor) dividend []
        remainder [] (divisor.reverse ++ backup)):=by
  induction divisor generalizing nz backup with
  | nil => simp [containsTrue]
  | cons b divisor ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,div_step_inspect_cons]
      rw [ih]
      simp [containsTrue,List.reverse_cons,List.append_assoc,Bool.or_assoc]

@[simp] theorem div_step_restore_inspected_cons (nz b:Bool)
    (dividend divisor remainder quotient backup:List Bool):
    divMachine.step (divCleanCfg .restoreInspectedDivisor nz dividend divisor remainder
        quotient (b::backup)) =
      some (divCleanCfg .restoreInspectedDivisor nz dividend (b::divisor) remainder
        quotient backup):=by
  simp [divMachine,divMoveIteration,divCleanCfg,divCfg,divStacks,
    DivControl.clearHeld,Function.update]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]
  funext k
  cases k <;> rfl

@[simp] theorem div_step_restore_inspected_nil (nz:Bool)
    (dividend divisor remainder quotient:List Bool):
    divMachine.step (divCleanCfg .restoreInspectedDivisor nz dividend divisor remainder
        quotient []) =
      some (divCleanCfg .dispatch nz dividend divisor remainder quotient []):=by
  simp [divMachine,divMoveIteration,divCleanCfg,divCfg,divStacks,
    DivControl.clearHeld]
  congr 2

theorem div_restore_inspected_iterate (nz:Bool)
    (dividend divisor remainder quotient backup:List Bool):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[backup.length])
        (some (divCleanCfg .restoreInspectedDivisor nz dividend divisor remainder
          quotient backup)) =
      some (divCleanCfg .restoreInspectedDivisor nz dividend
        (backup.reverse ++ divisor) remainder quotient []):=by
  induction backup generalizing divisor with
  | nil => rfl
  | cons b backup ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,div_step_restore_inspected_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

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

@[simp] theorem div_step_outer_nil
    (divisor remainder quotient:List Bool):
    divMachine.step (divCleanCfg .outer true [] divisor remainder quotient []) =
      some (divDoneCfg true divisor remainder quotient):=by
  simp [divMachine,divCleanCfg,divDoneCfg,divCfg,divStacks,
    DivControl.clearHeld]
  congr 2

@[simp] theorem div_step_zero_cons (b:Bool)
    (dividend divisor remainder quotient:List Bool):
    divMachine.step
        (divCleanCfg .zeroLoop false (b::dividend) divisor remainder quotient []) =
      some (divCleanCfg .zeroLoop false dividend divisor remainder
        (false::quotient) []):=by
  simp [divMachine,divCleanCfg,divCfg,divStacks,DivControl.clearHeld,
    Function.update]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]
  funext k
  cases k <;> rfl

@[simp] theorem div_step_zero_nil
    (divisor remainder quotient:List Bool):
    divMachine.step (divCleanCfg .zeroLoop false [] divisor remainder quotient []) =
      some (divDoneCfg false divisor remainder quotient):=by
  simp [divMachine,divCleanCfg,divDoneCfg,divCfg,divStacks,
    DivControl.clearHeld]
  congr 2

theorem div_zero_iterate (dividend divisor remainder quotient:List Bool):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[dividend.length])
        (some (divCleanCfg .zeroLoop false dividend divisor remainder quotient [])) =
      some (divCleanCfg .zeroLoop false [] divisor remainder
        ((dividend.map fun _ => false).reverse ++ quotient) []):=by
  induction dividend generalizing quotient with
  | nil => rfl
  | cons b dividend ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,div_step_zero_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

@[simp] theorem div_step_outer_cons (b:Bool)
    (dividend divisor remainder quotient:List Bool):
    divMachine.step
        (divCleanCfg .outer true (b::dividend) divisor remainder quotient []) =
      some (divPhaseCfg .shiftFirst b false dividend divisor remainder quotient
        [] [] [] []):=by
  simp [divMachine,divCleanCfg,divPhaseCfg,divCfg,divStacks,
    Function.update]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]
  funext k
  cases k <;> rfl

@[simp] theorem div_step_shiftFirst_cons (selected borrow x:Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp:List Bool):
    divMachine.step (divPhaseCfg .shiftFirst selected borrow dividend divisor
        (x::remainder) quotient divisorBackup remainderBackup differenceReverse
        shiftTemp) =
      some (divPhaseCfg .shiftFirst selected borrow dividend divisor remainder quotient
        divisorBackup remainderBackup differenceReverse (x::shiftTemp)):=by
  simp [divMachine,divMoveIteration,divPhaseCfg,divCfg,divStacks,
    DivControl.clearHeld,Function.update]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]
  funext k
  cases k <;> rfl

@[simp] theorem div_step_shiftFirst_nil (selected borrow:Bool)
    (dividend divisor quotient divisorBackup remainderBackup differenceReverse
      shiftTemp:List Bool):
    divMachine.step (divPhaseCfg .shiftFirst selected borrow dividend divisor []
        quotient divisorBackup remainderBackup differenceReverse shiftTemp) =
      some (divPhaseCfg .shiftDiscard selected borrow dividend divisor [] quotient
        divisorBackup remainderBackup differenceReverse shiftTemp):=by
  simp [divMachine,divMoveIteration,divPhaseCfg,divCfg,divStacks,
    DivControl.clearHeld]
  congr 2

theorem div_shiftFirst_iterate (selected borrow:Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp:List Bool):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[remainder.length])
      (some (divPhaseCfg .shiftFirst selected borrow dividend divisor remainder quotient
        divisorBackup remainderBackup differenceReverse shiftTemp)) =
      some (divPhaseCfg .shiftFirst selected borrow dividend divisor [] quotient
        divisorBackup remainderBackup differenceReverse
        (remainder.reverse ++ shiftTemp)):=by
  induction remainder generalizing shiftTemp with
  | nil => rfl
  | cons x remainder ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,div_step_shiftFirst_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

@[simp] theorem div_step_shiftDiscard_cons (selected borrow x:Bool)
    (dividend divisor quotient divisorBackup remainderBackup differenceReverse
      shiftTemp:List Bool):
    divMachine.step (divPhaseCfg .shiftDiscard selected borrow dividend divisor []
        quotient divisorBackup remainderBackup differenceReverse (x::shiftTemp)) =
      some (divPhaseCfg .shiftSecond selected borrow dividend divisor [] quotient
        divisorBackup remainderBackup differenceReverse shiftTemp):=by
  simp [divMachine,divPhaseCfg,divCfg,divStacks,DivControl.clearHeld,
    Function.update]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]
  funext k
  cases k <;> rfl

@[simp] theorem div_step_shiftSecond_cons (selected borrow x:Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp:List Bool):
    divMachine.step (divPhaseCfg .shiftSecond selected borrow dividend divisor remainder
        quotient divisorBackup remainderBackup differenceReverse (x::shiftTemp)) =
      some (divPhaseCfg .shiftSecond selected borrow dividend divisor (x::remainder)
        quotient divisorBackup remainderBackup differenceReverse shiftTemp):=by
  simp [divMachine,divMoveIteration,divPhaseCfg,divCfg,divStacks,
    DivControl.clearHeld,Function.update]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]
  funext k
  cases k <;> rfl

@[simp] theorem div_step_shiftSecond_nil (selected borrow:Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse:List Bool):
    divMachine.step (divPhaseCfg .shiftSecond selected borrow dividend divisor remainder
        quotient divisorBackup remainderBackup differenceReverse []) =
      some (divPhaseCfg .shiftPrepend selected borrow dividend divisor remainder quotient
        divisorBackup remainderBackup differenceReverse []):=by
  simp [divMachine,divMoveIteration,divPhaseCfg,divCfg,divStacks,
    DivControl.clearHeld]
  congr 2

theorem div_shiftSecond_iterate (selected borrow:Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse shiftTemp:List Bool):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[shiftTemp.length])
      (some (divPhaseCfg .shiftSecond selected borrow dividend divisor remainder quotient
        divisorBackup remainderBackup differenceReverse shiftTemp)) =
      some (divPhaseCfg .shiftSecond selected borrow dividend divisor
        (shiftTemp.reverse ++ remainder) quotient divisorBackup remainderBackup
        differenceReverse []):=by
  induction shiftTemp generalizing remainder with
  | nil => rfl
  | cons x shiftTemp ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,div_step_shiftSecond_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

@[simp] theorem div_step_shiftPrepend (selected borrow:Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse:List Bool):
    divMachine.step (divPhaseCfg .shiftPrepend selected borrow dividend divisor remainder
        quotient divisorBackup remainderBackup differenceReverse []) =
      some (divPhaseCfg .subtract selected false dividend divisor (selected::remainder)
        quotient divisorBackup remainderBackup differenceReverse []):=by
  simp [divMachine,divPhaseCfg,divCfg,divStacks,Function.update]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]
  funext k
  cases k <;> rfl

theorem div_shift_pipeline (b x:Bool)
    (dividend divisor remainder quotient:List Bool):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[
      2 * (x::remainder).length + 4])
      (some (divCleanCfg .outer true (b::dividend) divisor (x::remainder)
        quotient [])) =
      some (divPhaseCfg .subtract b false dividend divisor
        (shiftInBit b (x::remainder)) quotient [] [] [] []):=by
  let stepO:=fun o:Option divMachine.Cfg => o.bind divMachine.step
  have chain {m n:ℕ} {a c d:Option divMachine.Cfg}
      (h₁:(stepO^[m]) a=c) (h₂:(stepO^[n]) c=d):
      (stepO^[n + m]) a=d:=by
    rw [Function.iterate_add_apply,h₁,h₂]
  have houter:(stepO^[1])
      (some (divCleanCfg .outer true (b::dividend) divisor (x::remainder)
        quotient [])) =
      some (divPhaseCfg .shiftFirst b false dividend divisor (x::remainder)
        quotient [] [] [] []):=by
    simpa [stepO] using div_step_outer_cons b dividend divisor (x::remainder) quotient
  have hfirst:=div_shiftFirst_iterate b false dividend divisor (x::remainder)
    quotient [] [] [] []
  simp only [List.append_nil] at hfirst
  have hfirst0:(stepO^[1])
      (some (divPhaseCfg .shiftFirst b false dividend divisor [] quotient [] [] []
        (x::remainder).reverse)) =
      some (divPhaseCfg .shiftDiscard b false dividend divisor [] quotient [] [] []
        (x::remainder).reverse):=by
    simpa [stepO] using div_step_shiftFirst_nil b false dividend divisor quotient
      [] [] [] (x::remainder).reverse
  have hdiscard:(stepO^[1])
      (some (divPhaseCfg .shiftDiscard b false dividend divisor [] quotient [] [] []
        (x::remainder).reverse)) =
      some (divPhaseCfg .shiftSecond b false dividend divisor [] quotient [] [] []
        (x::remainder).reverse.tail):=by
    cases hrev:(x::remainder).reverse with
    | nil => simp at hrev
    | cons y ys =>
        simpa [stepO,hrev] using
          div_step_shiftDiscard_cons b false y dividend divisor quotient [] [] [] ys
  have hsecond:=div_shiftSecond_iterate b false dividend divisor [] quotient [] [] []
    (x::remainder).reverse.tail
  simp only [List.append_nil] at hsecond
  have hsecond0:(stepO^[1])
      (some (divPhaseCfg .shiftSecond b false dividend divisor
        ((x::remainder).reverse.tail.reverse) quotient [] [] [] [])) =
      some (divPhaseCfg .shiftPrepend b false dividend divisor
        ((x::remainder).reverse.tail.reverse) quotient [] [] [] []):=by
    simpa [stepO] using div_step_shiftSecond_nil b false dividend divisor
      ((x::remainder).reverse.tail.reverse) quotient [] [] []
  have hprepend:(stepO^[1])
      (some (divPhaseCfg .shiftPrepend b false dividend divisor
        ((x::remainder).reverse.tail.reverse) quotient [] [] [] [])) =
      some (divPhaseCfg .subtract b false dividend divisor
        (b::(x::remainder).reverse.tail.reverse) quotient [] [] [] []):=by
    simpa [stepO] using div_step_shiftPrepend b false dividend divisor
      ((x::remainder).reverse.tail.reverse) quotient [] [] []
  have h:=chain (chain (chain (chain (chain (chain houter hfirst) hfirst0)
    hdiscard) hsecond) hsecond0) hprepend
  have htime:
      1 + (1 + ((x::remainder).reverse.tail.length +
        (1 + (1 + ((x::remainder).length + 1))))) =
        2 * (x::remainder).length + 4:=by
    simp
    omega
  rw [htime] at h
  have hout:(x::remainder).reverse.tail.reverse =
      (x::remainder).take remainder.length:=by
    rw [List.tail_reverse,List.reverse_reverse,List.dropLast_eq_take]
    simp
  rw [hout] at h
  simpa [stepO,shiftInBit] using h

@[simp] theorem div_step_subtract_cons (selected borrow x y:Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse:List Bool):
    divMachine.step (divSubCfg selected borrow none none dividend (y::divisor)
        (x::remainder) quotient divisorBackup remainderBackup differenceReverse) =
      some (divSubCfg selected (fullSubtractor x y borrow).2 none none dividend divisor
        remainder quotient (y::divisorBackup) (x::remainderBackup)
        ((fullSubtractor x y borrow).1::differenceReverse)):=by
  simp [divMachine,divSubCfg,divCfg,divStacks,DivControl.diffBit,
    DivControl.subAdvance,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem div_step_subtract_nil (selected borrow:Bool)
    (dividend quotient divisorBackup remainderBackup differenceReverse:List Bool):
    divMachine.step (divSubCfg selected borrow none none dividend [] [] quotient
        divisorBackup remainderBackup differenceReverse) =
      some (divPhaseCfg .restoreDivisor selected borrow dividend [] [] quotient
        divisorBackup remainderBackup differenceReverse []):=by
  simp [divMachine,divSubCfg,divPhaseCfg,divCfg,divStacks]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]

theorem div_subtract_iterate (selected borrow:Bool)
    (dividend divisor remainder quotient divisorBackup remainderBackup
      differenceReverse:List Bool) (hlen:remainder.length=divisor.length):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[remainder.length])
      (some (divSubCfg selected borrow none none dividend divisor remainder quotient
        divisorBackup remainderBackup differenceReverse)) =
      some (divSubCfg selected (subBorrowOut remainder divisor borrow) none none dividend
        [] [] quotient (divisor.reverse ++ divisorBackup)
        (remainder.reverse ++ remainderBackup)
        ((subBits remainder divisor borrow).reverse ++ differenceReverse)):=by
  induction remainder generalizing divisor borrow divisorBackup remainderBackup
      differenceReverse with
  | nil =>
      cases divisor with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons x remainder ih =>
      cases divisor with
      | nil => simp at hlen
      | cons y divisor =>
          simp at hlen
          rw [List.length_cons,Function.iterate_succ_apply]
          simp only [Option.bind_some,div_step_subtract_cons]
          rw [ih (borrow:=(fullSubtractor x y borrow).2)
            (divisor:=divisor) (hlen:=hlen)]
          simp [subBorrowOut,subBits,List.reverse_cons,List.append_assoc]

@[simp] theorem div_step_restoreDivisor_cons (selected borrow y:Bool)
    (dividend divisor quotient divisorBackup remainderBackup differenceReverse:
      List Bool):
    divMachine.step (divPhaseCfg .restoreDivisor selected borrow dividend divisor []
        quotient (y::divisorBackup) remainderBackup differenceReverse []) =
      some (divPhaseCfg .restoreDivisor selected borrow dividend (y::divisor) []
        quotient divisorBackup remainderBackup differenceReverse []):=by
  simp [divMachine,divMoveIteration,divPhaseCfg,divCfg,divStacks,
    DivControl.clearHeld,Function.update]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]
  funext k
  cases k <;> rfl

@[simp] theorem div_step_restoreDivisor_nil (selected borrow:Bool)
    (dividend divisor quotient remainderBackup differenceReverse:List Bool):
    divMachine.step (divPhaseCfg .restoreDivisor selected borrow dividend divisor []
        quotient [] remainderBackup differenceReverse []) =
      some (divPhaseCfg .choose selected borrow dividend divisor [] quotient []
        remainderBackup differenceReverse []):=by
  simp [divMachine,divMoveIteration,divPhaseCfg,divCfg,divStacks,
    DivControl.clearHeld]
  congr 2

theorem div_restoreDivisor_iterate (selected borrow:Bool)
    (dividend divisor quotient divisorBackup remainderBackup differenceReverse:
      List Bool):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[divisorBackup.length])
      (some (divPhaseCfg .restoreDivisor selected borrow dividend divisor [] quotient
        divisorBackup remainderBackup differenceReverse [])) =
      some (divPhaseCfg .restoreDivisor selected borrow dividend
        (divisorBackup.reverse ++ divisor) [] quotient [] remainderBackup
        differenceReverse []):=by
  induction divisorBackup generalizing divisor with
  | nil => rfl
  | cons y divisorBackup ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,div_step_restoreDivisor_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

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

@[simp] theorem div_step_discardDifference_cons (selected x:Bool)
    (dividend divisor quotient remainderBackup differenceReverse:List Bool):
    divMachine.step (divPhaseCfg .discardDifference selected true dividend divisor []
        quotient [] remainderBackup (x::differenceReverse) []) =
      some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup differenceReverse []):=by
  simp [divMachine,divDiscardIteration,divPhaseCfg,divCfg,divStacks,
    DivControl.clearHeld,Function.update]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]
  funext k
  cases k <;> rfl

@[simp] theorem div_step_discardDifference_nil (selected:Bool)
    (dividend divisor quotient remainderBackup:List Bool):
    divMachine.step (divPhaseCfg .discardDifference selected true dividend divisor []
        quotient [] remainderBackup [] []) =
      some (divPhaseCfg .restoreRemainder selected true dividend divisor [] quotient []
        remainderBackup [] []):=by
  simp [divMachine,divDiscardIteration,divPhaseCfg,divCfg,divStacks,
    DivControl.clearHeld]
  congr 2

theorem div_discardDifference_iterate (selected:Bool)
    (dividend divisor quotient remainderBackup differenceReverse:List Bool):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[differenceReverse.length])
      (some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup [] []):=by
  induction differenceReverse with
  | nil => rfl
  | cons x differenceReverse ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,div_step_discardDifference_cons,ih]

@[simp] theorem div_step_restoreRemainder_cons (selected x:Bool)
    (dividend divisor remainder quotient remainderBackup:List Bool):
    divMachine.step (divPhaseCfg .restoreRemainder selected true dividend divisor
        remainder quotient [] (x::remainderBackup) [] []) =
      some (divPhaseCfg .restoreRemainder selected true dividend divisor
        (x::remainder) quotient [] remainderBackup [] []):=by
  simp [divMachine,divMoveIteration,divPhaseCfg,divCfg,divStacks,
    DivControl.clearHeld,Function.update]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]
  funext k
  cases k <;> rfl

@[simp] theorem div_step_restoreRemainder_nil (selected:Bool)
    (dividend divisor remainder quotient:List Bool):
    divMachine.step (divPhaseCfg .restoreRemainder selected true dividend divisor
        remainder quotient [] [] [] []) =
      some (divPhaseCfg .emit selected true dividend divisor remainder quotient
        [] [] [] []):=by
  simp [divMachine,divMoveIteration,divPhaseCfg,divCfg,divStacks,
    DivControl.clearHeld]
  congr 2

theorem div_restoreRemainder_iterate (selected:Bool)
    (dividend divisor remainder quotient remainderBackup:List Bool):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[remainderBackup.length])
      (some (divPhaseCfg .restoreRemainder selected true dividend divisor remainder
        quotient [] remainderBackup [] [])) =
      some (divPhaseCfg .restoreRemainder selected true dividend divisor
        (remainderBackup.reverse ++ remainder) quotient [] [] [] []):=by
  induction remainderBackup generalizing remainder with
  | nil => rfl
  | cons x remainderBackup ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,div_step_restoreRemainder_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

@[simp] theorem div_step_discardOldRemainder_cons (selected x:Bool)
    (dividend divisor quotient remainderBackup differenceReverse:List Bool):
    divMachine.step (divPhaseCfg .discardOldRemainder selected false dividend divisor []
        quotient [] (x::remainderBackup) differenceReverse []) =
      some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        remainderBackup differenceReverse []):=by
  simp [divMachine,divDiscardIteration,divPhaseCfg,divCfg,divStacks,
    DivControl.clearHeld,Function.update]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]
  funext k
  cases k <;> rfl

@[simp] theorem div_step_discardOldRemainder_nil (selected:Bool)
    (dividend divisor quotient differenceReverse:List Bool):
    divMachine.step (divPhaseCfg .discardOldRemainder selected false dividend divisor []
        quotient [] [] differenceReverse []) =
      some (divPhaseCfg .restoreDifference selected false dividend divisor [] quotient []
        [] differenceReverse []):=by
  simp [divMachine,divDiscardIteration,divPhaseCfg,divCfg,divStacks,
    DivControl.clearHeld]
  congr 2

theorem div_discardOldRemainder_iterate (selected:Bool)
    (dividend divisor quotient remainderBackup differenceReverse:List Bool):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[remainderBackup.length])
      (some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        [] differenceReverse []):=by
  induction remainderBackup with
  | nil => rfl
  | cons x remainderBackup ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,div_step_discardOldRemainder_cons,ih]

@[simp] theorem div_step_restoreDifference_cons (selected x:Bool)
    (dividend divisor remainder quotient differenceReverse:List Bool):
    divMachine.step (divPhaseCfg .restoreDifference selected false dividend divisor
        remainder quotient [] [] (x::differenceReverse) []) =
      some (divPhaseCfg .restoreDifference selected false dividend divisor
        (x::remainder) quotient [] [] differenceReverse []):=by
  simp [divMachine,divMoveIteration,divPhaseCfg,divCfg,divStacks,
    DivControl.clearHeld,Function.update]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]
  funext k
  cases k <;> rfl

@[simp] theorem div_step_restoreDifference_nil (selected:Bool)
    (dividend divisor remainder quotient:List Bool):
    divMachine.step (divPhaseCfg .restoreDifference selected false dividend divisor
        remainder quotient [] [] [] []) =
      some (divPhaseCfg .emit selected false dividend divisor remainder quotient
        [] [] [] []):=by
  simp [divMachine,divMoveIteration,divPhaseCfg,divCfg,divStacks,
    DivControl.clearHeld]
  congr 2

theorem div_restoreDifference_iterate (selected:Bool)
    (dividend divisor remainder quotient differenceReverse:List Bool):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[differenceReverse.length])
      (some (divPhaseCfg .restoreDifference selected false dividend divisor remainder
        quotient [] [] differenceReverse [])) =
      some (divPhaseCfg .restoreDifference selected false dividend divisor
        (differenceReverse.reverse ++ remainder) quotient [] [] [] []):=by
  induction differenceReverse generalizing remainder with
  | nil => rfl
  | cons x differenceReverse ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,div_step_restoreDifference_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

@[simp] theorem div_step_emit (selected borrow:Bool)
    (dividend divisor remainder quotient:List Bool):
    divMachine.step (divPhaseCfg .emit selected borrow dividend divisor remainder quotient
        [] [] [] []) =
      some (divCleanCfg .outer true dividend divisor remainder
        ((!borrow)::quotient) []):=by
  simp [divMachine,divPhaseCfg,divCleanCfg,divCfg,divStacks,Function.update]
  congr 2
  simp [show (default:DivControl)=⟨none,false,none,none,false,false⟩ from rfl]
  funext k
  cases k <;> rfl

theorem div_finalize_true (selected:Bool)
    (dividend divisor quotient remainderBackup differenceReverse:List Bool)
    (hlen:differenceReverse.length=remainderBackup.length):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[
      2 * remainderBackup.length + 4])
      (some (divPhaseCfg .choose selected true dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divCleanCfg .outer true dividend divisor remainderBackup.reverse
        (false::quotient) []):=by
  let stepO:=fun o:Option divMachine.Cfg => o.bind divMachine.step
  have chain {m n:ℕ} {a c d:Option divMachine.Cfg}
      (h₁:(stepO^[m]) a=c) (h₂:(stepO^[n]) c=d):
      (stepO^[n + m]) a=d:=by
    rw [Function.iterate_add_apply,h₁,h₂]
  have hc:(stepO^[1])
      (some (divPhaseCfg .choose selected true dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup differenceReverse []):=by
    simpa [stepO] using div_step_choose_true selected dividend divisor quotient
      remainderBackup differenceReverse
  have hd:=div_discardDifference_iterate selected dividend divisor quotient
    remainderBackup differenceReverse
  have hd0:(stepO^[1])
      (some (divPhaseCfg .discardDifference selected true dividend divisor [] quotient []
        remainderBackup [] [])) =
      some (divPhaseCfg .restoreRemainder selected true dividend divisor [] quotient []
        remainderBackup [] []):=by
    simpa [stepO] using div_step_discardDifference_nil selected dividend divisor quotient
      remainderBackup
  have hr:=div_restoreRemainder_iterate selected dividend divisor [] quotient
    remainderBackup
  simp only [List.append_nil] at hr
  have hr0:(stepO^[1])
      (some (divPhaseCfg .restoreRemainder selected true dividend divisor
        remainderBackup.reverse quotient [] [] [] [])) =
      some (divPhaseCfg .emit selected true dividend divisor remainderBackup.reverse
        quotient [] [] [] []):=by
    simpa [stepO] using div_step_restoreRemainder_nil selected dividend divisor
      remainderBackup.reverse quotient
  have he:(stepO^[1])
      (some (divPhaseCfg .emit selected true dividend divisor remainderBackup.reverse
        quotient [] [] [] [])) =
      some (divCleanCfg .outer true dividend divisor remainderBackup.reverse
        (false::quotient) []):=by
    simpa [stepO] using div_step_emit selected true dividend divisor
      remainderBackup.reverse quotient
  have h:=chain (chain (chain (chain (chain hc hd) hd0) hr) hr0) he
  have htime:
      1 + (1 + (remainderBackup.length +
        (1 + (differenceReverse.length + 1)))) =
        2 * remainderBackup.length + 4:=by omega
  rw [htime] at h
  simpa [stepO] using h

theorem div_finalize_false (selected:Bool)
    (dividend divisor quotient remainderBackup differenceReverse:List Bool)
    (hlen:remainderBackup.length=differenceReverse.length):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[
      2 * remainderBackup.length + 4])
      (some (divPhaseCfg .choose selected false dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divCleanCfg .outer true dividend divisor differenceReverse.reverse
        (true::quotient) []):=by
  let stepO:=fun o:Option divMachine.Cfg => o.bind divMachine.step
  have chain {m n:ℕ} {a c d:Option divMachine.Cfg}
      (h₁:(stepO^[m]) a=c) (h₂:(stepO^[n]) c=d):
      (stepO^[n + m]) a=d:=by
    rw [Function.iterate_add_apply,h₁,h₂]
  have hc:(stepO^[1])
      (some (divPhaseCfg .choose selected false dividend divisor [] quotient []
        remainderBackup differenceReverse [])) =
      some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        remainderBackup differenceReverse []):=by
    simpa [stepO] using div_step_choose_false selected dividend divisor quotient
      remainderBackup differenceReverse
  have hd:=div_discardOldRemainder_iterate selected dividend divisor quotient
    remainderBackup differenceReverse
  have hd0:(stepO^[1])
      (some (divPhaseCfg .discardOldRemainder selected false dividend divisor [] quotient []
        [] differenceReverse [])) =
      some (divPhaseCfg .restoreDifference selected false dividend divisor [] quotient []
        [] differenceReverse []):=by
    simpa [stepO] using div_step_discardOldRemainder_nil selected dividend divisor quotient
      differenceReverse
  have hr:=div_restoreDifference_iterate selected dividend divisor [] quotient
    differenceReverse
  simp only [List.append_nil] at hr
  have hr0:(stepO^[1])
      (some (divPhaseCfg .restoreDifference selected false dividend divisor
        differenceReverse.reverse quotient [] [] [] [])) =
      some (divPhaseCfg .emit selected false dividend divisor differenceReverse.reverse
        quotient [] [] [] []):=by
    simpa [stepO] using div_step_restoreDifference_nil selected dividend divisor
      differenceReverse.reverse quotient
  have he:(stepO^[1])
      (some (divPhaseCfg .emit selected false dividend divisor differenceReverse.reverse
        quotient [] [] [] [])) =
      some (divCleanCfg .outer true dividend divisor differenceReverse.reverse
        (true::quotient) []):=by
    simpa [stepO] using div_step_emit selected false dividend divisor
      differenceReverse.reverse quotient
  have h:=chain (chain (chain (chain (chain hc hd) hd0) hr) hr0) he
  have htime:
      1 + (1 + (differenceReverse.length +
        (1 + (remainderBackup.length + 1)))) =
        2 * remainderBackup.length + 4:=by omega
  rw [htime] at h
  simpa [stepO] using h

theorem div_subtract_pipeline (selected:Bool)
    (dividend divisor candidate quotient:List Bool)
    (hlen:candidate.length=divisor.length):
    let borrow:=subBorrowOut candidate divisor false
    let nextRemainder:=if borrow then candidate else subBits candidate divisor false
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[
      4 * candidate.length + 6])
      (some (divPhaseCfg .subtract selected false dividend divisor candidate quotient
        [] [] [] [])) =
      some (divCleanCfg .outer true dividend divisor nextRemainder
        ((!borrow)::quotient) []):=by
  let stepO:=fun o:Option divMachine.Cfg => o.bind divMachine.step
  let borrow:=subBorrowOut candidate divisor false
  let difference:=subBits candidate divisor false
  have chain {m n:ℕ} {a c d:Option divMachine.Cfg}
      (h₁:(stepO^[m]) a=c) (h₂:(stepO^[n]) c=d):
      (stepO^[n + m]) a=d:=by
    rw [Function.iterate_add_apply,h₁,h₂]
  have hs:=div_subtract_iterate selected false dividend divisor candidate quotient
    [] [] [] hlen
  change (stepO^[candidate.length])
      (some (divPhaseCfg .subtract selected false dividend divisor candidate quotient
        [] [] [] []))=_ at hs
  simp only [List.append_nil] at hs
  change _=some (divSubCfg selected borrow none none dividend [] [] quotient
    divisor.reverse candidate.reverse difference.reverse) at hs
  have hs0:(stepO^[1])
      (some (divSubCfg selected borrow none none dividend [] [] quotient
        divisor.reverse candidate.reverse difference.reverse)) =
      some (divPhaseCfg .restoreDivisor selected borrow dividend [] [] quotient
        divisor.reverse candidate.reverse difference.reverse []):=by
    simpa [stepO] using div_step_subtract_nil selected borrow dividend quotient
      divisor.reverse candidate.reverse difference.reverse
  have hr:=div_restoreDivisor_iterate selected borrow dividend [] quotient
    divisor.reverse candidate.reverse difference.reverse
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hr
  have hr0:(stepO^[1])
      (some (divPhaseCfg .restoreDivisor selected borrow dividend divisor [] quotient
        [] candidate.reverse difference.reverse [])) =
      some (divPhaseCfg .choose selected borrow dividend divisor [] quotient []
        candidate.reverse difference.reverse []):=by
    simpa [stepO] using div_step_restoreDivisor_nil selected borrow dividend divisor
      quotient candidate.reverse difference.reverse
  have hp:(stepO^[2 * candidate.length + 4])
      (some (divPhaseCfg .choose selected borrow dividend divisor [] quotient []
        candidate.reverse difference.reverse [])) =
      some (divCleanCfg .outer true dividend divisor
        (if borrow then candidate else difference) ((!borrow)::quotient) []):=by
    cases hb:borrow with
    | false =>
        have hdlen:candidate.reverse.length=difference.reverse.length:=by
          simp [difference,subBits_length_of_eq false hlen]
        simpa [hb] using! div_finalize_false selected dividend divisor quotient
          candidate.reverse difference.reverse hdlen
    | true =>
        have hdlen:difference.reverse.length=candidate.reverse.length:=by
          simp [difference,subBits_length_of_eq false hlen]
        simpa [hb] using! div_finalize_true selected dividend divisor quotient
          candidate.reverse difference.reverse hdlen
  have h:=chain (chain (chain (chain hs hs0) hr) hr0) hp
  have htime:
      2 * candidate.length + 4 +
        (1 + (divisor.length + (1 + candidate.length))) =
        4 * candidate.length + 6:=by omega
  rw [htime] at h
  simpa [stepO,borrow,difference] using h

theorem div_round (b x:Bool)
    (dividend divisor remainder quotient:List Bool)
    (hlen:(x::remainder).length=divisor.length):
    let candidate:=shiftInBit b (x::remainder)
    let borrow:=subBorrowOut candidate divisor false
    let nextRemainder:=if borrow then candidate else subBits candidate divisor false
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[
      6 * (x::remainder).length + 10])
      (some (divCleanCfg .outer true (b::dividend) divisor (x::remainder)
        quotient [])) =
      some (divCleanCfg .outer true dividend divisor nextRemainder
        ((!borrow)::quotient) []):=by
  let stepO:=fun o:Option divMachine.Cfg => o.bind divMachine.step
  let candidate:=shiftInBit b (x::remainder)
  let borrow:=subBorrowOut candidate divisor false
  have hs:=div_shift_pipeline b x dividend divisor remainder quotient
  change (stepO^[2 * (x::remainder).length + 4]) _=_ at hs
  change _=some (divPhaseCfg .subtract b false dividend divisor candidate quotient
    [] [] [] []) at hs
  have hcandidate:candidate.length=divisor.length:=by
    simp [candidate,hlen]
  have hd:=div_subtract_pipeline b dividend divisor candidate quotient hcandidate
  change (stepO^[4 * candidate.length + 6]) _=_ at hd
  have chain {m n:ℕ} {a c d:Option divMachine.Cfg}
      (h₁:(stepO^[m]) a=c) (h₂:(stepO^[n]) c=d):
      (stepO^[n + m]) a=d:=by
    rw [Function.iterate_add_apply,h₁,h₂]
  have h:=chain hs hd
  have htime:
      4 * candidate.length + 6 + (2 * (x::remainder).length + 4) =
        6 * (x::remainder).length + 10:=by
    simp [candidate]
    omega
  rw [htime] at h
  simpa [stepO,candidate,borrow] using h

theorem div_round_fixed (w d:ℕ) (s:DivisionScan) (b:Bool)
    (bits:List Bool)
    (hd:d < 2 ^ w) (hr:s.remainder < d):
    let s':=divisionScanStep d s b
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[
      6 * (w + 1) + 10])
      (some (divCleanCfg .outer true (b::bits) (fixedBits (w + 1) d)
        (fixedBits (w + 1) s.remainder) s.quotient [])) =
      some (divCleanCfg .outer true bits (fixedBits (w + 1) d)
        (fixedBits (w + 1) s'.remainder) s'.quotient []):=by
  let candidate:=2 * s.remainder + b.toNat
  have hc:candidate < 2 ^ (w + 1):=
    divisionScan_candidate_lt_extra_bit b hd hr
  have hdextra:d < 2 ^ (w + 1):=by
    rw [pow_succ]
    omega
  have hround:=div_round b s.remainder.bodd bits (fixedBits (w + 1) d)
    (fixedBits w s.remainder.div2) s.quotient (by simp)
  dsimp only at hround
  simp only [fixedBits_length,List.length_cons] at hround
  change ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[
      6 * (w + 1) + 10])
      (some (divCleanCfg .outer true (b::bits) (fixedBits (w + 1) d)
        (fixedBits (w + 1) s.remainder) s.quotient []))=_ at hround
  rw [show s.remainder.bodd::fixedBits w s.remainder.div2 =
    fixedBits (w + 1) s.remainder by rfl] at hround
  rw [shiftInBit_fixed] at hround
  change _=some (divCleanCfg .outer true bits (fixedBits (w + 1) d)
    (if subBorrowOut (fixedBits (w + 1) candidate) (fixedBits (w + 1) d) false
      then fixedBits (w + 1) candidate
      else subBits (fixedBits (w + 1) candidate) (fixedBits (w + 1) d) false)
    ((!subBorrowOut (fixedBits (w + 1) candidate) (fixedBits (w + 1) d) false)::
      s.quotient) []) at hround
  rw [subBorrowOut_fixed_eq_decide_lt (w + 1) candidate d hc hdextra] at hround
  by_cases hle:d≤ candidate
  · have hnlt:¬ candidate < d:=by omega
    have hsub:=fixedBits_sub_of_le (w + 1) hle
    simp [divisionScanStep,candidate,hle,hnlt,hsub] at hround ⊢
    exact hround
  · have hlt:candidate < d:=by omega
    simp [divisionScanStep,candidate,hle,hlt] at hround ⊢
    exact hround

theorem div_rounds_fixed (w d:ℕ) (bits:List Bool) (s:DivisionScan)
    (hd0:0 < d) (hd:d < 2 ^ w) (hr:s.remainder < d):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[
      bits.length * (6 * (w + 1) + 10)])
      (some (divCleanCfg .outer true bits (fixedBits (w + 1) d)
        (fixedBits (w + 1) s.remainder) s.quotient [])) =
      some (divCleanCfg .outer true [] (fixedBits (w + 1) d)
        (fixedBits (w + 1) (divisionScan d s bits).remainder)
        (divisionScan d s bits).quotient []):=by
  induction bits generalizing s with
  | nil => simp [divisionScan]
  | cons b bits ih =>
      let s':=divisionScanStep d s b
      have hr':s'.remainder < d:=
        (divisionScanStep_invariant hd0 s b hr).2
      have hround:=div_round_fixed w d s b bits hd hr
      have htail:=ih s' hr'
      have hchain:
          ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[
            bits.length * (6 * (w + 1) + 10) + (6 * (w + 1) + 10)])
            (some (divCleanCfg .outer true (b::bits) (fixedBits (w + 1) d)
              (fixedBits (w + 1) s.remainder) s.quotient [])) =
            some (divCleanCfg .outer true [] (fixedBits (w + 1) d)
              (fixedBits (w + 1) (divisionScan d s' bits).remainder)
              (divisionScan d s' bits).quotient []):=by
        rw [Function.iterate_add_apply,hround,htail]
      simpa [divisionScan,s',List.length_cons,Nat.add_mul,Nat.add_comm,
        Nat.add_left_comm,Nat.add_assoc] using hchain

def divZeroRunTime (w:ℕ):ℕ:=2 * (w + 1) + 3 + (w + 1)

def divPositiveRunTime (w:ℕ):ℕ:=
  2 * (w + 1) + 3 + w * (6 * (w + 1) + 10) + 1

theorem divZeroRunTime_le_bound (w:ℕ):
    divZeroRunTime w≤ divRunTimeBound w:=by
  simp [divZeroRunTime,divRunTimeBound]
  nlinarith

theorem divPositiveRunTime_le_bound (w:ℕ):
    divPositiveRunTime w≤ divRunTimeBound w:=by
  simp [divPositiveRunTime,divRunTimeBound]
  nlinarith

theorem divMachine_zero_correct (w a:ℕ):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[divZeroRunTime w])
        (some (divInitialCfg (fixedBits w a).reverse (fixedBits (w + 1) 0)
          (fixedBits (w + 1) 0))) =
      some (divDoneCfg false (fixedBits (w + 1) 0) (fixedBits (w + 1) 0)
        (fixedBits w 0)):=by
  let stepO:=fun o:Option divMachine.Cfg => o.bind divMachine.step
  have chain {m n:ℕ} {x y z:Option divMachine.Cfg}
      (h₁:(stepO^[m]) x=y) (h₂:(stepO^[n]) y=z):
      (stepO^[n + m]) x=z:=by
    rw [Function.iterate_add_apply,h₁,h₂]
  let dividend:=(fixedBits w a).reverse
  let divisor:=fixedBits (w + 1) 0
  let remainder:=fixedBits (w + 1) 0
  have hfalse:containsTrue divisor=false:=by
    simp [divisor,fixedBits_zero]
    induction w with
    | zero => decide
    | succ w ih => simpa [List.replicate_succ,containsTrue] using ih
  have hi:=div_inspect_iterate false dividend divisor remainder []
  simp only [Bool.false_or,hfalse,List.append_nil] at hi
  have hi0:(stepO^[1])
      (some (divCleanCfg .inspectDivisor false dividend [] remainder []
        divisor.reverse)) =
      some (divCleanCfg .restoreInspectedDivisor false dividend [] remainder []
        divisor.reverse):=by
    simpa [stepO] using
      div_step_inspect_nil false dividend remainder divisor.reverse
  have hr:=div_restore_inspected_iterate false dividend [] remainder [] divisor.reverse
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hr
  have hr0:(stepO^[1])
      (some (divCleanCfg .restoreInspectedDivisor false dividend divisor remainder [] [])) =
      some (divCleanCfg .dispatch false dividend divisor remainder [] []):=by
    simpa [stepO] using
      div_step_restore_inspected_nil false dividend divisor remainder ([]:List Bool)
  have hd:(stepO^[1])
      (some (divCleanCfg .dispatch false dividend divisor remainder [] [])) =
      some (divCleanCfg .zeroLoop false dividend divisor remainder [] []):=by
    simpa [stepO] using div_step_dispatch_false dividend divisor remainder []
  have hz:=div_zero_iterate dividend divisor remainder []
  simp only [List.append_nil] at hz
  have hz0:(stepO^[1])
      (some (divCleanCfg .zeroLoop false [] divisor remainder
        (dividend.map fun _ => false).reverse [])) =
      some (divDoneCfg false divisor remainder
        (dividend.map fun _ => false).reverse):=by
    simpa [stepO] using div_step_zero_nil divisor remainder
      (dividend.map fun _ => false).reverse
  have h:=chain (chain (chain (chain (chain (chain hi hi0) hr) hr0) hd) hz) hz0
  have htime:
      1 + (dividend.length + (1 + (1 + (divisor.length +
        (1 + divisor.length)))))=divZeroRunTime w:=by
    simp [dividend,divisor,divZeroRunTime]
    omega
  rw [htime] at h
  have hquot:(dividend.map fun _ => false).reverse=fixedBits w 0:=by
    simp [dividend,fixedBits_zero]
  simpa [stepO,divInitialCfg,divCleanCfg,dividend,divisor,remainder,hquot] using! h

theorem divMachine_positive_correct (w a d:ℕ)
    (ha:a < 2 ^ w) (hd0:0 < d) (hd:d < 2 ^ w):
    ((fun o:Option divMachine.Cfg => o.bind divMachine.step)^[
      divPositiveRunTime w])
      (some (divInitialCfg (fixedBits w a).reverse (fixedBits (w + 1) d)
        (fixedBits (w + 1) 0))) =
      some (divDoneCfg true (fixedBits (w + 1) d) (fixedBits (w + 1) (a % d))
        (fixedBits w (a / d))):=by
  let stepO:=fun o:Option divMachine.Cfg => o.bind divMachine.step
  have chain {m n:ℕ} {x y z:Option divMachine.Cfg}
      (h₁:(stepO^[m]) x=y) (h₂:(stepO^[n]) y=z):
      (stepO^[n + m]) x=z:=by
    rw [Function.iterate_add_apply,h₁,h₂]
  let dividend:=(fixedBits w a).reverse
  let divisor:=fixedBits (w + 1) d
  let remainder:=fixedBits (w + 1) 0
  let initialScan:DivisionScan:= ⟨[],0⟩
  let finalScan:=divisionScan d initialScan dividend
  have hdextra:d < 2 ^ (w + 1):=by
    rw [pow_succ]
    omega
  have htrue:containsTrue divisor=true:=by
    cases hc:containsTrue divisor with
    | false =>
        have hz:=containsTrue_false_bitsValue_zero hc
        rw [bitsValue_fixedBits_of_lt hdextra] at hz
        omega
    | true => rfl
  have hi:=div_inspect_iterate false dividend divisor remainder []
  simp only [Bool.false_or,htrue,List.append_nil] at hi
  have hi0:(stepO^[1])
      (some (divCleanCfg .inspectDivisor true dividend [] remainder [] divisor.reverse)) =
      some (divCleanCfg .restoreInspectedDivisor true dividend [] remainder []
        divisor.reverse):=by
    simpa [stepO] using div_step_inspect_nil true dividend remainder divisor.reverse
  have hr:=div_restore_inspected_iterate true dividend [] remainder [] divisor.reverse
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hr
  have hr0:(stepO^[1])
      (some (divCleanCfg .restoreInspectedDivisor true dividend divisor remainder [] [])) =
      some (divCleanCfg .dispatch true dividend divisor remainder [] []):=by
    simpa [stepO] using
      div_step_restore_inspected_nil true dividend divisor remainder ([]:List Bool)
  have hdsp:(stepO^[1])
      (some (divCleanCfg .dispatch true dividend divisor remainder [] [])) =
      some (divCleanCfg .outer true dividend divisor remainder [] []):=by
    simpa [stepO] using div_step_dispatch_true dividend divisor remainder []
  have hlo:=div_rounds_fixed w d dividend initialScan hd0 hd hd0
  change (stepO^[dividend.length * (6 * (w + 1) + 10)])
      (some (divCleanCfg .outer true dividend divisor remainder [] [])) =
      some (divCleanCfg .outer true [] divisor
        (fixedBits (w + 1) finalScan.remainder) finalScan.quotient []) at hlo
  have hdone:(stepO^[1])
      (some (divCleanCfg .outer true [] divisor
        (fixedBits (w + 1) finalScan.remainder) finalScan.quotient [])) =
      some (divDoneCfg true divisor (fixedBits (w + 1) finalScan.remainder)
        finalScan.quotient):=by
    simpa [stepO] using div_step_outer_nil divisor
      (fixedBits (w + 1) finalScan.remainder) finalScan.quotient
  have h:=chain (chain (chain (chain (chain (chain hi hi0) hr) hr0) hdsp) hlo) hdone
  have htime:
      1 + (dividend.length * (6 * (w + 1) + 10) +
        (1 + (1 + (divisor.length + (1 + divisor.length))))) =
        divPositiveRunTime w:=by
    simp [dividend,divisor,divPositiveRunTime]
    omega
  rw [htime] at h
  have hscan:=divisionScan_fixed_correct w a d ha hd0
  change bitsValue finalScan.quotient=a / d∧ finalScan.remainder=a % d at hscan
  have hlen:finalScan.quotient.length=w:=by
    dsimp [finalScan,initialScan,dividend]
    rw [divisionScan_quotient_length]
    simp
  have hquot:finalScan.quotient=fixedBits w (a / d):=by
    calc
      finalScan.quotient=fixedBits finalScan.quotient.length
          (bitsValue finalScan.quotient):=(fixedBits_bitsValue _).symm
      _=fixedBits w (a / d):=by rw [hlen,hscan.1]
  rw [hscan.2,hquot] at h
  simpa [stepO,divInitialCfg,divCleanCfg,dividend,divisor,remainder] using! h

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def sparseDivProgram:=
  mapAlphabetProgram sparseBitEncode sparseBitDecode divMachine.m

def sparseDivInitialCfg (dividend divisor remainder:List Bool):=
  mapAlphabetCfg sparseBitEncode (divInitialCfg dividend divisor remainder)

def sparseDivDoneCfg (divisorNonzero:Bool)
    (divisor remainder quotient:List Bool):=
  mapAlphabetCfg sparseBitEncode
    (divDoneCfg divisorNonzero divisor remainder quotient)

theorem sparseDiv_zero_correct (w a:ℕ):
    ((fun o => o.bind (TM2.step sparseDivProgram))^[divZeroRunTime w])
      (some (sparseDivInitialCfg (fixedBits w a).reverse (fixedBits (w + 1) 0)
        (fixedBits (w + 1) 0))) =
      some (sparseDivDoneCfg false (fixedBits (w + 1) 0) (fixedBits (w + 1) 0)
        (fixedBits w 0)):=by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode divMachine.m (divMachine_zero_correct w a)

theorem sparseDiv_positive_correct (w a d:ℕ)
    (ha:a < 2 ^ w) (hd0:0 < d) (hd:d < 2 ^ w):
    ((fun o => o.bind (TM2.step sparseDivProgram))^[divPositiveRunTime w])
      (some (sparseDivInitialCfg (fixedBits w a).reverse (fixedBits (w + 1) d)
        (fixedBits (w + 1) 0))) =
      some (sparseDivDoneCfg true (fixedBits (w + 1) d)
        (fixedBits (w + 1) (a % d)) (fixedBits w (a / d))):=by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode divMachine.m
    (divMachine_positive_correct w a d ha hd0 hd)

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

def sparseDivLocalInitialCfg (dividend divisor remainder:List Bool):
    TM2.Cfg (fun _:DivStack => SparseSymbol) DivLabel DivControl where
  l:=some .inspectDivisor
  var:=default
  stk:=mapAlphabetStacks sparseBitEncode
    (divStacks dividend divisor remainder [] [] [] [] [])

def sparseDivLocalDoneCfg (divisorNonzero:Bool)
    (divisor remainder quotient:List Bool):
    TM2.Cfg (fun _:DivStack => SparseSymbol) DivLabel DivControl where
  l:=some .done
  var:= { (default:DivControl) with divisorNonzero:=divisorNonzero }
  stk:=mapAlphabetStacks sparseBitEncode
    (divStacks [] divisor remainder quotient [] [] [] [])

theorem sparseDivLocal_zero_correct (w a:ℕ):
    ((fun o => o.bind (TM2.step sparseDivCoreProgram))^[divZeroRunTime w])
      (some (sparseDivLocalInitialCfg (fixedBits w a).reverse
        (fixedBits (w + 1) 0) (fixedBits (w + 1) 0))) =
      some (sparseDivLocalDoneCfg false (fixedBits (w + 1) 0)
        (fixedBits (w + 1) 0) (fixedBits w 0)):=by
  have hp:sparseDivCoreProgram=sparseDivProgram:=by
    funext l
    cases l <;> rfl
  rw [hp]
  simpa [sparseDivLocalInitialCfg,sparseDivLocalDoneCfg,sparseDivInitialCfg,
    sparseDivDoneCfg,divInitialCfg,divDoneCfg,divCfg,mapAlphabetCfg] using!
      sparseDiv_zero_correct w a

theorem sparseDivLocal_positive_correct (w a d:ℕ)
    (ha:a < 2 ^ w) (hd0:0 < d) (hd:d < 2 ^ w):
    ((fun o => o.bind (TM2.step sparseDivCoreProgram))^[divPositiveRunTime w])
      (some (sparseDivLocalInitialCfg (fixedBits w a).reverse
        (fixedBits (w + 1) d) (fixedBits (w + 1) 0))) =
      some (sparseDivLocalDoneCfg true (fixedBits (w + 1) d)
        (fixedBits (w + 1) (a % d)) (fixedBits w (a / d))):=by
  have hp:sparseDivCoreProgram=sparseDivProgram:=by
    funext l
    cases l <;> rfl
  rw [hp]
  simpa [sparseDivLocalInitialCfg,sparseDivLocalDoneCfg,sparseDivInitialCfg,
    sparseDivDoneCfg,divInitialCfg,divDoneCfg,divCfg,mapAlphabetCfg] using!
      sparseDiv_positive_correct w a d ha hd0 hd

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

@[simp] theorem renamedStacks_coreIdentity
    (inner ambient:CoreStack→ List SparseSymbol):
    renamedStacks coreIdentityRenaming inner ambient=inner:=by
  funext k
  rfl

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

namespace Lax759944Proofs.RamToTM

open Turing TM2

theorem chain_iterations {X:Type} (step:X -> X)
    {a b c:X} {m n:Nat}
    (h₁:(step^[m]) a=b) (h₂:(step^[n]) b=c):
    (step^[m + n]) a=c:=by
  rw [Nat.add_comm,Function.iterate_add_apply,h₁,h₂]

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

namespace Lax759944Proofs.RamToTM

open Turing TM2

abbrev FullDivideCoreLabel (R:Type):=Sum DivLabel R

def fullDivideCoreProgram {N:Nat} {R:Type} (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)):
    FullDivideCoreLabel R -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (FullDivideCoreLabel R)
      (FullInterpreterState N):=
  liftRightProgram
    (lensPhaseLeft preparedDivRenaming FullInterpreterState.divLens
      sparseDivCoreProgram .done returnLabel)
    right

def preparedDivideStacks (w a d:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol
  | .work7 => (fixedBits w a).reverse.map SparseSymbol.bit
  | .work1 => (fixedBits (w + 1) d).map SparseSymbol.bit
  | .work2 => (fixedBits (w + 1) 0).map SparseSymbol.bit
  | .accumulator | .work0 | .work3 | .work4 | .work5 | .work6 => []
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | k => base k

def divideCoreResultStacks (w d remainder quotient:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w quotient).map SparseSymbol.bit
  | .work1 => (fixedBits (w + 1) d).map SparseSymbol.bit
  | .work2 => (fixedBits (w + 1) remainder).map SparseSymbol.bit
  | .work0 | .work3 | .work4 | .work5 | .work6 | .work7 => []
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | k => base k

theorem divideCore_zero_return_bridge {N:Nat} {R:Type}
    (returnLabel:R) (w a:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    phaseReturnCfg preparedDivRenaming FullInterpreterState.divLens returnLabel
      (sparseDivLocalDoneCfg false (fixedBits (w + 1) 0)
        (fixedBits (w + 1) 0) (fixedBits w 0))
      state (preparedDivideStacks w a 0 m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.divLens.put state
        { (default:DivControl) with divisorNonzero:=false })
      (divideCoreResultStacks w 0 0 0 m base):=by
  simp [phaseReturnCfg,cleanReturnCfg,sparseDivLocalDoneCfg,
    preparedDivideStacks,divideCoreResultStacks,renamedStacks,
    preparedDivRenaming,preparedDivDecode,divStacks,mapAlphabetStacks,
    sparseBitEncode]
  funext k
  cases k <;> simp [renamedStacks,preparedDivRenaming,
    preparedDivDecode,divStacks,mapAlphabetStacks,sparseBitEncode,
    divideCoreResultStacks,preparedDivideStacks]

theorem divideCore_positive_return_bridge {N:Nat} {R:Type}
    (returnLabel:R) (w a d:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    phaseReturnCfg preparedDivRenaming FullInterpreterState.divLens returnLabel
      (sparseDivLocalDoneCfg true (fixedBits (w + 1) d)
        (fixedBits (w + 1) (a % d)) (fixedBits w (a / d)))
      state (preparedDivideStacks w a d m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.divLens.put state
        { (default:DivControl) with divisorNonzero:=true })
      (divideCoreResultStacks w d (a % d) (a / d) m base):=by
  simp [phaseReturnCfg,cleanReturnCfg,sparseDivLocalDoneCfg,
    preparedDivideStacks,divideCoreResultStacks,renamedStacks,
    preparedDivRenaming,preparedDivDecode,divStacks,mapAlphabetStacks,
    sparseBitEncode]
  funext k
  cases k <;> rfl

theorem fullDivideCore_zero_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    ((fun o => o.bind (TM2.step
      (fullDivideCoreProgram returnLabel right)))^[divZeroRunTime w + 1])
      (some (lensRenamedCfg preparedDivRenaming FullInterpreterState.divLens
        (sparseDivLocalInitialCfg (fixedBits w a).reverse
          (fixedBits (w + 1) 0) (fixedBits (w + 1) 0))
        state (preparedDivideStacks w a 0 m base))) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel
        (FullInterpreterState.divLens.put state
          { (default:DivControl) with divisorNonzero:=false })
        (divideCoreResultStacks w 0 0 0 m base))):=by
  have h:=run_lensPhase_to_right preparedDivRenaming
    FullInterpreterState.divLens sparseDivCoreProgram .done (by rfl)
    returnLabel right (sparseDivLocal_zero_correct w a) rfl state
    (preparedDivideStacks w a 0 m base)
  rw [divideCore_zero_return_bridge returnLabel w a m base state] at h
  simpa [fullDivideCoreProgram] using h

theorem fullDivideCore_positive_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a d:Nat) (ha:a < 2 ^ w) (hd0:0 < d) (hd:d < 2 ^ w)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ((fun o => o.bind (TM2.step
      (fullDivideCoreProgram returnLabel right)))^[divPositiveRunTime w + 1])
      (some (lensRenamedCfg preparedDivRenaming FullInterpreterState.divLens
        (sparseDivLocalInitialCfg (fixedBits w a).reverse
          (fixedBits (w + 1) d) (fixedBits (w + 1) 0))
        state (preparedDivideStacks w a d m base))) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel
        (FullInterpreterState.divLens.put state
          { (default:DivControl) with divisorNonzero:=true })
        (divideCoreResultStacks w d (a % d) (a / d) m base))):=by
  have h:=run_lensPhase_to_right preparedDivRenaming
    FullInterpreterState.divLens sparseDivCoreProgram .done (by rfl)
    returnLabel right (sparseDivLocal_positive_correct w a d ha hd0 hd) rfl
    state (preparedDivideStacks w a d m base)
  rw [divideCore_positive_return_bridge returnLabel w a d m base state] at h
  simpa [fullDivideCoreProgram] using h

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def divideAfterFirstCleanupStacks (w remainder quotient:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w quotient).map SparseSymbol.bit
  | .work2 => (fixedBits (w + 1) remainder).map SparseSymbol.bit
  | .work0 | .work1 | .work3 | .work4 | .work5 | .work6 | .work7 => []
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | k => base k

theorem divideFirstCleanup_bridge {N:Nat} {R:Type}
    (w d remainder quotient:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N)
    (hmove:FullInterpreterState.moveLens.get state=default):
    cleanReturnCfg (Sum.inl DiscardLabel.loop:DivideCleanupTailLabel R)
      state (divideCoreResultStacks w d remainder quotient m base) =
    lensRenamedCfg (discardCoreRenaming .work1)
      FullInterpreterState.moveLens
      (discardCfg .loop ((fixedBits (w + 1) d).map SparseSymbol.bit))
      state (divideCoreResultStacks w d remainder quotient m base):=by
  simp [cleanReturnCfg,lensRenamedCfg,discardCoreRenaming,discardCfg,
    discardStacks,divideCoreResultStacks,renamedStacks]
  constructor
  · symm
    rw [← hmove,FullInterpreterState.moveLens.put_get]
  · funext k
    cases k <;> simp [renamedStacks,discardCoreRenaming,discardCfg,
      discardStacks,divideCoreResultStacks]

theorem divideSecondCleanup_bridge {N:Nat} {R:Type}
    (w remainder quotient:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    phaseReturnCfg (discardCoreRenaming .work1)
      FullInterpreterState.moveLens
      (Sum.inl DiscardLabel.loop:DivideCleanupFinalLabel R)
      (discardCfg .done []) state
      (divideCoreResultStacks w 0 remainder quotient m base) =
    lensRenamedCfg (discardCoreRenaming .work2)
      FullInterpreterState.moveLens
      (discardCfg .loop
        ((fixedBits (w + 1) remainder).map SparseSymbol.bit))
      (FullInterpreterState.moveLens.put state default)
      (divideAfterFirstCleanupStacks w remainder quotient m base):=by
  simp [phaseReturnCfg,lensRenamedCfg,discardCoreRenaming,discardCfg,
    discardStacks,divideCoreResultStacks,divideAfterFirstCleanupStacks,
    renamedStacks]
  constructor
  · rfl
  · funext k
    cases k <;> rfl

theorem divideCleanup_return_bridge {N:Nat} {R:Type}
    (returnLabel:R) (w remainder quotient:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    phaseReturnCfg (discardCoreRenaming .work2)
      FullInterpreterState.moveLens returnLabel
      (discardCfg .done []) state
      (divideAfterFirstCleanupStacks w remainder quotient m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (operandBoundaryBase w quotient m base):=by
  simp [phaseReturnCfg,cleanReturnCfg,lensRenamedCfg,
    discardCoreRenaming,discardCfg,discardStacks,
    divideAfterFirstCleanupStacks,operandBoundaryBase,renamedStacks]
  funext k
  cases k <;> rfl

theorem fullDivideClean_zero_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N)
    (hmove:FullInterpreterState.moveLens.get state=default):
    ∃ finalState,
      FullInterpreterState.moveLens.get finalState=default∧
      FullInterpreterState.literalLens.get finalState =
        FullInterpreterState.literalLens.get state∧
      ((fun o => o.bind (TM2.step
        (fullDivideCleanProgram returnLabel right)))^[
          divZeroRunTime w + 2 * w + 7])
        (some (lensRenamedCfg preparedDivRenaming FullInterpreterState.divLens
          (sparseDivLocalInitialCfg (fixedBits w a).reverse
            (fixedBits (w + 1) 0) (fixedBits (w + 1) 0))
          state (preparedDivideStacks w a 0 m base))) =
      some (mapLabelCfg (fun l:DivideCleanupTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l:DivideCleanupFinalLabel R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w 0 m base))))):=by
  have hcore:=fullDivideCore_zero_correct
    (Sum.inl DiscardLabel.loop:DivideCleanupTailLabel R)
    (divideCleanupTailProgram returnLabel right) w a m base state
  let coreState:=FullInterpreterState.divLens.put state
    { (default:DivControl) with divisorNonzero:=false }
  rw [divideFirstCleanup_bridge (R:=R) w 0 0 0 m base coreState
    (by simpa [coreState] using! hmove)] at hcore
  have hfirstRaw:=run_lensPhase_to_right (discardCoreRenaming .work1)
    FullInterpreterState.moveLens discardProgram .done (by rfl)
    (Sum.inl DiscardLabel.loop) (divideCleanupFinalProgram returnLabel right)
    (discard_correct ((fixedBits (w + 1) 0).map SparseSymbol.bit)) rfl
    coreState (divideCoreResultStacks w 0 0 0 m base)
  simp only [List.length_map,fixedBits_length] at hfirstRaw
  rw [divideSecondCleanup_bridge (R:=R) w 0 0 m base coreState] at hfirstRaw
  let firstState:=FullInterpreterState.moveLens.put coreState default
  have hsecondRaw:=run_lensPhase_to_right (discardCoreRenaming .work2)
    FullInterpreterState.moveLens discardProgram .done (by rfl)
    returnLabel right
    (discard_correct ((fixedBits (w + 1) 0).map SparseSymbol.bit)) rfl
    firstState (divideAfterFirstCleanupStacks w 0 0 m base)
  simp only [List.length_map,fixedBits_length] at hsecondRaw
  rw [divideCleanup_return_bridge returnLabel w 0 0 m base firstState]
    at hsecondRaw
  have hcleanup:=chain_liftRightProgram (m:=w + 3) (n:=w + 3)
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl DiscardLabel.loop))
    (divideCleanupFinalProgram returnLabel right) hfirstRaw hsecondRaw
  have hcleanup':
      ((fun o => o.bind (TM2.step
        (divideCleanupTailProgram returnLabel right)))^[2 * w + 6])
        (some (lensRenamedCfg (discardCoreRenaming .work1)
          FullInterpreterState.moveLens
          (discardCfg .loop ((fixedBits (w + 1) 0).map SparseSymbol.bit))
          coreState (divideCoreResultStacks w 0 0 0 m base))) =
      some (mapLabelCfg (fun l:DivideCleanupFinalLabel R => Sum.inr l)
        (mapLabelCfg (fun l:R => Sum.inr l)
          (cleanReturnCfg returnLabel
            (FullInterpreterState.moveLens.put firstState default)
            (operandBoundaryBase w 0 m base)))):=by
    simpa only [divideCleanupTailProgram,
      show w + 3 + (w + 3)=2 * w + 6 by omega] using hcleanup
  have hall:=chain_liftRightProgram
    (m:=divZeroRunTime w + 1) (n:=2 * w + 6)
    (lensPhaseLeft preparedDivRenaming FullInterpreterState.divLens
      sparseDivCoreProgram .done (Sum.inl DiscardLabel.loop))
    (divideCleanupTailProgram returnLabel right) hcore hcleanup'
  refine ⟨FullInterpreterState.moveLens.put firstState default,
    FullInterpreterState.moveLens.get_put _ _,by rfl, ?_⟩
  have ht:divZeroRunTime w + 2 * w + 7 =
      (divZeroRunTime w + 1) + (2 * w + 6):=by omega
  rw [ht]
  simpa [fullDivideCleanProgram,coreState,firstState] using hall

theorem fullDivideClean_positive_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a d:Nat) (ha:a < 2 ^ w) (hd0:0 < d) (hd:d < 2 ^ w)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N)
    (hmove:FullInterpreterState.moveLens.get state=default):
    ∃ finalState,
      FullInterpreterState.moveLens.get finalState=default∧
      FullInterpreterState.literalLens.get finalState =
        FullInterpreterState.literalLens.get state∧
      ((fun o => o.bind (TM2.step
        (fullDivideCleanProgram returnLabel right)))^[
          divPositiveRunTime w + 2 * w + 7])
        (some (lensRenamedCfg preparedDivRenaming FullInterpreterState.divLens
          (sparseDivLocalInitialCfg (fixedBits w a).reverse
            (fixedBits (w + 1) d) (fixedBits (w + 1) 0))
          state (preparedDivideStacks w a d m base))) =
      some (mapLabelCfg (fun l:DivideCleanupTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l:DivideCleanupFinalLabel R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w (a / d) m base))))):=by
  have hcore:=fullDivideCore_positive_correct
    (Sum.inl DiscardLabel.loop:DivideCleanupTailLabel R)
    (divideCleanupTailProgram returnLabel right) w a d ha hd0 hd m base state
  let coreState:=FullInterpreterState.divLens.put state
    { (default:DivControl) with divisorNonzero:=true }
  rw [divideFirstCleanup_bridge (R:=R) w d (a % d) (a / d) m base coreState
    (by simpa [coreState] using! hmove)]
    at hcore
  have hfirstRaw:=run_lensPhase_to_right (discardCoreRenaming .work1)
    FullInterpreterState.moveLens discardProgram .done (by rfl)
    (Sum.inl DiscardLabel.loop) (divideCleanupFinalProgram returnLabel right)
    (discard_correct ((fixedBits (w + 1) d).map SparseSymbol.bit)) rfl
    coreState (divideCoreResultStacks w d (a % d) (a / d) m base)
  simp only [List.length_map,fixedBits_length] at hfirstRaw
  have hbridge:phaseReturnCfg (discardCoreRenaming .work1)
      FullInterpreterState.moveLens
      (Sum.inl DiscardLabel.loop:DivideCleanupFinalLabel R)
      (discardCfg .done []) coreState
      (divideCoreResultStacks w d (a % d) (a / d) m base) =
    lensRenamedCfg (discardCoreRenaming .work2)
      FullInterpreterState.moveLens
      (discardCfg .loop ((fixedBits (w + 1) (a % d)).map SparseSymbol.bit))
      (FullInterpreterState.moveLens.put coreState default)
      (divideAfterFirstCleanupStacks w (a % d) (a / d) m base):=by
    simp [phaseReturnCfg,lensRenamedCfg,discardCoreRenaming,discardCfg,
      discardStacks,divideCoreResultStacks,divideAfterFirstCleanupStacks,
      renamedStacks]
    constructor
    · rfl
    · funext k
      cases k <;> rfl
  rw [hbridge] at hfirstRaw
  let firstState:=FullInterpreterState.moveLens.put coreState default
  have hsecondRaw:=run_lensPhase_to_right (discardCoreRenaming .work2)
    FullInterpreterState.moveLens discardProgram .done (by rfl)
    returnLabel right
    (discard_correct ((fixedBits (w + 1) (a % d)).map SparseSymbol.bit)) rfl
    firstState (divideAfterFirstCleanupStacks w (a % d) (a / d) m base)
  simp only [List.length_map,fixedBits_length] at hsecondRaw
  rw [divideCleanup_return_bridge returnLabel w (a % d) (a / d) m base firstState]
    at hsecondRaw
  have hcleanup:=chain_liftRightProgram (m:=w + 3) (n:=w + 3)
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl DiscardLabel.loop))
    (divideCleanupFinalProgram returnLabel right) hfirstRaw hsecondRaw
  have hcleanup':
      ((fun o => o.bind (TM2.step
        (divideCleanupTailProgram returnLabel right)))^[2 * w + 6])
        (some (lensRenamedCfg (discardCoreRenaming .work1)
          FullInterpreterState.moveLens
          (discardCfg .loop ((fixedBits (w + 1) d).map SparseSymbol.bit))
          coreState (divideCoreResultStacks w d (a % d) (a / d) m base))) =
      some (mapLabelCfg (fun l:DivideCleanupFinalLabel R => Sum.inr l)
        (mapLabelCfg (fun l:R => Sum.inr l)
          (cleanReturnCfg returnLabel
            (FullInterpreterState.moveLens.put firstState default)
            (operandBoundaryBase w (a / d) m base)))):=by
    simpa only [divideCleanupTailProgram,
      show w + 3 + (w + 3)=2 * w + 6 by omega] using hcleanup
  have hall:=chain_liftRightProgram
    (m:=divPositiveRunTime w + 1) (n:=2 * w + 6)
    (lensPhaseLeft preparedDivRenaming FullInterpreterState.divLens
      sparseDivCoreProgram .done (Sum.inl DiscardLabel.loop))
    (divideCleanupTailProgram returnLabel right) hcore hcleanup'
  refine ⟨FullInterpreterState.moveLens.put firstState default,
    FullInterpreterState.moveLens.get_put _ _,by rfl, ?_⟩
  have ht:divPositiveRunTime w + 2 * w + 7 =
      (divPositiveRunTime w + 1) + (2 * w + 6):=by omega
  rw [ht]
  simpa [fullDivideCleanProgram,coreState,firstState] using hall

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

theorem fixedBits_succ_of_lt (w n:Nat) (h:n < 2 ^ w):
    fixedBits (w + 1) n=fixedBits w n ++ [false]:=by
  apply bitsValue_injective_of_length
  · simp
  · rw [bitsValue_append_false,bitsValue_fixedBits_of_lt h]
    exact bitsValue_fixedBits_of_lt (lt_trans h (by
      rw [pow_succ]
      omega))

def divideDivisorReadyStacks (w a d:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w a).map SparseSymbol.bit
  | .work1 => (fixedBits (w + 1) d).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work0 | .work2 | .work3 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def divideDividendReadyStacks (w a d:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol
  | .work7 => (fixedBits w a).reverse.map SparseSymbol.bit
  | .work1 => (fixedBits (w + 1) d).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .accumulator | .work0 | .work2 | .work3 | .work4 | .work5 | .work6 => []
  | k => base k

theorem dividePrepare_step {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a d:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    TM2.step (fullDivideProgram returnLabel right)
      (mapLabelCfg Sum.inl
        (cleanReturnCfg DividePrepareLabel.pushExtension state
          (operandResultBase w a d m base))) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg
        (symbolMoveCoreRenaming .work0 .work1 (by decide))
        FullInterpreterState.moveLens
        (symbolMoveLocalCfg .loop
          (.bit false::(fixedBits w d).reverse.map SparseSymbol.bit) [])
        (dividePrepareReset state) (operandResultBase w a d m base))):=by
  simp [fullDivideProgram,dividePrepareProgram,cleanReturnCfg,mapLabelCfg,
    liftRightProgram,TM2.step,lensRenamedCfg,dividePrepareReset]
  constructor
  · rfl
  · constructor
    · rfl
    · funext k
      cases k <;> simp [operandResultBase,renamedStacks,
        symbolMoveCoreRenaming,symbolMoveCoreDecode,symbolMoveLocalCfg,
        symbolMoveStacks]

theorem divideDivisor_bridge {N:Nat} {R:Type}
    (w a d:Nat) (hd:d < 2 ^ w) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    phaseReturnCfg (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl SymbolMoveLabel.loop:DivideDividendTailLabel R)
      (symbolMoveLocalCfg .done []
        ((.bit false::(fixedBits w d).reverse.map SparseSymbol.bit).reverse))
      state (operandResultBase w a d m base) =
    lensRenamedCfg
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((fixedBits w a).map SparseSymbol.bit) [])
      (FullInterpreterState.moveLens.put state default)
      (divideDivisorReadyStacks w a d m base):=by
  simp [phaseReturnCfg,lensRenamedCfg,symbolMoveCoreRenaming,
    symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks,
    operandResultBase,divideDivisorReadyStacks,renamedStacks,
    fixedBits_succ_of_lt w d hd,List.map_append,List.map_reverse]
  constructor
  · rfl
  · funext k
    cases k <;> simp [operandResultBase,divideDivisorReadyStacks,
      renamedStacks,symbolMoveCoreRenaming,symbolMoveCoreDecode,
      symbolMoveLocalCfg,symbolMoveStacks,fixedBits_succ_of_lt w d hd,
      List.map_append,List.map_reverse]

theorem divideDividend_bridge {N:Nat} {R:Type}
    (w a d:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N)
    (hzero:FullInterpreterState.zeroLens.get state=default):
    phaseReturnCfg
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl ZeroWordLabel.fill:DivideZeroTailLabel R)
      (symbolMoveLocalCfg .done []
        ((fixedBits w a).map SparseSymbol.bit).reverse)
      state (divideDivisorReadyStacks w a d m base) =
    lensRenamedCfg divideZeroRenaming FullInterpreterState.zeroLens
      (zeroWordTypedCfg .fill
        ((fixedBits (w + 1) d).map SparseSymbol.bit) [] [])
      (FullInterpreterState.moveLens.put state default)
      (divideDividendReadyStacks w a d m base):=by
  simp [phaseReturnCfg,lensRenamedCfg,symbolMoveCoreRenaming,
    symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks,
    divideDivisorReadyStacks,divideDividendReadyStacks,
    divideZeroRenaming,divideZeroDecode,zeroWordTypedCfg,
    zeroWordStacks,renamedStacks]
  constructor
  · symm
    have hz:FullInterpreterState.zeroLens.get
        (FullInterpreterState.moveLens.put state default)=default:=by
      simpa using! hzero
    rw [← hz,FullInterpreterState.zeroLens.put_get]
  · funext k
    cases k <;> simp [divideDivisorReadyStacks,divideDividendReadyStacks,
      divideZeroRenaming,divideZeroDecode,zeroWordTypedCfg,
      zeroWordStacks,renamedStacks,symbolMoveCoreRenaming,
      symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks,
      List.map_reverse]

theorem divideZero_bridge {N:Nat} {R:Type}
    (w a d:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N)
    (hdiv:FullInterpreterState.divLens.get state=default):
    phaseReturnCfg divideZeroRenaming FullInterpreterState.zeroLens
      (Sum.inl DivLabel.inspectDivisor:FullDivideCleanLabel R)
      (zeroWordTypedCfg .done
        ((fixedBits (w + 1) d).map SparseSymbol.bit) []
        (List.replicate (w + 1) (.bit false)))
      state (divideDividendReadyStacks w a d m base) =
    lensRenamedCfg preparedDivRenaming FullInterpreterState.divLens
      (sparseDivLocalInitialCfg (fixedBits w a).reverse
        (fixedBits (w + 1) d) (fixedBits (w + 1) 0))
      (FullInterpreterState.zeroLens.put state default)
      (preparedDivideStacks w a d m base):=by
  simp [phaseReturnCfg,lensRenamedCfg,divideZeroRenaming,
    divideZeroDecode,zeroWordTypedCfg,zeroWordStacks,
    divideDividendReadyStacks,preparedDivideStacks,
    preparedDivRenaming,preparedDivDecode,sparseDivLocalInitialCfg,
    divStacks,mapAlphabetStacks,sparseBitEncode,renamedStacks]
  constructor
  · symm
    have hd:FullInterpreterState.divLens.get
        (FullInterpreterState.zeroLens.put state default)=default:=by
      simpa using! hdiv
    rw [← hd,FullInterpreterState.divLens.put_get]
  · funext k
    cases k <;> simp [divideZeroRenaming,divideZeroDecode,
      zeroWordTypedCfg,zeroWordStacks,divideDividendReadyStacks,
      preparedDivideStacks,preparedDivRenaming,preparedDivDecode,
      sparseDivLocalInitialCfg,divStacks,mapAlphabetStacks,
      sparseBitEncode,renamedStacks]

theorem dividePrepare_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a d:Nat) (hd:d < 2 ^ w) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    ∃ preparedState,
      FullInterpreterState.moveLens.get preparedState=default∧
      FullInterpreterState.literalLens.get preparedState =
        FullInterpreterState.literalLens.get state∧
      ((fun o => o.bind (TM2.step
        (fullDivideProgram returnLabel right)))^[4 * w + 11])
        (some (mapLabelCfg Sum.inl
          (cleanReturnCfg DividePrepareLabel.pushExtension state
            (operandResultBase w a d m base)))) =
      (some <| mapLabelCfg (fun l:DivideDivisorTailLabel R => Sum.inr l) <|
        mapLabelCfg (fun l:DivideDividendTailLabel R => Sum.inr l) <|
          mapLabelCfg (fun l:DivideZeroTailLabel R => Sum.inr l) <|
            mapLabelCfg (fun l:FullDivideCleanLabel R => Sum.inr l) <|
              lensRenamedCfg (Λx:=DivideCleanupTailLabel R)
                preparedDivRenaming FullInterpreterState.divLens
                (sparseDivLocalInitialCfg (fixedBits w a).reverse
                  (fixedBits (w + 1) d) (fixedBits (w + 1) 0))
                preparedState (preparedDivideStacks w a d m base)):=by
  have hpush:=dividePrepare_step returnLabel right w a d m base state
  have hpush':
      ((fun x => x.bind (TM2.step
        (fullDivideProgram returnLabel right)))^[1])
        (some (mapLabelCfg Sum.inl
          (cleanReturnCfg DividePrepareLabel.pushExtension state
            (operandResultBase w a d m base)))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .work1 (by decide))
          FullInterpreterState.moveLens
          (symbolMoveLocalCfg .loop
            (.bit false::(fixedBits w d).reverse.map SparseSymbol.bit) [])
          (dividePrepareReset state) (operandResultBase w a d m base))):=by
    simpa using hpush
  have hdivisor:=run_lensPhase_to_right
    (symbolMoveCoreRenaming .work0 .work1 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop)
    (divideDividendTailProgram returnLabel right)
    (symbolMoveLocal_correct
      (.bit false::(fixedBits w d).reverse.map SparseSymbol.bit) []) rfl
    (dividePrepareReset state) (operandResultBase w a d m base)
  simp only [List.length_cons,List.length_map,List.length_reverse,
    fixedBits_length,List.append_nil] at hdivisor
  rw [divideDivisor_bridge (R:=R) w a d hd m base
    (dividePrepareReset state)] at hdivisor
  let divisorState:=FullInterpreterState.moveLens.put
    (dividePrepareReset state) default
  have hdividend:=run_lensPhase_to_right
    (symbolMoveCoreRenaming .accumulator .work7 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl ZeroWordLabel.fill) (divideZeroTailProgram returnLabel right)
    (symbolMoveLocal_correct ((fixedBits w a).map SparseSymbol.bit) []) rfl
    divisorState (divideDivisorReadyStacks w a d m base)
  simp only [List.length_map,fixedBits_length,List.append_nil] at hdividend
  rw [divideDividend_bridge (R:=R) w a d m base divisorState
    (by rfl)] at hdividend
  let dividendState:=FullInterpreterState.moveLens.put divisorState default
  have hzero:=run_lensPhase_to_right divideZeroRenaming
    FullInterpreterState.zeroLens zeroWordProgram .done (by rfl)
    (Sum.inl DivLabel.inspectDivisor) (fullDivideCleanProgram returnLabel right)
    (zeroWordTyped_correct
      ((fixedBits (w + 1) d).map SparseSymbol.bit) []) rfl
    dividendState (divideDividendReadyStacks w a d m base)
  simp only [List.length_map,fixedBits_length,List.append_nil] at hzero
  rw [divideZero_bridge (R:=R) w a d m base dividendState
    (by rfl)] at hzero
  have h23:=chain_liftRightProgram (m:=w + 2) (n:=2 * w + 5)
    (lensPhaseLeft
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl ZeroWordLabel.fill))
    (divideZeroTailProgram returnLabel right) hdividend hzero
  have h123:=chain_liftRightProgram
    (m:=w + 3) (n:=(w + 2) + (2 * w + 5))
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (divideDividendTailProgram returnLabel right) hdivisor h23
  have hrest:=transport_iterate_liftRightProgram dividePrepareProgram
    (divideDivisorTailProgram returnLabel right) h123
  have hall:=chain_loadInstruction_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (FullDivideLabel R) (FullInterpreterState N)) =>
      x.bind (TM2.step (fullDivideProgram returnLabel right))) hpush' hrest
  refine ⟨FullInterpreterState.zeroLens.put dividendState default,by rfl,
    by rfl, ?_⟩
  have ht:4 * w + 11 =
      1 + ((w + 3) + ((w + 2) + (2 * w + 5))):=by omega
  rw [ht]
  simpa [fullDivideProgram,divisorState,dividendState] using hall

def embedFullDivideReturnCfg {N:Nat} {R:Type}
    (c:TM2.Cfg (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)):
    TM2.Cfg (fun _:CoreStack => SparseSymbol) (FullDivideLabel R)
      (FullInterpreterState N):=
  mapLabelCfg (fun l:DivideDivisorTailLabel R => Sum.inr l) <|
    mapLabelCfg (fun l:DivideDividendTailLabel R => Sum.inr l) <|
      mapLabelCfg (fun l:DivideZeroTailLabel R => Sum.inr l) <|
        mapLabelCfg (fun l:FullDivideCleanLabel R => Sum.inr l) <|
          mapLabelCfg (fun l:DivideCleanupTailLabel R => Sum.inr l) <|
            mapLabelCfg (fun l:DivideCleanupFinalLabel R => Sum.inr l) <|
              mapLabelCfg (fun l:R => Sum.inr l) c

theorem fullDivide_zero_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    ∃ finalState,
      FullInterpreterState.moveLens.get finalState=default∧
      FullInterpreterState.literalLens.get finalState =
        FullInterpreterState.literalLens.get state∧
      ((fun o => o.bind (TM2.step
        (fullDivideProgram returnLabel right)))^[divZeroRunTime w + 6 * w + 18])
        (some (mapLabelCfg Sum.inl
          (cleanReturnCfg DividePrepareLabel.pushExtension state
            (operandResultBase w a 0 m base)))) =
      some (embedFullDivideReturnCfg
        (cleanReturnCfg returnLabel finalState
          (operandBoundaryBase w 0 m base))):=by
  have hzeroLt:0 < 2 ^ w:=by positivity
  rcases dividePrepare_correct returnLabel right w a 0 hzeroLt m base state with
    ⟨preparedState,hmove,hprepareLiteral,hprepare⟩
  rcases fullDivideClean_zero_correct returnLabel right w a m base
      preparedState hmove with
    ⟨finalState,hfinalMove,hfinalLiteral,hclean⟩
  have hzeroLift:=transport_iterate_liftRightProgram
    (lensPhaseLeft divideZeroRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done (Sum.inl DivLabel.inspectDivisor))
    (fullDivideCleanProgram returnLabel right) hclean
  have hdividendLift:=transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl ZeroWordLabel.fill))
    (divideZeroTailProgram returnLabel right) hzeroLift
  have hdivisorLift:=transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (divideDividendTailProgram returnLabel right) hdividendLift
  have hcleanLift:=transport_iterate_liftRightProgram dividePrepareProgram
    (divideDivisorTailProgram returnLabel right) hdivisorLift
  have hall:=chain_loadInstruction_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (FullDivideLabel R) (FullInterpreterState N)) =>
      x.bind (TM2.step (fullDivideProgram returnLabel right)))
    hprepare hcleanLift
  refine ⟨finalState,hfinalMove,hfinalLiteral.trans hprepareLiteral, ?_⟩
  have ht:divZeroRunTime w + 6 * w + 18 =
      (4 * w + 11) + (divZeroRunTime w + 2 * w + 7):=by omega
  rw [ht]
  simpa [fullDivideProgram,divideDivisorTailProgram,
    divideDividendTailProgram,divideZeroTailProgram,
    embedFullDivideReturnCfg] using hall

theorem fullDivide_positive_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a d:Nat) (ha:a < 2 ^ w) (hd0:0 < d) (hd:d < 2 ^ w)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ finalState,
      FullInterpreterState.moveLens.get finalState=default∧
      FullInterpreterState.literalLens.get finalState =
        FullInterpreterState.literalLens.get state∧
      ((fun o => o.bind (TM2.step
        (fullDivideProgram returnLabel right)))^[
          divPositiveRunTime w + 6 * w + 18])
        (some (mapLabelCfg Sum.inl
          (cleanReturnCfg DividePrepareLabel.pushExtension state
            (operandResultBase w a d m base)))) =
      some (embedFullDivideReturnCfg
        (cleanReturnCfg returnLabel finalState
          (operandBoundaryBase w (a / d) m base))):=by
  rcases dividePrepare_correct returnLabel right w a d hd m base state with
    ⟨preparedState,hmove,hprepareLiteral,hprepare⟩
  rcases fullDivideClean_positive_correct returnLabel right w a d ha hd0 hd
      m base preparedState hmove with
    ⟨finalState,hfinalMove,hfinalLiteral,hclean⟩
  have hzeroLift:=transport_iterate_liftRightProgram
    (lensPhaseLeft divideZeroRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done (Sum.inl DivLabel.inspectDivisor))
    (fullDivideCleanProgram returnLabel right) hclean
  have hdividendLift:=transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl ZeroWordLabel.fill))
    (divideZeroTailProgram returnLabel right) hzeroLift
  have hdivisorLift:=transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (divideDividendTailProgram returnLabel right) hdividendLift
  have hcleanLift:=transport_iterate_liftRightProgram dividePrepareProgram
    (divideDivisorTailProgram returnLabel right) hdivisorLift
  have hall:=chain_loadInstruction_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (FullDivideLabel R) (FullInterpreterState N)) =>
      x.bind (TM2.step (fullDivideProgram returnLabel right)))
    hprepare hcleanLift
  refine ⟨finalState,hfinalMove,hfinalLiteral.trans hprepareLiteral, ?_⟩
  have ht:divPositiveRunTime w + 6 * w + 18 =
      (4 * w + 11) + (divPositiveRunTime w + 2 * w + 7):=by omega
  rw [ht]
  simpa [fullDivideProgram,divideDivisorTailProgram,
    divideDividendTailProgram,divideZeroTailProgram,
    embedFullDivideReturnCfg] using hall

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

def conditionalZeroCfg {N:Nat} (label:ConditionalZeroLabel)
    (state:FullInterpreterState N) (source target:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol) ConditionalZeroLabel
      (FullInterpreterState N) where
  l:=some label
  var:=state
  stk:=fun
    | .accumulator => source
    | .work0 => target
    | k => base k

@[simp] theorem operandLiteralOversized_move_put {N:Nat} (o:Op)
    (state:FullInterpreterState N) (move:SymbolMoveControl):
    operandLiteralOversized o (FullInterpreterState.moveLens.put state move) =
      operandLiteralOversized o state:=by
  cases o <;> rfl

@[simp] theorem conditionalZero_step_nil {N:Nat} (o:Op)
    (state:FullInterpreterState N) (target:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol):
    TM2.step (conditionalZeroProgram N o)
      (conditionalZeroCfg .rewrite state [] target base) =
    some (conditionalZeroCfg .done
      (FullInterpreterState.moveLens.put state default) [] target base):=by
  simp [conditionalZeroProgram,conditionalZeroCfg,TM2.step,
    FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]

@[simp] theorem conditionalZero_step_cons {N:Nat} (o:Op)
    (state:FullInterpreterState N) (x:SparseSymbol)
    (xs target:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol):
    TM2.step (conditionalZeroProgram N o)
      (conditionalZeroCfg .rewrite state (x::xs) target base) =
    some (conditionalZeroCfg .rewrite
      (FullInterpreterState.moveLens.put state default) xs
      ((if operandLiteralOversized o state then .bit false else x)::target)
      base):=by
  simp [conditionalZeroProgram,conditionalZeroCfg,TM2.step,
    Function.update,FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  congr 2
  funext k
  cases k <;> rfl

def conditionallyRewritten (zero:Bool) (source:List SparseSymbol):
    List SparseSymbol:=
  if zero then List.replicate source.length (.bit false) else source.reverse

theorem conditionalZero_iterate {N:Nat} (o:Op)
    (state:FullInterpreterState N) (source target:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol)
    (hmove:FullInterpreterState.moveLens.get state=default):
    ((fun x => x.bind (TM2.step (conditionalZeroProgram N o)))^[source.length])
      (some (conditionalZeroCfg .rewrite state source target base)) =
    some (conditionalZeroCfg .rewrite
      (FullInterpreterState.moveLens.put state default) []
      (conditionallyRewritten (operandLiteralOversized o state) source ++ target)
      base):=by
  induction source generalizing state target base with
  | nil =>
      have hs:FullInterpreterState.moveLens.put state default=state:=by
        rw [← hmove,FullInterpreterState.moveLens.put_get]
      simp [conditionallyRewritten,hs]
  | cons x xs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,conditionalZero_step_cons]
      rw [ih (FullInterpreterState.moveLens.put state default)
        ((if operandLiteralOversized o state then .bit false else x)::target)
        base (FullInterpreterState.moveLens.get_put _ _)]
      by_cases h:operandLiteralOversized o state <;>
        simp [conditionallyRewritten,h,List.replicate_succ,
          List.reverse_cons,List.append_assoc,
          FullInterpreterState.moveLens.put_put,
          replicate_append_same_cons]

theorem conditionalZero_correct {N:Nat} (o:Op)
    (state:FullInterpreterState N) (source:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol)
    (hmove:FullInterpreterState.moveLens.get state=default):
    ((fun x => x.bind (TM2.step (conditionalZeroProgram N o)))^[source.length + 1])
      (some (conditionalZeroCfg .rewrite state source [] base)) =
    some (conditionalZeroCfg .done
      (FullInterpreterState.moveLens.put state default) []
      (conditionallyRewritten (operandLiteralOversized o state) source) base):=by
  rw [Nat.add_comm,Function.iterate_add_apply,
    conditionalZero_iterate o state source [] base hmove]
  simp only [List.append_nil,Function.iterate_one,Option.bind_some,
    conditionalZero_step_nil,FullInterpreterState.moveLens.put_put]

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

def conditionalZeroIntermediateStacks (w value:Nat) (zero:Bool)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    CoreStack -> List SparseSymbol
  | .work0 => conditionallyRewritten zero
      ((fixedBits w value).map SparseSymbol.bit)
  | .accumulator => []
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work1 | .work2 | .work3 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

theorem conditionalZero_head_bridge {N:Nat} {R:Type}
    (o:Op) (w value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    phaseReturnCfg coreIdentityRenaming (fullStateIdentityLens N)
      (Sum.inl SymbolMoveLabel.loop:ConditionalZeroTailLabel R)
      (conditionalZeroCfg .done
        (FullInterpreterState.moveLens.put state default) []
        (conditionallyRewritten (operandLiteralOversized o state)
          ((fixedBits w value).map SparseSymbol.bit))
        (operandBoundaryBase w value m base))
      state (operandBoundaryBase w value m base) =
    lensRenamedCfg
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        (conditionallyRewritten (operandLiteralOversized o state)
          ((fixedBits w value).map SparseSymbol.bit)) [])
      (FullInterpreterState.moveLens.put state default)
      (conditionalZeroIntermediateStacks w value
        (operandLiteralOversized o state) m base):=by
  simp [phaseReturnCfg,lensRenamedCfg,fullStateIdentityLens,
    conditionalZeroCfg,operandBoundaryBase,conditionalZeroIntermediateStacks,
    renamedStacks_coreIdentity,symbolMoveCoreRenaming,
    symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks,renamedStacks]
  constructor
  · rfl
  · funext k
    cases k <;> simp [conditionalZeroIntermediateStacks,
      operandBoundaryBase,symbolMoveCoreRenaming,symbolMoveCoreDecode,
      symbolMoveLocalCfg,symbolMoveStacks,renamedStacks]

theorem conditionallyRewritten_reverse (w value:Nat) (zero:Bool):
    (conditionallyRewritten zero ((fixedBits w value).map SparseSymbol.bit)).reverse =
      (fixedBits w (if zero then 0 else value)).map SparseSymbol.bit:=by
  cases zero
  · simp [conditionallyRewritten,List.map_reverse]
  · simp [conditionallyRewritten]

theorem conditionalZero_return_bridge {N:Nat} {R:Type}
    (returnLabel:R) (w value:Nat) (zero:Bool) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens returnLabel
      (symbolMoveLocalCfg .done []
        (conditionallyRewritten zero
          ((fixedBits w value).map SparseSymbol.bit)).reverse)
      state (conditionalZeroIntermediateStacks w value zero m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (operandBoundaryBase w (if zero then 0 else value) m base):=by
  simp [phaseReturnCfg,cleanReturnCfg,lensRenamedCfg,
    symbolMoveCoreRenaming,symbolMoveCoreDecode,symbolMoveLocalCfg,
    symbolMoveStacks,conditionalZeroIntermediateStacks,
    operandBoundaryBase,renamedStacks,conditionallyRewritten_reverse]
  funext k
  cases k <;> simp [conditionalZeroIntermediateStacks,operandBoundaryBase,
    renamedStacks,symbolMoveCoreRenaming,symbolMoveCoreDecode,
    symbolMoveLocalCfg,symbolMoveStacks,conditionallyRewritten_reverse]

theorem conditionalZeroPhase_correct {N:Nat} {R:Type}
    (o:Op) (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N)
    (hmove:FullInterpreterState.moveLens.get state=default):
    ∃ finalState,
      ((fun x => x.bind (TM2.step
        (conditionalZeroPhaseProgram o returnLabel right)))^[2 * w + 4])
        (some (lensRenamedCfg coreIdentityRenaming (fullStateIdentityLens N)
          (conditionalZeroCfg .rewrite state
            ((fixedBits w value).map SparseSymbol.bit) []
            (operandBoundaryBase w value m base))
          state (operandBoundaryBase w value m base))) =
      some (mapLabelCfg (fun l:ConditionalZeroTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l:R => Sum.inr l)
          (cleanReturnCfg returnLabel finalState
            (operandBoundaryBase w
              (if operandLiteralOversized o state then 0 else value) m base)))):=by
  have hhead:=run_lensPhase_to_right coreIdentityRenaming
    (fullStateIdentityLens N) (conditionalZeroProgram N o) .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop) (conditionalZeroTailProgram returnLabel right)
    (conditionalZero_correct o state
      ((fixedBits w value).map SparseSymbol.bit)
      (operandBoundaryBase w value m base) hmove) rfl
    state (operandBoundaryBase w value m base)
  simp only [List.length_map,fixedBits_length] at hhead
  rw [conditionalZero_head_bridge (R:=R) o w value m base state] at hhead
  let headState:=FullInterpreterState.moveLens.put state default
  let zero:=operandLiteralOversized o state
  have htail:=run_lensPhase_to_right
    (symbolMoveCoreRenaming .work0 .accumulator (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    returnLabel right
    (symbolMoveLocal_correct
      (conditionallyRewritten zero ((fixedBits w value).map SparseSymbol.bit)) [])
    rfl headState (conditionalZeroIntermediateStacks w value zero m base)
  have hrewriteLength:
      (conditionallyRewritten zero
        ((fixedBits w value).map SparseSymbol.bit)).length=w:=by
    cases zero <;> simp [conditionallyRewritten]
  simp only [hrewriteLength,List.append_nil] at htail
  rw [conditionalZero_return_bridge returnLabel w value zero m base headState]
    at htail
  have hall:=chain_liftRightProgram (m:=w + 2) (n:=w + 2)
    (lensPhaseLeft coreIdentityRenaming (fullStateIdentityLens N)
    (conditionalZeroProgram N o) .done (Sum.inl SymbolMoveLabel.loop))
    (conditionalZeroTailProgram returnLabel right) hhead htail
  rw [show 2 * w + 4=(w + 2) + (w + 2) by omega]
  refine ⟨FullInterpreterState.moveLens.put headState default, ?_⟩
  simpa [conditionalZeroPhaseProgram,headState,zero] using hall

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

@[simp] theorem BoundedOp.operandArgument_toOp {N:Nat} (o:BoundedOp N):
    operandArgument o.toOp <= N:=by
  cases o <;> simp [BoundedOp.toOp,operandArgument] <;> omega

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

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

theorem dividePost_start_bridge {N:Nat} {R:Type}
    (w value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    cleanReturnCfg
        (Sum.inl ConditionalZeroLabel.rewrite:ConditionalZeroPhaseLabel R)
        state (operandBoundaryBase w value m base) =
      lensRenamedCfg coreIdentityRenaming (fullStateIdentityLens N)
        (conditionalZeroCfg .rewrite state
          ((fixedBits w value).map SparseSymbol.bit) []
          (operandBoundaryBase w value m base))
        state (operandBoundaryBase w value m base):=by
  simp [cleanReturnCfg,lensRenamedCfg,fullStateIdentityLens,
    conditionalZeroCfg,operandBoundaryBase,renamedStacks_coreIdentity]
  funext k
  cases k <;> rfl

theorem transport_iterate_fullDivide_right {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    {steps:Nat}
    {c d:TM2.Cfg (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)}
    (hrun:((fun x => x.bind (TM2.step right))^[steps])
      (some c)=some d):
    ((fun x => x.bind (TM2.step
      (fullDivideProgram returnLabel right)))^[steps])
      (some (embedFullDivideReturnCfg c)) =
    some (embedFullDivideReturnCfg d):=by
  have h1:=transport_iterate_liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work2)
      FullInterpreterState.moveLens discardProgram .done returnLabel)
    right hrun
  have h2:=transport_iterate_liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl DiscardLabel.loop))
    (divideCleanupFinalProgram returnLabel right) h1
  have h3:=transport_iterate_liftRightProgram
    (lensPhaseLeft preparedDivRenaming FullInterpreterState.divLens
      sparseDivCoreProgram .done (Sum.inl DiscardLabel.loop))
    (divideCleanupTailProgram returnLabel right) h2
  have h4:=transport_iterate_liftRightProgram
    (lensPhaseLeft divideZeroRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done (Sum.inl DivLabel.inspectDivisor))
    (fullDivideCleanProgram returnLabel right) h3
  have h5:=transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl ZeroWordLabel.fill))
    (divideZeroTailProgram returnLabel right) h4
  have h6:=transport_iterate_liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (divideDividendTailProgram returnLabel right) h5
  have h7:=transport_iterate_liftRightProgram dividePrepareProgram
    (divideDivisorTailProgram returnLabel right) h6
  simpa [fullDivideProgram,divideDivisorTailProgram,
    divideDividendTailProgram,divideZeroTailProgram,
    fullDivideCleanProgram,divideCleanupTailProgram,
    divideCleanupFinalProgram,embedFullDivideReturnCfg] using h7

theorem fullDividePost_zero_correct {N:Nat} {R:Type}
    (o:Op) (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    ∃ finalState,
      ((fun x => x.bind (TM2.step
        (fullDividePostProgram o returnLabel right)))^[
          divZeroRunTime w + 8 * w + 22])
        (some (mapLabelCfg Sum.inl
          (cleanReturnCfg DividePrepareLabel.pushExtension state
            (operandResultBase w a 0 m base)))) =
      some (embedFullDivideReturnCfg
        (mapLabelCfg (fun l:ConditionalZeroTailLabel R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w 0 m base))))):=by
  rcases fullDivide_zero_correct
      (Sum.inl ConditionalZeroLabel.rewrite:ConditionalZeroPhaseLabel R)
      (conditionalZeroPhaseProgram o returnLabel right)
      w a m base state with
    ⟨divideState,hmove,_,hdivide⟩
  rw [dividePost_start_bridge (R:=R) w 0 m base divideState] at hdivide
  rcases conditionalZeroPhase_correct o returnLabel right w 0 m base
      divideState hmove with ⟨finalState,hpost⟩
  have hpostLift:=transport_iterate_fullDivide_right
    (Sum.inl ConditionalZeroLabel.rewrite:ConditionalZeroPhaseLabel R)
    (conditionalZeroPhaseProgram o returnLabel right) hpost
  have hall:=chain_loadInstruction_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (FullDividePostLabel R) (FullInterpreterState N)) =>
      x.bind (TM2.step (fullDividePostProgram o returnLabel right)))
    hdivide hpostLift
  refine ⟨finalState, ?_⟩
  have ht:divZeroRunTime w + 8 * w + 22 =
      (divZeroRunTime w + 6 * w + 18) + (2 * w + 4):=by omega
  rw [ht]
  simpa [fullDividePostProgram] using hall

theorem fullDividePost_positive_correct {N:Nat} {R:Type}
    (o:Op) (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a d:Nat) (ha:a < 2 ^ w) (hd0:0 < d) (hd:d < 2 ^ w)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ finalState,
      ((fun x => x.bind (TM2.step
        (fullDividePostProgram o returnLabel right)))^[
          divPositiveRunTime w + 8 * w + 22])
        (some (mapLabelCfg Sum.inl
          (cleanReturnCfg DividePrepareLabel.pushExtension state
            (operandResultBase w a d m base)))) =
      some (embedFullDivideReturnCfg
        (mapLabelCfg (fun l:ConditionalZeroTailLabel R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w
                (if operandLiteralOversized o state then 0 else a / d)
                m base))))):=by
  rcases fullDivide_positive_correct
      (Sum.inl ConditionalZeroLabel.rewrite:ConditionalZeroPhaseLabel R)
      (conditionalZeroPhaseProgram o returnLabel right)
      w a d ha hd0 hd m base state with
    ⟨divideState,hmove,hliteral,hdivide⟩
  rw [dividePost_start_bridge (R:=R) w (a / d) m base divideState]
    at hdivide
  rcases conditionalZeroPhase_correct o returnLabel right w (a / d) m base
      divideState hmove with ⟨finalState,hpost⟩
  have hpostLift:=transport_iterate_fullDivide_right
    (Sum.inl ConditionalZeroLabel.rewrite:ConditionalZeroPhaseLabel R)
    (conditionalZeroPhaseProgram o returnLabel right) hpost
  have hall:=chain_loadInstruction_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (FullDividePostLabel R) (FullInterpreterState N)) =>
      x.bind (TM2.step (fullDividePostProgram o returnLabel right)))
    hdivide hpostLift
  refine ⟨finalState, ?_⟩
  have hover:operandLiteralOversized o divideState =
      operandLiteralOversized o state:=by
    cases o <;> simp [operandLiteralOversized,hliteral]
  have ht:divPositiveRunTime w + 8 * w + 22 =
      (divPositiveRunTime w + 6 * w + 18) + (2 * w + 4):=by omega
  rw [ht]
  simpa [fullDividePostProgram,hover] using hall

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

theorem divideInstructionTotal_finish {N:Nat} {R:Type}
    (o:Op) (hN:operandArgument o <= N)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a:Nat) (ha:a < 2 ^ w)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state operandState:FullInterpreterState N)
    (operandSteps:Nat) (operandBound:operandSteps <= operandEvalBound w m)
    (hoperand:
      ((fun x => x.bind (TM2.step
        (divideInstructionTotalProgram o returnLabel right)))^[operandSteps])
        (some (operandEvalStartCfg
          (R:=FullDividePostLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg Sum.inl
          (cleanReturnCfg DividePrepareLabel.pushExtension operandState
            (operandResultBase w a (operandWordValue w o m) m base)))))
    (hsemantic:
      (if operandLiteralOversized o operandState then 0
        else a / operandWordValue w o m)=a / sparseValue w o m):
    ∃ steps,steps <= divideInstructionTotalBound w m∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (divideInstructionTotalProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=FullDividePostLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (embedFullDivideReturnCfg
          (mapLabelCfg (fun l:ConditionalZeroTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l:R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w (a / sparseValue w o m) m base)))))):=by
  let d:=operandWordValue w o m
  have hd:d < 2 ^ w:=operandWordValue_lt w o m
  by_cases hd0:d=0
  · have hoperandZero:=hoperand
    rw [show operandWordValue w o m=d by rfl,hd0] at hoperandZero
    have hdivide:=fullDividePost_zero_correct o returnLabel right
      w a m base operandState
    have hlift:=transport_iterate_operand_right o
      (Sum.inl DividePrepareLabel.pushExtension)
      (fullDividePostProgram o returnLabel right) hdivide.choose_spec
    have hchain:=chain_loadInstruction_iterations
      (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
          (DivideInstructionTotalLabel o R) (FullInterpreterState N)) =>
        x.bind (TM2.step (divideInstructionTotalProgram o returnLabel right)))
      hoperandZero hlift
    refine ⟨operandSteps + (divZeroRunTime w + 8 * w + 22), ?_,
      hdivide.choose, ?_⟩
    · simp [divideInstructionTotalBound]
      have hz:=divZeroRunTime_le_bound w
      omega
    · have hresult:a / sparseValue w o m=0:=by
        have hs:=hsemantic
        simp [d,hd0] at hs
        exact hs.symm
      simpa [divideInstructionTotalProgram,hresult] using hchain
  · have hdPos:0 < d:=Nat.pos_of_ne_zero hd0
    rcases fullDividePost_positive_correct o returnLabel right
        w a d ha hdPos hd m base operandState with
      ⟨divideState,hdivide⟩
    have hlift:=transport_iterate_operand_right o
      (Sum.inl DividePrepareLabel.pushExtension)
      (fullDividePostProgram o returnLabel right) hdivide
    have hchain:=chain_loadInstruction_iterations
      (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
          (DivideInstructionTotalLabel o R) (FullInterpreterState N)) =>
        x.bind (TM2.step (divideInstructionTotalProgram o returnLabel right)))
      (by simpa [d] using hoperand) hlift
    refine ⟨operandSteps + (divPositiveRunTime w + 8 * w + 22), ?_,
      divideState, ?_⟩
    · simp [divideInstructionTotalBound]
      have hp:=divPositiveRunTime_le_bound w
      omega
    · simpa [divideInstructionTotalProgram,d,hsemantic] using hchain

theorem divideInstructionTotal_correct {N:Nat} {R:Type}
    (o:Op) (hN:operandArgument o <= N)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a:Nat) (ha:a < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ steps,steps <= divideInstructionTotalBound w m∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (divideInstructionTotalProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=FullDividePostLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (embedFullDivideReturnCfg
          (mapLabelCfg (fun l:ConditionalZeroTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l:R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w (a / sparseValue w o m) m base)))))):=by
  cases o with
  | mem address =>
      rcases operandEval_correct (.mem address) hN w a m hm
          (Sum.inl DividePrepareLabel.pushExtension)
          (fullDividePostProgram (.mem address) returnLabel right)
          state base with ⟨steps,hsteps,operandState,hoperand⟩
      apply divideInstructionTotal_finish (.mem address) hN returnLabel right
        w a ha m base state operandState steps hsteps
      · simpa [divideInstructionTotalProgram] using! hoperand
      · simp [operandLiteralOversized,operandWordValue,
          Nat.mod_eq_of_lt (sparseValue_mem_lt hm address)]
  | ind address =>
      rcases operandEval_correct (.ind address) hN w a m hm
          (Sum.inl DividePrepareLabel.pushExtension)
          (fullDividePostProgram (.ind address) returnLabel right)
          state base with ⟨steps,hsteps,operandState,hoperand⟩
      apply divideInstructionTotal_finish (.ind address) hN returnLabel right
        w a ha m base state operandState steps hsteps
      · simpa [divideInstructionTotalProgram] using! hoperand
      · simp [operandLiteralOversized,operandWordValue,
          Nat.mod_eq_of_lt (sparseValue_ind_lt hm address)]
  | lit n =>
      change n <= N at hN
      let operandState:=FullInterpreterState.literalLens.put state
        ⟨none, ⟨n / 2 ^ w,by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
      have hoperand:=literalOperand_correct n hN w a m
        (Sum.inl DividePrepareLabel.pushExtension)
        (fullDividePostProgram (.lit n) returnLabel right) state base
      have hbound:2 * w + 3 <= operandEvalBound w m:=by
        simp [operandEvalBound]
        omega
      apply divideInstructionTotal_finish (.lit n) hN returnLabel right
        w a ha m base state operandState (2 * w + 3) hbound
      · simpa [divideInstructionTotalProgram,operandEvalStartCfg,
          operandArgument,embedOperandReturnCfg,operandState] using! hoperand
      · by_cases hnlt:n < 2 ^ w
        · have hzero:n / 2 ^ w=0:=
            (literalWord_remaining_eq_zero_iff n w).2 hnlt
          have hover:operandLiteralOversized (.lit n) operandState=false:=by
            simp only [operandLiteralOversized]
            rw [show FullInterpreterState.literalLens.get operandState =
                ⟨none, ⟨n / 2 ^ w,by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩ by
              exact FullInterpreterState.literalLens.get_put _ _]
            simp [hzero]
          simp [hover,operandWordValue,sparseValue,Op.value,
            Nat.mod_eq_of_lt hnlt]
        · have hquot:n / 2 ^ w ≠ 0:=by
            intro hz
            exact hnlt ((literalWord_remaining_eq_zero_iff n w).1 hz)
          have han:a < n:=lt_of_lt_of_le ha (Nat.le_of_not_gt hnlt)
          have hover:operandLiteralOversized (.lit n) operandState=true:=by
            simp only [operandLiteralOversized]
            rw [show FullInterpreterState.literalLens.get operandState =
                ⟨none, ⟨n / 2 ^ w,by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩ by
              exact FullInterpreterState.literalLens.get_put _ _]
            simp [hquot]
          simp [hover,sparseValue,Op.value,Nat.div_eq_of_lt han]

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

theorem transport_finiteLocal_run {p:Program} {N n:Nat} {L:Type}
    [Fintype L] (encode:L -> FiniteInterpreterLabel p N)
    (next:BoundedPC p)
    (program:L -> TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (target:FiniteInterpreterLabel p N -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N))
    (htarget:∀ label,target (encode label) =
      wrapFiniteLocal encode next program (localCodeEquiv L label))
    {c d:TM2.Cfg (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N)}
    (hrun:((fun x => x.bind (TM2.step program))^[n]) (some c)=some d)
    (hd:d.l.isSome):
    ((fun x => x.bind (TM2.step target))^[n])
      (some (finiteEmbedCfg encode c))=some (finiteEmbedCfg encode d):=by
  apply iterate_mapLabelProgram_until_exit program target encode
  · intro label hn
    rw [htarget]
    exact wrapFiniteLocal_encode_nonhalt encode next program label hn
  · exact hrun
  · exact hd

theorem finite_step_local_exit {p:Program} {N:Nat} {L:Type}
    [Fintype L] (encode:L -> FiniteInterpreterLabel p N)
    (next:BoundedPC p)
    (program:L -> TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (target:FiniteInterpreterLabel p N -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N))
    (htarget:∀ label,target (encode label) =
      wrapFiniteLocal encode next program (localCodeEquiv L label))
    (label:L) (h:program label=.halt)
    (state:FullInterpreterState N) (tapes:CoreStack -> List SparseSymbol):
    TM2.step target (finiteInterpreterCfg (encode label) state tapes) =
      some (finiteInterpreterCfg (.fetch next) state tapes):=by
  change some (TM2.stepAux (target (encode label)) state tapes)=_
  rw [htarget]
  simp [wrapFiniteLocal,h,stmtIsHalt,finiteInterpreterCfg,TM2.step]

theorem transport_finiteLocal_run_to_fetch
    {p:Program} {N n:Nat} {L:Type} [Fintype L]
    (encode:L -> FiniteInterpreterLabel p N) (next:BoundedPC p)
    (program:L -> TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (target:FiniteInterpreterLabel p N -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N))
    (htarget:∀ label,target (encode label) =
      wrapFiniteLocal encode next program (localCodeEquiv L label))
    {c:TM2.Cfg (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N)}
    (finalLabel:L) (finalState:FullInterpreterState N)
    (finalTapes:CoreStack -> List SparseSymbol)
    (hrun:((fun x => x.bind (TM2.step program))^[n]) (some c) =
      some (⟨some finalLabel,finalState,finalTapes⟩:
        TM2.Cfg (fun _:CoreStack => SparseSymbol) L
          (FullInterpreterState N)))
    (hhalt:program finalLabel=.halt):
    ((fun x => x.bind (TM2.step target))^[n + 1])
      (some (finiteEmbedCfg encode c)) =
      some (finiteInterpreterCfg (.fetch next) finalState finalTapes):=by
  have htransport:=transport_finiteLocal_run encode next program target
    htarget hrun (by rfl)
  have hexit:=finite_step_local_exit encode next program target htarget
    finalLabel hhalt finalState finalTapes
  have htransport':
      ((fun x => x.bind (TM2.step target))^[n])
        (some (finiteEmbedCfg encode c)) =
      some (finiteInterpreterCfg (encode finalLabel) finalState finalTapes):=by
    simpa [finiteEmbedCfg,mapLabelCfg,finiteInterpreterCfg] using htransport
  have hexit':
      ((fun x => x.bind (TM2.step target))^[1])
        (some (finiteInterpreterCfg (encode finalLabel) finalState finalTapes)) =
      some (finiteInterpreterCfg (.fetch next) finalState finalTapes):=by
    simpa using hexit
  exact chain_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N)) =>
      x.bind (TM2.step target))
    htransport' hexit'

theorem cfg_eq_some_get {α K L σ:Type}
    (c:TM2.Cfg (fun _:K => α) L σ) (h:c.l.isSome):
    c=⟨some (c.l.get h),c.var,c.stk⟩:=by
  cases c with
  | mk label state tapes =>
      cases label <;> simp_all

theorem transport_finiteLocal_cfg_to_fetch
    {p:Program} {N n:Nat} {L:Type} [Fintype L]
    (encode:L -> FiniteInterpreterLabel p N) (next:BoundedPC p)
    (program:L -> TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (target:FiniteInterpreterLabel p N -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N))
    (htarget:∀ label,target (encode label) =
      wrapFiniteLocal encode next program (localCodeEquiv L label))
    {c d:TM2.Cfg (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N)}
    (hrun:((fun x => x.bind (TM2.step program))^[n]) (some c)=some d)
    (hd:d.l.isSome) (hhalt:program (d.l.get hd)=.halt):
    ((fun x => x.bind (TM2.step target))^[n + 1])
      (some (finiteEmbedCfg encode c)) =
      some (finiteInterpreterCfg (.fetch next) d.var d.stk):=by
  rw [cfg_eq_some_get d hd] at hrun
  exact transport_finiteLocal_run_to_fetch encode next program target htarget
    (d.l.get hd) d.var d.stk hrun hhalt

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

def ProgramPreservesDispatch {N:Nat} {I L:Type}
    (program:I -> TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N)):Prop:=
  ∀ label,PreservesDispatch (program label)

def StmtPreservesDispatch {N:Nat} {L:Type}:
    TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N)→ Prop
  | .push _ _ q => StmtPreservesDispatch q
  | .peek _ f q =>
      (∀ s a, (f s a).dispatch=s.dispatch)∧ StmtPreservesDispatch q
  | .pop _ f q =>
      (∀ s a, (f s a).dispatch=s.dispatch)∧ StmtPreservesDispatch q
  | .load f q =>
      (∀ s, (f s).dispatch=s.dispatch)∧ StmtPreservesDispatch q
  | .branch _ q₁ q₂ => StmtPreservesDispatch q₁∧ StmtPreservesDispatch q₂
  | .goto _ | .halt => True

theorem StmtPreservesDispatch.sound {N:Nat} {L:Type}
    {q:TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N)} (hq:StmtPreservesDispatch q):
    PreservesDispatch q:=by
  intro state tapes
  induction q generalizing state tapes with
  | push k f q ih =>
      simpa only [TM2.stepAux] using
        ih hq state (Function.update tapes k (f state::tapes k))
  | peek k f q ih =>
      exact (ih hq.2 (f state (tapes k).head?) tapes).trans (hq.1 state _)
  | pop k f q ih =>
      exact (ih hq.2 (f state (tapes k).head?)
        (Function.update tapes k (tapes k).tail)).trans (hq.1 state _)
  | load f q ih =>
      exact (ih hq.2 (f state) tapes).trans (hq.1 state)
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases h:f state <;> simp [TM2.stepAux,h]
      · exact ih₂ hq.2 state tapes
      · exact ih₁ hq.1 state tapes
  | goto f => rfl
  | halt => rfl

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

theorem PreservesDispatch.lensPhaseLeft
    {N:Nat} {K L R σ:Type} [DecidableEq K] [DecidableEq L]
    (stackMap:StackRenaming K CoreStack)
    (lens:StateLens σ (FullInterpreterState N))
    (hdisjoint:∀ s v, (lens.put s v).dispatch=s.dispatch)
    (program:L→ TM2.Stmt (fun _:K => SparseSymbol) L σ)
    (done:L) (entry:R) (label:L):
    PreservesDispatch (lensPhaseLeft stackMap lens program done entry label):=by
  unfold Lax759944Proofs.RamToTM.lensPhaseLeft
  split
  · intro state tapes
    rfl
  · exact PreservesDispatch.lensRenameStmt (X:=R)
      stackMap lens hdisjoint (program label)

theorem ProgramPreservesDispatch.lensPhaseLeft
    {N:Nat} {K L R σ:Type} [DecidableEq K] [DecidableEq L]
    (stackMap:StackRenaming K CoreStack)
    (lens:StateLens σ (FullInterpreterState N))
    (hdisjoint:∀ s v, (lens.put s v).dispatch=s.dispatch)
    (program:L→ TM2.Stmt (fun _:K => SparseSymbol) L σ)
    (done:L) (entry:R):
    ProgramPreservesDispatch
      (lensPhaseLeft stackMap lens program done entry):=by
  intro label
  exact PreservesDispatch.lensPhaseLeft stackMap lens hdisjoint
    program done entry label

theorem ProgramPreservesDispatch.liftRightProgram
    {N:Nat} {L R:Type}
    (left:L→ TM2.Stmt (fun _:CoreStack => SparseSymbol) (Sum L R)
      (FullInterpreterState N))
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (hleft:ProgramPreservesDispatch left)
    (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (liftRightProgram left right):=by
  intro label
  cases label with
  | inl label =>
      change PreservesDispatch (left label)
      exact hleft label
  | inr label =>
      exact PreservesDispatch.mapLabelStmt Sum.inr (hright label)

theorem ProgramPreservesDispatch.lensMultiPhaseLeft
    {N:Nat} {K L R σ:Type} [DecidableEq K]
    (stackMap:StackRenaming K CoreStack)
    (lens:StateLens σ (FullInterpreterState N))
    (hdisjoint:∀ s v, (lens.put s v).dispatch=s.dispatch)
    (program:L→ TM2.Stmt (fun _:K => SparseSymbol) L σ)
    (exit:L→ Option R)
    (onExit:L→ FullInterpreterState N→ FullInterpreterState N)
    (hexit:∀ label state, (onExit label state).dispatch=state.dispatch):
    ProgramPreservesDispatch
      (lensMultiPhaseLeft stackMap lens program exit onExit):=by
  intro label
  unfold Lax759944Proofs.RamToTM.lensMultiPhaseLeft
  cases h:exit label with
  | none =>
      exact PreservesDispatch.lensRenameStmt (X:=R)
        stackMap lens hdisjoint (program label)
  | some next =>
      intro state tapes
      simpa only [TM2.stepAux] using! hexit label state

theorem haltProgram_preservesDispatch {N:Nat} {L:Type}:
    ProgramPreservesDispatch
      (fun _:L => (.halt:TM2.Stmt (fun _:CoreStack => SparseSymbol) L
        (FullInterpreterState N))):=by
  intro label state tapes
  rfl

theorem unifiedLookupProgram_preservesDispatch {N:Nat} {R:Type}
    (right:UnifiedLookupTail R→ TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (UnifiedLookupTail R)
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (unifiedLookupProgram right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensMultiPhaseLeft lookupCoreRenaming
      FullInterpreterState.lookupLens (by intros; rfl)
      lookupScanProgram lookupExit lookupRecordOutcome (by intros; rfl)
  · exact hright

theorem lookupDecisionProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R):
    ProgramPreservesDispatch
      (lookupDecisionProgram (N:=N) returnLabel):=by
  intro label
  cases label
  intro state tapes
  cases h:state.lookupFound <;>
    simp [lookupDecisionProgram,TM2.stepAux,h]

theorem unifiedCleanFinishProgram_preservesDispatch
    {N:Nat} {R:Type} (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch
      (unifiedCleanFinishProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft zeroWordCoreRenaming
      FullInterpreterState.zeroLens (by intros; rfl)
      zeroWordProgram .done returnLabel
  · exact hright

theorem unifiedCleanLookupProgram_preservesDispatch
    {N:Nat} {R:Type} (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch
      (unifiedCleanLookupProgram returnLabel right):=by
  apply unifiedLookupProgram_preservesDispatch
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft
      (discardCoreRenaming .work1) FullInterpreterState.moveLens
      (by intros; rfl) discardProgram .done
      (Sum.inl LookupDecisionLabel.decide)
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact lookupDecisionProgram_preservesDispatch returnLabel
    · exact unifiedCleanFinishProgram_preservesDispatch returnLabel right hright

theorem lookupInitProgram_preservesDispatch {N:Nat} {R:Type}:
    ProgramPreservesDispatch (lookupInitProgram (N:=N) (R:=R)):=by
  intro label
  cases label
  intro state tapes
  simp [lookupInitProgram,FullInterpreterState.lookupLens,
    FullInterpreterState.dispatchLens,FullInterpreterState.macroLens,
    InterpreterMacroState.lookupLens,StateLens.comp,TM2.stepAux]

theorem directOperandProgram_preservesDispatch
    {N:Nat} {R:Type} (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (directOperandProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft literalQueryCoreRenaming
      FullInterpreterState.literalLens (by intros; rfl)
      (boundedLiteralWordProgram N) .done (Sum.inl LookupInitLabel.init)
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact lookupInitProgram_preservesDispatch
    · exact unifiedCleanLookupProgram_preservesDispatch returnLabel right hright

theorem queryTransferProgram_preservesDispatch
    {N:Nat} {R:Type} (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (queryTransferProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      FullInterpreterState.moveLens (by intros; rfl)
      symbolMoveCoreProgram .done (Sum.inl SymbolMoveLabel.loop)
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft
        (symbolMoveCoreRenaming .work2 .work1 (by decide))
        FullInterpreterState.moveLens (by intros; rfl)
        symbolMoveCoreProgram .done returnLabel
    · exact hright

theorem indirectOperandProgram_preservesDispatch
    {N:Nat} {R:Type} (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (indirectOperandProgram returnLabel right):=by
  apply directOperandProgram_preservesDispatch
  apply queryTransferProgram_preservesDispatch
  apply ProgramPreservesDispatch.liftRightProgram
  · exact lookupInitProgram_preservesDispatch
  · exact unifiedCleanLookupProgram_preservesDispatch returnLabel right hright

theorem literalOperandProgram_preservesDispatch
    {N:Nat} {R:Type} (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (literalOperandProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft literalWordCoreRenaming
      FullInterpreterState.literalLens (by intros; rfl)
      (boundedLiteralWordProgram N) .done returnLabel
  · exact hright

theorem operandEvalProgram_preservesDispatch
    {N:Nat} {R:Type} (o:Op) (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (operandEvalProgram o returnLabel right):=by
  cases o with
  | lit n => exact literalOperandProgram_preservesDispatch returnLabel right hright
  | mem a => exact directOperandProgram_preservesDispatch returnLabel right hright
  | ind a => exact indirectOperandProgram_preservesDispatch returnLabel right hright

theorem fullDivideCleanProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R) (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (fullDivideCleanProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft preparedDivRenaming
      FullInterpreterState.divLens (by intros; rfl)
      sparseDivCoreProgram .done (Sum.inl DiscardLabel.loop)
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft (discardCoreRenaming .work1)
        FullInterpreterState.moveLens (by intros; rfl)
        discardProgram .done (Sum.inl DiscardLabel.loop)
    · apply ProgramPreservesDispatch.liftRightProgram
      · exact ProgramPreservesDispatch.lensPhaseLeft (discardCoreRenaming .work2)
          FullInterpreterState.moveLens (by intros; rfl)
          discardProgram .done returnLabel
      · exact hright

theorem fullDivideProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R) (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (fullDivideProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label; cases label; intro state tapes
    simp [dividePrepareProgram,dividePrepareReset,TM2.stepAux,
      FullInterpreterState.moveLens,FullInterpreterState.zeroLens,
      FullInterpreterState.divLens,FullInterpreterState.dispatchLens,
      FullInterpreterState.macroLens,InterpreterMacroState.moveLens,
      InterpreterMacroState.divLens,StateLens.comp]
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft
        (symbolMoveCoreRenaming .work0 .work1 (by decide))
        FullInterpreterState.moveLens (by intros; rfl)
        symbolMoveCoreProgram .done (Sum.inl SymbolMoveLabel.loop)
    · apply ProgramPreservesDispatch.liftRightProgram
      · exact ProgramPreservesDispatch.lensPhaseLeft
          (symbolMoveCoreRenaming .accumulator .work7 (by decide))
          FullInterpreterState.moveLens (by intros; rfl)
          symbolMoveCoreProgram .done (Sum.inl ZeroWordLabel.fill)
      · apply ProgramPreservesDispatch.liftRightProgram
        · exact ProgramPreservesDispatch.lensPhaseLeft divideZeroRenaming
            FullInterpreterState.zeroLens (by intros; rfl)
            zeroWordProgram .done (Sum.inl DivLabel.inspectDivisor)
        · exact fullDivideCleanProgram_preservesDispatch returnLabel right hright

theorem conditionalZeroPhaseProgram_preservesDispatch {N:Nat} {R:Type}
    (o:Op) (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (conditionalZeroPhaseProgram o returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label
    unfold lensPhaseLeft
    split
    · intro state tapes; rfl
    · apply StmtPreservesDispatch.sound
      cases label <;>
        simp [StmtPreservesDispatch,lensRenameStmt,conditionalZeroProgram,
          fullStateIdentityLens,coreIdentityRenaming,
          FullInterpreterState.moveLens,FullInterpreterState.dispatchLens,
          FullInterpreterState.macroLens,InterpreterMacroState.moveLens,
          StateLens.comp]
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft
        (symbolMoveCoreRenaming .work0 .accumulator (by decide))
        FullInterpreterState.moveLens (by intros; rfl)
        symbolMoveCoreProgram .done returnLabel
    · exact hright

theorem fullDividePostProgram_preservesDispatch {N:Nat} {R:Type}
    (o:Op) (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (fullDividePostProgram o returnLabel right):=by
  exact fullDivideProgram_preservesDispatch _ _
    (conditionalZeroPhaseProgram_preservesDispatch o returnLabel right hright)

theorem iterate_preservesDispatch {N n:Nat} {L:Type}
    (program:L -> TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (hprogram:ProgramPreservesDispatch program)
    (c d:TM2.Cfg (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (hrun:((fun x => x.bind (TM2.step program))^[n]) (some c)=some d):
    FullInterpreterState.dispatchLens.get d.var =
      FullInterpreterState.dispatchLens.get c.var:=by
  induction n generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply,Option.some.injEq] at hrun
      subst d
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun
      simp only [Option.bind_some] at hrun
      cases hs:TM2.step program c with
      | none =>
          rw [hs,iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          rw [hs] at hrun
          rcases c with ⟨label,state,tapes⟩
          cases label with
          | none => simp [TM2.step] at hs
          | some label =>
              simp only [TM2.step] at hs
              have hc':=Option.some.inj hs
              subst c'
              exact (ih _ hrun).trans (hprogram label state tapes)

theorem divideInstructionProgram_preservesDispatch {N:Nat} {R:Type}
    (o:Op) (returnLabel:R):
    ProgramPreservesDispatch
      (divideInstructionTotalProgram (N:=N) o returnLabel
        (fun _ => .halt)):=by
  exact operandEvalProgram_preservesDispatch o _ _
    (fullDividePostProgram_preservesDispatch o returnLabel _
      haltProgram_preservesDispatch)

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

set_option maxHeartbeats 5000000 in
theorem finite_div_to_fetch {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (pc:BoundedPC p)
    (o:BoundedOp N) (w:Nat) (s:SparseState) (hacc:s.acc < 2 ^ w)
    (hm:s.mem.Normalized w) (state:FullInterpreterState N):
    ∃ steps,steps <= divideInstructionTotalBound w s.mem + 1∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeDivLabel pc o)
          (operandEvalStartCfg
            (R:=FullDividePostLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc:=s.acc / sparseValue w o.toOp s.mem})):=by
  let haltRight:BoundedPC p -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N):=fun _ => .halt
  rcases divideInstructionTotal_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc hacc s.mem hm
      (coreStacks w s) state with
    ⟨steps,hsteps,finalState,hrun⟩
  let finalCfg:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (DivideInstructionTotalLabel o.toOp (BoundedPC p))
      (FullInterpreterState N):=
    embedOperandReturnCfg o.toOp
      (embedFullDivideReturnCfg
        (mapLabelCfg (fun l:ConditionalZeroTailLabel (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l:BoundedPC p => Sum.inr l)
            (cleanReturnCfg (nextPC p pc) finalState
              (operandBoundaryBase w (s.acc / sparseValue w o.toOp s.mem)
                s.mem (coreStacks w s))))))
  have hfinal:finalCfg.l.isSome:=by cases o <;> rfl
  have hhalt:divideInstructionTotalProgram o.toOp (nextPC p pc) haltRight
      (finalCfg.l.get hfinal)=.halt:=by
    cases o <;> simp only [queryTransferTailProgram, queryTransferProgram, unifiedLookupProgram, unifiedCleanTailProgram, unifiedCleanAfterProgram, unifiedCleanFinishProgram, unifiedCleanLookupProgram, mapLabelStmt, Option.map_some, Option.get_some, BoundedOp.toOp, finalCfg, divideInstructionTotalProgram, operandEvalProgram, embedOperandReturnCfg, embedFullDivideReturnCfg, mapLabelCfg, cleanReturnCfg, literalOperandProgram, directOperandProgram, directOperandTailProgram, embedDirectReturnCfg, indirectOperandProgram, indirectTransferProgram, embedIndirectReturnCfg, embedIndirectTransferReturnCfg, embedDirectTailReturnCfg, fullDividePostProgram, fullDivideProgram, divideDivisorTailProgram, divideDividendTailProgram, divideZeroTailProgram, fullDivideCleanProgram, divideCleanupTailProgram, divideCleanupFinalProgram, conditionalZeroPhaseProgram, conditionalZeroTailProgram, liftRightProgram, haltRight]
  have hglobal:=transport_finiteLocal_cfg_to_fetch
    (encodeDivLabel pc o) (nextPC p pc)
    (divideInstructionTotalProgram o.toOp (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label; simp [finiteInterpreterProgram,encodeDivLabel,haltRight])
    (d:=finalCfg) hrun hfinal hhalt
  have hpres:=iterate_preservesDispatch
    (divideInstructionTotalProgram o.toOp (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (divideInstructionProgram_preservesDispatch
        (N:=N) o.toOp (nextPC p pc))) _ finalCfg hrun
  have hdispatch:FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state:=by
    cases o <;> simpa [finalCfg,operandEvalStartCfg,literalOperandStartCfg,
      lensRenamedCfg,FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens,FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens,StateLens.comp] using! hpres
  refine ⟨steps + 1,by omega,finalState,hdispatch, ?_⟩
  cases o <;>
    simpa [finalCfg,operandBoundaryBase_coreStacks,
      Function.iterate_succ_apply,embedOperandReturnCfg,
      embedDirectReturnCfg,embedIndirectReturnCfg,
      embedIndirectTransferReturnCfg,embedDirectTailReturnCfg,
      embedFullDivideReturnCfg]
      using! hglobal

set_option maxHeartbeats 1500000 in
theorem finite_div_instruction {p:Program} {N pc w:Nat}
    (hbound:programArgumentBound p <= N) (o:Op)
    (hfetch:p[pc]?=some (.div o)) (s:SparseState)
    (hacc:s.acc < 2 ^ w) (hm:s.mem.Normalized w)
    (state:FullInterpreterState N):
    ∃ steps,steps <= divideInstructionTotalBound w s.mem + 3∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc:=
          (s.acc / sparseValue w o s.mem) % 2 ^ w})):=by
  let harg:operandArgument o <= N:=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo:=BoundedOp.ofOp o harg
  let localCfg:=finiteEmbedCfg (encodeDivLabel (boundPC p pc) bo)
    (operandEvalStartCfg
      (R:=FullDividePostLabel (BoundedPC p)) bo.toOp
      bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))
  have hprepare:=finite_step_prepare_entry hbound (boundPC p pc) (.div o)
    .div (by simpa [fetch_boundPC] using hfetch) rfl state (coreStacks w s)
  have hentry:TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .div))
        state (coreStacks w s))=some localCfg:=by
    rw [hprepare]
    simp [finitePrepareInstr,finiteInitializeEntry,instrArgument,
      localCfg,operandEvalStartCfg_coreStacks,finiteEmbedCfg,
      mapLabelCfg,finiteInterpreterCfg]
    cases o <;> simp [bo,BoundedOp.ofOp] <;> constructor <;> congr
  rcases finite_div_to_fetch hbound (boundPC p pc) bo w s hacc hm state with
    ⟨localSteps,hlocalBound,finalState,hdispatch,hlocal⟩
  have hall:=finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with acc:=s.acc / sparseValue w bo.toOp s.mem}))
    hentry hlocal
  refine ⟨2 + localSteps,by omega,finalState,hdispatch, ?_⟩
  have hlt:s.acc / sparseValue w o s.mem < 2 ^ w:=
    lt_of_le_of_lt (Nat.div_le_self _ _) hacc
  simpa [bo,Nat.mod_eq_of_lt hlt] using hall

end

end Lax759944Proofs.RamToTM

end

theorem solution:∀ {p:Lax759944Proofs.Microcode.Program} {N pc w:ℕ} (hbound:Lax759944Proofs.RamToTM.programArgumentBound p≤ N)
  (o:Lax759944Proofs.Microcode.Op),
  p[pc]?=Option.some (Lax759944Proofs.Microcode.Instr.div o)→
    ∀ (s:Lax759944Proofs.RamToTM.SparseState),
      s.acc < 2 ^ w→
        Lax759944Proofs.RamToTM.SparseMemory.Normalized w s.mem→
          ∀ (state:Lax759944Proofs.RamToTM.FullInterpreterState N),
            ∃ steps≤ Lax759944Proofs.RamToTM.divideInstructionTotalBound w s.mem + 3,
              ∃ finalState,
                Lax759944Proofs.RamToTM.FullInterpreterState.dispatchLens.get finalState =
                    Lax759944Proofs.RamToTM.FullInterpreterState.dispatchLens.get state∧
                  (fun x =>
                          x.bind
                            (Turing.TM2.step (Lax759944Proofs.RamToTM.finiteInterpreterProgram p N hbound)))^[steps]
                      (Option.some
                        (Lax759944Proofs.RamToTM.finiteInterpreterCfg
                          (Lax759944Proofs.RamToTM.FiniteInterpreterLabel.fetch (Lax759944Proofs.RamToTM.boundPC p pc))
                          state (Lax759944Proofs.RamToTM.coreStacks w s))) =
                    Option.some
                      (Lax759944Proofs.RamToTM.finiteInterpreterCfg
                        (Lax759944Proofs.RamToTM.FiniteInterpreterLabel.fetch
                          (Lax759944Proofs.RamToTM.nextPC p (Lax759944Proofs.RamToTM.boundPC p pc)))
                        finalState
                        (Lax759944Proofs.RamToTM.coreStacks w
                          { pc:=s.pc,acc:=s.acc / Lax759944Proofs.RamToTM.sparseValue w o s.mem % 2 ^ w,
                            mem:=s.mem,inp:=s.inp,out:=s.out })):= @Lax759944Proofs.RamToTM.finite_div_instruction
