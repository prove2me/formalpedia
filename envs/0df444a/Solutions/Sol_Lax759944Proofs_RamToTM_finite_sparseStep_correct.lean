-- Prove2me | solution 1 for Lax759944Proofs.RamToTM.finite_sparseStep_correct
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:59:07.2782+00:00
-- url     : https://prove2.me/submissions/3dcc5d33-533a-4e68-a8df-34987377d4ed

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces
import Theorems.Thm_Lax759944Proofs_RamToTM_finite_mul_instruction
import Theorems.Thm_Lax759944Proofs_RamToTM_finite_div_instruction

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

def zipBits (f:Bool→ Bool→ Bool):List Bool→ List Bool→ List Bool
  | a::as,b::bs => f a b::zipBits f as bs
  | _,_ => []

theorem fixedBits_land (w a b:ℕ):
    fixedBits w (Nat.land a b)=zipBits (· && ·) (fixedBits w a) (fixedBits w b):=by
  induction w generalizing a b with
  | zero => rfl
  | succ w ih =>
      rw [← Nat.bit_bodd_div2 a, ← Nat.bit_bodd_div2 b]
      change fixedBits (w + 1)
          (Nat.bit a.bodd a.div2 &&& Nat.bit b.bodd b.div2)=_
      rw [Nat.land_bit]
      simp only [fixedBits,Nat.bodd_bit,Nat.div2_bit,zipBits]
      exact congrArg ((a.bodd && b.bodd)::·) (ih a.div2 b.div2)

theorem fixedBits_lor (w a b:ℕ):
    fixedBits w (Nat.lor a b)=zipBits (· || ·) (fixedBits w a) (fixedBits w b):=by
  induction w generalizing a b with
  | zero => rfl
  | succ w ih =>
      rw [← Nat.bit_bodd_div2 a, ← Nat.bit_bodd_div2 b]
      change fixedBits (w + 1)
          (Nat.bit a.bodd a.div2 ||| Nat.bit b.bodd b.div2)=_
      rw [Nat.lor_bit]
      simp only [fixedBits,Nat.bodd_bit,Nat.div2_bit,zipBits]
      exact congrArg ((a.bodd || b.bodd)::·) (ih a.div2 b.div2)

theorem fixedBits_xor (w a b:ℕ):
    fixedBits w (Nat.xor a b)=zipBits xor (fixedBits w a) (fixedBits w b):=by
  induction w generalizing a b with
  | zero => rfl
  | succ w ih =>
      rw [← Nat.bit_bodd_div2 a, ← Nat.bit_bodd_div2 b]
      change fixedBits (w + 1)
          (Nat.bit a.bodd a.div2 ^^^ Nat.bit b.bodd b.div2)=_
      rw [Nat.xor_bit]
      simp only [fixedBits,Nat.bodd_bit,Nat.div2_bit,zipBits]
      exact congrArg ((xor a.bodd b.bodd)::·) (ih a.div2 b.div2)

theorem bitsValue_complement_add (bs:List Bool):
    bitsValue (bs.map Bool.not) + bitsValue bs + 1=2 ^ bs.length:=by
  induction bs with
  | nil => simp [bitsValue]
  | cons b bs ih =>
      cases b <;> simp [bitsValue,Nat.bit_val,pow_succ] at * <;> omega

theorem zipBits_complement (as bs:List Bool) (h:as.length=bs.length):
    zipBits (fun a _ => !a) as bs=as.map Bool.not:=by
  induction as generalizing bs with
  | nil => simp [zipBits]
  | cons a as ih =>
      cases bs with
      | nil => simp at h
      | cons b bs => simp [zipBits,ih bs (by simpa using h)]

theorem fixedBits_complement (w a b:Nat):
    fixedBits w (2 ^ w - 1 - a % 2 ^ w) =
      zipBits (fun a _ => !a) (fixedBits w a) (fixedBits w b):=by
  rw [zipBits_complement _ _ (by simp)]
  apply bitsValue_injective_of_length
  · simp
  · have h:=bitsValue_complement_add (fixedBits w a)
    simp only [bitsValue_fixedBits,fixedBits_length] at h ⊢
    have hpos:=Nat.two_pow_pos w
    have hlt:2 ^ w - 1 - a % 2 ^ w < 2 ^ w:=by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

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

theorem fixedBits_add (w a b:ℕ):
    fixedBits w (a + b)=addBits (fixedBits w a) (fixedBits w b) false:=by
  simpa using fixedBits_add_carry w a b false

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

@[simp] theorem subBits_length_fixed (w a b:ℕ) (borrow:Bool):
    (subBits (fixedBits w a) (fixedBits w b) borrow).length=w:=by
  induction w generalizing a b borrow <;> simp [fixedBits,subBits, *]

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

def shiftLeftBits:List Bool→ List Bool
  | [] => []
  | x::xs => false::(x::xs).take xs.length

@[simp] theorem shiftLeftBits_length (xs:List Bool):
    (shiftLeftBits xs).length=xs.length:=by
  cases xs <;> simp [shiftLeftBits]

theorem shiftLeftBits_fixed (w n:ℕ):
    shiftLeftBits (fixedBits w n)=fixedBits w (2 * n):=by
  cases w with
  | zero => rfl
  | succ w =>
      simp only [fixedBits]
      rw [shiftLeftBits]
      simp only [fixedBits_length]
      change false::(n.bodd::fixedBits w n.div2).take w =
        (2 * n).bodd::fixedBits w (2 * n).div2
      rw [show n.bodd::fixedBits w n.div2=fixedBits (w + 1) n by rfl,
        fixedBits_take]
      simp [Nat.div2_val]

@[simp] theorem fixedBits_zero (w:ℕ):
    fixedBits w 0=List.replicate w false:=by
  induction w <;> simp [fixedBits,List.replicate_succ, *]

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem stepAux_addIteration_nil {K Λ:Type} [DecidableEq K]
    (left right result:K) (loop done:Λ) (s:AddControl)
    (S:K→ List Bool) (hleft:S left=[]):
    TM2.stepAux (addIteration left right result loop done) s S =
      ⟨some done, { s with left:=none },S⟩:=by
  simp [addIteration,AddControl.setLeft,hleft]

theorem stepAux_addIteration_cons {K Λ:Type} [DecidableEq K]
    (left right result:K) (loop done:Λ) (s:AddControl)
    (S:K→ List Bool) (a b:Bool) (as bs:List Bool)
    (hleft:S left=a::as) (hright:S right=b::bs)
    (hlr:left ≠ right) (hlres:left ≠ result) (hrres:right ≠ result):
    TM2.stepAux (addIteration left right result loop done) s S =
      ⟨some loop,
        { carry:=(fullAdder a b s.carry).2,left:=none,right:=none },
        Function.update (Function.update (Function.update S left as) right bs)
          result ((fullAdder a b s.carry).1::S result)⟩:=by
  have hright':Function.update S left as right=b::bs:=by
    rw [Function.update_of_ne hlr.symm,hright]
  have hresult':Function.update (Function.update S left as) right bs result=S result:=by
    rw [Function.update_of_ne hrres.symm,Function.update_of_ne hlres.symm]
  simp [addIteration,AddControl.setLeft,AddControl.setRight,
    AddControl.sumBit,AddControl.advance,hleft,hright',hresult']

def addMachine:Turing.FinTM2 where
  K:=AddStack
  k₀:=.left
  k₁:=.result
  Γ _:=Bool
  Λ:=AddLabel
  main:=.loop
  σ:=AddControl
  initialState:=default
  m
    | .loop => addIteration .left .right .result .loop .done
    | .done => .halt

def addStackFamily (left right result:List Bool):AddStack→ List Bool
  | .left => left
  | .right => right
  | .result => result

def addCfg (carry:Bool) (left right result:List Bool):addMachine.Cfg where
  l:=some .loop
  var:= ⟨carry,none,none⟩
  stk:=addStackFamily left right result

def addDoneCfg (carry:Bool) (right result:List Bool):addMachine.Cfg where
  l:=some AddLabel.done
  var:= ⟨carry,none,none⟩
  stk:=addStackFamily [] right result

def addCarryOut:List Bool→ List Bool→ Bool→ Bool
  | a::as,b::bs,carry => (addCarryOut as bs (fullAdder a b carry).2)
  | _,_,carry => carry

@[simp] theorem addMachine_step_nil (carry:Bool) (right result:List Bool):
    addMachine.step (addCfg carry [] right result)=some
      { l:=some .done,var:= ⟨carry,none,none⟩,
        stk:=addStackFamily [] right result }:=by
  change some (TM2.stepAux
      (addIteration AddStack.left AddStack.right AddStack.result AddLabel.loop AddLabel.done)
      ⟨carry,none,none⟩ (addStackFamily [] right result))=_
  rw [stepAux_addIteration_nil]
  · rfl

@[simp] theorem addMachine_step_cons (carry a b:Bool)
    (as bs result:List Bool):
    addMachine.step (addCfg carry (a::as) (b::bs) result) =
      some (addCfg (fullAdder a b carry).2 as bs
        ((fullAdder a b carry).1::result)):=by
  change some (TM2.stepAux
      (addIteration AddStack.left AddStack.right AddStack.result AddLabel.loop AddLabel.done)
      ⟨carry,none,none⟩ (addStackFamily (a::as) (b::bs) result))=_
  have h:=stepAux_addIteration_cons
    (left:=AddStack.left) (right:=AddStack.right) (result:=AddStack.result)
    (loop:=AddLabel.loop) (done:=AddLabel.done)
    (s:=(⟨carry,none,none⟩:AddControl))
    (S:=addStackFamily (a::as) (b::bs) result)
    (a:=a) (b:=b) (as:=as) (bs:=bs) rfl rfl
    (by decide) (by decide) (by decide)
  rw [h]
  congr 2
  funext k
  cases k <;> rfl

theorem addMachine_iterate (carry:Bool) (as bs result:List Bool)
    (hlen:as.length=bs.length):
    ((fun o:Option addMachine.Cfg => o.bind addMachine.step)^[as.length])
        (some (addCfg carry as bs result)) =
      some (addCfg (addCarryOut as bs carry) [] []
        ((addBits as bs carry).reverse ++ result)):=by
  induction as generalizing bs carry result with
  | nil =>
      cases bs with
      | nil => rfl
      | cons b bs => simp at hlen
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
        simp at hlen
        rw [List.length_cons,Function.iterate_succ_apply]
        simp only [Option.bind_some,addMachine_step_cons]
        rw [ih (fullAdder a b carry).2 bs
          ((fullAdder a b carry).1::result) hlen]
        simp [addBits,addCarryOut,List.reverse_cons,List.append_assoc]

theorem addMachine_reaches_done (carry:Bool) (as bs result:List Bool)
    (hlen:as.length=bs.length):
    ((fun o:Option addMachine.Cfg => o.bind addMachine.step)^[as.length + 1])
        (some (addCfg carry as bs result)) =
      some (addDoneCfg (addCarryOut as bs carry) []
        ((addBits as bs carry).reverse ++ result)):=by
  rw [Nat.add_comm,Function.iterate_add_apply,
    addMachine_iterate carry as bs result hlen]
  simp only [Function.iterate_one,Option.bind_some]
  rw [addMachine_step_nil]
  rfl

inductive MoveStack | source | target
  deriving DecidableEq,Fintype,Inhabited

inductive MoveLabel | loop | done
  deriving DecidableEq,Fintype,Inhabited

def zipMachine (f:Bool→ Bool→ Bool):Turing.FinTM2 where
  K:=AddStack
  k₀:=.left
  k₁:=.result
  Γ _:=Bool
  Λ:=AddLabel
  main:=.loop
  σ:=ZipControl
  initialState:=default
  m
    | .loop => zipIteration f .left .right .result .loop .done
    | .done => .halt

def zipCfg (f:Bool→ Bool→ Bool) (left right result:List Bool):
    (zipMachine f).Cfg where
  l:=some .loop
  var:= ⟨none,none⟩
  stk:=addStackFamily left right result

def zipPartialDoneCfg (f:Bool→ Bool→ Bool) (right result:List Bool):
    (zipMachine f).Cfg where
  l:=some .done
  var:= ⟨none,none⟩
  stk:=addStackFamily [] right result

def zipDoneCfg (f:Bool→ Bool→ Bool) (result:List Bool):
    (zipMachine f).Cfg:=zipPartialDoneCfg f [] result

@[simp] theorem zipMachine_step_nil (f:Bool→ Bool→ Bool)
    (right result:List Bool):
    (zipMachine f).step (zipCfg f [] right result) =
      some (zipPartialDoneCfg f right result):=by
  change some (TM2.stepAux
    (zipIteration f AddStack.left AddStack.right AddStack.result AddLabel.loop AddLabel.done)
    ⟨none,none⟩ (addStackFamily [] right result))=_
  simp [zipIteration,zipPartialDoneCfg,addStackFamily]

@[simp] theorem zipMachine_step_cons (f:Bool→ Bool→ Bool) (a b:Bool)
    (as bs result:List Bool):
    (zipMachine f).step (zipCfg f (a::as) (b::bs) result) =
      some (zipCfg f as bs (f a b::result)):=by
  change some (TM2.stepAux
    (zipIteration f AddStack.left AddStack.right AddStack.result AddLabel.loop AddLabel.done)
    ⟨none,none⟩ (addStackFamily (a::as) (b::bs) result))=_
  simp [zipIteration,zipCfg,addStackFamily,Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem zipMachine_iterate (f:Bool→ Bool→ Bool) (as bs result:List Bool)
    (hlen:as.length=bs.length):
    ((fun o:Option (zipMachine f).Cfg => o.bind (zipMachine f).step)^[as.length])
      (some (zipCfg f as bs result)) =
      some (zipCfg f [] [] ((zipBits f as bs).reverse ++ result)):=by
  induction as generalizing bs result with
  | nil =>
      cases bs with
      | nil => rfl
      | cons b bs => simp at hlen
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
        simp at hlen
        rw [List.length_cons,Function.iterate_succ_apply]
        simp only [Option.bind_some,zipMachine_step_cons]
        rw [ih bs (f a b::result) hlen]
        simp [zipBits,List.reverse_cons,List.append_assoc]

theorem zipMachine_reaches_done (f:Bool→ Bool→ Bool)
    (as bs result:List Bool) (hlen:as.length=bs.length):
    ((fun o:Option (zipMachine f).Cfg => o.bind (zipMachine f).step)^[as.length + 1])
      (some (zipCfg f as bs result)) =
      some (zipDoneCfg f ((zipBits f as bs).reverse ++ result)):=by
  rw [Nat.add_comm,Function.iterate_add_apply,
    zipMachine_iterate f as bs result hlen]
  simp only [Function.iterate_one,Option.bind_some,zipMachine_step_nil]
  rfl

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

open Turing TM2

def subMachine:Turing.FinTM2 where
  K:=AddStack
  k₀:=.left
  k₁:=.result
  Γ _:=Bool
  Λ:=AddLabel
  main:=.loop
  σ:=SubControl
  initialState:=default
  m
    | .loop => subIteration .left .right .result .loop .done
    | .done => .halt

def subCfg (borrow:Bool) (left right result:List Bool):subMachine.Cfg where
  l:=some .loop
  var:= ⟨borrow,none,none⟩
  stk:=addStackFamily left right result

def subPartialDoneCfg (borrow:Bool) (right result:List Bool):subMachine.Cfg where
  l:=some .done
  var:= ⟨borrow,none,none⟩
  stk:=addStackFamily [] right result

def subDoneCfg (borrow:Bool) (result:List Bool):subMachine.Cfg:=
  subPartialDoneCfg borrow [] result

@[simp] theorem subMachine_step_nil (borrow:Bool) (right result:List Bool):
    subMachine.step (subCfg borrow [] right result) =
      some (subPartialDoneCfg borrow right result):=by
  change some (TM2.stepAux
    (subIteration AddStack.left AddStack.right AddStack.result AddLabel.loop AddLabel.done)
    ⟨borrow,none,none⟩ (addStackFamily [] right result))=_
  simp [subIteration,subPartialDoneCfg,addStackFamily]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem subMachine_step_cons (borrow a b:Bool)
    (as bs result:List Bool):
    subMachine.step (subCfg borrow (a::as) (b::bs) result) =
      some (subCfg (fullSubtractor a b borrow).2 as bs
        ((fullSubtractor a b borrow).1::result)):=by
  change some (TM2.stepAux
    (subIteration AddStack.left AddStack.right AddStack.result AddLabel.loop AddLabel.done)
    ⟨borrow,none,none⟩ (addStackFamily (a::as) (b::bs) result))=_
  simp [subIteration,SubControl.differenceBit,SubControl.advance,
    subCfg,addStackFamily,Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem subMachine_iterate (borrow:Bool) (as bs result:List Bool)
    (hlen:as.length=bs.length):
    ((fun o:Option subMachine.Cfg => o.bind subMachine.step)^[as.length])
      (some (subCfg borrow as bs result)) =
      some (subCfg (subBorrowOut as bs borrow) [] []
        ((subBits as bs borrow).reverse ++ result)):=by
  induction as generalizing bs borrow result with
  | nil =>
      cases bs with
      | nil => rfl
      | cons b bs => simp at hlen
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
        simp at hlen
        rw [List.length_cons,Function.iterate_succ_apply]
        simp only [Option.bind_some,subMachine_step_cons]
        rw [ih (fullSubtractor a b borrow).2 bs
          ((fullSubtractor a b borrow).1::result) hlen]
        simp [subBits,subBorrowOut,List.reverse_cons,List.append_assoc]

theorem subMachine_reaches_done (borrow:Bool) (as bs result:List Bool)
    (hlen:as.length=bs.length):
    ((fun o:Option subMachine.Cfg => o.bind subMachine.step)^[as.length + 1])
      (some (subCfg borrow as bs result)) =
      some (subDoneCfg (subBorrowOut as bs borrow)
        ((subBits as bs borrow).reverse ++ result)):=by
  rw [Nat.add_comm,Function.iterate_add_apply,
    subMachine_iterate borrow as bs result hlen]
  simp only [Function.iterate_one,Option.bind_some,subMachine_step_nil]
  rfl

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def shiftStacks (source temp result:List Bool):ShiftStack→ List Bool
  | .source => source
  | .temp => temp
  | .result => result

def shiftCfg (l:ShiftLabel) (source temp result:List Bool):shiftMachine.Cfg where
  l:=some l
  var:= ⟨none⟩
  stk:=shiftStacks source temp result

@[simp] theorem shift_step_first_cons (a:Bool) (as temp result:List Bool):
    shiftMachine.step (shiftCfg .first (a::as) temp result) =
      some (shiftCfg .first as (a::temp) result):=by
  change some (TM2.stepAux
    (moveIteration ShiftStack.source ShiftStack.temp ShiftLabel.first ShiftLabel.discard)
    ⟨none⟩ (shiftStacks (a::as) temp result))=_
  simp [moveIteration,shiftCfg,shiftStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem shift_step_first_nil (temp result:List Bool):
    shiftMachine.step (shiftCfg .first [] temp result) =
      some (shiftCfg .discard [] temp result):=by
  change some (TM2.stepAux
    (moveIteration ShiftStack.source ShiftStack.temp ShiftLabel.first ShiftLabel.discard)
    ⟨none⟩ (shiftStacks [] temp result))=_
  simp [moveIteration,shiftCfg,shiftStacks]

@[simp] theorem shift_step_discard (source result:List Bool):
    shiftMachine.step (shiftCfg .discard source [] result) =
      some (shiftCfg .second source [] result):=by
  change some (TM2.stepAux
    (.pop ShiftStack.temp (fun _ _ => (⟨none⟩:MoveControl))
      (.goto fun _ => ShiftLabel.second))
    ⟨none⟩ (shiftStacks source [] result))=_
  simp [shiftCfg,shiftStacks]

@[simp] theorem shift_step_discard_cons (source result:List Bool) (a:Bool)
    (temp:List Bool):
    shiftMachine.step (shiftCfg .discard source (a::temp) result) =
      some (shiftCfg .second source temp result):=by
  change some (TM2.stepAux
    (.pop ShiftStack.temp (fun _ _ => (⟨none⟩:MoveControl))
      (.goto fun _ => ShiftLabel.second))
    ⟨none⟩ (shiftStacks source (a::temp) result))=_
  simp [shiftCfg,shiftStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem shift_step_discard_any (source temp result:List Bool):
    shiftMachine.step (shiftCfg .discard source temp result) =
      some (shiftCfg .second source temp.tail result):=by
  cases temp with
  | nil => exact shift_step_discard source result
  | cons a temp => exact shift_step_discard_cons source result a temp

@[simp] theorem shift_step_second_cons (source result:List Bool) (a:Bool)
    (temp:List Bool):
    shiftMachine.step (shiftCfg .second source (a::temp) result) =
      some (shiftCfg .second source temp (a::result)):=by
  change some (TM2.stepAux
    (moveIteration ShiftStack.temp ShiftStack.result ShiftLabel.second ShiftLabel.prepend)
    ⟨none⟩ (shiftStacks source (a::temp) result))=_
  simp [moveIteration,shiftCfg,shiftStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem shift_step_second_nil (source result:List Bool):
    shiftMachine.step (shiftCfg .second source [] result) =
      some (shiftCfg .prepend source [] result):=by
  change some (TM2.stepAux
    (moveIteration ShiftStack.temp ShiftStack.result ShiftLabel.second ShiftLabel.prepend)
    ⟨none⟩ (shiftStacks source [] result))=_
  simp [moveIteration,shiftCfg,shiftStacks]

@[simp] theorem shift_step_prepend (source temp result:List Bool):
    shiftMachine.step (shiftCfg .prepend source temp result) =
      some (shiftCfg .done source temp (false::result)):=by
  change some (TM2.stepAux
    (.push ShiftStack.result (fun _:MoveControl => false)
      (.goto fun _ => ShiftLabel.done))
    ⟨none⟩ (shiftStacks source temp result))=_
  simp [shiftCfg,shiftStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem shift_first_iterate (source temp result:List Bool):
    ((fun o:Option shiftMachine.Cfg => o.bind shiftMachine.step)^[source.length])
      (some (shiftCfg .first source temp result)) =
      some (shiftCfg .first [] (source.reverse ++ temp) result):=by
  induction source generalizing temp with
  | nil => rfl
  | cons a as ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,shift_step_first_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem shift_second_iterate (source temp result:List Bool):
    ((fun o:Option shiftMachine.Cfg => o.bind shiftMachine.step)^[temp.length])
      (some (shiftCfg .second source temp result)) =
      some (shiftCfg .second source [] (temp.reverse ++ result)):=by
  induction temp generalizing result with
  | nil => rfl
  | cons a temp ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,shift_step_second_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem shiftMachine_correct_nonempty (a:Bool) (as:List Bool):
    ((fun o:Option shiftMachine.Cfg => o.bind shiftMachine.step)^[2 * (a::as).length + 3])
      (some (shiftCfg .first (a::as) [] [])) =
      some (shiftCfg .done [] [] (shiftLeftBits (a::as))):=by
  let stepO:=fun o:Option shiftMachine.Cfg => o.bind shiftMachine.step
  have chain {m n:ℕ} {x y z:Option shiftMachine.Cfg}
      (h₁:(stepO^[m]) x=y) (h₂:(stepO^[n]) y=z):
      (stepO^[n + m]) x=z:=by
    rw [Function.iterate_add_apply,h₁,h₂]
  have hfirst:=shift_first_iterate (a::as) [] []
  have hsecond:=shift_second_iterate ([]:List Bool) (a::as).reverse.tail []
  simp only [List.append_nil] at hfirst hsecond
  have h₁:(stepO^[1]) (some (shiftCfg .first [] (a::as).reverse [])) =
      some (shiftCfg .discard [] (a::as).reverse []):=by
    simpa [stepO] using! shift_step_first_nil (a::as).reverse ([]:List Bool)
  have h₂:(stepO^[1]) (some (shiftCfg .discard [] (a::as).reverse [])) =
      some (shiftCfg .second [] (a::as).reverse.tail []):=by
    simpa [stepO] using! shift_step_discard_any ([]:List Bool) (a::as).reverse []
  have h₃:(stepO^[1])
      (some (shiftCfg .second [] [] (a::as).reverse.tail.reverse)) =
      some (shiftCfg .prepend [] [] (a::as).reverse.tail.reverse):=by
    simpa [stepO] using!
      shift_step_second_nil ([]:List Bool) (a::as).reverse.tail.reverse
  have h₄:(stepO^[1])
      (some (shiftCfg .prepend [] [] (a::as).reverse.tail.reverse)) =
      some (shiftCfg .done [] [] (false::(a::as).reverse.tail.reverse)):=by
    simpa [stepO] using!
      shift_step_prepend ([]:List Bool) ([]:List Bool) (a::as).reverse.tail.reverse
  have h01:=chain hfirst h₁
  have h02:=chain h01 h₂
  have h03:=chain h02 hsecond
  have h04:=chain h03 h₃
  have h05:=chain h04 h₄
  dsimp [stepO] at h05
  have hexp:
      1 + (1 + ((a::as).reverse.tail.length + (1 + (1 + (as.length + 1))))) =
        2 * (a::as).length + 3:=by simp; omega
  rw [hexp] at h05
  have hout:(a::as).reverse.tail.reverse=(a::as).take as.length:=by
    rw [List.tail_reverse,List.reverse_reverse,List.dropLast_eq_take]
    simp
  rw [hout] at h05
  simpa [shiftLeftBits] using h05

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

def shiftRightBits:List Bool→ List Bool
  | [] => []
  | _::bits => bits ++ [false]

@[simp] theorem bitsValue_append_false (bits:List Bool):
    bitsValue (bits ++ [false])=bitsValue bits:=by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [bitsValue,ih]

@[simp] theorem shiftRightBits_length_of_ne_nil {bits:List Bool}
    (h:bits ≠ []):(shiftRightBits bits).length=bits.length:=by
  cases bits with
  | nil => contradiction
  | cons b bs => simp [shiftRightBits]

theorem shiftRightBits_fixed (w a:ℕ) (ha:a < 2 ^ w):
    shiftRightBits (fixedBits w a)=fixedBits w (a / 2):=by
  cases w with
  | zero => simp [shiftRightBits,fixedBits]
  | succ w =>
      have hdiv:a / 2 < 2 ^ w:=by
        rw [pow_succ'] at ha
        omega
      change fixedBits w (a / 2) ++ [false]=fixedBits (w + 1) (a / 2)
      rw [← fixedBits_bitsValue (fixedBits w (a / 2) ++ [false])]
      rw [bitsValue_append_false,bitsValue_fixedBits_of_lt hdiv]
      simp

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

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def prependCellStacks (address value memory:List SparseSymbol):
    PrependCellStack→ List SparseSymbol
  | .address => address
  | .value => value
  | .memory => memory

def prependCellCfg (label:PrependCellLabel)
    (address value memory:List SparseSymbol):prependCellMachine.Cfg where
  l:=some label
  var:=default
  stk:=prependCellStacks address value memory

@[simp] theorem prependCell_step_cellEnd (address value memory:List SparseSymbol):
    prependCellMachine.step (prependCellCfg .cellEnd address value memory) =
      some (prependCellCfg .valueEnd address value (.cellEnd::memory)):=by
  simp [prependCellMachine,prependCellCfg,prependCellStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem prependCell_step_valueEnd (address value memory:List SparseSymbol):
    prependCellMachine.step (prependCellCfg .valueEnd address value memory) =
      some (prependCellCfg .value address value (.wordEnd::memory)):=by
  simp [prependCellMachine,prependCellCfg,prependCellStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem prependCell_step_value_cons (a:SparseSymbol)
    (address value memory:List SparseSymbol):
    prependCellMachine.step (prependCellCfg .value address (a::value) memory) =
      some (prependCellCfg .value address value (a::memory)):=by
  simp [prependCellMachine,prependCellMoveIteration,prependCellCfg,
    prependCellStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem prependCell_step_value_nil (address memory:List SparseSymbol):
    prependCellMachine.step (prependCellCfg .value address [] memory) =
      some (prependCellCfg .addressEnd address [] memory):=by
  simp [prependCellMachine,prependCellMoveIteration,prependCellCfg,
    prependCellStacks]
  congr 2

@[simp] theorem prependCell_step_addressEnd (address value memory:List SparseSymbol):
    prependCellMachine.step (prependCellCfg .addressEnd address value memory) =
      some (prependCellCfg .address address value (.wordEnd::memory)):=by
  simp [prependCellMachine,prependCellCfg,prependCellStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem prependCell_step_address_cons (a:SparseSymbol)
    (address value memory:List SparseSymbol):
    prependCellMachine.step (prependCellCfg .address (a::address) value memory) =
      some (prependCellCfg .address address value (a::memory)):=by
  simp [prependCellMachine,prependCellMoveIteration,prependCellCfg,
    prependCellStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem prependCell_step_address_nil (value memory:List SparseSymbol):
    prependCellMachine.step (prependCellCfg .address [] value memory) =
      some (prependCellCfg .done [] value memory):=by
  simp [prependCellMachine,prependCellMoveIteration,prependCellCfg,
    prependCellStacks]
  congr 2

theorem prependCell_value_iterate (address value memory:List SparseSymbol):
    ((fun o:Option prependCellMachine.Cfg => o.bind prependCellMachine.step)^[
      value.length])
      (some (prependCellCfg .value address value memory)) =
    some (prependCellCfg .value address [] (value.reverse ++ memory)):=by
  induction value generalizing memory with
  | nil => rfl
  | cons a value ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,prependCell_step_value_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem prependCell_address_iterate (address value memory:List SparseSymbol):
    ((fun o:Option prependCellMachine.Cfg => o.bind prependCellMachine.step)^[
      address.length])
      (some (prependCellCfg .address address value memory)) =
    some (prependCellCfg .address [] value (address.reverse ++ memory)):=by
  induction address generalizing memory with
  | nil => rfl
  | cons a address ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,prependCell_step_address_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem prependCell_correct (address value memory:List SparseSymbol):
    ((fun o:Option prependCellMachine.Cfg => o.bind prependCellMachine.step)^[
      address.length + value.length + 5])
      (some (prependCellCfg .cellEnd address value memory)) =
    some (prependCellCfg .done [] []
      (address.reverse ++
        (.wordEnd::value.reverse ++ (.wordEnd::.cellEnd::memory)))):=by
  let stepO:=fun o:Option prependCellMachine.Cfg => o.bind prependCellMachine.step
  have chain {r s:ℕ} {x y z:Option prependCellMachine.Cfg}
      (hr:(stepO^[r]) x=y) (hs:(stepO^[s]) y=z):
      (stepO^[s + r]) x=z:=by
    rw [Function.iterate_add_apply,hr,hs]
  have h0:(stepO^[1]) (some (prependCellCfg .cellEnd address value memory)) =
      some (prependCellCfg .valueEnd address value (.cellEnd::memory)):=by
    simpa [stepO] using prependCell_step_cellEnd address value memory
  have h1:(stepO^[1])
      (some (prependCellCfg .valueEnd address value (.cellEnd::memory))) =
      some (prependCellCfg .value address value (.wordEnd::.cellEnd::memory)):=by
    simpa [stepO] using prependCell_step_valueEnd address value (.cellEnd::memory)
  have h2:=prependCell_value_iterate address value (.wordEnd::.cellEnd::memory)
  have h3:(stepO^[1])
      (some (prependCellCfg .value address []
        (value.reverse ++ .wordEnd::.cellEnd::memory))) =
      some (prependCellCfg .addressEnd address []
        (value.reverse ++ .wordEnd::.cellEnd::memory)):=by
    simpa [stepO] using prependCell_step_value_nil address
      (value.reverse ++ .wordEnd::.cellEnd::memory)
  have h4:(stepO^[1])
      (some (prependCellCfg .addressEnd address []
        (value.reverse ++ .wordEnd::.cellEnd::memory))) =
      some (prependCellCfg .address address []
        (.wordEnd::value.reverse ++ (.wordEnd::.cellEnd::memory))):=by
    simpa [stepO,List.append_assoc] using prependCell_step_addressEnd address []
      (value.reverse ++ .wordEnd::.cellEnd::memory)
  have h5:=prependCell_address_iterate address []
    (.wordEnd::value.reverse ++ (.wordEnd::.cellEnd::memory))
  have h6:(stepO^[1])
      (some (prependCellCfg .address [] []
        (address.reverse ++
          (.wordEnd::value.reverse ++ (.wordEnd::.cellEnd::memory))))) =
      some (prependCellCfg .done [] []
        (address.reverse ++
          (.wordEnd::value.reverse ++ (.wordEnd::.cellEnd::memory)))):=by
    simpa [stepO,List.append_assoc] using prependCell_step_address_nil []
      (address.reverse ++
        (.wordEnd::value.reverse ++ (.wordEnd::.cellEnd::memory)))
  have hrun:=chain (chain (chain (chain (chain (chain h0 h1) h2) h3) h4) h5) h6
  have hexp:1 + (address.length + (1 + (1 + (value.length + (1 + 1))))) =
      address.length + value.length + 5:=by omega
  rw [hexp] at hrun
  simpa [stepO,List.append_assoc] using hrun

theorem prependCell_fixed_correct (w a v:ℕ) (memory:List SparseSymbol):
    ((fun o:Option prependCellMachine.Cfg => o.bind prependCellMachine.step)^[
      2 * w + 5])
      (some (prependCellCfg .cellEnd
        ((fixedBits w a).reverse.map SparseSymbol.bit)
        ((fixedBits w v).reverse.map SparseSymbol.bit) memory)) =
    some (prependCellCfg .done [] [] (encodeSparseCell w (a,v) ++ memory)):=by
  have h:=prependCell_correct
    ((fixedBits w a).reverse.map SparseSymbol.bit)
    ((fixedBits w v).reverse.map SparseSymbol.bit) memory
  simp only [List.length_map,List.length_reverse,fixedBits_length] at h
  have htime:w + w + 5=2 * w + 5:=by omega
  rw [htime] at h
  simpa [encodeSparseCell,encodeFixedWord,List.map_reverse,
    List.append_assoc] using h

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

namespace Lax759944Proofs.RamToTM

open Turing TM2

def sparseAddProgram:=
  mapAlphabetProgram sparseBitEncode sparseBitDecode addMachine.m

def sparseAddCfg (carry:Bool) (left right result:List Bool):=
  mapAlphabetCfg sparseBitEncode (addCfg carry left right result)

def sparseAddDoneCfg (carry:Bool) (right result:List Bool):=
  mapAlphabetCfg sparseBitEncode (addDoneCfg carry right result)

theorem sparseAdd_reaches_done (carry:Bool) (as bs result:List Bool)
    (hlen:as.length=bs.length):
    ((fun o => o.bind (TM2.step sparseAddProgram))^[as.length + 1])
        (some (sparseAddCfg carry as bs result)) =
      some (sparseAddDoneCfg (addCarryOut as bs carry) []
        ((addBits as bs carry).reverse ++ result)):=by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode addMachine.m
    (addMachine_reaches_done carry as bs result hlen)

def sparseZipProgram (f:Bool→ Bool→ Bool):=
  mapAlphabetProgram sparseBitEncode sparseBitDecode (zipMachine f).m

def sparseZipCfg (f:Bool→ Bool→ Bool) (left right result:List Bool):=
  mapAlphabetCfg sparseBitEncode (zipCfg f left right result)

def sparseZipDoneCfg (f:Bool→ Bool→ Bool) (result:List Bool):=
  mapAlphabetCfg sparseBitEncode (zipDoneCfg f result)

theorem sparseZip_reaches_done (f:Bool→ Bool→ Bool)
    (as bs result:List Bool) (hlen:as.length=bs.length):
    ((fun o => o.bind (TM2.step (sparseZipProgram f)))^[as.length + 1])
        (some (sparseZipCfg f as bs result)) =
      some (sparseZipDoneCfg f ((zipBits f as bs).reverse ++ result)):=by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode (zipMachine f).m
    (zipMachine_reaches_done f as bs result hlen)

def sparseSubProgram:=
  mapAlphabetProgram sparseBitEncode sparseBitDecode subMachine.m

def sparseSubCfg (borrow:Bool) (left right result:List Bool):=
  mapAlphabetCfg sparseBitEncode (subCfg borrow left right result)

def sparseSubDoneCfg (borrow:Bool) (result:List Bool):=
  mapAlphabetCfg sparseBitEncode (subDoneCfg borrow result)

def sparseShiftCfg (label:ShiftLabel) (source temp result:List Bool):=
  mapAlphabetCfg sparseBitEncode (shiftCfg label source temp result)

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

@[simp] theorem boundPC_val_of_lt {p:Program} {pc:ℕ} (h:pc < p.length):
    (boundPC p pc).val=pc:=by
  simp [boundPC,h]

@[simp] theorem fetch_boundPC (p:Program) (pc:ℕ):
    (boundPC p pc).fetch=p[pc]?:=by
  by_cases h:pc < p.length
  · simp [BoundedPC.fetch,boundPC,h]
  · have hout:p[pc]?=none:=List.getElem?_eq_none (by omega)
    simp [BoundedPC.fetch,boundPC,h,hout]

theorem nextPC_boundPC_of_lt {p:Program} {pc:ℕ} (h:pc < p.length):
    nextPC p (boundPC p pc)=boundPC p (pc + 1):=by
  apply Fin.ext
  simp [nextPC,h]

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

def controlBoundaryCfg (p:Program) (pc:ℕ) (w:ℕ) (s:SparseState):
    (controlDispatchMachine p).Cfg:=
  controlDispatchCfg p (.fetch (boundPC p pc)) default (coreStacks w s)

def controlWorkTapes (base:CoreStack→ List SparseSymbol)
    (accumulator work:List SparseSymbol):CoreStack→ List SparseSymbol
  | .accumulator => accumulator
  | .work0 => work
  | k => base k

def controlScanCfg (p:Program) (pc target:BoundedPC p) (jumpOnZero any:Bool)
    (accumulator work:List SparseSymbol)
    (base:CoreStack→ List SparseSymbol):(controlDispatchMachine p).Cfg:=
  controlDispatchCfg p (.scanAccumulator pc target jumpOnZero)
    { held:=none,anyTrue:=any } (controlWorkTapes base accumulator work)

def controlRestoreCfg (p:Program) (pc target:BoundedPC p)
    (jumpOnZero any:Bool) (accumulator work:List SparseSymbol)
    (base:CoreStack→ List SparseSymbol):(controlDispatchMachine p).Cfg:=
  controlDispatchCfg p (.restoreAccumulator pc target jumpOnZero)
    { held:=none,anyTrue:=any } (controlWorkTapes base accumulator work)

@[simp] theorem control_step_scan_bit (p:Program) (pc target:BoundedPC p)
    (jumpOnZero any bit:Bool) (bits work:List SparseSymbol)
    (base:CoreStack→ List SparseSymbol):
    (controlDispatchMachine p).step
      (controlScanCfg p pc target jumpOnZero any (.bit bit::bits) work base) =
      some (controlScanCfg p pc target jumpOnZero (any || bit) bits
        (.bit bit::work) base):=by
  cases bit <;>
  simp [controlDispatchMachine,controlScanCfg,controlDispatchCfg,controlWorkTapes,
    DispatchControl.observe,DispatchControl.clearHeld,Function.update]
  all_goals
    congr 2
    funext k
    cases k <;> rfl

@[simp] theorem control_step_scan_nil (p:Program) (pc target:BoundedPC p)
    (jumpOnZero any:Bool) (work:List SparseSymbol)
    (base:CoreStack→ List SparseSymbol):
    (controlDispatchMachine p).step
      (controlScanCfg p pc target jumpOnZero any [] work base) =
      some (controlRestoreCfg p pc target jumpOnZero any [] work base):=by
  simp [controlDispatchMachine,controlScanCfg,controlRestoreCfg,
    controlDispatchCfg,controlWorkTapes,DispatchControl.observe,
    DispatchControl.clearHeld]

theorem control_scan_iterate (p:Program) (pc target:BoundedPC p)
    (jumpOnZero any:Bool) (bits:List Bool) (work:List SparseSymbol)
    (base:CoreStack→ List SparseSymbol):
    ((fun o:Option (controlDispatchMachine p).Cfg =>
      o.bind (controlDispatchMachine p).step)^[bits.length])
      (some (controlScanCfg p pc target jumpOnZero any
        (bits.map SparseSymbol.bit) work base)) =
      some (controlScanCfg p pc target jumpOnZero (any || containsTrue bits) []
        ((bits.reverse.map SparseSymbol.bit) ++ work) base):=by
  induction bits generalizing any work with
  | nil => simp [containsTrue]
  | cons bit bits ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [List.map_cons,Option.bind_some,control_step_scan_bit]
      rw [ih]
      simp [containsTrue,List.reverse_cons,List.append_assoc,Bool.or_assoc]

@[simp] theorem control_step_restore_bit (p:Program) (pc target:BoundedPC p)
    (jumpOnZero any bit:Bool) (accumulator:List SparseSymbol) (bits:List Bool)
    (base:CoreStack→ List SparseSymbol):
    (controlDispatchMachine p).step
      (controlRestoreCfg p pc target jumpOnZero any accumulator
        (.bit bit::bits.map SparseSymbol.bit) base) =
      some (controlRestoreCfg p pc target jumpOnZero any
        (.bit bit::accumulator) (bits.map SparseSymbol.bit) base):=by
  simp [controlDispatchMachine,controlRestoreCfg,controlDispatchCfg,
    controlWorkTapes,DispatchControl.clearHeld,Function.update]
  congr 2
  funext k
  cases k <;> rfl

theorem control_restore_iterate (p:Program) (pc target:BoundedPC p)
    (jumpOnZero any:Bool) (accumulator:List SparseSymbol) (bits:List Bool)
    (base:CoreStack→ List SparseSymbol):
    ((fun o:Option (controlDispatchMachine p).Cfg =>
      o.bind (controlDispatchMachine p).step)^[bits.length])
      (some (controlRestoreCfg p pc target jumpOnZero any accumulator
        (bits.map SparseSymbol.bit) base)) =
      some (controlRestoreCfg p pc target jumpOnZero any
        (bits.reverse.map SparseSymbol.bit ++ accumulator) [] base):=by
  induction bits generalizing accumulator with
  | nil => rfl
  | cons bit bits ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [List.map_cons,Option.bind_some,control_step_restore_bit]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

def conditionalDestination (p:Program) (pc target:BoundedPC p)
    (jumpOnZero any:Bool):BoundedPC p:=
  if any == !jumpOnZero then target else nextPC p pc

@[simp] theorem control_step_restore_nil (p:Program) (pc target:BoundedPC p)
    (jumpOnZero any:Bool) (accumulator:List SparseSymbol)
    (base:CoreStack→ List SparseSymbol):
    (controlDispatchMachine p).step
      (controlRestoreCfg p pc target jumpOnZero any accumulator [] base) =
      some (controlDispatchCfg p
        (.fetch (conditionalDestination p pc target jumpOnZero any)) default
        (controlWorkTapes base accumulator [])):=by
  by_cases h:any == !jumpOnZero <;>
    simp [controlDispatchMachine,controlRestoreCfg,controlDispatchCfg,
      controlWorkTapes,DispatchControl.clearHeld,conditionalDestination,h]
  all_goals
    congr 2
    funext k
    cases k <;> rfl

@[simp] theorem controlWorkTapes_boundary (w:ℕ) (s:SparseState):
    controlWorkTapes (coreStacks w s) (encodeAccumulator w s.acc) [] =
      coreStacks w s:=by
  funext k
  cases k <;> rfl

theorem containsTrue_fixedBits (w a:ℕ) (ha:a < 2 ^ w):
    containsTrue (fixedBits w a)=decide (0 < a):=by
  by_cases hp:0 < a
  · cases hc:containsTrue (fixedBits w a) with
    | false =>
        have hz:=containsTrue_false_bitsValue_zero hc
        rw [bitsValue_fixedBits_of_lt ha] at hz
        omega
    | true => simp [hp]
  · have hz:a=0:=by omega
    subst a
    simp [fixedBits_zero]
    induction w with
    | zero => rfl
    | succ w ih => simpa [List.replicate_succ,containsTrue] using ih

@[simp] theorem control_step_jzero_fetch {p:Program} {pc target w:ℕ}
    {s:SparseState} (hfetch:p[pc]?=some (.jzero target)):
    (controlDispatchMachine p).step (controlBoundaryCfg p pc w s) =
      some (controlScanCfg p (boundPC p pc) (jumpPC p target) true false
        (fixedBits w s.acc |>.map SparseSymbol.bit) [] (coreStacks w s)):=by
  simp [controlDispatchMachine,controlBoundaryCfg,controlScanCfg,
    controlDispatchCfg,controlWorkTapes,encodeAccumulator,fetch_boundPC,hfetch]
  congr 2
  simp [show (default:DispatchControl)=⟨none,false⟩ from rfl]
  funext k
  cases k <;> rfl

theorem control_jzero_correct {p:Program} {pc target w:ℕ} {s:SparseState}
    (hfetch:p[pc]?=some (.jzero target)) (hacc:s.acc < 2 ^ w):
    let next:=if s.acc=0 then target else pc + 1
    ((fun o:Option (controlDispatchMachine p).Cfg =>
      o.bind (controlDispatchMachine p).step)^[2 * w + 3])
      (some (controlBoundaryCfg p pc w s)) =
      some (controlBoundaryCfg p next w { s with pc:=next }):=by
  let stepO:=fun o:Option (controlDispatchMachine p).Cfg =>
    o.bind fun a => (controlDispatchMachine p).step a
  let bits:=fixedBits w s.acc
  let sourcePC:=boundPC p pc
  let targetPC:=jumpPC p target
  change (stepO^[2 * w + 3]) (some (controlBoundaryCfg p pc w s))=_
  have hpc:pc < p.length:=fetch_some_pc_lt hfetch
  have chain {m n:ℕ} {a b c:Option (controlDispatchMachine p).Cfg}
      (h₁:(stepO^[m]) a=b) (h₂:(stepO^[n]) b=c):
      (stepO^[n + m]) a=c:=by
    rw [Function.iterate_add_apply,h₁,h₂]
  have hf:(stepO^[1]) (some (controlBoundaryCfg p pc w s)) =
      some (controlScanCfg p sourcePC targetPC true false
        (bits.map SparseSymbol.bit) [] (coreStacks w s)):=by
    simpa [stepO,bits,sourcePC,targetPC] using
      control_step_jzero_fetch (w:=w) (s:=s) hfetch
  have hs:=control_scan_iterate p sourcePC targetPC true false bits []
    (coreStacks w s)
  simp only [List.append_nil,Bool.false_or] at hs
  have hs0:(stepO^[1])
      (some (controlScanCfg p sourcePC targetPC true (containsTrue bits) []
        (bits.reverse.map SparseSymbol.bit) (coreStacks w s))) =
      some (controlRestoreCfg p sourcePC targetPC true (containsTrue bits) []
        (bits.reverse.map SparseSymbol.bit) (coreStacks w s)):=by
    simpa [stepO] using control_step_scan_nil p sourcePC targetPC true
      (containsTrue bits) (bits.reverse.map SparseSymbol.bit) (coreStacks w s)
  have hr:=control_restore_iterate p sourcePC targetPC true (containsTrue bits) []
    bits.reverse (coreStacks w s)
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hr
  have hr0:=control_step_restore_nil p sourcePC targetPC true (containsTrue bits)
    (bits.map SparseSymbol.bit) (coreStacks w s)
  have h:=chain (chain (chain (chain hf hs) hs0) hr)
    (show (stepO^[1]) _=_ by simpa [stepO] using hr0)
  have htime:1 + (bits.length + (1 + (bits.length + 1)))=2 * w + 3:=by
    simp [bits]
    omega
  rw [htime] at h
  have htapes:
      controlWorkTapes (coreStacks w s) (bits.map SparseSymbol.bit) [] =
        coreStacks w s:=by
    simpa [bits,encodeAccumulator] using controlWorkTapes_boundary w s
  rw [htapes] at h
  rw [containsTrue_fixedBits w s.acc hacc] at h
  by_cases hz:s.acc=0
  · rw [← coreStacks_set_pc w target s] at h
    simpa [conditionalDestination,sourcePC,targetPC,jumpPC,hz,
      controlBoundaryCfg,bits,encodeAccumulator,controlWorkTapes_boundary,
      ] using h
  · have hp:0 < s.acc:=by omega
    rw [← coreStacks_set_pc w (pc + 1) s] at h
    simpa [conditionalDestination,sourcePC,targetPC,hz,hp,
      controlBoundaryCfg,bits,encodeAccumulator,controlWorkTapes_boundary,
      nextPC_boundPC_of_lt hpc] using h

@[simp] theorem control_step_jgtz_fetch {p:Program} {pc target w:ℕ}
    {s:SparseState} (hfetch:p[pc]?=some (.jgtz target)):
    (controlDispatchMachine p).step (controlBoundaryCfg p pc w s) =
      some (controlScanCfg p (boundPC p pc) (jumpPC p target) false false
        (fixedBits w s.acc |>.map SparseSymbol.bit) [] (coreStacks w s)):=by
  simp [controlDispatchMachine,controlBoundaryCfg,controlScanCfg,
    controlDispatchCfg,controlWorkTapes,fetch_boundPC,hfetch]
  congr 2
  simp [show (default:DispatchControl)=⟨none,false⟩ from rfl]
  funext k
  cases k <;> rfl

theorem control_jgtz_correct {p:Program} {pc target w:ℕ} {s:SparseState}
    (hfetch:p[pc]?=some (.jgtz target)) (hacc:s.acc < 2 ^ w):
    let next:=if 0 < s.acc then target else pc + 1
    ((fun o:Option (controlDispatchMachine p).Cfg =>
      o.bind (controlDispatchMachine p).step)^[2 * w + 3])
      (some (controlBoundaryCfg p pc w s)) =
      some (controlBoundaryCfg p next w { s with pc:=next }):=by
  let stepO:=fun o:Option (controlDispatchMachine p).Cfg =>
    o.bind fun a => (controlDispatchMachine p).step a
  let bits:=fixedBits w s.acc
  let sourcePC:=boundPC p pc
  let targetPC:=jumpPC p target
  change (stepO^[2 * w + 3]) (some (controlBoundaryCfg p pc w s))=_
  have hpc:pc < p.length:=fetch_some_pc_lt hfetch
  have chain {m n:ℕ} {a b c:Option (controlDispatchMachine p).Cfg}
      (h₁:(stepO^[m]) a=b) (h₂:(stepO^[n]) b=c):
      (stepO^[n + m]) a=c:=by
    rw [Function.iterate_add_apply,h₁,h₂]
  have hf:(stepO^[1]) (some (controlBoundaryCfg p pc w s)) =
      some (controlScanCfg p sourcePC targetPC false false
        (bits.map SparseSymbol.bit) [] (coreStacks w s)):=by
    simpa [stepO,bits,sourcePC,targetPC] using
      control_step_jgtz_fetch (w:=w) (s:=s) hfetch
  have hs:=control_scan_iterate p sourcePC targetPC false false bits []
    (coreStacks w s)
  simp only [List.append_nil,Bool.false_or] at hs
  have hs0:(stepO^[1])
      (some (controlScanCfg p sourcePC targetPC false (containsTrue bits) []
        (bits.reverse.map SparseSymbol.bit) (coreStacks w s))) =
      some (controlRestoreCfg p sourcePC targetPC false (containsTrue bits) []
        (bits.reverse.map SparseSymbol.bit) (coreStacks w s)):=by
    simpa [stepO] using control_step_scan_nil p sourcePC targetPC false
      (containsTrue bits) (bits.reverse.map SparseSymbol.bit) (coreStacks w s)
  have hr:=control_restore_iterate p sourcePC targetPC false (containsTrue bits) []
    bits.reverse (coreStacks w s)
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hr
  have hr0:=control_step_restore_nil p sourcePC targetPC false (containsTrue bits)
    (bits.map SparseSymbol.bit) (coreStacks w s)
  have h:=chain (chain (chain (chain hf hs) hs0) hr)
    (show (stepO^[1]) _=_ by simpa [stepO] using hr0)
  have htime:1 + (bits.length + (1 + (bits.length + 1)))=2 * w + 3:=by
    simp [bits]
    omega
  rw [htime] at h
  have htapes:
      controlWorkTapes (coreStacks w s) (bits.map SparseSymbol.bit) [] =
        coreStacks w s:=by
    simpa [bits,encodeAccumulator] using controlWorkTapes_boundary w s
  rw [htapes] at h
  rw [containsTrue_fixedBits w s.acc hacc] at h
  by_cases hp:0 < s.acc
  · rw [← coreStacks_set_pc w target s] at h
    simpa [conditionalDestination,sourcePC,targetPC,jumpPC,hp,
      controlBoundaryCfg,bits,encodeAccumulator,controlWorkTapes_boundary] using h
  · have hz:s.acc=0:=by omega
    rw [← coreStacks_set_pc w (pc + 1) s] at h
    simpa [conditionalDestination,sourcePC,targetPC,hp,hz,
      controlBoundaryCfg,bits,encodeAccumulator,controlWorkTapes_boundary,
      nextPC_boundPC_of_lt hpc] using h

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

def sparseAddLocalCfg (carry:Bool) (left right result:List Bool):
    TM2.Cfg (fun _:AddStack => SparseSymbol) AddLabel AddControl where
  l:=some .loop
  var:= ⟨carry,none,none⟩
  stk:=mapAlphabetStacks sparseBitEncode (addStackFamily left right result)

def sparseAddLocalDoneCfg (carry:Bool) (right result:List Bool):
    TM2.Cfg (fun _:AddStack => SparseSymbol) AddLabel AddControl where
  l:=some .done
  var:= ⟨carry,none,none⟩
  stk:=mapAlphabetStacks sparseBitEncode (addStackFamily [] right result)

theorem sparseAddLocal_correct (carry:Bool) (left right result:List Bool)
    (hlen:left.length=right.length):
    ((fun o => o.bind (TM2.step sparseAddCoreProgram))^[left.length + 1])
      (some (sparseAddLocalCfg carry left right result)) =
      some (sparseAddLocalDoneCfg (addCarryOut left right carry) []
        ((addBits left right carry).reverse ++ result)):=by
  have hp:sparseAddCoreProgram=sparseAddProgram:=by
    funext l
    cases l <;> rfl
  rw [hp]
  simpa [sparseAddLocalCfg,sparseAddLocalDoneCfg,sparseAddCfg,
    sparseAddDoneCfg,addCfg,addDoneCfg,mapAlphabetCfg] using!
      sparseAdd_reaches_done carry left right result hlen

def sparseZipLocalCfg (f:Bool→ Bool→ Bool)
    (left right result:List Bool):
    TM2.Cfg (fun _:AddStack => SparseSymbol) AddLabel ZipControl where
  l:=some .loop
  var:= ⟨none,none⟩
  stk:=mapAlphabetStacks sparseBitEncode (addStackFamily left right result)

def sparseZipLocalDoneCfg (f:Bool→ Bool→ Bool) (result:List Bool):
    TM2.Cfg (fun _:AddStack => SparseSymbol) AddLabel ZipControl where
  l:=some .done
  var:= ⟨none,none⟩
  stk:=mapAlphabetStacks sparseBitEncode (addStackFamily [] [] result)

theorem sparseZipLocal_correct (f:Bool→ Bool→ Bool)
    (left right result:List Bool) (hlen:left.length=right.length):
    ((fun o => o.bind (TM2.step (sparseZipCoreProgram f)))^[left.length + 1])
      (some (sparseZipLocalCfg f left right result)) =
      some (sparseZipLocalDoneCfg f ((zipBits f left right).reverse ++ result)):=by
  have hp:sparseZipCoreProgram f=sparseZipProgram f:=by
    funext l
    cases l <;> rfl
  rw [hp]
  simpa [sparseZipLocalCfg,sparseZipLocalDoneCfg,sparseZipCfg,
    sparseZipDoneCfg,zipCfg,zipDoneCfg,zipPartialDoneCfg,
    mapAlphabetCfg] using!
      sparseZip_reaches_done f left right result hlen

def sparseSubLocalCfg (borrow:Bool) (left right result:List Bool):
    TM2.Cfg (fun _:AddStack => SparseSymbol) AddLabel SubControl where
  l:=some .loop
  var:= ⟨borrow,none,none⟩
  stk:=mapAlphabetStacks sparseBitEncode (addStackFamily left right result)

def sparseSubLocalDoneCfg (borrow:Bool) (result:List Bool):
    TM2.Cfg (fun _:AddStack => SparseSymbol) AddLabel SubControl where
  l:=some .done
  var:= ⟨borrow,none,none⟩
  stk:=mapAlphabetStacks sparseBitEncode (addStackFamily [] [] result)

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def prependLocalCfg (label:PrependCellLabel)
    (address value memory:List SparseSymbol):
    TM2.Cfg (fun _:PrependCellStack => SparseSymbol)
      PrependCellLabel PrependCellControl where
  l:=some label
  var:=default
  stk:=prependCellStacks address value memory

theorem prependLocal_fixed_correct (w a v:ℕ) (memory:List SparseSymbol):
    ((fun o => o.bind (TM2.step prependCoreProgram))^[2 * w + 5])
      (some (prependLocalCfg .cellEnd
        ((fixedBits w a).reverse.map SparseSymbol.bit)
        ((fixedBits w v).reverse.map SparseSymbol.bit) memory)) =
      some (prependLocalCfg .done [] [] (encodeSparseCell w (a,v) ++ memory)):=by
  have hp:prependCoreProgram=prependCellMachine.m:=by
    funext l
    rfl
  rw [hp]
  simpa [prependLocalCfg,prependCellCfg] using!
    prependCell_fixed_correct w a v memory

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

def countdownStacks (count temp:List Bool):CountdownStack -> List Bool
  | .count => count
  | .temp => temp

def countdownCfg (label:CountdownLabel) (state:CountdownControl)
    (count temp:List Bool):countdownMachine.Cfg where
  l:=some label
  var:=state
  stk:=countdownStacks count temp

def countdownBits:Bool -> List Bool -> List Bool
  | _, [] => []
  | borrow,bit::bits =>
      let r:=fullSubtractor bit false borrow
      r.1::countdownBits r.2 bits

@[simp] theorem countdownBits_length (borrow:Bool) (bits:List Bool):
    (countdownBits borrow bits).length=bits.length:=by
  induction bits generalizing borrow with
  | nil => rfl
  | cons bit bits ih => simp [countdownBits,ih]

theorem countdownBits_eq_subBits_zero (borrow:Bool) (bits:List Bool):
    countdownBits borrow bits =
      subBits bits (List.replicate bits.length false) borrow:=by
  induction bits generalizing borrow with
  | nil => rfl
  | cons bit bits ih =>
      simp [countdownBits,subBits,ih,List.replicate_succ]

@[simp] theorem countdown_step_scan_cons (state:CountdownControl)
    (bit:Bool) (bits temp:List Bool):
    countdownMachine.step (countdownCfg .scan state (bit::bits) temp) =
      some (countdownCfg .scan
        { held:=none
          borrow:=(fullSubtractor bit false state.borrow).2
          positiveSeen:=state.positiveSeen || bit }
        bits ((fullSubtractor bit false state.borrow).1::temp)):=by
  rcases state with ⟨held,borrow,positiveSeen⟩
  cases bit <;> cases borrow <;>
    simp [countdownMachine,countdownCfg,countdownStacks,
      countdownOutput,countdownAdvance,fullSubtractor,Function.update]
  all_goals
    congr 2
    funext k
    cases k <;> rfl

@[simp] theorem countdown_step_scan_nil (state:CountdownControl)
    (temp:List Bool):
    countdownMachine.step (countdownCfg .scan state [] temp) =
      some (countdownCfg
        (if state.positiveSeen then .restore else .zero)
        { state with held:=none } [] temp):=by
  cases h:state.positiveSeen <;>
    simp [countdownMachine,countdownCfg,countdownStacks,h]
  all_goals
    congr 2
    funext k
    cases k <;> rfl

theorem countdown_scan_iterate (state:CountdownControl)
    (bits temp:List Bool) (hheld:state.held=none):
    ((fun x:Option countdownMachine.Cfg =>
      x.bind countdownMachine.step)^[bits.length])
      (some (countdownCfg .scan state bits temp)) =
    some (countdownCfg .scan
      { held:=none
        borrow:=(subBorrowOut bits
          (List.replicate bits.length false) state.borrow)
        positiveSeen:=state.positiveSeen || containsTrue bits }
      [] ((countdownBits state.borrow bits).reverse ++ temp)):=by
  induction bits generalizing state temp with
  | nil =>
      cases state
      simp_all [countdownBits,subBorrowOut,containsTrue]
  | cons bit bits ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,countdown_step_scan_cons]
      rw [ih _ _ rfl]
      cases bit <;> cases state.borrow <;>
        simp [countdownBits,subBorrowOut,containsTrue,List.replicate_succ,
          List.reverse_cons,
          List.append_assoc,fullSubtractor,Bool.or_assoc]

@[simp] theorem countdown_step_restore_cons (state:CountdownControl)
    (count:List Bool) (bit:Bool) (bits:List Bool):
    countdownMachine.step
      (countdownCfg .restore state count (bit::bits)) =
    some (countdownCfg .restore { state with held:=none }
      (bit::count) bits):=by
  cases bit <;>
    simp [countdownMachine,countdownCfg,countdownStacks,
      countdownClearHeld,Function.update]
  all_goals
    congr 2
    funext k
    cases k <;> rfl

@[simp] theorem countdown_step_restore_nil (state:CountdownControl)
    (count:List Bool):
    countdownMachine.step (countdownCfg .restore state count []) =
      some (countdownCfg .positive { state with held:=none } count []):=by
  simp [countdownMachine,countdownCfg,countdownStacks]

theorem countdown_restore_iterate (state:CountdownControl)
    (count temp:List Bool) (hheld:state.held=none):
    ((fun x:Option countdownMachine.Cfg =>
      x.bind countdownMachine.step)^[temp.length])
      (some (countdownCfg .restore state count temp)) =
    some (countdownCfg .restore { state with held:=none }
      (temp.reverse ++ count) []):=by
  induction temp generalizing state count with
  | nil =>
      cases state
      simp_all
  | cons bit bits ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,countdown_step_restore_cons]
      rw [ih _ _ rfl]
      simp [List.reverse_cons,List.append_assoc]

@[simp] theorem countdownBits_zero_word (w:Nat):
    countdownBits true (List.replicate w false)=List.replicate w true:=by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ,countdownBits,fullSubtractor,ih]

@[simp] theorem subBorrowOut_zero_word (w:Nat):
    subBorrowOut (List.replicate w false) (List.replicate w false) true=true:=by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ,subBorrowOut,fullSubtractor,ih]

@[simp] theorem containsTrue_zero_word (w:Nat):
    containsTrue (List.replicate w false)=false:=by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ,containsTrue,ih]

theorem countdownMachine_zero_correct (w:Nat):
    ((fun x:Option countdownMachine.Cfg =>
      x.bind countdownMachine.step)^[w + 1])
      (some (countdownCfg .scan default (fixedBits w 0) [])) =
    some (countdownCfg .zero
      { held:=none,borrow:=true,positiveSeen:=false }
      [] (List.replicate w true)):=by
  have hscan:=countdown_scan_iterate default (fixedBits w 0) [] rfl
  simp only [fixedBits_length] at hscan
  simp only [show (default:CountdownControl).borrow=true by rfl,
    show (default:CountdownControl).positiveSeen=false by rfl,
    Bool.false_or] at hscan
  have hstep:=countdown_step_scan_nil
    ({ held:=none,borrow:=true,positiveSeen:=false }:CountdownControl)
    (List.replicate w true)
  rw [Nat.add_comm,Function.iterate_add_apply]
  have hscan':
      ((fun x:Option countdownMachine.Cfg =>
        x.bind countdownMachine.step)^[w])
        (some (countdownCfg .scan default (fixedBits w 0) [])) =
      some (countdownCfg .scan
        { held:=none,borrow:=true,positiveSeen:=false }
        [] (List.replicate w true)):=by
    simpa [fixedBits_zero] using hscan
  rw [hscan']
  simpa using hstep

theorem countdownMachine_positive_correct (w d:Nat)
    (hd0:0 < d) (hd:d < 2 ^ w):
    ∃ finalState,
      ((fun x:Option countdownMachine.Cfg =>
        x.bind countdownMachine.step)^[2 * w + 2])
        (some (countdownCfg .scan default (fixedBits w d) [])) =
      some (countdownCfg .positive finalState (fixedBits w (d - 1)) []):=by
  have htrue:containsTrue (fixedBits w d)=true:=by
    cases h:containsTrue (fixedBits w d) with
    | true => rfl
    | false =>
        have hz:=containsTrue_false_bitsValue_zero h
        rw [bitsValue_fixedBits_of_lt hd] at hz
        omega
  have hscan:=countdown_scan_iterate default (fixedBits w d) [] rfl
  simp only [List.append_nil,htrue,Bool.false_or,List.length_replicate,
    fixedBits_length,
    show (default:CountdownControl).borrow=true by rfl,
    show (default:CountdownControl).positiveSeen=false by rfl] at hscan
  let scanState:CountdownControl:=
    { held:=none
      borrow:=subBorrowOut (fixedBits w d) (List.replicate w false) true
      positiveSeen:=true }
  have htoRestore:=countdown_step_scan_nil scanState
    (countdownBits true (fixedBits w d)).reverse
  have hrestore:=countdown_restore_iterate { scanState with held:=none } []
    (countdownBits true (fixedBits w d)).reverse rfl
  simp only [List.length_reverse,countdownBits_length,
    fixedBits_length,List.reverse_reverse,List.append_nil] at hrestore
  have hdone:=countdown_step_restore_nil
    { scanState with held:=none }
    (countdownBits true (fixedBits w d))
  let stepO:=fun x:Option countdownMachine.Cfg =>
    x.bind countdownMachine.step
  have hchain {m n:Nat} {a b c:Option countdownMachine.Cfg}
      (h₁:(stepO^[m]) a=b) (h₂:(stepO^[n]) b=c):
      (stepO^[m + n]) a=c:=by
    rw [Nat.add_comm,Function.iterate_add_apply,h₁,h₂]
  have hall:=hchain (hchain (hchain hscan
    (show (stepO^[1]) _=_ by simpa [stepO,scanState] using htoRestore))
    hrestore) (show (stepO^[1]) _=_ by simpa [stepO] using hdone)
  have hbits:countdownBits true (fixedBits w d)=fixedBits w (d - 1):=by
    rw [countdownBits_eq_subBits_zero]
    simp only [fixedBits_length]
    rw [← fixedBits_zero w]
    rw [← fixedBits_sub_borrow w d 0 true
      (show 0 + true.toNat≤ d by simpa using! hd0)]
    simp
  refine ⟨{ scanState with held:=none }, ?_⟩
  have ht:w + 1 + w + 1=2 * w + 2:=by omega
  rw [ht] at hall
  simpa [hbits] using! hall

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

private theorem iterate_two_more_8d17a88a {X:Type} (f:X→ X) (n:ℕ)
    {x y:X} (h:(f^[n]) (f (f x))=y):
    (f^[n + 2]) x=y:=by
  rw [show n + 2=(n + 1) + 1 by omega,
    Function.iterate_succ_apply,Function.iterate_succ_apply]
  exact h

def addPipelineBase (left:List Bool)
    (base:CoreStack→ List SparseSymbol):CoreStack→ List SparseSymbol:=
  fun
  | .accumulator => left.map SparseSymbol.bit
  | .work0 | .work1 | .work2 | .work3
  | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

theorem moveOperand_add_bridge {R:Type} (left rightBits:List Bool)
    (base:CoreStack→ List SparseSymbol):
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens
      (Sum.inl AddLabel.loop:AddTailLabel R)
      (symbolMoveLocalCfg .done [] (rightBits.map SparseSymbol.bit))
      default (addPipelineBase left base) =
    lensRenamedCfg (Λx:=AddFinishLabel R) binaryCoreRenaming
      InterpreterMacroState.addLens
      (sparseAddLocalCfg false left rightBits []) default
      (addPipelineBase left base):=by
  simp [phaseReturnCfg,lensRenamedCfg,
    addPipelineBase,renamedStacks,symbolMoveCoreRenaming,
    symbolMoveCoreDecode,binaryCoreRenaming,binaryCoreDecode,
    symbolMoveLocalCfg,sparseAddLocalCfg,symbolMoveStacks,
    mapAlphabetStacks,addStackFamily]
  constructor
  · rfl
  · funext k
    cases k <;> first | rfl | simp [renamedStacks,binaryCoreRenaming,
      binaryCoreDecode,symbolMoveCoreRenaming,symbolMoveCoreDecode,
      mapAlphabetStacks,addStackFamily,symbolMoveStacks,List.map_reverse,
      sparseBitEncode,Function.update]

def addAfterState (left rightBits:List Bool):InterpreterMacroState:=
  InterpreterMacroState.addLens.put default
    ⟨addCarryOut left rightBits false,none,none⟩

theorem add_resultMove_bridge {R:Type} (left rightBits:List Bool)
    (base:CoreStack→ List SparseSymbol):
    phaseReturnCfg binaryCoreRenaming InterpreterMacroState.addLens
      (Sum.inl SymbolMoveLabel.loop:AddFinishLabel R)
      (sparseAddLocalDoneCfg (addCarryOut left rightBits false) []
        (addBits left rightBits false).reverse)
      default (addPipelineBase left base) =
    lensRenamedCfg (Λx:=R)
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop
        ((addBits left rightBits false).reverse.map SparseSymbol.bit) [])
      (addAfterState left rightBits) (addPipelineBase left base):=by
  simp [phaseReturnCfg,lensRenamedCfg,
    addAfterState,addPipelineBase,renamedStacks,symbolMoveCoreRenaming,
    symbolMoveCoreDecode,binaryCoreRenaming,binaryCoreDecode,
    symbolMoveLocalCfg,sparseAddLocalDoneCfg,symbolMoveStacks,
    mapAlphabetStacks,addStackFamily]
  constructor
  · rfl
  · funext k
    cases k <;> first | rfl | simp [renamedStacks,binaryCoreRenaming,
      binaryCoreDecode,symbolMoveCoreRenaming,symbolMoveCoreDecode,
      mapAlphabetStacks,addStackFamily,symbolMoveStacks,List.map_reverse,
      sparseBitEncode,Function.update]

theorem addPipeline_correct {R:Type} (returnLabel:R)
    (rightProgram:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      InterpreterMacroState)
    (left rightBits:List Bool) (hlen:left.length=rightBits.length)
    (base:CoreStack→ List SparseSymbol):
    ((fun o => o.bind (TM2.step (addPipelineProgram returnLabel rightProgram)))^[
      3 * left.length + 6])
      (some (lensRenamedCfg
        (symbolMoveCoreRenaming .work0 .work1 (by decide))
        InterpreterMacroState.moveLens
        (symbolMoveLocalCfg .loop (rightBits.reverse.map SparseSymbol.bit) [])
        default (addPipelineBase left base))) =
    some (mapLabelCfg (fun l:AddTailLabel R => Sum.inr l)
      (mapLabelCfg (fun l:AddFinishLabel R => Sum.inr l)
        (mapLabelCfg (fun l:R => Sum.inr l)
      (phaseReturnCfg
        (symbolMoveCoreRenaming .work0 .accumulator (by decide))
        InterpreterMacroState.moveLens returnLabel
        (symbolMoveLocalCfg .done []
          ((addBits left rightBits false).map SparseSymbol.bit))
        (addAfterState left rightBits) (addPipelineBase left base))))):=by
  let moveToOperand:=symbolMoveCoreRenaming .work0 .work1 (by decide)
  let moveToAccumulator:=symbolMoveCoreRenaming .work0 .accumulator (by decide)
  have h₁:=run_lensPhase_to_right moveToOperand
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl AddLabel.loop) (addTailProgram returnLabel rightProgram)
    (symbolMoveLocal_correct (rightBits.reverse.map SparseSymbol.bit) []) rfl
    default (addPipelineBase left base)
  simp only [List.length_map,List.length_reverse] at h₁
  simp only [List.append_nil] at h₁
  dsimp [moveToOperand] at h₁
  rw [show (rightBits.reverse.map SparseSymbol.bit).reverse =
      rightBits.map SparseSymbol.bit by simp] at h₁
  rw [moveOperand_add_bridge (R:=R) left rightBits base] at h₁
  have h₁':=iterate_two_more_8d17a88a
    (fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (AddPipelineLabel R) InterpreterMacroState) =>
      o.bind (TM2.step (addPipelineProgram returnLabel rightProgram)))
    rightBits.length
    (x:=some (lensRenamedCfg
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop (rightBits.reverse.map SparseSymbol.bit) [])
      default (addPipelineBase left base))) h₁
  have h₂:=run_lensPhase_to_right binaryCoreRenaming
    InterpreterMacroState.addLens sparseAddCoreProgram .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop) (addResultMoveProgram returnLabel rightProgram)
    (sparseAddLocal_correct false left rightBits [] hlen) rfl
    default (addPipelineBase left base)
  simp only [List.append_nil] at h₂
  rw [add_resultMove_bridge (R:=R) left rightBits base] at h₂
  have h₃:=run_lensPhase_to_right moveToAccumulator
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    returnLabel rightProgram
    (symbolMoveLocal_correct
      ((addBits left rightBits false).reverse.map SparseSymbol.bit) []) rfl
    (addAfterState left rightBits) (addPipelineBase left base)
  simp only [List.length_map,List.length_reverse] at h₃
  simp only [List.append_nil] at h₃
  simp only [List.map_reverse,List.reverse_reverse] at h₃
  have h₃raw:=h₃
  have h₃':
      ((fun o => o.bind (TM2.step
        (addResultMoveProgram returnLabel rightProgram)))^[
          (addBits left rightBits false).length + 2])
        (some (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .accumulator (by decide))
          InterpreterMacroState.moveLens
          (symbolMoveLocalCfg .loop
            ((addBits left rightBits false).reverse.map SparseSymbol.bit) [])
          (addAfterState left rightBits) (addPipelineBase left base))) =
        some (mapLabelCfg (fun l:R => Sum.inr l)
          (phaseReturnCfg
            (symbolMoveCoreRenaming .work0 .accumulator (by decide))
            InterpreterMacroState.moveLens returnLabel
            (symbolMoveLocalCfg .done []
              ((addBits left rightBits false).map SparseSymbol.bit))
            (addAfterState left rightBits) (addPipelineBase left base))):=by
    simpa [addResultMoveProgram,moveToAccumulator,
      List.map_reverse] using h₃raw
  have h₂₃:=chain_liftRightProgram
    (lensPhaseLeft binaryCoreRenaming InterpreterMacroState.addLens
      sparseAddCoreProgram .done (Sum.inl SymbolMoveLabel.loop))
    (addResultMoveProgram returnLabel rightProgram) h₂ h₃'
  have h:=chain_liftRightProgram
    (lensPhaseLeft moveToOperand InterpreterMacroState.moveLens
      symbolMoveCoreProgram .done (Sum.inl AddLabel.loop))
    (addTailProgram returnLabel rightProgram) h₁' h₂₃
  have hadd:(addBits left rightBits false).length=left.length:=
    addBits_length_of_eq false hlen
  rw [hadd] at h
  have htime:3 * left.length + 6 =
      rightBits.length + 2 + (left.length + 1 + 1 + (left.length + 2)):=by
    omega
  rw [htime]
  simpa [addPipelineProgram,moveToOperand] using h

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem closedAddPipelineProgram_done:
    closedAddPipelineProgram closedAddDone=.halt:=rfl

def addInitialLocal (w a b:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      FullAddLabel InterpreterMacroState:=
  lensRenamedCfg (Λx:=AddTailLabel Unit)
    (symbolMoveCoreRenaming .work0 .work1 (by decide))
    InterpreterMacroState.moveLens
    (symbolMoveLocalCfg .loop
      ((fixedBits w b).reverse.map SparseSymbol.bit) [])
    default (addPipelineBase (fixedBits w a)
      (operandBoundaryBase w a m base))

def addFinalLocal (w a b:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      FullAddLabel InterpreterMacroState:=
  mapLabelCfg (fun l:AddTailLabel Unit => Sum.inr l)
    (mapLabelCfg (fun l:AddFinishLabel Unit => Sum.inr l)
      (mapLabelCfg (fun l:Unit => Sum.inr l)
        (phaseReturnCfg
          (symbolMoveCoreRenaming .work0 .accumulator (by decide))
          InterpreterMacroState.moveLens ()
          (symbolMoveLocalCfg .done []
            ((addBits (fixedBits w a) (fixedBits w b) false).map
              SparseSymbol.bit))
          (addAfterState (fixedBits w a) (fixedBits w b))
          (addPipelineBase (fixedBits w a)
            (operandBoundaryBase w a m base)))))

theorem addPhase_return_bridge {N:Nat} {R:Type}
    (returnLabel:R) (w a b:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (ambient:FullInterpreterState N)
    (ambientStacks:CoreStack -> List SparseSymbol):
    phaseReturnCfg coreIdentityRenaming FullInterpreterState.macroLens
      returnLabel (addFinalLocal w a b m base) ambient ambientStacks =
    cleanReturnCfg returnLabel
      (FullInterpreterState.macroLens.put ambient
        (addFinalLocal w a b m base).var)
      (operandBoundaryBase w ((a + b) % 2 ^ w) m base):=by
  dsimp [addFinalLocal]
  simp [phaseReturnCfg,cleanReturnCfg,lensRenamedCfg,
    coreIdentityRenaming,renamedStacks_coreIdentity,addPipelineBase,
    operandBoundaryBase,symbolMoveCoreRenaming,symbolMoveCoreDecode,
    symbolMoveLocalCfg,symbolMoveStacks,renamedStacks,fixedBits_add,
    fixedBits_mod_word]
  funext k
  cases k <;> simp [addPipelineBase,operandBoundaryBase,
    symbolMoveCoreRenaming,symbolMoveCoreDecode,symbolMoveLocalCfg,
    symbolMoveStacks,renamedStacks,fixedBits_add,fixedBits_mod_word]

theorem fullAddPhase_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (ambient:FullInterpreterState N):
    ∃ finalState,
      ((fun o => o.bind (TM2.step
        (fullAddPhaseProgram returnLabel right)))^[3 * w + 7])
        (some (lensRenamedCfg coreIdentityRenaming
          FullInterpreterState.macroLens (addInitialLocal w a b m base)
          ambient (operandResultBase w a b m base))) =
      some (mapLabelCfg Sum.inr
        (cleanReturnCfg returnLabel finalState
          (operandBoundaryBase w ((a + b) % 2 ^ w) m base))):=by
  have hsmall:=addPipeline_correct () (fun _ => .halt)
    (fixedBits w a) (fixedBits w b) (by simp)
    (operandBoundaryBase w a m base)
  change _=some (addFinalLocal w a b m base) at hsmall
  have h:=run_lensPhase_to_right coreIdentityRenaming
    FullInterpreterState.macroLens closedAddPipelineProgram closedAddDone
    closedAddPipelineProgram_done returnLabel right hsmall rfl ambient
    (operandResultBase w a b m base)
  rw [addPhase_return_bridge returnLabel w a b m base ambient
    (operandResultBase w a b m base)] at h
  let finalState:=FullInterpreterState.macroLens.put ambient
    (addFinalLocal w a b m base).var
  refine ⟨finalState, ?_⟩
  simpa [fullAddPhaseProgram,addInitialLocal,finalState] using h

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

def accInstallBase (old value:List Bool)
    (base:CoreStack→ List SparseSymbol):CoreStack→ List SparseSymbol:=
  fun
  | .accumulator => old.map SparseSymbol.bit
  | .work0 => value.reverse.map SparseSymbol.bit
  | .work1 | .work2 | .work3 | .work4
  | .work5 | .work6 | .work7 => []
  | k => base k

def accInstallClearedBase (old value:List Bool)
    (base:CoreStack→ List SparseSymbol):CoreStack→ List SparseSymbol:=
  fun
  | .work0 => value.reverse.map SparseSymbol.bit
  | .work7 => old.reverse.map SparseSymbol.bit
  | .accumulator | .work1 | .work2 | .work3
  | .work4 | .work5 | .work6 => []
  | k => base k

theorem accInstall_clear_bridge {R:Type} (old value:List Bool)
    (base:CoreStack→ List SparseSymbol):
    phaseReturnCfg
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      InterpreterMacroState.moveLens
      (Sum.inl SymbolMoveLabel.loop:AccInstallTailLabel R)
      (symbolMoveLocalCfg .done [] (old.reverse.map SparseSymbol.bit))
      default (accInstallBase old value base) =
    lensRenamedCfg (Λx:=R)
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop
        (value.reverse.map SparseSymbol.bit) [])
      default (accInstallClearedBase old value base):=by
  simp [phaseReturnCfg,lensRenamedCfg,renamedStacks,
    symbolMoveCoreRenaming,symbolMoveCoreDecode,symbolMoveLocalCfg,
    symbolMoveStacks,accInstallBase,accInstallClearedBase]
  funext k
  cases k <;> simp [renamedStacks,symbolMoveCoreRenaming,
    symbolMoveCoreDecode,symbolMoveStacks,accInstallBase,
    accInstallClearedBase]

def accInstallFinalCfg {R:Type} (returnLabel:R)
    (old value:List Bool) (base:CoreStack→ List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (AccInstallLabel R) InterpreterMacroState:=
  mapLabelCfg (fun l:AccInstallTailLabel R => Sum.inr l)
    (mapLabelCfg (fun l:R => Sum.inr l)
      (phaseReturnCfg
        (symbolMoveCoreRenaming .work0 .accumulator (by decide))
        InterpreterMacroState.moveLens returnLabel
        (symbolMoveLocalCfg .done [] (value.map SparseSymbol.bit))
        default (accInstallClearedBase old value base)))

theorem accInstall_correct {R:Type} (returnLabel:R)
    (rightProgram:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      InterpreterMacroState)
    (old value:List Bool) (hlen:old.length=value.length)
    (base:CoreStack→ List SparseSymbol):
    ((fun o => o.bind (TM2.step
      (accInstallProgram returnLabel rightProgram)))^[
        2 * old.length + 4])
      (some (lensRenamedCfg
        (symbolMoveCoreRenaming .accumulator .work7 (by decide))
        InterpreterMacroState.moveLens
        (symbolMoveLocalCfg .loop (old.map SparseSymbol.bit) [])
        default (accInstallBase old value base))) =
    some (accInstallFinalCfg returnLabel old value base):=by
  let clearMove:=symbolMoveCoreRenaming .accumulator .work7 (by decide)
  let installMove:=symbolMoveCoreRenaming .work0 .accumulator (by decide)
  have h₁:=run_lensPhase_to_right clearMove
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop) (accInstallTailProgram returnLabel rightProgram)
    (symbolMoveLocal_correct (old.map SparseSymbol.bit) []) rfl
    default (accInstallBase old value base)
  simp only [List.length_map,List.append_nil] at h₁
  rw [show (old.map SparseSymbol.bit).reverse =
      old.reverse.map SparseSymbol.bit by simp] at h₁
  rw [accInstall_clear_bridge (R:=R) old value base] at h₁
  have h₂:=run_lensPhase_to_right installMove
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    returnLabel rightProgram
    (symbolMoveLocal_correct (value.reverse.map SparseSymbol.bit) []) rfl
    default (accInstallClearedBase old value base)
  simp only [List.length_map,List.length_reverse,List.append_nil] at h₂
  simp only [List.map_reverse,List.reverse_reverse] at h₂
  have h₂':
      ((fun o => o.bind (TM2.step
        (accInstallTailProgram returnLabel rightProgram)))^[
          value.length + 2])
        (some (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .accumulator (by decide))
          InterpreterMacroState.moveLens
          (symbolMoveLocalCfg .loop
            (value.reverse.map SparseSymbol.bit) [])
          default (accInstallClearedBase old value base))) =
      some (mapLabelCfg (fun l:R => Sum.inr l)
        (phaseReturnCfg
          (symbolMoveCoreRenaming .work0 .accumulator (by decide))
          InterpreterMacroState.moveLens returnLabel
          (symbolMoveLocalCfg .done [] (value.map SparseSymbol.bit))
          default (accInstallClearedBase old value base))):=by
    simpa [accInstallTailProgram,installMove] using h₂
  have h:=chain_liftRightProgram
    (lensPhaseLeft clearMove InterpreterMacroState.moveLens
      symbolMoveCoreProgram .done (Sum.inl SymbolMoveLabel.loop))
    (accInstallTailProgram returnLabel rightProgram) h₁ h₂'
  have htime:2 * old.length + 4 =
      (old.length + 2) + (value.length + 2):=by omega
  rw [htime]
  simpa [accInstallProgram,accInstallFinalCfg,clearMove] using h

theorem loadPipeline_fixed_correct {R:Type} (returnLabel:R)
    (rightProgram:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      InterpreterMacroState)
    (w accumulator value:ℕ)
    (base:CoreStack→ List SparseSymbol):
    ((fun o => o.bind (TM2.step
      (accInstallProgram returnLabel rightProgram)))^[2 * w + 4])
      (some (lensRenamedCfg
        (symbolMoveCoreRenaming .accumulator .work7 (by decide))
        InterpreterMacroState.moveLens
        (symbolMoveLocalCfg .loop
          ((fixedBits w accumulator).map SparseSymbol.bit) [])
        default
        (accInstallBase (fixedBits w accumulator) (fixedBits w value) base))) =
    some (accInstallFinalCfg returnLabel
      (fixedBits w accumulator) (fixedBits w value) base):=by
  simpa using accInstall_correct returnLabel rightProgram
    (fixedBits w accumulator) (fixedBits w value) (by simp) base

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem closedAccInstallProgram_done:
    closedAccInstallProgram closedAccInstallDone=.halt:=rfl

theorem accInstall_discard_bridge {N:Nat} {R:Type}
    (w old value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (ambient:FullInterpreterState N)
    (ambientStacks:CoreStack -> List SparseSymbol):
    phaseReturnCfg coreIdentityRenaming FullInterpreterState.macroLens
      (Sum.inl DiscardLabel.loop:FullLoadFinishLabel R)
      (accInstallFinalCfg () (fixedBits w old) (fixedBits w value)
        (operandBoundaryBase w old m base))
      ambient ambientStacks =
    lensRenamedCfg (discardCoreRenaming .work7)
        FullInterpreterState.moveLens
        (discardCfg .loop
          ((fixedBits w old).reverse.map SparseSymbol.bit))
        (FullInterpreterState.macroLens.put ambient
          (accInstallFinalCfg () (fixedBits w old) (fixedBits w value)
            (operandBoundaryBase w old m base)).var)
        (operandBoundaryBase w value m base):=by
  dsimp [accInstallFinalCfg]
  simp [phaseReturnCfg,accInstallFinalCfg,lensRenamedCfg,
    coreIdentityRenaming,renamedStacks_coreIdentity,
    discardCoreRenaming,discardCfg,discardStacks,
    accInstallClearedBase,operandBoundaryBase,
    symbolMoveCoreRenaming,symbolMoveCoreDecode,symbolMoveLocalCfg,
    symbolMoveStacks,renamedStacks,List.map_reverse]
  constructor
  · rfl
  · funext k
    cases k <;> simp [accInstallFinalCfg,accInstallClearedBase,
      operandBoundaryBase,symbolMoveCoreRenaming,symbolMoveCoreDecode,
      symbolMoveLocalCfg,symbolMoveStacks,renamedStacks,List.map_reverse]
      <;> rfl

theorem discard_loadReturn_bridge {N:Nat} {R:Type}
    (returnLabel:R) (w old value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    phaseReturnCfg (discardCoreRenaming .work7)
      FullInterpreterState.moveLens returnLabel
      (discardCfg .done []) state (operandBoundaryBase w value m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (operandBoundaryBase w value m base):=by
  simp [phaseReturnCfg,cleanReturnCfg,lensRenamedCfg,
    discardCoreRenaming,discardCfg,discardStacks,renamedStacks,
    operandBoundaryBase]
  funext k
  cases k <;> rfl

theorem fullLoadMacro_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w old value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (ambient:FullInterpreterState N):
    let initialLocal:=lensRenamedCfg (Λx:=AccInstallTailLabel Unit)
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop
        ((fixedBits w old).map SparseSymbol.bit) [])
      default
      (accInstallBase (fixedBits w old) (fixedBits w value)
        (operandBoundaryBase w old m base))
    ∃ finalState,
      ((fun o => o.bind (TM2.step
        (fullLoadProgram returnLabel right)))^[3 * w + 7])
        (some (lensRenamedCfg coreIdentityRenaming
          FullInterpreterState.macroLens initialLocal ambient
          (operandResultBase w old value m base))) =
      some (mapLabelCfg (fun l:FullLoadFinishLabel R => Sum.inr l)
        (mapLabelCfg (fun l:R => Sum.inr l)
          (cleanReturnCfg returnLabel finalState
            (operandBoundaryBase w value m base)))):=by
  dsimp only
  let initialLocal:=lensRenamedCfg (Λx:=AccInstallTailLabel Unit)
    (symbolMoveCoreRenaming .accumulator .work7 (by decide))
    InterpreterMacroState.moveLens
    (symbolMoveLocalCfg .loop
      ((fixedBits w old).map SparseSymbol.bit) [])
    default
    (accInstallBase (fixedBits w old) (fixedBits w value)
      (operandBoundaryBase w old m base))
  have hsmall:=loadPipeline_fixed_correct () (fun _ => .halt)
    w old value (operandBoundaryBase w old m base)
  have hacc:=run_lensPhase_to_right coreIdentityRenaming
    FullInterpreterState.macroLens closedAccInstallProgram
    closedAccInstallDone closedAccInstallProgram_done
    (Sum.inl DiscardLabel.loop) (fullLoadFinishProgram returnLabel right)
    hsmall rfl ambient (operandResultBase w old value m base)
  rw [accInstall_discard_bridge (R:=R) w old value m base ambient
    (operandResultBase w old value m base)] at hacc
  let stateAfterAcc:=FullInterpreterState.macroLens.put ambient
    (accInstallFinalCfg () (fixedBits w old) (fixedBits w value)
      (operandBoundaryBase w old m base)).var
  have hdiscard:=run_lensPhase_to_right
    (discardCoreRenaming .work7) FullInterpreterState.moveLens
    discardProgram .done (by rfl) returnLabel right
    (discard_correct
      ((fixedBits w old).reverse.map SparseSymbol.bit)) rfl
    stateAfterAcc (operandBoundaryBase w value m base)
  simp only [List.length_map,List.length_reverse,fixedBits_length] at hdiscard
  rw [discard_loadReturn_bridge returnLabel w old value m base stateAfterAcc]
    at hdiscard
  have hchain:=chain_liftRightProgram
    (lensPhaseLeft coreIdentityRenaming FullInterpreterState.macroLens
      closedAccInstallProgram closedAccInstallDone
      (Sum.inl DiscardLabel.loop))
    (fullLoadFinishProgram returnLabel right) hacc hdiscard
  refine ⟨FullInterpreterState.moveLens.put stateAfterAcc default, ?_⟩
  have htime:3 * w + 7=(2 * w + 4 + 1) + (w + 1 + 1):=by omega
  rw [htime]
  simpa [fullLoadProgram,initialLocal,stateAfterAcc] using hchain

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

def loadInitialLocal (w old value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      ClosedAccInstallLabel InterpreterMacroState:=
  lensRenamedCfg (Λx:=AccInstallTailLabel Unit)
    (symbolMoveCoreRenaming .accumulator .work7 (by decide))
    InterpreterMacroState.moveLens
    (symbolMoveLocalCfg .loop ((fixedBits w old).map SparseSymbol.bit) [])
    default
    (accInstallBase (fixedBits w old) (fixedBits w value)
      (operandBoundaryBase w old m base))

theorem loadReset_step {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w old value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    TM2.step (loadInstructionTailProgram returnLabel right)
      (cleanReturnCfg (Sum.inl LoadResetLabel.reset)
        state (operandResultBase w old value m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg coreIdentityRenaming FullInterpreterState.macroLens
        (loadInitialLocal w old value m base) state
        (operandResultBase w old value m base))):=by
  simp [loadInstructionTailProgram,loadResetProgram,cleanReturnCfg,
    mapLabelCfg,liftRightProgram,TM2.step,lensRenamedCfg,
    loadInitialLocal,coreIdentityRenaming,renamedStacks_coreIdentity]
  constructor
  · rfl
  · constructor
    · rfl
    · funext k
      cases k <;> simp [loadInitialLocal,lensRenamedCfg,renamedStacks,
        coreIdentityRenaming,accInstallBase,operandBoundaryBase,
        operandResultBase,symbolMoveCoreRenaming,symbolMoveCoreDecode,
        symbolMoveLocalCfg,symbolMoveStacks,List.map_reverse]

theorem chain_loadInstruction_iterations {X:Type} (step:X -> X)
    {a b c:X} {m n:Nat}
    (h1:(step^[m]) a=b) (h2:(step^[n]) b=c):
    (step^[m + n]) a=c:=by
  rw [Nat.add_comm,Function.iterate_add_apply,h1,h2]

theorem loadInstruction_correct {N:Nat} {R:Type}
    (o:Op) (hN:operandArgument o <= N)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w old:Nat) (m:SparseMemory) (hm:m.Normalized w)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ steps,steps <= loadInstructionBound w m∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (loadInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=LoadInstructionTailLabel R) o hN w old m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l:FullLoadLabel R => Sum.inr l)
          (mapLabelCfg (fun l:FullLoadFinishLabel R => Sum.inr l)
            (mapLabelCfg (fun l:R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w (operandWordValue w o m) m base)))))):=by
  rcases operandEval_correct o hN w old m hm
      (Sum.inl LoadResetLabel.reset)
      (loadInstructionTailProgram returnLabel right) state base with
    ⟨operandSteps,operandBound,operandState,hoperand⟩
  have hresetStep:=loadReset_step returnLabel right w old
    (operandWordValue w o m) m base operandState
  have hreset:
      ((fun x => x.bind (TM2.step
        (loadInstructionTailProgram returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl LoadResetLabel.reset)
          operandState
          (operandResultBase w old (operandWordValue w o m) m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg coreIdentityRenaming
          FullInterpreterState.macroLens
          (loadInitialLocal w old (operandWordValue w o m) m base)
          operandState
          (operandResultBase w old (operandWordValue w o m) m base))):=by
    simpa using hresetStep
  rcases fullLoadMacro_correct returnLabel right w old
      (operandWordValue w o m) m base operandState with
    ⟨loadState,hload⟩
  have htail:=chain_liftRightProgram loadResetProgram
    (fullLoadProgram returnLabel right) hreset hload
  have hlift:=transport_iterate_operand_right o
    (Sum.inl LoadResetLabel.reset)
    (loadInstructionTailProgram returnLabel right) htail
  have hchain:=chain_loadInstruction_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (LoadInstructionLabel o R) (FullInterpreterState N)) =>
      x.bind (TM2.step (loadInstructionProgram o returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (1 + (3 * w + 7)), ?_,loadState, ?_⟩
  · simp [loadInstructionBound]
    omega
  · simpa [loadInstructionProgram,loadInstructionTailProgram] using hchain

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

theorem addReset_step {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    TM2.step (addInstructionTailProgram returnLabel right)
      (cleanReturnCfg (Sum.inl AddResetLabel.reset)
        state (operandResultBase w a b m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg coreIdentityRenaming FullInterpreterState.macroLens
        (addInitialLocal w a b m base) state
        (operandResultBase w a b m base))):=by
  simp [addInstructionTailProgram,addResetProgram,cleanReturnCfg,
    mapLabelCfg,liftRightProgram,TM2.step,lensRenamedCfg,
    addInitialLocal,coreIdentityRenaming]
  constructor
  · rfl
  · constructor
    · rfl
    · funext k
      cases k <;> simp [addInitialLocal,lensRenamedCfg,renamedStacks,
        coreIdentityRenaming,addPipelineBase,operandBoundaryBase,
        operandResultBase,symbolMoveCoreRenaming,symbolMoveCoreDecode,
        symbolMoveLocalCfg,symbolMoveStacks,List.map_reverse]

theorem addInstruction_correct {N:Nat} {R:Type}
    (o:Op) (hN:operandArgument o <= N)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a:Nat) (m:SparseMemory) (hm:m.Normalized w)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ steps,steps <= addInstructionBound w m∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (addInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=AddInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l:FullAddPhaseLabel R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w
                ((a + operandWordValue w o m) % 2 ^ w) m base))))):=by
  rcases operandEval_correct o hN w a m hm
      (Sum.inl AddResetLabel.reset)
      (addInstructionTailProgram returnLabel right) state base with
    ⟨operandSteps,operandBound,operandState,hoperand⟩
  have hresetStep:=addReset_step returnLabel right w a
    (operandWordValue w o m) m base operandState
  have hreset:
      ((fun x => x.bind (TM2.step
        (addInstructionTailProgram returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl AddResetLabel.reset)
          operandState
          (operandResultBase w a (operandWordValue w o m) m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg coreIdentityRenaming FullInterpreterState.macroLens
          (addInitialLocal w a (operandWordValue w o m) m base)
          operandState
          (operandResultBase w a (operandWordValue w o m) m base))):=by
    simpa using hresetStep
  rcases fullAddPhase_correct returnLabel right w a
      (operandWordValue w o m) m base operandState with
    ⟨addState,hadd⟩
  have htail:=chain_liftRightProgram addResetProgram
    (fullAddPhaseProgram returnLabel right) hreset hadd
  have hlift:=transport_iterate_operand_right o
    (Sum.inl AddResetLabel.reset)
    (addInstructionTailProgram returnLabel right) htail
  have hchain:=chain_loadInstruction_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (AddInstructionLabel o R) (FullInterpreterState N)) =>
      x.bind (TM2.step (addInstructionProgram o returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (1 + (3 * w + 7)), ?_,addState, ?_⟩
  · simp [addInstructionBound]
    omega
  · simpa [addInstructionProgram,addInstructionTailProgram] using hchain

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

private theorem iterate_two_more_1f9c1b88 {X:Type} (f:X→ X) (n:ℕ)
    {x y:X} (h:(f^[n]) (f (f x))=y):
    (f^[n + 2]) x=y:=by
  rw [show n + 2=(n + 1) + 1 by omega,
    Function.iterate_succ_apply,Function.iterate_succ_apply]
  exact h

private theorem zipBits_length_of_eq (f:Bool→ Bool→ Bool)
    {left right:List Bool} (h:left.length=right.length):
    (zipBits f left right).length=left.length:=by
  induction left generalizing right with
  | nil => simp [zipBits]
  | cons a left ih =>
      cases right with
      | nil => simp at h
      | cons b right =>
          have htail:left.length=right.length:=by simpa using h
          simp [zipBits,ih htail]

def zipPipelineBase (left:List Bool)
    (base:CoreStack→ List SparseSymbol):CoreStack→ List SparseSymbol:=
  fun
  | .accumulator => left.map SparseSymbol.bit
  | .work0 | .work1 | .work2 | .work3
  | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

theorem moveOperand_zip_bridge {R:Type} (f:Bool→ Bool→ Bool)
    (left rightBits:List Bool)
    (base:CoreStack→ List SparseSymbol):
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens
      (Sum.inl AddLabel.loop:ZipTailLabel R)
      (symbolMoveLocalCfg .done [] (rightBits.map SparseSymbol.bit))
      default (zipPipelineBase left base) =
    lensRenamedCfg (Λx:=ZipFinishLabel R) binaryCoreRenaming
      InterpreterMacroState.zipLens
      (sparseZipLocalCfg f left rightBits []) default
      (zipPipelineBase left base):=by
  simp [phaseReturnCfg,lensRenamedCfg,
    zipPipelineBase,renamedStacks,symbolMoveCoreRenaming,
    symbolMoveCoreDecode,binaryCoreRenaming,binaryCoreDecode,
    symbolMoveLocalCfg,sparseZipLocalCfg,symbolMoveStacks,
    mapAlphabetStacks,addStackFamily]
  constructor
  · rfl
  · funext k
    cases k <;> first | rfl | simp [renamedStacks,binaryCoreRenaming,
      binaryCoreDecode,symbolMoveCoreRenaming,symbolMoveCoreDecode,
      mapAlphabetStacks,addStackFamily,symbolMoveStacks,List.map_reverse,
      sparseBitEncode,Function.update]

def zipAfterState (left rightBits:List Bool):InterpreterMacroState:=
  InterpreterMacroState.zipLens.put default
    ⟨none,none⟩

theorem zip_resultMove_bridge {R:Type} (f:Bool→ Bool→ Bool)
    (left rightBits:List Bool)
    (base:CoreStack→ List SparseSymbol):
    phaseReturnCfg binaryCoreRenaming InterpreterMacroState.zipLens
      (Sum.inl SymbolMoveLabel.loop:ZipFinishLabel R)
      (sparseZipLocalDoneCfg f (zipBits f left rightBits).reverse)
      default (zipPipelineBase left base) =
    lensRenamedCfg (Λx:=R)
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop
        ((zipBits f left rightBits).reverse.map SparseSymbol.bit) [])
      (zipAfterState left rightBits) (zipPipelineBase left base):=by
  simp [phaseReturnCfg,lensRenamedCfg,
    zipAfterState,zipPipelineBase,renamedStacks,symbolMoveCoreRenaming,
    symbolMoveCoreDecode,binaryCoreRenaming,binaryCoreDecode,
    symbolMoveLocalCfg,sparseZipLocalDoneCfg,symbolMoveStacks,
    mapAlphabetStacks,addStackFamily]
  constructor
  · rfl
  · funext k
    cases k <;> first | rfl | simp [renamedStacks,binaryCoreRenaming,
      binaryCoreDecode,symbolMoveCoreRenaming,symbolMoveCoreDecode,
      mapAlphabetStacks,addStackFamily,symbolMoveStacks,List.map_reverse,
      sparseBitEncode,Function.update]

theorem zipPipeline_correct {R:Type} (f:Bool→ Bool→ Bool)
    (returnLabel:R)
    (rightProgram:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      InterpreterMacroState)
    (left rightBits:List Bool) (hlen:left.length=rightBits.length)
    (base:CoreStack→ List SparseSymbol):
    ((fun o => o.bind (TM2.step (zipPipelineProgram f returnLabel rightProgram)))^[
      3 * left.length + 6])
      (some (lensRenamedCfg
        (symbolMoveCoreRenaming .work0 .work1 (by decide))
        InterpreterMacroState.moveLens
        (symbolMoveLocalCfg .loop (rightBits.reverse.map SparseSymbol.bit) [])
        default (zipPipelineBase left base))) =
    some (mapLabelCfg (fun l:ZipTailLabel R => Sum.inr l)
      (mapLabelCfg (fun l:ZipFinishLabel R => Sum.inr l)
        (mapLabelCfg (fun l:R => Sum.inr l)
      (phaseReturnCfg
        (symbolMoveCoreRenaming .work0 .accumulator (by decide))
        InterpreterMacroState.moveLens returnLabel
        (symbolMoveLocalCfg .done []
          ((zipBits f left rightBits).map SparseSymbol.bit))
        (zipAfterState left rightBits) (zipPipelineBase left base))))):=by
  let moveToOperand:=symbolMoveCoreRenaming .work0 .work1 (by decide)
  let moveToAccumulator:=symbolMoveCoreRenaming .work0 .accumulator (by decide)
  have h₁:=run_lensPhase_to_right moveToOperand
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl AddLabel.loop) (zipTailProgram f returnLabel rightProgram)
    (symbolMoveLocal_correct (rightBits.reverse.map SparseSymbol.bit) []) rfl
    default (zipPipelineBase left base)
  simp only [List.length_map,List.length_reverse] at h₁
  simp only [List.append_nil] at h₁
  dsimp [moveToOperand] at h₁
  rw [show (rightBits.reverse.map SparseSymbol.bit).reverse =
      rightBits.map SparseSymbol.bit by simp] at h₁
  rw [moveOperand_zip_bridge (R:=R) f left rightBits base] at h₁
  have h₁':=iterate_two_more_1f9c1b88
    (fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (ZipPipelineLabel R) InterpreterMacroState) =>
      o.bind (TM2.step (zipPipelineProgram f returnLabel rightProgram)))
    rightBits.length
    (x:=some (lensRenamedCfg
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens
      (symbolMoveLocalCfg .loop (rightBits.reverse.map SparseSymbol.bit) [])
      default (zipPipelineBase left base))) h₁
  have h₂:=run_lensPhase_to_right binaryCoreRenaming
    InterpreterMacroState.zipLens (sparseZipCoreProgram f) .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop) (zipResultMoveProgram returnLabel rightProgram)
    (sparseZipLocal_correct f left rightBits [] hlen) rfl
    default (zipPipelineBase left base)
  simp only [List.append_nil] at h₂
  rw [zip_resultMove_bridge (R:=R) f left rightBits base] at h₂
  have h₃:=run_lensPhase_to_right moveToAccumulator
    InterpreterMacroState.moveLens symbolMoveCoreProgram .done (by rfl)
    returnLabel rightProgram
    (symbolMoveLocal_correct
      ((zipBits f left rightBits).reverse.map SparseSymbol.bit) []) rfl
    (zipAfterState left rightBits) (zipPipelineBase left base)
  simp only [List.length_map,List.length_reverse] at h₃
  simp only [List.append_nil] at h₃
  simp only [List.map_reverse,List.reverse_reverse] at h₃
  have h₃raw:=h₃
  have h₃':
      ((fun o => o.bind (TM2.step
        (zipResultMoveProgram returnLabel rightProgram)))^[
          (zipBits f left rightBits).length + 2])
        (some (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .accumulator (by decide))
          InterpreterMacroState.moveLens
          (symbolMoveLocalCfg .loop
            ((zipBits f left rightBits).reverse.map SparseSymbol.bit) [])
          (zipAfterState left rightBits) (zipPipelineBase left base))) =
        some (mapLabelCfg (fun l:R => Sum.inr l)
          (phaseReturnCfg
            (symbolMoveCoreRenaming .work0 .accumulator (by decide))
            InterpreterMacroState.moveLens returnLabel
            (symbolMoveLocalCfg .done []
              ((zipBits f left rightBits).map SparseSymbol.bit))
            (zipAfterState left rightBits) (zipPipelineBase left base))):=by
    simpa [zipResultMoveProgram,moveToAccumulator,
      List.map_reverse] using h₃raw
  have h₂₃:=chain_liftRightProgram
    (lensPhaseLeft binaryCoreRenaming InterpreterMacroState.zipLens
      (sparseZipCoreProgram f) .done (Sum.inl SymbolMoveLabel.loop))
    (zipResultMoveProgram returnLabel rightProgram) h₂ h₃'
  have h:=chain_liftRightProgram
    (lensPhaseLeft moveToOperand InterpreterMacroState.moveLens
      symbolMoveCoreProgram .done (Sum.inl AddLabel.loop))
    (zipTailProgram f returnLabel rightProgram) h₁' h₂₃
  have hadd:(zipBits f left rightBits).length=left.length:=
    zipBits_length_of_eq f hlen
  rw [hadd] at h
  have htime:3 * left.length + 6 =
      rightBits.length + 2 + (left.length + 1 + 1 + (left.length + 2)):=by
    omega
  rw [htime]
  simpa [zipPipelineProgram,moveToOperand] using h

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem closedZipProgram_done (f:Bool -> Bool -> Bool):
    closedZipProgram f closedZipDone=.halt:=rfl

def zipInitialLocal (f:Bool -> Bool -> Bool) (w a b:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      ClosedZipLabel InterpreterMacroState:=
  lensRenamedCfg (Λx:=ZipTailLabel Unit)
    (symbolMoveCoreRenaming .work0 .work1 (by decide))
    InterpreterMacroState.moveLens
    (symbolMoveLocalCfg .loop
      ((fixedBits w b).reverse.map SparseSymbol.bit) [])
    default (zipPipelineBase (fixedBits w a)
      (operandBoundaryBase w a m base))

def zipFinalLocal (f:Bool -> Bool -> Bool) (w a b:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol)
      ClosedZipLabel InterpreterMacroState:=
  mapLabelCfg (fun l:ZipTailLabel Unit => Sum.inr l)
    (mapLabelCfg (fun l:ZipFinishLabel Unit => Sum.inr l)
      (mapLabelCfg (fun l:Unit => Sum.inr l)
        (phaseReturnCfg
          (symbolMoveCoreRenaming .work0 .accumulator (by decide))
          InterpreterMacroState.moveLens ()
          (symbolMoveLocalCfg .done []
            ((zipBits f (fixedBits w a) (fixedBits w b)).map
              SparseSymbol.bit))
          (zipAfterState (fixedBits w a) (fixedBits w b))
          (zipPipelineBase (fixedBits w a)
            (operandBoundaryBase w a m base)))))

theorem zipPhase_return_bridge {N:Nat} {R:Type}
    (f:Bool -> Bool -> Bool) (w a b result:Nat)
    (hresult:fixedBits w result =
      zipBits f (fixedBits w a) (fixedBits w b))
    (returnLabel:R) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (ambient:FullInterpreterState N)
    (ambientStacks:CoreStack -> List SparseSymbol):
    phaseReturnCfg coreIdentityRenaming FullInterpreterState.macroLens
      returnLabel (zipFinalLocal f w a b m base) ambient ambientStacks =
    cleanReturnCfg returnLabel
      (FullInterpreterState.macroLens.put ambient
        (zipFinalLocal f w a b m base).var)
      (operandBoundaryBase w (result % 2 ^ w) m base):=by
  dsimp [zipFinalLocal]
  simp [phaseReturnCfg,cleanReturnCfg,lensRenamedCfg,
    coreIdentityRenaming,zipPipelineBase,operandBoundaryBase,
    symbolMoveCoreRenaming,symbolMoveCoreDecode,symbolMoveLocalCfg,
    symbolMoveStacks,renamedStacks,fixedBits_mod_word, ← hresult]
  funext k
  cases k <;> simp [zipPipelineBase,operandBoundaryBase,
    symbolMoveCoreRenaming,symbolMoveCoreDecode,symbolMoveLocalCfg,
    symbolMoveStacks,renamedStacks,fixedBits_mod_word, ← hresult]

theorem fullZipPhase_correct {N:Nat} {R:Type}
    (f:Bool -> Bool -> Bool) (w a b result:Nat)
    (hresult:fixedBits w result =
      zipBits f (fixedBits w a) (fixedBits w b))
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (ambient:FullInterpreterState N):
    ∃ finalState,
      ((fun o => o.bind (TM2.step
        (fullZipPhaseProgram f returnLabel right)))^[3 * w + 7])
        (some (lensRenamedCfg coreIdentityRenaming
          FullInterpreterState.macroLens (zipInitialLocal f w a b m base)
          ambient (operandResultBase w a b m base))) =
      some (mapLabelCfg Sum.inr
        (cleanReturnCfg returnLabel finalState
          (operandBoundaryBase w (result % 2 ^ w) m base))):=by
  have hsmall:=zipPipeline_correct f () (fun _ => .halt)
    (fixedBits w a) (fixedBits w b) (by simp)
    (operandBoundaryBase w a m base)
  change _=some (zipFinalLocal f w a b m base) at hsmall
  have h:=run_lensPhase_to_right coreIdentityRenaming
    FullInterpreterState.macroLens (closedZipProgram f) closedZipDone
    (closedZipProgram_done f) returnLabel right hsmall rfl ambient
    (operandResultBase w a b m base)
  rw [zipPhase_return_bridge f w a b result hresult returnLabel m base
    ambient (operandResultBase w a b m base)] at h
  refine ⟨FullInterpreterState.macroLens.put ambient
    (zipFinalLocal f w a b m base).var, ?_⟩
  simpa [fullZipPhaseProgram,zipInitialLocal] using h

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

theorem zipReset_step {N:Nat} {R:Type}
    (f:Bool -> Bool -> Bool) (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    TM2.step (zipInstructionTailProgram f returnLabel right)
      (cleanReturnCfg (Sum.inl ZipResetLabel.reset)
        state (operandResultBase w a b m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg coreIdentityRenaming FullInterpreterState.macroLens
        (zipInitialLocal f w a b m base) state
        (operandResultBase w a b m base))):=by
  simp [zipInstructionTailProgram,zipResetProgram,cleanReturnCfg,
    mapLabelCfg,liftRightProgram,TM2.step,lensRenamedCfg,
    zipInitialLocal,coreIdentityRenaming]
  constructor
  · rfl
  · constructor
    · rfl
    · funext k
      cases k <;> simp [zipInitialLocal,lensRenamedCfg,renamedStacks,
        coreIdentityRenaming,zipPipelineBase,operandBoundaryBase,
        operandResultBase,symbolMoveCoreRenaming,symbolMoveCoreDecode,
        symbolMoveLocalCfg,symbolMoveStacks,List.map_reverse]

theorem zipInstruction_correct {N:Nat} {R:Type}
    (f:Bool -> Bool -> Bool) (o:Op) (hN:operandArgument o <= N)
    (w a result:Nat) (m:SparseMemory)
    (hresult:fixedBits w result =
      zipBits f (fixedBits w a) (fixedBits w (operandWordValue w o m)))
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (hm:m.Normalized w)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ steps,steps <= zipInstructionBound w m∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (zipInstructionProgram f o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=ZipInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l:FullZipPhaseLabel R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w (result % 2 ^ w) m base))))):=by
  rcases operandEval_correct o hN w a m hm
      (Sum.inl ZipResetLabel.reset)
      (zipInstructionTailProgram f returnLabel right) state base with
    ⟨operandSteps,operandBound,operandState,hoperand⟩
  have hresetStep:=zipReset_step f returnLabel right w a
    (operandWordValue w o m) m base operandState
  have hreset:
      ((fun x => x.bind (TM2.step
        (zipInstructionTailProgram f returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl ZipResetLabel.reset)
          operandState
          (operandResultBase w a (operandWordValue w o m) m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg coreIdentityRenaming FullInterpreterState.macroLens
          (zipInitialLocal f w a (operandWordValue w o m) m base)
          operandState
          (operandResultBase w a (operandWordValue w o m) m base))):=by
    simpa using hresetStep
  rcases fullZipPhase_correct f w a (operandWordValue w o m) result hresult
      returnLabel right m base operandState with ⟨zipState,hzip⟩
  have htail:=chain_liftRightProgram zipResetProgram
    (fullZipPhaseProgram f returnLabel right) hreset hzip
  have hlift:=transport_iterate_operand_right o
    (Sum.inl ZipResetLabel.reset)
    (zipInstructionTailProgram f returnLabel right) htail
  have hchain:=chain_loadInstruction_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (ZipInstructionLabel o R) (FullInterpreterState N)) =>
      x.bind (TM2.step (zipInstructionProgram f o returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (1 + (3 * w + 7)), ?_,zipState, ?_⟩
  · simp [zipInstructionBound]
    omega
  · simpa [zipInstructionProgram,zipInstructionTailProgram] using hchain

def BitwiseKind.natFn (w:Nat):BitwiseKind -> Nat -> Nat -> Nat
  | .and => Nat.land
  | .or => Nat.lor
  | .xor => Nat.xor
  | .compl => fun a _ => 2 ^ w - 1 - a % 2 ^ w

theorem fixedBits_bitwiseKind (kind:BitwiseKind) (w a b:Nat):
    fixedBits w (kind.natFn w a b) =
      zipBits kind.boolFn (fixedBits w a) (fixedBits w b):=by
  cases kind with
  | and => exact fixedBits_land w a b
  | or => exact fixedBits_lor w a b
  | xor => exact fixedBits_xor w a b
  | compl => exact fixedBits_complement w a b

theorem bitwiseInstruction_correct {N:Nat} {R:Type}
    (kind:BitwiseKind) (o:Op) (hN:operandArgument o <= N)
    (w a:Nat) (m:SparseMemory) (hm:m.Normalized w)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ steps,steps <= zipInstructionBound w m∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (bitwiseInstructionProgram kind o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=ZipInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l:FullZipPhaseLabel R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w
                (kind.natFn w a (operandWordValue w o m) % 2 ^ w)
                m base))))):=by
  simpa [bitwiseInstructionProgram] using
    zipInstruction_correct kind.boolFn o hN w a
      (kind.natFn w a (operandWordValue w o m)) m
      (fixedBits_bitwiseKind kind w a (operandWordValue w o m))
      returnLabel right hm base state

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

def writeResultBase (w accumulator value:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .output => .wordEnd::
      (fixedBits w value).reverse.map SparseSymbol.bit ++ base .output
  | .work0 | .work1 | .work2 | .work3
  | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def writeMove1Base (w accumulator value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):=
  operandResultBase w accumulator value m base

def writeMove2Base (w accumulator value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work1 => (fixedBits w value).map SparseSymbol.bit
  | .work0 | .work2 | .work3 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def writeBeforeFinishBase (w accumulator value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .output => (fixedBits w value).reverse.map SparseSymbol.bit ++ base .output
  | .work0 | .work1 | .work2 | .work3 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

theorem writeReset_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    ((fun o => o.bind (TM2.step (writeTailProgram returnLabel right)))^[1])
      (some (cleanReturnCfg (Sum.inl WriteResetLabel.reset) state
        (operandResultBase w accumulator value m base))) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg
        (symbolMoveCoreRenaming .work0 .work1 (by decide))
        FullInterpreterState.moveLens
        (symbolMoveLocalCfg .loop
          ((fixedBits w value).reverse.map SparseSymbol.bit) [])
        (FullInterpreterState.moveLens.put state default)
        (writeMove1Base w accumulator value m base))):=by
  simp [writeTailProgram,writeResetProgram,cleanReturnCfg,liftRightProgram,
    mapLabelCfg,TM2.step,lensRenamedCfg,writeMove1Base,
    operandResultBase,renamedStacks,symbolMoveCoreRenaming,
    symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks,symbolMoveCoreRenaming,
      symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks,
      operandResultBase,writeMove1Base]

theorem writeMove1_bridge {N:Nat} {R:Type}
    (w accumulator value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    phaseReturnCfg (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl SymbolMoveLabel.loop:WriteMove2Label R)
      (symbolMoveLocalCfg .done []
        ((fixedBits w value).map SparseSymbol.bit))
      state (writeMove1Base w accumulator value m base) =
    lensRenamedCfg (symbolMoveCoreRenaming .work1 .output (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((fixedBits w value).map SparseSymbol.bit) (base .output))
      (FullInterpreterState.moveLens.put state default)
      (writeMove2Base w accumulator value m base):=by
  simp [phaseReturnCfg,lensRenamedCfg,writeMove1Base,writeMove2Base,
    operandResultBase,renamedStacks,symbolMoveCoreRenaming,
    symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks]
  constructor
  · rfl
  · funext k
    cases k <;> simp [writeMove1Base,writeMove2Base,operandResultBase,
      renamedStacks,symbolMoveCoreRenaming,symbolMoveCoreDecode,
      symbolMoveLocalCfg,symbolMoveStacks]

theorem writeMove2_finish_bridge {N:Nat} {R:Type}
    (w accumulator value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    phaseReturnCfg (symbolMoveCoreRenaming .work1 .output (by decide))
      FullInterpreterState.moveLens
      (Sum.inl WriteFinishLabel.finish:WriteAfterLabel R)
      (symbolMoveLocalCfg .done []
        (((fixedBits w value).map SparseSymbol.bit).reverse ++ base .output))
      state (writeMove2Base w accumulator value m base) =
    cleanReturnCfg (Sum.inl WriteFinishLabel.finish)
      (FullInterpreterState.moveLens.put state default)
      (writeBeforeFinishBase w accumulator value m base):=by
  simp [phaseReturnCfg,cleanReturnCfg,lensRenamedCfg,
    writeMove2Base,writeBeforeFinishBase,renamedStacks,
    symbolMoveCoreRenaming,symbolMoveCoreDecode,symbolMoveLocalCfg,
    symbolMoveStacks]
  funext k
  cases k <;> simp [writeMove2Base,writeBeforeFinishBase,
    renamedStacks,symbolMoveCoreRenaming,symbolMoveCoreDecode,
    symbolMoveLocalCfg,symbolMoveStacks]

theorem writeFinish_step {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    TM2.step (writeAfterProgram returnLabel right)
      (cleanReturnCfg (Sum.inl WriteFinishLabel.finish) state
        (writeBeforeFinishBase w accumulator value m base)) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel state
        (writeResultBase w accumulator value m base))):=by
  simp [writeAfterProgram,writeFinishProgram,cleanReturnCfg,
    liftRightProgram,TM2.step,mapLabelCfg,writeBeforeFinishBase,
    writeResultBase,Function.update]
  congr 2
  funext k
  cases k <;> simp [writeBeforeFinishBase,writeResultBase,Function.update]

theorem writeTail_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator value:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    ∃ finalState,
      ((fun o => o.bind (TM2.step (writeTailProgram returnLabel right)))^[
        2 * w + 6])
        (some (cleanReturnCfg (Sum.inl WriteResetLabel.reset) state
          (operandResultBase w accumulator value m base))) =
      some (mapLabelCfg (fun l:WriteMove1Label R => Sum.inr l)
        (mapLabelCfg (fun l:WriteMove2Label R => Sum.inr l)
          (mapLabelCfg (fun l:WriteAfterLabel R => Sum.inr l)
            (mapLabelCfg (fun l:R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (writeResultBase w accumulator value m base)))))):=by
  have h0:=writeReset_correct returnLabel right w accumulator value m base state
  simp only [List.map_reverse] at h0
  let state0:=FullInterpreterState.moveLens.put state default
  have h1:=run_lensPhase_to_right
    (symbolMoveCoreRenaming .work0 .work1 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl SymbolMoveLabel.loop) (writeMove2Program returnLabel right)
    (symbolMoveLocal_correct
      ((fixedBits w value).reverse.map SparseSymbol.bit) []) rfl
    state0 (writeMove1Base w accumulator value m base)
  simp only [List.length_map,List.length_reverse,fixedBits_length,
    List.append_nil,List.map_reverse,List.reverse_reverse] at h1
  rw [writeMove1_bridge (R:=R) w accumulator value m base state0] at h1
  let state1:=FullInterpreterState.moveLens.put state0 default
  have h2:=run_lensPhase_to_right
    (symbolMoveCoreRenaming .work1 .output (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl WriteFinishLabel.finish) (writeAfterProgram returnLabel right)
    (symbolMoveLocal_correct ((fixedBits w value).map SparseSymbol.bit)
      (base .output)) rfl
    state1 (writeMove2Base w accumulator value m base)
  simp only [List.length_map,fixedBits_length,List.map_reverse] at h2
  rw [writeMove2_finish_bridge (R:=R) w accumulator value m base state1] at h2
  have h3:
      ((fun o => o.bind (TM2.step (writeAfterProgram returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl WriteFinishLabel.finish)
          (FullInterpreterState.moveLens.put state1 default)
          (writeBeforeFinishBase w accumulator value m base))) =
      some (mapLabelCfg Sum.inr
        (cleanReturnCfg returnLabel
          (FullInterpreterState.moveLens.put state1 default)
          (writeResultBase w accumulator value m base))):=by
    simpa using writeFinish_step returnLabel right w accumulator value m base
      (FullInterpreterState.moveLens.put state1 default)
  have h23:=chain_liftRightProgram
    (lensPhaseLeft (symbolMoveCoreRenaming .work1 .output (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl WriteFinishLabel.finish))
    (writeAfterProgram returnLabel right) h2 h3
  have h123:=chain_liftRightProgram
    (lensPhaseLeft (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (writeMove2Program returnLabel right) h1 h23
  have h:=chain_liftRightProgram writeResetProgram
    (writeMove1Program returnLabel right) h0 h123
  refine ⟨FullInterpreterState.moveLens.put state1 default, ?_⟩
  have htime:2 * w + 6=1 + ((w + 2) + ((w + 2) + 1)):=by omega
  rw [htime]
  simpa [writeTailProgram,writeMove1Program,writeMove2Program,
    state0,state1] using h

theorem writeInstruction_correct {N:Nat} {R:Type}
    (o:Op) (hN:operandArgument o <= N)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator:Nat) (m:SparseMemory) (hm:m.Normalized w)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ steps,steps <= writeInstructionBound w m∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (writeInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg (R:=WriteTailLabel R)
          o hN w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l:WriteMove1Label R => Sum.inr l)
          (mapLabelCfg (fun l:WriteMove2Label R => Sum.inr l)
            (mapLabelCfg (fun l:WriteAfterLabel R => Sum.inr l)
              (mapLabelCfg (fun l:R => Sum.inr l)
                (cleanReturnCfg returnLabel finalState
                  (writeResultBase w accumulator
                    (operandWordValue w o m) m base))))))):=by
  rcases operandEval_correct o hN w accumulator m hm
      (Sum.inl WriteResetLabel.reset) (writeTailProgram returnLabel right)
      state base with ⟨operandSteps,operandBound,operandState,hoperand⟩
  rcases writeTail_correct returnLabel right w accumulator
      (operandWordValue w o m) m base operandState with
    ⟨writeState,hwrite⟩
  have hlift:=transport_iterate_operand_right o
    (Sum.inl WriteResetLabel.reset) (writeTailProgram returnLabel right) hwrite
  have hchain:=chain_loadInstruction_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (WriteInstructionLabel o R) (FullInterpreterState N)) =>
      x.bind (TM2.step (writeInstructionProgram o returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (2 * w + 6), ?_,writeState, ?_⟩
  · simp [writeInstructionBound]
    omega
  · simpa [writeInstructionProgram] using hchain

theorem encodeOutputStack_append_one (w:Nat) (out:List Nat) (value:Nat):
    encodeOutputStack w (out ++ [value]) =
      .wordEnd::(fixedBits w value).reverse.map SparseSymbol.bit ++
        encodeOutputStack w out:=by
  simp [encodeOutputStack,encodeWordList,encodeFixedWord,
    List.reverse_append,List.map_reverse,List.append_assoc]

theorem writeResultBase_coreStacks (w value:Nat) (s:SparseState):
    writeResultBase w s.acc value s.mem (coreStacks w s) =
      coreStacks w { s with out:=s.out ++ [value] }:=by
  funext k
  cases k <;> simp [writeResultBase,coreStacks,encodeMemoryStack,
    encodeAccumulator,encodeOutputStack_append_one]

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def copyStacks (source destination backup:List SparseSymbol):
    CopyStack -> List SparseSymbol
  | .source => source
  | .destination => destination
  | .backup => backup

def copyCfgState (label:CopyLabel) (state:SymbolMoveControl)
    (source destination backup:List SparseSymbol):
    TM2.Cfg (fun _:CopyStack => SparseSymbol) CopyLabel SymbolMoveControl where
  l:=some label
  var:=state
  stk:=copyStacks source destination backup

def copyCfg (label:CopyLabel)
    (source destination backup:List SparseSymbol):=
  copyCfgState label default source destination backup

@[simp] theorem copy_step_scan_cons (a:SparseSymbol) (xs ys bs:List SparseSymbol):
    TM2.step copyProgram (copyCfg .scan (a::xs) ys bs) =
      some (copyCfg .scan xs (a::ys) (a::bs)):=by
  simp [copyProgram,copyCfg,copyCfgState,copyStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem copy_step_scan_nil (ys bs:List SparseSymbol):
    TM2.step copyProgram (copyCfg .scan [] ys bs) =
      some (copyCfg .restore [] ys bs):=by
  simp [copyProgram,copyCfg,copyCfgState,copyStacks]

@[simp] theorem copy_step_restore_cons (a:SparseSymbol) (xs ys bs:List SparseSymbol):
    TM2.step copyProgram (copyCfg .restore xs ys (a::bs)) =
      some (copyCfg .restore (a::xs) ys bs):=by
  simp [copyProgram,copyCfg,copyCfgState,copyStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem copy_step_restore_nil (xs ys:List SparseSymbol):
    TM2.step copyProgram (copyCfg .restore xs ys []) =
      some (copyCfg .done xs ys []):=by
  simp [copyProgram,copyCfg,copyCfgState,copyStacks]

private theorem chain_copy {X:Type} (step:X -> X)
    {a b c:X} {m n:Nat} (h1:(step^[m]) a=b)
    (h2:(step^[n]) b=c):(step^[m + n]) a=c:=by
  rw [Nat.add_comm,Function.iterate_add_apply,h1,h2]

theorem copy_scan_iterate (xs:List SparseSymbol) (ys bs:List SparseSymbol):
    ((fun o => o.bind (TM2.step copyProgram))^[xs.length])
      (some (copyCfg .scan xs ys bs)) =
    some (copyCfg .scan [] (xs.reverse ++ ys) (xs.reverse ++ bs)):=by
  induction xs generalizing ys bs with
  | nil => rfl
  | cons a xs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,copy_step_scan_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem copy_restore_iterate (xs ys bs:List SparseSymbol):
    ((fun o => o.bind (TM2.step copyProgram))^[bs.length])
      (some (copyCfg .restore xs ys bs)) =
    some (copyCfg .restore (bs.reverse ++ xs) ys []):=by
  induction bs generalizing xs with
  | nil => rfl
  | cons a bs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,copy_step_restore_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem copy_correct (xs ys:List SparseSymbol):
    ((fun o => o.bind (TM2.step copyProgram))^[2 * xs.length + 2])
      (some (copyCfg .scan xs ys [])) =
    some (copyCfg .done xs (xs.reverse ++ ys) []):=by
  have h0:=copy_scan_iterate xs ys []
  simp only [List.append_nil] at h0
  have h1:((fun o => o.bind (TM2.step copyProgram))^[1])
      (some (copyCfg .scan [] (xs.reverse ++ ys) xs.reverse)) =
      some (copyCfg .restore [] (xs.reverse ++ ys) xs.reverse):=by
    simpa using copy_step_scan_nil (xs.reverse ++ ys) xs.reverse
  have h2:=copy_restore_iterate [] (xs.reverse ++ ys) xs.reverse
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h2
  have h3:((fun o => o.bind (TM2.step copyProgram))^[1])
      (some (copyCfg .restore xs (xs.reverse ++ ys) [])) =
      some (copyCfg .done xs (xs.reverse ++ ys) []):=by
    simpa using copy_step_restore_nil xs (xs.reverse ++ ys)
  have h:=chain_copy _ (chain_copy _ (chain_copy _ h0 h1) h2) h3
  have ht:2 * xs.length + 2=xs.length + 1 + xs.length + 1:=by omega
  rw [ht]
  exact h

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def copyAccumulatorStacks (xs:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol
  | .accumulator => xs
  | .work1 => xs.reverse
  | .work7 => []
  | k => base k

theorem fullCopy_generic_return_bridge {N:Nat} {R:Type}
    (returnLabel:R) (xs:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    phaseReturnCfg
      (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide)
        (by decide))
      FullInterpreterState.moveLens returnLabel
      (copyCfg .done xs xs.reverse []) state base =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (copyAccumulatorStacks xs base):=by
  simp only [phaseReturnCfg,cleanReturnCfg,lensRenamedCfg,copyCfg,
    copyCfgState]
  have hs:
      renamedStacks
        (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide)
          (by decide))
        (copyStacks xs xs.reverse []) base=copyAccumulatorStacks xs base:=by
    funext k
    cases k <;> simp [renamedStacks,copyCoreRenaming,copyStacks,
      copyAccumulatorStacks]
  rw [hs]

theorem fullCopyAccumulator_generic_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (xs:List SparseSymbol) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ((fun o => o.bind (TM2.step (fullCopyProgram returnLabel right)))^[
      2 * xs.length + 3])
      (some (lensRenamedCfg
        (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide)
          (by decide))
        FullInterpreterState.moveLens (copyCfg .scan xs [] []) state base)) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel
        (FullInterpreterState.moveLens.put state default)
        (copyAccumulatorStacks xs base))):=by
  have h:=run_lensPhase_to_right
    (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide)
      (by decide))
    FullInterpreterState.moveLens copyProgram .done (by rfl) returnLabel right
    (copy_correct xs []) rfl state base
  simp only [List.append_nil] at h
  rw [fullCopy_generic_return_bridge returnLabel xs base state] at h
  simpa [fullCopyProgram] using h

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def prependResultStacks (w a v:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol
  | .work0 | .work1 => []
  | .memory => encodeSparseMemory w (m.write w a v) ++ [.memoryEnd]
  | k => base k

theorem encodeSparseMemory_write (w:Nat) (m:SparseMemory) (a v:Nat):
    encodeSparseMemory w (m.write w a v) =
      encodeSparseCell w (a,v) ++ encodeSparseMemory w m:=by
  simp [SparseMemory.write,encodeSparseMemory]
  simp [encodeSparseCell,encodeFixedWord,fixedBits_mod_word]

theorem fullPrepend_return_bridge {N:Nat} {R:Type}
    (returnLabel:R) (w a v:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    phaseReturnCfg prependCoreRenaming FullInterpreterState.prependLens
      returnLabel
      (prependLocalCfg .done [] []
        (encodeSparseCell w (a,v) ++ (encodeSparseMemory w m ++ [.memoryEnd])))
      state
      (fun
        | .work0 => (fixedBits w a).reverse.map SparseSymbol.bit
        | .work1 => (fixedBits w v).reverse.map SparseSymbol.bit
        | .memory => encodeSparseMemory w m ++ [.memoryEnd]
        | k => base k) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.prependLens.put state default)
      (prependResultStacks w a v m base):=by
  simp only [phaseReturnCfg,cleanReturnCfg,lensRenamedCfg,prependLocalCfg]
  have hs:renamedStacks prependCoreRenaming
      (prependCellStacks [] []
        (encodeSparseCell w (a,v) ++ (encodeSparseMemory w m ++ [.memoryEnd])))
      (fun
        | .work0 => (fixedBits w a).reverse.map SparseSymbol.bit
        | .work1 => (fixedBits w v).reverse.map SparseSymbol.bit
        | .memory => encodeSparseMemory w m ++ [.memoryEnd]
        | k => base k)=prependResultStacks w a v m base:=by
    funext k
    cases k <;> simp [renamedStacks,prependCoreRenaming,prependCoreDecode,
      prependCoreEncode,prependCellStacks,prependResultStacks,
      encodeSparseMemory_write,List.append_assoc]
  rw [hs]

theorem fullPrepend_fixed_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a v:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    let initialStacks:CoreStack -> List SparseSymbol:=fun
      | .work0 => (fixedBits w a).reverse.map SparseSymbol.bit
      | .work1 => (fixedBits w v).reverse.map SparseSymbol.bit
      | .memory => encodeSparseMemory w m ++ [.memoryEnd]
      | k => base k
    ((fun o => o.bind (TM2.step (fullPrependProgram returnLabel right)))^[
      2 * w + 6])
      (some (lensRenamedCfg prependCoreRenaming
        FullInterpreterState.prependLens
        (prependLocalCfg .cellEnd
          ((fixedBits w a).reverse.map SparseSymbol.bit)
          ((fixedBits w v).reverse.map SparseSymbol.bit)
          (encodeSparseMemory w m ++ [.memoryEnd])) state initialStacks)) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel
        (FullInterpreterState.prependLens.put state default)
        (prependResultStacks w a v m base))):=by
  dsimp only
  let initialStacks:CoreStack -> List SparseSymbol:=fun
    | .work0 => (fixedBits w a).reverse.map SparseSymbol.bit
    | .work1 => (fixedBits w v).reverse.map SparseSymbol.bit
    | .memory => encodeSparseMemory w m ++ [.memoryEnd]
    | k => base k
  have h:=run_lensPhase_to_right prependCoreRenaming
    FullInterpreterState.prependLens prependCoreProgram .done (by rfl)
    returnLabel right
    (prependLocal_fixed_correct w a v
      (encodeSparseMemory w m ++ [.memoryEnd])) rfl state initialStacks
  dsimp [initialStacks] at h
  rw [fullPrepend_return_bridge returnLabel w a v m base state] at h
  simpa [fullPrependProgram,initialStacks] using h

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def storePreparedStacks (w address accumulator:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .work0 => (fixedBits w address).reverse.map SparseSymbol.bit
  | .work1 => (fixedBits w accumulator).reverse.map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .input => base .input
  | .output => base .output
  | _ => []

theorem copyAccumulatorStacks_operandResult (w address accumulator:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    copyAccumulatorStacks
      ((fixedBits w accumulator).map SparseSymbol.bit)
      (operandResultBase w accumulator address m base) =
    storePreparedStacks w address accumulator m base:=by
  funext k
  cases k <;> simp [copyAccumulatorStacks,operandResultBase,
    storePreparedStacks,List.map_reverse]

theorem prependResultStacks_storePrepared (w address accumulator:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    prependResultStacks w address accumulator m
      (storePreparedStacks w address accumulator m base) =
    operandBoundaryBase w accumulator (m.write w address accumulator) base:=by
  funext k
  cases k <;> rfl

theorem storePrependReset_step {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w address accumulator:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    TM2.step (storePrependTailProgram returnLabel right)
      (cleanReturnCfg (Sum.inl StorePrependResetLabel.reset) state
        (storePreparedStacks w address accumulator m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg prependCoreRenaming FullInterpreterState.prependLens
        (prependLocalCfg .cellEnd
          ((fixedBits w address).reverse.map SparseSymbol.bit)
          ((fixedBits w accumulator).reverse.map SparseSymbol.bit)
          (encodeSparseMemory w m ++ [.memoryEnd])) state
        (storePreparedStacks w address accumulator m base))):=by
  simp [storePrependTailProgram,storePrependResetProgram,cleanReturnCfg,
    liftRightProgram,mapLabelCfg,TM2.step,lensRenamedCfg,
    prependLocalCfg]
  have hs:renamedStacks prependCoreRenaming
      (prependCellStacks
        ((fixedBits w address).reverse.map SparseSymbol.bit)
        ((fixedBits w accumulator).reverse.map SparseSymbol.bit)
        (encodeSparseMemory w m ++ [.memoryEnd]))
      (storePreparedStacks w address accumulator m base) =
      storePreparedStacks w address accumulator m base:=by
    funext k
    cases k <;> simp [renamedStacks,prependCoreRenaming,
      prependCoreDecode,prependCellStacks,storePreparedStacks]
  rw [← List.map_reverse, ← List.map_reverse]
  exact hs.symm

theorem fullStore_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w address accumulator:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ finalState,
      ((fun o => o.bind (TM2.step (fullStoreProgram returnLabel right)))^[
        4 * w + 10])
        (some (lensRenamedCfg
          (copyCoreRenaming .accumulator .work1 .work7
            (by decide) (by decide) (by decide))
          FullInterpreterState.moveLens
          (copyCfg .scan ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
          state (operandResultBase w accumulator address m base))) =
      some (mapLabelCfg (fun l:StorePrependTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l:FullPrependLabel R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w accumulator
                (m.write w address accumulator) base))))):=by
  have hcopy:=fullCopyAccumulator_generic_correct
    (Sum.inl StorePrependResetLabel.reset)
    (storePrependTailProgram returnLabel right)
    ((fixedBits w accumulator).map SparseSymbol.bit)
    (operandResultBase w accumulator address m base) state
  simp only [List.length_map,fixedBits_length] at hcopy
  rw [copyAccumulatorStacks_operandResult w address accumulator m base] at hcopy
  let copyState:=FullInterpreterState.moveLens.put state default
  have hresetStep:=storePrependReset_step returnLabel right
    w address accumulator m base copyState
  have hreset:
      ((fun o => o.bind (TM2.step
        (storePrependTailProgram returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl StorePrependResetLabel.reset)
          copyState (storePreparedStacks w address accumulator m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg prependCoreRenaming FullInterpreterState.prependLens
          (prependLocalCfg .cellEnd
            ((fixedBits w address).reverse.map SparseSymbol.bit)
            ((fixedBits w accumulator).reverse.map SparseSymbol.bit)
            (encodeSparseMemory w m ++ [.memoryEnd])) copyState
          (storePreparedStacks w address accumulator m base))):=by
    simpa using hresetStep
  have hprepend:=fullPrepend_fixed_correct returnLabel right
    w address accumulator m
    (storePreparedStacks w address accumulator m base) copyState
  rw [prependResultStacks_storePrepared w address accumulator m base] at hprepend
  dsimp only at hprepend
  have hstacks:
      (fun
        | .work0 => (fixedBits w address).reverse.map SparseSymbol.bit
        | .work1 => (fixedBits w accumulator).reverse.map SparseSymbol.bit
        | .memory => encodeSparseMemory w m ++ [.memoryEnd]
        | k => storePreparedStacks w address accumulator m base k) =
      storePreparedStacks w address accumulator m base:=by
    funext k
    cases k <;> rfl
  have hcfg:
      lensRenamedCfg (Λx:=R) prependCoreRenaming FullInterpreterState.prependLens
        (prependLocalCfg .cellEnd
          ((fixedBits w address).reverse.map SparseSymbol.bit)
          ((fixedBits w accumulator).reverse.map SparseSymbol.bit)
          (encodeSparseMemory w m ++ [.memoryEnd])) copyState
        (fun
          | .work0 => (fixedBits w address).reverse.map SparseSymbol.bit
          | .work1 => (fixedBits w accumulator).reverse.map SparseSymbol.bit
          | .memory => encodeSparseMemory w m ++ [.memoryEnd]
          | k => storePreparedStacks w address accumulator m base k) =
      lensRenamedCfg (Λx:=R) prependCoreRenaming FullInterpreterState.prependLens
        (prependLocalCfg .cellEnd
          ((fixedBits w address).reverse.map SparseSymbol.bit)
          ((fixedBits w accumulator).reverse.map SparseSymbol.bit)
          (encodeSparseMemory w m ++ [.memoryEnd])) copyState
        (storePreparedStacks w address accumulator m base):=by
    rw [hstacks]
  have hprepend':
      ((fun o => o.bind (TM2.step
        (fullPrependProgram returnLabel right)))^[2 * w + 6])
        (some (lensRenamedCfg (Λx:=R) prependCoreRenaming
          FullInterpreterState.prependLens
          (prependLocalCfg .cellEnd
            ((fixedBits w address).reverse.map SparseSymbol.bit)
            ((fixedBits w accumulator).reverse.map SparseSymbol.bit)
            (encodeSparseMemory w m ++ [.memoryEnd])) copyState
          (storePreparedStacks w address accumulator m base))) =
      some (mapLabelCfg Sum.inr
        (cleanReturnCfg returnLabel
          (FullInterpreterState.prependLens.put copyState default)
          (operandBoundaryBase w accumulator
            (m.write w address accumulator) base))):=by
    calc
      _=((fun o => o.bind (TM2.step
          (fullPrependProgram returnLabel right)))^[2 * w + 6])
          (some (lensRenamedCfg (Λx:=R) prependCoreRenaming
            FullInterpreterState.prependLens
            (prependLocalCfg .cellEnd
              ((fixedBits w address).reverse.map SparseSymbol.bit)
              ((fixedBits w accumulator).reverse.map SparseSymbol.bit)
              (encodeSparseMemory w m ++ [.memoryEnd])) copyState
            (fun
              | .work0 => (fixedBits w address).reverse.map SparseSymbol.bit
              | .work1 => (fixedBits w accumulator).reverse.map SparseSymbol.bit
              | .memory => encodeSparseMemory w m ++ [.memoryEnd]
              | k => storePreparedStacks w address accumulator m base k))):=
        congrArg
          (fun c => ((fun o => o.bind (TM2.step
            (fullPrependProgram returnLabel right)))^[2 * w + 6]) (some c))
          hcfg.symm
      _=_:=hprepend
  have htail:=chain_liftRightProgram storePrependResetProgram
    (fullPrependProgram returnLabel right) hreset hprepend'
  have hlift:=transport_iterate_liftRightProgram
    (lensPhaseLeft
      (copyCoreRenaming .accumulator .work1 .work7
        (by decide) (by decide) (by decide))
      FullInterpreterState.moveLens copyProgram .done
      (Sum.inl StorePrependResetLabel.reset))
    (storePrependTailProgram returnLabel right) htail
  have hchain:=chain_loadInstruction_iterations
    (fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (FullStoreLabel R) (FullInterpreterState N)) =>
        o.bind (TM2.step (fullStoreProgram returnLabel right)))
    hcopy hlift
  refine ⟨FullInterpreterState.prependLens.put copyState default, ?_⟩
  have htime:4 * w + 10=(2 * w + 3) + (1 + (2 * w + 6)):=by omega
  rw [htime]
  simpa [fullStoreProgram,copyState] using hchain

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

theorem storeReset_step {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w address accumulator:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    TM2.step (storeInstructionTailProgram returnLabel right)
      (cleanReturnCfg (Sum.inl StoreResetLabel.reset) state
        (operandResultBase w accumulator address m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg
        (copyCoreRenaming .accumulator .work1 .work7
          (by decide) (by decide) (by decide))
        FullInterpreterState.moveLens
        (copyCfg .scan ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
        state (operandResultBase w accumulator address m base))):=by
  simp [storeInstructionTailProgram,storeResetProgram,cleanReturnCfg,
    liftRightProgram,mapLabelCfg,TM2.step,lensRenamedCfg,copyCfg,
    copyCfgState]
  have hs:renamedStacks
      (copyCoreRenaming .accumulator .work1 .work7
        (by decide) (by decide) (by decide))
      (copyStacks ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
      (operandResultBase w accumulator address m base) =
      operandResultBase w accumulator address m base:=by
    funext k
    cases k <;> simp [renamedStacks,copyCoreRenaming,copyStacks,
      operandResultBase]
  rw [hs]

theorem SparseMemory.write_mod_address (w:Nat) (m:SparseMemory)
    (address value:Nat):
    m.write w (address % 2 ^ w) value=m.write w address value:=by
  simp [SparseMemory.write,Nat.mod_mod]

theorem storeInstruction_correct {N:Nat} {R:Type}
    (address:Nat) (hN:address <= N)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator:Nat) (m:SparseMemory) (hm:m.Normalized w)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ steps,steps <= storeInstructionBound w m∧ ∃ finalState,
      ((fun o => o.bind (TM2.step
        (storeInstructionProgram address returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=StoreInstructionTailLabel R) (.lit address) hN
          w accumulator m state base)) =
      some (embedOperandReturnCfg (.lit address)
        (mapLabelCfg (fun l:FullStoreLabel R => Sum.inr l)
          (mapLabelCfg (fun l:StorePrependTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l:FullPrependLabel R => Sum.inr l)
              (mapLabelCfg (fun l:R => Sum.inr l)
                (cleanReturnCfg returnLabel finalState
                  (operandBoundaryBase w accumulator
                    (m.write w address accumulator) base))))))):=by
  rcases operandEval_correct (.lit address) hN w accumulator m hm
      (Sum.inl StoreResetLabel.reset)
      (storeInstructionTailProgram returnLabel right) state base with
    ⟨operandSteps,operandBound,operandState,hoperand⟩
  let wordAddress:=operandWordValue w (.lit address) m
  have hresetStep:=storeReset_step returnLabel right w wordAddress
    accumulator m base operandState
  have hreset:
      ((fun o => o.bind (TM2.step
        (storeInstructionTailProgram returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl StoreResetLabel.reset) operandState
          (operandResultBase w accumulator wordAddress m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg
          (copyCoreRenaming .accumulator .work1 .work7
            (by decide) (by decide) (by decide))
          FullInterpreterState.moveLens
          (copyCfg .scan ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
          operandState
          (operandResultBase w accumulator wordAddress m base))):=by
    simpa using hresetStep
  rcases fullStore_correct returnLabel right w wordAddress accumulator m base
      operandState with ⟨storeState,hstore⟩
  have htail:=chain_liftRightProgram storeResetProgram
    (fullStoreProgram returnLabel right) hreset hstore
  have hlift:=transport_iterate_operand_right (.lit address)
    (Sum.inl StoreResetLabel.reset)
    (storeInstructionTailProgram returnLabel right) htail
  have hchain:=chain_loadInstruction_iterations
    (fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (StoreInstructionLabel address R) (FullInterpreterState N)) =>
        o.bind (TM2.step (storeInstructionProgram address returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (1 + (4 * w + 10)), ?_,storeState, ?_⟩
  · simp [storeInstructionBound]
    omega
  · have hwrite:m.write w wordAddress accumulator =
        m.write w address accumulator:=by
      simp [wordAddress,operandWordValue,
        SparseMemory.write_mod_address]
    rw [hwrite] at hchain
    simpa [storeInstructionProgram,storeInstructionTailProgram,
      wordAddress,operandWordValue] using hchain

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

@[simp] theorem readTransfer_step_bit {N:Nat} {R:Type}
    (exhaustedLabel returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N) (bit:Bool)
    (input value:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol):
    TM2.step (readTransferProgram exhaustedLabel returnLabel right)
      (readTransferCfg state (.bit bit::input) value base) =
    some (readTransferCfg
      (FullInterpreterState.moveLens.put state default)
      input (.bit bit::value) base):=by
  simp [readTransferProgram,readTransferCfg,readTransferStacks,
    readTransferLeftProgram,liftRightProgram,TM2.step,Function.update,
    FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem readTransfer_step_end {N:Nat} {R:Type}
    (exhaustedLabel returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N) (input value:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol):
    TM2.step (readTransferProgram exhaustedLabel returnLabel right)
      (readTransferCfg state (.wordEnd::input) value base) =
    some (⟨some (Sum.inr (Sum.inl PrependCellLabel.cellEnd)),
      FullInterpreterState.prependLens.put
        (FullInterpreterState.moveLens.put state default) default,
      readTransferStacks input value base⟩):=by
  simp [readTransferProgram,readTransferCfg,readTransferStacks,
    readTransferLeftProgram,liftRightProgram,TM2.step,Function.update,
    FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  congr 2
  funext k
  cases k <;> rfl

theorem readTransfer_fixed_correct {N:Nat} {R:Type}
    (exhaustedLabel returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w value:Nat) (input:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ((fun o => o.bind (TM2.step
      (readTransferProgram exhaustedLabel returnLabel right)))^[w + 1])
      (some (readTransferCfg (FullInterpreterState.moveLens.put state default)
        (encodeFixedWord w value ++ input) [] base)) =
    some (⟨some (Sum.inr (Sum.inl PrependCellLabel.cellEnd)),
      FullInterpreterState.prependLens.put
        (FullInterpreterState.moveLens.put state default) default,
      readTransferStacks input
        ((fixedBits w value).reverse.map SparseSymbol.bit) base⟩):=by
  let stepO:=fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (ReadTailLabel R) (FullInterpreterState N)) =>
    o.bind (TM2.step (readTransferProgram exhaustedLabel returnLabel right))
  let cleanState:=FullInterpreterState.moveLens.put state default
  have bitsRun (xs:List Bool) (acc:List SparseSymbol):
      (stepO^[xs.length])
        (some (readTransferCfg cleanState
          (xs.map SparseSymbol.bit ++ .wordEnd::input) acc base)) =
      some (readTransferCfg cleanState
        (.wordEnd::input) (xs.reverse.map SparseSymbol.bit ++ acc) base):=by
    induction xs generalizing acc with
    | nil => rfl
    | cons bit bits ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [List.map_cons,List.cons_append,stepO,Option.bind_some,
        readTransfer_step_bit,cleanState,
        FullInterpreterState.moveLens.put_put]
      rw [ih]
      change some (readTransferCfg cleanState (.wordEnd::input)
        ((bits.reverse.map SparseSymbol.bit) ++ .bit bit::acc) base)=_
      simp [List.reverse_cons,List.map_append,List.append_assoc,cleanState]
  rw [encodeFixedWord,Nat.add_comm,Function.iterate_add_apply]
  simp only [List.append_assoc,List.singleton_append]
  change (stepO^[1]) ((stepO^[w]) _)=_
  have hrun:=bitsRun (fixedBits w value) []
  simp only [fixedBits_length] at hrun
  rw [hrun]
  simp [stepO,cleanState,FullInterpreterState.moveLens.put_put]

theorem readTail_correct {N:Nat} {R:Type}
    (exhaustedLabel returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator address value:Nat) (m:SparseMemory)
    (inputTail:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol)
    (hinput:base .input=encodeFixedWord w value ++ inputTail)
    (state:FullInterpreterState N):
    ∃ finalState,
      ((fun o => o.bind (TM2.step
        (readTransferProgram exhaustedLabel returnLabel right)))^[
        3 * w + 8])
        (some (cleanReturnCfg (Sum.inl ReadTransferLabel.initializeState) state
          (operandResultBase w accumulator address m base))) =
      some (mapLabelCfg Sum.inr (mapLabelCfg Sum.inr
        (cleanReturnCfg returnLabel finalState
          (prependResultStacks w address value m
            (readTransferStacks inputTail
              ((fixedBits w value).reverse.map SparseSymbol.bit)
              (operandResultBase w accumulator address m base)))))):=by
  let cleanState:=FullInterpreterState.moveLens.put state default
  let transferBase:=operandResultBase w accumulator address m base
  have hinit:
      ((fun o => o.bind (TM2.step
        (readTransferProgram exhaustedLabel returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl ReadTransferLabel.initializeState) state
          transferBase)) =
      some (readTransferCfg cleanState
        (encodeFixedWord w value ++ inputTail) [] transferBase):=by
    simpa [cleanState,transferBase,hinput] using
      readTransfer_initialize exhaustedLabel returnLabel right w accumulator address m base state
  have htransfer:=readTransfer_fixed_correct exhaustedLabel returnLabel right
    w value inputTail transferBase state
  let prependBase:=readTransferStacks inputTail
    ((fixedBits w value).reverse.map SparseSymbol.bit) transferBase
  let prependCfg:=lensRenamedCfg (Λx:=R) prependCoreRenaming
    FullInterpreterState.prependLens
    (prependLocalCfg .cellEnd
      ((fixedBits w address).reverse.map SparseSymbol.bit)
      ((fixedBits w value).reverse.map SparseSymbol.bit)
      (encodeSparseMemory w m ++ [.memoryEnd])) cleanState prependBase
  have hcfg:
      (⟨some (Sum.inr (Sum.inl PrependCellLabel.cellEnd)),
        FullInterpreterState.prependLens.put cleanState default,
        prependBase⟩:TM2.Cfg (fun _:CoreStack => SparseSymbol)
          (ReadTailLabel R) (FullInterpreterState N)) =
      mapLabelCfg Sum.inr prependCfg:=by
    simp [prependCfg,prependBase,transferBase,lensRenamedCfg,
      prependLocalCfg,mapLabelCfg,renamedStacks,prependCoreRenaming,
      prependCoreDecode,prependCoreEncode,prependCellStacks,
      readTransferStacks,operandResultBase]
    funext k
    cases k <;> simp [renamedStacks,prependCoreRenaming,
      prependCoreDecode,prependCellStacks,prependBase,transferBase,
      readTransferStacks,operandResultBase]
  have hfirst:
      ((fun o => o.bind (TM2.step
        (readTransferProgram exhaustedLabel returnLabel right)))^[
        1 + (w + 1)])
        (some (cleanReturnCfg (Sum.inl ReadTransferLabel.initializeState) state
          transferBase))=some (mapLabelCfg Sum.inr prependCfg):=by
    rw [Nat.add_comm,Function.iterate_add_apply,hinit,htransfer,hcfg]
  have hprepend:=fullPrepend_fixed_correct returnLabel right
    w address value m prependBase cleanState
  have hprependCfg:prependCfg =
      lensRenamedCfg (Λx:=R) prependCoreRenaming
        FullInterpreterState.prependLens
        (prependLocalCfg .cellEnd
          ((fixedBits w address).reverse.map SparseSymbol.bit)
          ((fixedBits w value).reverse.map SparseSymbol.bit)
          (encodeSparseMemory w m ++ [.memoryEnd])) cleanState
        (fun
          | .work0 => (fixedBits w address).reverse.map SparseSymbol.bit
          | .work1 => (fixedBits w value).reverse.map SparseSymbol.bit
          | .memory => encodeSparseMemory w m ++ [.memoryEnd]
          | k => prependBase k):=by
    simp [prependCfg,lensRenamedCfg]
    funext k
    cases k <;> simp [renamedStacks,prependCoreRenaming,
      prependCoreDecode,prependCellStacks]
  have hprepend':
      ((fun o => o.bind (TM2.step (fullPrependProgram returnLabel right)))^[
        2 * w + 6]) (some prependCfg) =
      some (mapLabelCfg Sum.inr
        (cleanReturnCfg returnLabel
          (FullInterpreterState.prependLens.put cleanState default)
          (prependResultStacks w address value m prependBase))):=by
    rw [hprependCfg]
    exact hprepend
  have hall:=chain_liftRightProgram (readTransferLeftProgram exhaustedLabel)
    (fullPrependProgram returnLabel right) hfirst hprepend'
  refine ⟨FullInterpreterState.prependLens.put cleanState default, ?_⟩
  have htime:3 * w + 8=(1 + (w + 1)) + (2 * w + 6):=by omega
  rw [htime]
  simpa [readTransferProgram,transferBase,prependBase,prependCfg] using hall

theorem readResultStacks_coreStacks (w address value:Nat)
    (s:SparseState) (inputTail:List Nat):
    prependResultStacks w address value s.mem
        (readTransferStacks (encodeInputStack w inputTail)
          ((fixedBits w value).reverse.map SparseSymbol.bit)
          (operandResultBase w s.acc (address % 2 ^ w) s.mem
            (coreStacks w s))) =
      coreStacks w { s with
        mem:=s.mem.write w address value
        inp:=inputTail }:=by
  funext k
  cases k <;> simp [prependResultStacks,readTransferStacks,
    operandResultBase,coreStacks,encodeAccumulator,encodeMemoryStack,
    encodeInputStack]

theorem readInstruction_correct {N:Nat} {R:Type}
    (address:Nat) (hN:address <= N)
    (exhaustedLabel returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator value:Nat) (inputTail:List SparseSymbol)
    (m:SparseMemory) (hm:m.Normalized w)
    (base:CoreStack -> List SparseSymbol)
    (hinput:base .input=encodeFixedWord w value ++ inputTail)
    (state:FullInterpreterState N):
    ∃ steps,steps <= readInstructionBound w m∧ ∃ finalState,
      ((fun o => o.bind (TM2.step
        (readInstructionProgram address exhaustedLabel returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=ReadTailLabel R) (.lit address) hN
          w accumulator m state base)) =
      some (embedOperandReturnCfg (.lit address)
        (mapLabelCfg Sum.inr (mapLabelCfg Sum.inr
          (cleanReturnCfg returnLabel finalState
            (prependResultStacks w address value m
              (readTransferStacks inputTail
                ((fixedBits w value).reverse.map SparseSymbol.bit)
                (operandResultBase w accumulator
                  (operandWordValue w (.lit address) m) m base))))))):=by
  rcases operandEval_correct (.lit address) hN w accumulator m hm
      (Sum.inl ReadTransferLabel.initializeState)
      (readTransferProgram exhaustedLabel returnLabel right) state base with
    ⟨operandSteps,operandBound,operandState,hoperand⟩
  let wordAddress:=operandWordValue w (.lit address) m
  rcases readTail_correct exhaustedLabel returnLabel right w accumulator wordAddress value m
      inputTail base hinput operandState with ⟨tailState,htail⟩
  have hlift:=transport_iterate_operand_right (.lit address)
    (Sum.inl ReadTransferLabel.initializeState)
    (readTransferProgram exhaustedLabel returnLabel right) htail
  have hchain:=chain_loadInstruction_iterations
    (fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (ReadInstructionLabel address R) (FullInterpreterState N)) =>
        o.bind (TM2.step
          (readInstructionProgram address exhaustedLabel returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (3 * w + 8), ?_,tailState, ?_⟩
  · simp [readInstructionBound]
    omega
  · have hwrite:m.write w wordAddress value=m.write w address value:=by
      simp [wordAddress,operandWordValue,SparseMemory.write_mod_address]
    have hresult:
        prependResultStacks w wordAddress value m
            (readTransferStacks inputTail
              ((fixedBits w value).reverse.map SparseSymbol.bit)
              (operandResultBase w accumulator wordAddress m base)) =
          prependResultStacks w address value m
            (readTransferStacks inputTail
              ((fixedBits w value).reverse.map SparseSymbol.bit)
              (operandResultBase w accumulator wordAddress m base)):=by
      funext k
      cases k <;> simp [prependResultStacks,hwrite]
    rw [hresult] at hchain
    simpa [readInstructionProgram,wordAddress] using hchain

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

namespace Lax759944Proofs.RamToTM

open Turing TM2

def sparseCountdownCfg (label:CountdownLabel) (state:CountdownControl)
    (count temp:List Bool):
    TM2.Cfg (fun _:CountdownStack => SparseSymbol)
      CountdownLabel CountdownControl:=
  mapAlphabetCfg sparseBitEncode (countdownCfg label state count temp)

theorem sparseCountdown_zero_correct (w:Nat):
    ((fun x => x.bind (TM2.step sparseCountdownProgram))^[w + 1])
      (some (sparseCountdownCfg .scan default (fixedBits w 0) [])) =
    some (sparseCountdownCfg .zero
      { held:=none,borrow:=true,positiveSeen:=false }
      [] (List.replicate w true)):=by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode countdownMachine.m
    (countdownMachine_zero_correct w)

theorem sparseCountdown_positive_correct (w d:Nat)
    (hd0:0 < d) (hd:d < 2 ^ w):
    ∃ finalState,
      ((fun x => x.bind (TM2.step sparseCountdownProgram))^[2 * w + 2])
        (some (sparseCountdownCfg .scan default (fixedBits w d) [])) =
      some (sparseCountdownCfg .positive finalState
        (fixedBits w (d - 1)) []):=by
  rcases countdownMachine_positive_correct w d hd0 hd with
    ⟨finalState,hrun⟩
  refine ⟨finalState, ?_⟩
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode countdownMachine.m hrun

theorem countdownExit_halt {R:Type} (zeroLabel positiveLabel:R)
    (label:CountdownLabel)
    (h:(countdownExit zeroLabel positiveLabel label).isSome):
    sparseCountdownProgram label=.halt:=by
  cases label <;> simp [countdownExit] at h ⊢ <;> rfl

theorem globalCountdown_zero_correct {N:Nat} {R:Type}
    (zeroLabel positiveLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w:Nat) (state:FullInterpreterState N)
    (base:CoreStack -> List SparseSymbol):
    ((fun x => x.bind (TM2.step
      (liftRightProgram (countdownMultiLeft zeroLabel positiveLabel) right)))^[
        w + 2])
      (some (lensRenamedCfg countdownCoreRenaming
        FullInterpreterState.countdownLens
        (sparseCountdownCfg .scan default (fixedBits w 0) [])
        state base)) =
    some (mapLabelCfg Sum.inr
      (multiPhaseReturnCfg countdownCoreRenaming
        FullInterpreterState.countdownLens zeroLabel id
        (sparseCountdownCfg .zero
          { held:=none,borrow:=true,positiveSeen:=false }
          [] (List.replicate w true)) state base)):=by
  have h:=run_lensMultiPhase_to_right countdownCoreRenaming
    FullInterpreterState.countdownLens sparseCountdownProgram
    (countdownExit zeroLabel positiveLabel) countdownOnExit
    (countdownExit_halt zeroLabel positiveLabel) right
    (sparseCountdown_zero_correct w) rfl (by rfl) state base
  simpa [countdownMultiLeft,countdownOnExit] using! h

theorem globalCountdown_positive_correct {N:Nat} {R:Type}
    (zeroLabel positiveLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w d:Nat) (hd0:0 < d) (hd:d < 2 ^ w)
    (state:FullInterpreterState N)
    (base:CoreStack -> List SparseSymbol):
    ∃ localFinal,
      ((fun x => x.bind (TM2.step
        (liftRightProgram (countdownMultiLeft zeroLabel positiveLabel) right)))^[
          2 * w + 3])
        (some (lensRenamedCfg countdownCoreRenaming
          FullInterpreterState.countdownLens
          (sparseCountdownCfg .scan default (fixedBits w d) [])
          state base)) =
      some (mapLabelCfg Sum.inr
        (multiPhaseReturnCfg countdownCoreRenaming
          FullInterpreterState.countdownLens positiveLabel id
          (sparseCountdownCfg .positive localFinal
            (fixedBits w (d - 1)) []) state base)):=by
  rcases sparseCountdown_positive_correct w d hd0 hd with
    ⟨localFinal,hrun⟩
  refine ⟨localFinal, ?_⟩
  have h:=run_lensMultiPhase_to_right countdownCoreRenaming
    FullInterpreterState.countdownLens sparseCountdownProgram
    (countdownExit zeroLabel positiveLabel) countdownOnExit
    (countdownExit_halt zeroLabel positiveLabel) right hrun rfl (by rfl)
    state base
  simpa [countdownMultiLeft,countdownOnExit] using! h

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def shiftRightCfg (l:ShiftRightLabel) (source temp result:List Bool):
    shiftRightMachine.Cfg where
  l:=some l
  var:=default
  stk:=shiftStacks source temp result

@[simp] theorem shiftRight_step_discard (a:Bool) (as temp result:List Bool):
    shiftRightMachine.step (shiftRightCfg .discard (a::as) temp result) =
      some (shiftRightCfg .prepend as temp result):=by
  change some (TM2.stepAux
    (.pop ShiftStack.source (fun _ _ => (default:MoveControl))
      (.goto fun _ => ShiftRightLabel.prepend))
    default (shiftStacks (a::as) temp result))=_
  simp [shiftRightCfg,shiftStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem shiftRight_step_prepend (source temp result:List Bool):
    shiftRightMachine.step (shiftRightCfg .prepend source temp result) =
      some (shiftRightCfg .first source temp (false::result)):=by
  change some (TM2.stepAux
    (.push ShiftStack.result (fun _:MoveControl => false)
      (.goto fun _ => ShiftRightLabel.first))
    default (shiftStacks source temp result))=_
  simp [shiftRightCfg,shiftStacks,Function.update]
  congr 2
  funext k
  cases k <;> rfl

@[simp] theorem shiftRight_step_first_cons (a:Bool)
    (as temp result:List Bool):
    shiftRightMachine.step (shiftRightCfg .first (a::as) temp result) =
      some (shiftRightCfg .first as (a::temp) result):=by
  change some (TM2.stepAux
    (moveIteration ShiftStack.source ShiftStack.temp ShiftRightLabel.first
      ShiftRightLabel.second)
    default (shiftStacks (a::as) temp result))=_
  simp [moveIteration,shiftRightCfg,shiftStacks,Function.update]
  congr 2
  constructor
  · rfl
  · funext k
    cases k <;> rfl

@[simp] theorem shiftRight_step_first_nil (temp result:List Bool):
    shiftRightMachine.step (shiftRightCfg .first [] temp result) =
      some (shiftRightCfg .second [] temp result):=by
  change some (TM2.stepAux
    (moveIteration ShiftStack.source ShiftStack.temp ShiftRightLabel.first
      ShiftRightLabel.second)
    default (shiftStacks [] temp result))=_
  simp [moveIteration,shiftRightCfg,shiftStacks]
  rfl

@[simp] theorem shiftRight_step_second_cons (source result:List Bool)
    (a:Bool) (temp:List Bool):
    shiftRightMachine.step (shiftRightCfg .second source (a::temp) result) =
      some (shiftRightCfg .second source temp (a::result)):=by
  change some (TM2.stepAux
    (moveIteration ShiftStack.temp ShiftStack.result ShiftRightLabel.second
      ShiftRightLabel.done)
    default (shiftStacks source (a::temp) result))=_
  simp [moveIteration,shiftRightCfg,shiftStacks,Function.update]
  congr 2
  constructor
  · rfl
  · funext k
    cases k <;> rfl

@[simp] theorem shiftRight_step_second_nil (source result:List Bool):
    shiftRightMachine.step (shiftRightCfg .second source [] result) =
      some (shiftRightCfg .done source [] result):=by
  change some (TM2.stepAux
    (moveIteration ShiftStack.temp ShiftStack.result ShiftRightLabel.second
      ShiftRightLabel.done)
    default (shiftStacks source [] result))=_
  simp [moveIteration,shiftRightCfg,shiftStacks]
  rfl

theorem shiftRight_first_iterate (source temp result:List Bool):
    ((fun o:Option shiftRightMachine.Cfg =>
      o.bind shiftRightMachine.step)^[source.length])
      (some (shiftRightCfg .first source temp result)) =
    some (shiftRightCfg .first [] (source.reverse ++ temp) result):=by
  induction source generalizing temp with
  | nil => rfl
  | cons a as ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,shiftRight_step_first_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem shiftRight_second_iterate (source temp result:List Bool):
    ((fun o:Option shiftRightMachine.Cfg =>
      o.bind shiftRightMachine.step)^[temp.length])
      (some (shiftRightCfg .second source temp result)) =
    some (shiftRightCfg .second source [] (temp.reverse ++ result)):=by
  induction temp generalizing result with
  | nil => rfl
  | cons a temp ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,shiftRight_step_second_cons]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

theorem shiftRightMachine_correct_nonempty (a:Bool) (as:List Bool):
    ((fun o:Option shiftRightMachine.Cfg =>
      o.bind shiftRightMachine.step)^[2 * (a::as).length + 2])
      (some (shiftRightCfg .discard (a::as) [] [])) =
    some (shiftRightCfg .done [] [] (shiftRightBits (a::as))):=by
  let stepO:=fun o:Option shiftRightMachine.Cfg =>
    o.bind shiftRightMachine.step
  have chain {m n:Nat} {x y z:Option shiftRightMachine.Cfg}
      (h₁:(stepO^[m]) x=y) (h₂:(stepO^[n]) y=z):
      (stepO^[m + n]) x=z:=by
    rw [Nat.add_comm,Function.iterate_add_apply,h₁,h₂]
  have hd:(stepO^[1])
      (some (shiftRightCfg .discard (a::as) [] [])) =
      some (shiftRightCfg .prepend as [] []):=by
    simpa [stepO] using! shiftRight_step_discard a as [] []
  have hp:(stepO^[1]) (some (shiftRightCfg .prepend as [] [])) =
      some (shiftRightCfg .first as [] [false]):=by
    simpa [stepO] using! shiftRight_step_prepend as [] []
  have hfirst:=shiftRight_first_iterate as [] [false]
  simp only [List.append_nil] at hfirst
  have hf:(stepO^[1])
      (some (shiftRightCfg .first [] as.reverse [false])) =
      some (shiftRightCfg .second [] as.reverse [false]):=by
    simpa [stepO] using! shiftRight_step_first_nil as.reverse [false]
  have hsecond:=shiftRight_second_iterate [] as.reverse [false]
  simp only [List.reverse_reverse] at hsecond
  have hs:(stepO^[1])
      (some (shiftRightCfg .second [] [] (as ++ [false]))) =
      some (shiftRightCfg .done [] [] (as ++ [false])):=by
    simpa [stepO] using! shiftRight_step_second_nil [] (as ++ [false])
  have hall:=chain (chain (chain (chain (chain hd hp) hfirst) hf) hsecond) hs
  simp only [List.length_reverse] at hall
  have ht:1 + 1 + as.length + 1 + as.length + 1 =
      2 * (a::as).length + 2:=by simp; omega
  rw [ht] at hall
  simpa [stepO,shiftRightBits] using hall

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def sparseShiftLeftLocalCfg (label:ShiftLabel)
    (source temp result:List Bool):
    TM2.Cfg (fun _:ShiftStack => SparseSymbol) ShiftLabel MoveControl:=
  mapAlphabetCfg sparseBitEncode (shiftCfg label source temp result)

theorem sparseShiftLeftLocal_correct_nonempty (a:Bool) (as:List Bool):
    ((fun x => x.bind (TM2.step sparseShiftLeftCoreProgram))^[
      2 * (a::as).length + 3])
      (some (sparseShiftLeftLocalCfg .first (a::as) [] [])) =
    some (sparseShiftLeftLocalCfg .done [] []
      (shiftLeftBits (a::as))):=by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode shiftMachine.m
    (shiftMachine_correct_nonempty a as)

def sparseShiftRightLocalCfg (label:ShiftRightLabel)
    (source temp result:List Bool):
    TM2.Cfg (fun _:ShiftStack => SparseSymbol) ShiftRightLabel MoveControl:=
  mapAlphabetCfg sparseBitEncode (shiftRightCfg label source temp result)

theorem sparseShiftRightLocal_correct_nonempty (a:Bool) (as:List Bool):
    ((fun x => x.bind (TM2.step sparseShiftRightCoreProgram))^[
      2 * (a::as).length + 2])
      (some (sparseShiftRightLocalCfg .discard (a::as) [] [])) =
    some (sparseShiftRightLocalCfg .done [] []
      (shiftRightBits (a::as))):=by
  exact transport_iterate_mapAlphabetProgram sparseBitEncode sparseBitDecode
    sparseBitDecode_encode shiftRightMachine.m
    (shiftRightMachine_correct_nonempty a as)

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def shiftRoundBase (w word count:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w word).map SparseSymbol.bit
  | .work1 => fuel
  | .work3 => (fixedBits w count).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work0 | .work2 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def shiftAfterCoreStacks (w word count:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    CoreStack -> List SparseSymbol
  | .work6 => (shiftLeftBits (fixedBits w word)).map SparseSymbol.bit
  | .work1 => fuel
  | .work3 => (fixedBits w count).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .accumulator | .work0 | .work2 | .work4 | .work5 | .work7 => []
  | k => base k

def shiftAfterFirstMoveStacks (w word count:Nat)
    (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol
  | .work0 => (shiftLeftBits (fixedBits w word)).reverse.map SparseSymbol.bit
  | .work1 => fuel
  | .work3 => (fixedBits w count).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .accumulator | .work2 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

theorem shiftLeft_core_bridge {N:Nat} {R:Type}
    (w word count:Nat) (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N)
    (hmove:FullInterpreterState.moveLens.get state=default):
    phaseReturnCfg shiftRoundRenaming FullInterpreterState.shiftLens
      (Sum.inl SymbolMoveLabel.loop:ShiftLeftRoundTailLabel R)
      (sparseShiftLeftLocalCfg .done [] []
        (shiftLeftBits (fixedBits w word)))
      state (shiftRoundBase w word count fuel m base) =
    lensRenamedCfg
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((shiftLeftBits (fixedBits w word)).map SparseSymbol.bit) [])
      (FullInterpreterState.shiftLens.put state default)
      (shiftAfterCoreStacks w word count fuel m base):=by
  simp [phaseReturnCfg,lensRenamedCfg,shiftRoundRenaming,
    shiftRoundDecode,sparseShiftLeftLocalCfg,sparseShiftCfg,shiftCfg,
    shiftStacks,mapAlphabetCfg,mapAlphabetStacks,sparseBitEncode,
    shiftRoundBase,shiftAfterCoreStacks,renamedStacks,
    symbolMoveCoreRenaming,symbolMoveCoreDecode,symbolMoveLocalCfg,
    symbolMoveStacks]
  constructor
  · rw [show ({ held:=none }:MoveControl)=default by rfl]
    have hm:FullInterpreterState.moveLens.get
        (FullInterpreterState.shiftLens.put state default)=default:=by
      simpa using! hmove
    rw [← hm,FullInterpreterState.moveLens.put_get]
  · funext k
    cases k <;> simp [shiftRoundBase,shiftAfterCoreStacks,renamedStacks,
      shiftRoundRenaming,shiftRoundDecode,sparseShiftLeftLocalCfg,
      sparseShiftCfg,shiftCfg,shiftStacks,mapAlphabetCfg,
      mapAlphabetStacks,sparseBitEncode,symbolMoveCoreRenaming,
      symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks]

theorem shiftLeft_firstMove_bridge {N:Nat} {R:Type}
    (w word count:Nat) (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    phaseReturnCfg
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl SymbolMoveLabel.loop:ShiftRoundFinalLabel R)
      (symbolMoveLocalCfg .done []
        ((shiftLeftBits (fixedBits w word)).map SparseSymbol.bit).reverse)
      state (shiftAfterCoreStacks w word count fuel m base) =
    lensRenamedCfg
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((shiftLeftBits (fixedBits w word)).map SparseSymbol.bit).reverse [])
      (FullInterpreterState.moveLens.put state default)
      (shiftAfterFirstMoveStacks w word count fuel m base):=by
  simp [phaseReturnCfg,lensRenamedCfg,shiftAfterCoreStacks,
    shiftAfterFirstMoveStacks,renamedStacks,symbolMoveCoreRenaming,
    symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks]
  constructor
  · rfl
  · funext k
    cases k <;> simp [shiftAfterCoreStacks,shiftAfterFirstMoveStacks,
      renamedStacks,symbolMoveCoreRenaming,symbolMoveCoreDecode,
      symbolMoveLocalCfg,symbolMoveStacks]

theorem shiftLeft_return_bridge {N:Nat} {R:Type}
    (returnLabel:R) (w word count:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens returnLabel
      (symbolMoveLocalCfg .done []
        ((shiftLeftBits (fixedBits w word)).map SparseSymbol.bit).reverse.reverse)
      state (shiftAfterFirstMoveStacks w word count fuel m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (shiftRoundBase w (2 * word) count fuel m base):=by
  simp [phaseReturnCfg,cleanReturnCfg,lensRenamedCfg,
    shiftAfterFirstMoveStacks,shiftRoundBase,renamedStacks,
    symbolMoveCoreRenaming,symbolMoveCoreDecode,symbolMoveLocalCfg,
    symbolMoveStacks,shiftLeftBits_fixed,List.map_reverse]
  funext k
  cases k <;> simp [shiftAfterFirstMoveStacks,shiftRoundBase,
    renamedStacks,symbolMoveCoreRenaming,symbolMoveCoreDecode,
    symbolMoveLocalCfg,symbolMoveStacks,shiftLeftBits_fixed]

theorem shiftLeftRound_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w word count:Nat) (hw:0 < w) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N)
    (hmove:FullInterpreterState.moveLens.get state=default):
    ∃ finalState,
      ((fun x => x.bind (TM2.step
        (shiftLeftRoundProgram returnLabel right)))^[4 * w + 8])
        (some (lensRenamedCfg shiftRoundRenaming
          FullInterpreterState.shiftLens
          (sparseShiftLeftLocalCfg .first (fixedBits w word) [] [])
          state (shiftRoundBase w word count fuel m base))) =
      some (mapLabelCfg (fun l:ShiftLeftRoundTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l:ShiftRoundFinalLabel R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (shiftRoundBase w (2 * word) count fuel m base))))):=by
  cases w with
  | zero => omega
  | succ w =>
      have hcore:=run_lensPhase_to_right shiftRoundRenaming
        FullInterpreterState.shiftLens sparseShiftLeftCoreProgram .done (by rfl)
        (Sum.inl SymbolMoveLabel.loop) (shiftLeftRoundTailProgram returnLabel right)
        (sparseShiftLeftLocal_correct_nonempty
          (Nat.bodd word) (fixedBits w word.div2)) rfl state
        (shiftRoundBase (w + 1) word count fuel m base)
      rw [show Nat.bodd word::fixedBits w word.div2 =
        fixedBits (w + 1) word by rfl] at hcore
      simp only [fixedBits_length] at hcore
      rw [shiftLeft_core_bridge (R:=R) (w + 1) word count fuel m base state
        hmove] at hcore
      let coreState:=FullInterpreterState.shiftLens.put state default
      have hfirst:=run_lensPhase_to_right
        (symbolMoveCoreRenaming .work6 .work0 (by decide))
        FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
        (Sum.inl SymbolMoveLabel.loop) (shiftRoundFinalProgram returnLabel right)
        (symbolMoveLocal_correct
          ((shiftLeftBits (fixedBits (w + 1) word)).map SparseSymbol.bit) [])
        rfl coreState (shiftAfterCoreStacks (w + 1) word count fuel m base)
      simp only [shiftLeftBits_length,fixedBits_length,List.length_map,
        List.append_nil] at hfirst
      rw [shiftLeft_firstMove_bridge (R:=R) (w + 1) word count fuel m base
        coreState] at hfirst
      let firstState:=FullInterpreterState.moveLens.put coreState default
      have hsecond:=run_lensPhase_to_right
        (symbolMoveCoreRenaming .work0 .accumulator (by decide))
        FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
        returnLabel right
        (symbolMoveLocal_correct
          ((shiftLeftBits (fixedBits (w + 1) word)).map SparseSymbol.bit).reverse [])
        rfl firstState
        (shiftAfterFirstMoveStacks (w + 1) word count fuel m base)
      simp only [List.length_reverse,List.length_map,shiftLeftBits_length,
        fixedBits_length,List.append_nil] at hsecond
      rw [shiftLeft_return_bridge returnLabel (w + 1) word count fuel m base
        firstState] at hsecond
      have htail:=chain_liftRightProgram
        (lensPhaseLeft
          (symbolMoveCoreRenaming .work6 .work0 (by decide))
          FullInterpreterState.moveLens symbolMoveCoreProgram .done
          (Sum.inl SymbolMoveLabel.loop))
        (shiftRoundFinalProgram returnLabel right) hfirst hsecond
      dsimp [coreState] at htail
      have hall:=chain_liftRightProgram
        (lensPhaseLeft shiftRoundRenaming FullInterpreterState.shiftLens
          sparseShiftLeftCoreProgram .done (Sum.inl SymbolMoveLabel.loop))
        (shiftLeftRoundTailProgram returnLabel right) hcore htail
      refine ⟨FullInterpreterState.moveLens.put firstState default, ?_⟩
      simpa [shiftLeftRoundProgram,
        show 4 * (w + 1) + 8=(2 * (w + 1) + 4) +
          ((w + 1 + 2) + (w + 1 + 2)) by omega] using hall

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def shiftRightAfterCoreStacks (w word count:Nat)
    (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol
  | .work6 => (shiftRightBits (fixedBits w word)).map SparseSymbol.bit
  | .work1 => fuel
  | .work3 => (fixedBits w count).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .accumulator | .work0 | .work2 | .work4 | .work5 | .work7 => []
  | k => base k

def shiftRightAfterFirstMoveStacks (w word count:Nat)
    (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol
  | .work0 => (shiftRightBits (fixedBits w word)).reverse.map SparseSymbol.bit
  | .work1 => fuel
  | .work3 => (fixedBits w count).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .accumulator | .work2 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

theorem shiftRight_core_bridge {N:Nat} {R:Type}
    (w word count:Nat) (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N)
    (hmove:FullInterpreterState.moveLens.get state=default):
    phaseReturnCfg shiftRoundRenaming FullInterpreterState.shiftLens
      (Sum.inl SymbolMoveLabel.loop:ShiftLeftRoundTailLabel R)
      (sparseShiftRightLocalCfg .done [] []
        (shiftRightBits (fixedBits w word)))
      state (shiftRoundBase w word count fuel m base) =
    lensRenamedCfg
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((shiftRightBits (fixedBits w word)).map SparseSymbol.bit) [])
      (FullInterpreterState.shiftLens.put state default)
      (shiftRightAfterCoreStacks w word count fuel m base):=by
  simp [phaseReturnCfg,lensRenamedCfg,shiftRoundRenaming,
    shiftRoundDecode,sparseShiftRightLocalCfg,shiftRightCfg,
    shiftStacks,mapAlphabetCfg,mapAlphabetStacks,sparseBitEncode,
    shiftRoundBase,shiftRightAfterCoreStacks,renamedStacks,
    symbolMoveCoreRenaming,symbolMoveCoreDecode,symbolMoveLocalCfg,
    symbolMoveStacks]
  constructor
  · have hm:FullInterpreterState.moveLens.get
        (FullInterpreterState.shiftLens.put state default)=default:=by
      simpa using! hmove
    rw [← hm,FullInterpreterState.moveLens.put_get]
    rfl
  · funext k
    cases k <;> simp [shiftRoundBase,shiftRightAfterCoreStacks,
      renamedStacks,shiftRoundRenaming,shiftRoundDecode,
      sparseShiftRightLocalCfg,shiftRightCfg,shiftStacks,
      mapAlphabetCfg,mapAlphabetStacks,sparseBitEncode,
      symbolMoveCoreRenaming,symbolMoveCoreDecode,symbolMoveLocalCfg,
      symbolMoveStacks]

theorem shiftRight_firstMove_bridge {N:Nat} {R:Type}
    (w word count:Nat) (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    phaseReturnCfg
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl SymbolMoveLabel.loop:ShiftRoundFinalLabel R)
      (symbolMoveLocalCfg .done []
        ((shiftRightBits (fixedBits w word)).map SparseSymbol.bit).reverse)
      state (shiftRightAfterCoreStacks w word count fuel m base) =
    lensRenamedCfg
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens
      (symbolMoveLocalCfg .loop
        ((shiftRightBits (fixedBits w word)).map SparseSymbol.bit).reverse [])
      (FullInterpreterState.moveLens.put state default)
      (shiftRightAfterFirstMoveStacks w word count fuel m base):=by
  simp [phaseReturnCfg,lensRenamedCfg,shiftRightAfterCoreStacks,
    shiftRightAfterFirstMoveStacks,renamedStacks,symbolMoveCoreRenaming,
    symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks]
  constructor
  · rfl
  · funext k
    cases k <;> simp [shiftRightAfterCoreStacks,
      shiftRightAfterFirstMoveStacks,renamedStacks,symbolMoveCoreRenaming,
      symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks]

theorem shiftRight_return_bridge {N:Nat} {R:Type}
    (returnLabel:R) (w word count:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N) (hword:word < 2 ^ w):
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens returnLabel
      (symbolMoveLocalCfg .done []
        ((shiftRightBits (fixedBits w word)).map SparseSymbol.bit).reverse.reverse)
      state (shiftRightAfterFirstMoveStacks w word count fuel m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (shiftRoundBase w (word / 2) count fuel m base):=by
  simp [phaseReturnCfg,cleanReturnCfg,lensRenamedCfg,
    shiftRightAfterFirstMoveStacks,shiftRoundBase,renamedStacks,
    symbolMoveCoreRenaming,symbolMoveCoreDecode,symbolMoveLocalCfg,
    symbolMoveStacks,shiftRightBits_fixed w word hword,List.map_reverse]
  funext k
  cases k <;> simp [shiftRightAfterFirstMoveStacks,shiftRoundBase,
    renamedStacks,symbolMoveCoreRenaming,symbolMoveCoreDecode,
    symbolMoveLocalCfg,symbolMoveStacks,shiftRightBits_fixed w word hword]

theorem shiftRightRound_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w word count:Nat) (hw:0 < w) (hword:word < 2 ^ w)
    (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N)
    (hmove:FullInterpreterState.moveLens.get state=default):
    ∃ finalState,
      ((fun x => x.bind (TM2.step
        (shiftRightRoundProgram returnLabel right)))^[4 * w + 7])
        (some (lensRenamedCfg shiftRoundRenaming
          FullInterpreterState.shiftLens
          (sparseShiftRightLocalCfg .discard (fixedBits w word) [] [])
          state (shiftRoundBase w word count fuel m base))) =
      some (mapLabelCfg (fun l:ShiftLeftRoundTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l:ShiftRoundFinalLabel R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (shiftRoundBase w (word / 2) count fuel m base))))):=by
  cases w with
  | zero => omega
  | succ w =>
      have hcore:=run_lensPhase_to_right shiftRoundRenaming
        FullInterpreterState.shiftLens sparseShiftRightCoreProgram .done (by rfl)
        (Sum.inl SymbolMoveLabel.loop) (shiftLeftRoundTailProgram returnLabel right)
        (sparseShiftRightLocal_correct_nonempty
          (Nat.bodd word) (fixedBits w word.div2)) rfl state
        (shiftRoundBase (w + 1) word count fuel m base)
      rw [show Nat.bodd word::fixedBits w word.div2 =
        fixedBits (w + 1) word by rfl] at hcore
      simp only [fixedBits_length] at hcore
      rw [shiftRight_core_bridge (R:=R) (w + 1) word count fuel m base state
        hmove] at hcore
      let coreState:=FullInterpreterState.shiftLens.put state default
      have hfirst:=run_lensPhase_to_right
        (symbolMoveCoreRenaming .work6 .work0 (by decide))
        FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
        (Sum.inl SymbolMoveLabel.loop) (shiftRoundFinalProgram returnLabel right)
        (symbolMoveLocal_correct
          ((shiftRightBits (fixedBits (w + 1) word)).map SparseSymbol.bit) [])
        rfl coreState (shiftRightAfterCoreStacks (w + 1) word count fuel m base)
      have hshiftLength:
          (shiftRightBits (fixedBits (w + 1) word)).length=w + 1:=by
        rw [shiftRightBits_length_of_ne_nil (by
          intro hnil
          have hlen:=congrArg List.length hnil
          simp at hlen)]
        simp
      simp only [hshiftLength,
        List.length_map,List.append_nil] at hfirst
      rw [shiftRight_firstMove_bridge (R:=R) (w + 1) word count fuel m base
        coreState] at hfirst
      let firstState:=FullInterpreterState.moveLens.put coreState default
      have hsecond:=run_lensPhase_to_right
        (symbolMoveCoreRenaming .work0 .accumulator (by decide))
        FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
        returnLabel right
        (symbolMoveLocal_correct
          ((shiftRightBits (fixedBits (w + 1) word)).map SparseSymbol.bit).reverse [])
        rfl firstState
        (shiftRightAfterFirstMoveStacks (w + 1) word count fuel m base)
      simp only [List.length_reverse,List.length_map,hshiftLength,
        List.append_nil] at hsecond
      rw [shiftRight_return_bridge returnLabel (w + 1) word count fuel m base
        firstState hword] at hsecond
      have htail:=chain_liftRightProgram
        (lensPhaseLeft
          (symbolMoveCoreRenaming .work6 .work0 (by decide))
          FullInterpreterState.moveLens symbolMoveCoreProgram .done
          (Sum.inl SymbolMoveLabel.loop))
        (shiftRoundFinalProgram returnLabel right) hfirst hsecond
      dsimp [coreState] at htail
      have hall:=chain_liftRightProgram
        (lensPhaseLeft shiftRoundRenaming FullInterpreterState.shiftLens
          sparseShiftRightCoreProgram .done (Sum.inl SymbolMoveLabel.loop))
        (shiftLeftRoundTailProgram returnLabel right) hcore htail
      refine ⟨FullInterpreterState.moveLens.put firstState default, ?_⟩
      simpa [shiftRightRoundProgram,
        show 4 * (w + 1) + 7=(2 * (w + 1) + 3) +
          ((w + 1 + 2) + (w + 1 + 2)) by omega] using hall

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

@[simp] theorem resetShiftControls_move {N:Nat}
    (state:FullInterpreterState N):
    FullInterpreterState.moveLens.get (resetShiftControls state)=default:=by
  cases state <;> rfl

@[simp] theorem resetShiftControls_countdown {N:Nat}
    (state:FullInterpreterState N):
    FullInterpreterState.countdownLens.get (resetShiftControls state)=default:=by
  cases state <;> rfl

@[simp] theorem resetShiftControls_shift {N:Nat}
    (state:FullInterpreterState N):
    FullInterpreterState.shiftLens.get (resetShiftControls state)=default:=by
  cases state <;> rfl

def cappedShiftStacks (w word count:Nat)
    (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol:=
  shiftRoundBase w word count fuel m base

def cappedShiftCfg {N:Nat} (label:CappedShiftLabel)
    (state:FullInterpreterState N) (w word count:Nat)
    (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N):=
  cleanReturnCfg label state (cappedShiftStacks w word count fuel m base)

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def cappedCountdownSource {N:Nat} (rightShift:Bool):
    Sum CountdownLabel CappedShiftLabel -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol)
      (Sum CountdownLabel CappedShiftLabel) (FullInterpreterState N):=
  liftRightProgram (countdownMultiLeft .cleanupFuel .fuel)
    (cappedShiftProgram rightShift)

theorem cappedCountdownSource_embeds {N:Nat} (rightShift:Bool)
    (label:Sum CountdownLabel CappedShiftLabel)
    (hn:cappedCountdownSource (N:=N) rightShift label ≠ .halt):
    cappedShiftProgram (N:=N) rightShift
        (embedCountdownController label) =
      mapLabelStmt embedCountdownController
        (cappedCountdownSource (N:=N) rightShift label):=by
  cases label with
  | inl label => rfl
  | inr label =>
      simp only [cappedCountdownSource,liftRightProgram]
      rw [mapLabelStmt_comp]
      change cappedShiftProgram (N:=N) rightShift label =
        mapLabelStmt id (cappedShiftProgram (N:=N) rightShift label)
      exact (mapLabelStmt_id _).symm

theorem cappedCountdown_zero_correct {N:Nat} (rightShift:Bool)
    (w:Nat) (state:FullInterpreterState N)
    (base:CoreStack -> List SparseSymbol):
    ((fun x => x.bind (TM2.step (cappedShiftProgram rightShift)))^[w + 2])
      (some (mapLabelCfg embedCountdownController
        (lensRenamedCfg countdownCoreRenaming
          FullInterpreterState.countdownLens
          (sparseCountdownCfg .scan default (fixedBits w 0) [])
          state base))) =
    some (mapLabelCfg embedCountdownController
      (mapLabelCfg Sum.inr
        (multiPhaseReturnCfg countdownCoreRenaming
          FullInterpreterState.countdownLens CappedShiftLabel.cleanupFuel id
          (sparseCountdownCfg .zero
            { held:=none,borrow:=true,positiveSeen:=false }
            [] (List.replicate w true)) state base))):=by
  have hrun:=globalCountdown_zero_correct
    CappedShiftLabel.cleanupFuel CappedShiftLabel.fuel
    (cappedShiftProgram rightShift) w state base
  apply iterate_mapLabelProgram_until_exit
    (cappedCountdownSource rightShift) (cappedShiftProgram rightShift)
    embedCountdownController (cappedCountdownSource_embeds rightShift)
    hrun
  rfl

theorem cappedCountdown_positive_correct {N:Nat} (rightShift:Bool)
    (w d:Nat) (hd0:0 < d) (hd:d < 2 ^ w)
    (state:FullInterpreterState N)
    (base:CoreStack -> List SparseSymbol):
    ∃ localFinal,
      ((fun x => x.bind (TM2.step (cappedShiftProgram rightShift)))^[
          2 * w + 3])
        (some (mapLabelCfg embedCountdownController
          (lensRenamedCfg countdownCoreRenaming
            FullInterpreterState.countdownLens
            (sparseCountdownCfg .scan default (fixedBits w d) [])
            state base))) =
      some (mapLabelCfg embedCountdownController
        (mapLabelCfg Sum.inr
          (multiPhaseReturnCfg countdownCoreRenaming
            FullInterpreterState.countdownLens CappedShiftLabel.fuel id
            (sparseCountdownCfg .positive localFinal
              (fixedBits w (d - 1)) []) state base))):=by
  rcases globalCountdown_positive_correct
      CappedShiftLabel.cleanupFuel CappedShiftLabel.fuel
      (cappedShiftProgram rightShift) w d hd0 hd state base with
    ⟨localFinal,hrun⟩
  refine ⟨localFinal, ?_⟩
  apply iterate_mapLabelProgram_until_exit
    (cappedCountdownSource rightShift) (cappedShiftProgram rightShift)
    embedCountdownController (cappedCountdownSource_embeds rightShift)
    hrun
  rfl

def embedLeftController:ShiftLeftRoundLabel Unit -> CappedShiftLabel:=
  CappedShiftLabel.left

theorem cappedLeftSource_embeds {N:Nat}
    (label:ShiftLeftRoundLabel Unit)
    (hn:shiftLeftRoundProgram (N:=N) () (fun _ => .halt) label ≠ .halt):
    cappedShiftProgram (N:=N) false (embedLeftController label) =
      mapLabelStmt embedLeftController
        (shiftLeftRoundProgram () (fun _ => .halt) label):=by
  rcases label with label | tail
  · rfl
  rcases tail with label | tail
  · rfl
  rcases tail with label | tail
  · rfl
  cases tail
  exact False.elim (hn rfl)

theorem cappedLeftRound_correct {N:Nat}
    (w word count:Nat) (hw:0 < w)
    (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N)
    (hmove:FullInterpreterState.moveLens.get state=default):
    ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram false)))^[4 * w + 8])
        (some (mapLabelCfg embedLeftController
          (lensRenamedCfg shiftRoundRenaming FullInterpreterState.shiftLens
            (sparseShiftLeftLocalCfg .first (fixedBits w word) [] [])
            state (shiftRoundBase w word count fuel m base)))) =
      some (mapLabelCfg embedLeftController
        (mapLabelCfg (fun l:ShiftLeftRoundTailLabel Unit => Sum.inr l)
          (mapLabelCfg (fun l:ShiftRoundFinalLabel Unit => Sum.inr l)
            (mapLabelCfg (fun l:Unit => Sum.inr l)
              (cleanReturnCfg () finalState
                (shiftRoundBase w (2 * word) count fuel m base)))))):=by
  rcases shiftLeftRound_correct () (fun _ => .halt) w word count hw fuel m
      base state hmove with ⟨finalState,hrun⟩
  refine ⟨finalState, ?_⟩
  apply iterate_mapLabelProgram_until_exit
    (shiftLeftRoundProgram () (fun _ => .halt))
    (cappedShiftProgram false) embedLeftController cappedLeftSource_embeds hrun
  rfl

def embedRightController:ShiftRightRoundLabel Unit -> CappedShiftLabel:=
  CappedShiftLabel.right

theorem cappedRightSource_embeds {N:Nat}
    (label:ShiftRightRoundLabel Unit)
    (hn:shiftRightRoundProgram (N:=N) () (fun _ => .halt) label ≠ .halt):
    cappedShiftProgram (N:=N) true (embedRightController label) =
      mapLabelStmt embedRightController
        (shiftRightRoundProgram () (fun _ => .halt) label):=by
  rcases label with label | tail
  · rfl
  rcases tail with label | tail
  · rfl
  rcases tail with label | tail
  · rfl
  cases tail
  exact False.elim (hn rfl)

theorem cappedRightRound_correct {N:Nat}
    (w word count:Nat) (hw:0 < w) (hword:word < 2 ^ w)
    (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N)
    (hmove:FullInterpreterState.moveLens.get state=default):
    ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram true)))^[4 * w + 7])
        (some (mapLabelCfg embedRightController
          (lensRenamedCfg shiftRoundRenaming FullInterpreterState.shiftLens
            (sparseShiftRightLocalCfg .discard (fixedBits w word) [] [])
            state (shiftRoundBase w word count fuel m base)))) =
      some (mapLabelCfg embedRightController
        (mapLabelCfg (fun l:ShiftLeftRoundTailLabel Unit => Sum.inr l)
          (mapLabelCfg (fun l:ShiftRoundFinalLabel Unit => Sum.inr l)
            (mapLabelCfg (fun l:Unit => Sum.inr l)
              (cleanReturnCfg () finalState
                (shiftRoundBase w (word / 2) count fuel m base)))))):=by
  rcases shiftRightRound_correct () (fun _ => .halt) w word count hw hword
      fuel m base state hmove with ⟨finalState,hrun⟩
  refine ⟨finalState, ?_⟩
  apply iterate_mapLabelProgram_until_exit
    (shiftRightRoundProgram () (fun _ => .halt))
    (cappedShiftProgram true) embedRightController cappedRightSource_embeds hrun
  rfl

theorem cappedShift_fuel_left_step {N:Nat}
    (w word count:Nat) (symbol:SparseSymbol)
    (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    TM2.step (cappedShiftProgram false)
      (cappedShiftCfg .fuel state w word count (symbol::fuel) m base) =
    some (cappedShiftCfg (.left (Sum.inl .first))
      (resetShiftControls state) w word count fuel m base):=by
  simp [cappedShiftProgram,cappedShiftCfg,cappedShiftStacks,
    cleanReturnCfg,shiftRoundBase,TM2.step,TM2.stepAux,
    resetShiftControls,FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  congr 2
  funext k
  cases k <;> simp [shiftRoundBase,Function.update]

theorem cappedShift_fuel_right_step {N:Nat}
    (w word count:Nat) (symbol:SparseSymbol)
    (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    TM2.step (cappedShiftProgram true)
      (cappedShiftCfg .fuel state w word count (symbol::fuel) m base) =
    some (cappedShiftCfg (.right (Sum.inl .discard))
      (resetShiftControls state) w word count fuel m base):=by
  simp [cappedShiftProgram,cappedShiftCfg,cappedShiftStacks,
    cleanReturnCfg,shiftRoundBase,TM2.step,TM2.stepAux,
    resetShiftControls,FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  congr 2
  funext k
  cases k <;> simp [shiftRoundBase,Function.update]

theorem cappedShift_fuel_empty_step {N:Nat} (rightShift:Bool)
    (w word count:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    TM2.step (cappedShiftProgram rightShift)
      (cappedShiftCfg .fuel state w word count [] m base) =
    some (cappedShiftCfg .cleanupFuel
      (FullInterpreterState.moveLens.put state ⟨none⟩)
      w word count [] m base):=by
  simp [cappedShiftProgram,cappedShiftCfg,cappedShiftStacks,
    cleanReturnCfg,shiftRoundBase,TM2.step,TM2.stepAux,
    FullInterpreterState.moveLens.get_put]

def controllerCfg {N:Nat} (label:CappedShiftLabel)
    (state:FullInterpreterState N)
    (tapes:CoreStack -> List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N):=
  cleanReturnCfg label state tapes

theorem cappedShift_cleanup_cons_step {N:Nat} (rightShift:Bool)
    (stack:CoreStack) (again next:CappedShiftLabel)
    (hprogram:cappedShiftProgram (N:=N) rightShift again =
      cappedShiftCleanupStmt stack again next)
    (symbol:SparseSymbol) (rest:List SparseSymbol)
    (state:FullInterpreterState N)
    (tapes:CoreStack -> List SparseSymbol)
    (hstack:tapes stack=symbol::rest):
    TM2.step (cappedShiftProgram rightShift)
      (controllerCfg again state tapes) =
    some (controllerCfg again
      (FullInterpreterState.moveLens.put state default)
      (Function.update tapes stack rest)):=by
  simp [controllerCfg,cleanReturnCfg,TM2.step,hprogram,
    cappedShiftCleanupStmt,TM2.stepAux,hstack,
    FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]

theorem cappedShift_cleanup_nil_step {N:Nat} (rightShift:Bool)
    (stack:CoreStack) (again next:CappedShiftLabel)
    (hprogram:cappedShiftProgram (N:=N) rightShift again =
      cappedShiftCleanupStmt stack again next)
    (state:FullInterpreterState N)
    (tapes:CoreStack -> List SparseSymbol)
    (hstack:tapes stack=[]):
    TM2.step (cappedShiftProgram rightShift)
      (controllerCfg again state tapes) =
    some (controllerCfg next
      (FullInterpreterState.moveLens.put state ⟨none⟩)
      (Function.update tapes stack [])):=by
  simp [controllerCfg,cleanReturnCfg,TM2.step,hprogram,
    cappedShiftCleanupStmt,TM2.stepAux,hstack,
    FullInterpreterState.moveLens.get_put]

theorem cappedShift_cleanup_drain {N:Nat} (rightShift:Bool)
    (stack:CoreStack) (again next:CappedShiftLabel)
    (hprogram:cappedShiftProgram (N:=N) rightShift again =
      cappedShiftCleanupStmt stack again next)
    (data:List SparseSymbol) (state:FullInterpreterState N)
    (tapes:CoreStack -> List SparseSymbol)
    (hstack:tapes stack=data):
    ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram rightShift)))^[
          data.length + 1])
        (some (controllerCfg again state tapes)) =
      some (controllerCfg next finalState
        (Function.update tapes stack [])):=by
  induction data generalizing state tapes with
  | nil =>
      refine ⟨FullInterpreterState.moveLens.put state ⟨none⟩, ?_⟩
      simpa using cappedShift_cleanup_nil_step rightShift stack again next
        hprogram state tapes hstack
  | cons symbol rest ih =>
      have hfirst:=cappedShift_cleanup_cons_step rightShift stack again next
        hprogram symbol rest state tapes hstack
      let tapes':=Function.update tapes stack rest
      have hstack':tapes' stack=rest:=by
        simp [tapes']
      rcases ih (FullInterpreterState.moveLens.put state default)
          tapes' hstack' with ⟨finalState,hrest⟩
      refine ⟨finalState, ?_⟩
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,hfirst]
      simpa [tapes',Function.update_idem] using hrest

theorem cappedShift_cleanup_all {N:Nat} (rightShift:Bool)
    (fuel count temp:List SparseSymbol)
    (state:FullInterpreterState N)
    (tapes:CoreStack -> List SparseSymbol)
    (hfuel:tapes .work1=fuel) (hcount:tapes .work3=count)
    (htemp:tapes .work4=temp):
    ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram rightShift)))^[
          fuel.length + count.length + temp.length + 3])
        (some (controllerCfg .cleanupFuel state tapes)) =
      some (controllerCfg .done finalState
        (Function.update
          (Function.update (Function.update tapes .work1 []) .work3 [])
          .work4 [])):=by
  rcases cappedShift_cleanup_drain rightShift .work1 .cleanupFuel
      .cleanupCount (by rfl) fuel state tapes hfuel with
    ⟨state₁,h₁⟩
  let tapes₁:=Function.update tapes CoreStack.work1 []
  have hcount₁:tapes₁ .work3=count:=by
    simp [tapes₁,hcount]
  rcases cappedShift_cleanup_drain rightShift .work3 .cleanupCount
      .cleanupTemp (by rfl) count state₁ tapes₁ hcount₁ with
    ⟨state₂,h₂⟩
  let tapes₂:=Function.update tapes₁ CoreStack.work3 []
  have htemp₂:tapes₂ .work4=temp:=by
    simp [tapes₂,tapes₁,htemp]
  rcases cappedShift_cleanup_drain rightShift .work4 .cleanupTemp
      .done (by rfl) temp state₂ tapes₂ htemp₂ with
    ⟨state₃,h₃⟩
  refine ⟨state₃, ?_⟩
  let stepO:=fun x:Option (TM2.Cfg
      (fun _:CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (cappedShiftProgram rightShift))
  have h₁₂:=chain_iterations stepO h₁ h₂
  have h₁₂₃:=chain_iterations stepO h₁₂ h₃
  simpa [stepO,tapes₂,tapes₁,
    show (fuel.length + 1) + (count.length + 1) + (temp.length + 1) =
      fuel.length + count.length + temp.length + 3 by omega] using h₁₂₃

theorem cappedCountdown_start_bridge {N:Nat}
    (w word count:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    mapLabelCfg embedCountdownController
      (lensRenamedCfg countdownCoreRenaming
        FullInterpreterState.countdownLens
        (sparseCountdownCfg .scan default (fixedBits w count) [])
        state (shiftRoundBase w word count fuel m base)) =
    cappedShiftCfg (.countdown .scan)
      (FullInterpreterState.countdownLens.put state default)
      w word count fuel m base:=by
  simp [mapLabelCfg,lensRenamedCfg,sparseCountdownCfg,countdownCfg,
    mapAlphabetCfg,mapAlphabetStacks,sparseBitEncode,
    cappedShiftCfg,cappedShiftStacks,cleanReturnCfg,shiftRoundBase,
    renamedStacks,countdownCoreRenaming,countdownCoreDecode]
  constructor
  · exact Or.inl ⟨.scan,rfl,rfl⟩
  · funext k
    cases k <;> simp [shiftRoundBase,renamedStacks,countdownCoreRenaming,
      countdownCoreDecode,countdownCfg,countdownStacks,
      mapAlphabetCfg,mapAlphabetStacks,sparseBitEncode]

theorem cappedCountdown_positive_bridge {N:Nat}
    (localFinal:CountdownControl) (w word oldCount count:Nat)
    (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    mapLabelCfg embedCountdownController
      (mapLabelCfg Sum.inr
        (multiPhaseReturnCfg countdownCoreRenaming
          FullInterpreterState.countdownLens CappedShiftLabel.fuel id
          (sparseCountdownCfg .positive localFinal
            (fixedBits w count) []) state
          (shiftRoundBase w word oldCount fuel m base))) =
    cappedShiftCfg .fuel
      (FullInterpreterState.countdownLens.put state localFinal)
      w word count fuel m base:=by
  simp [mapLabelCfg,multiPhaseReturnCfg,sparseCountdownCfg,countdownCfg,
    mapAlphabetCfg,mapAlphabetStacks,sparseBitEncode,
    cappedShiftCfg,cappedShiftStacks,cleanReturnCfg,shiftRoundBase,
    renamedStacks,countdownCoreRenaming,countdownCoreDecode]
  constructor
  · rfl
  · funext k
    cases k <;> simp [shiftRoundBase,renamedStacks,countdownCoreRenaming,
      countdownCoreDecode,countdownCfg,countdownStacks,
      mapAlphabetCfg,mapAlphabetStacks,sparseBitEncode]

theorem cappedLeft_start_bridge {N:Nat}
    (w word count:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    mapLabelCfg embedLeftController
      (lensRenamedCfg shiftRoundRenaming FullInterpreterState.shiftLens
        (sparseShiftLeftLocalCfg .first (fixedBits w word) [] [])
        state (shiftRoundBase w word count fuel m base)) =
    cappedShiftCfg (.left (Sum.inl .first))
      (FullInterpreterState.shiftLens.put state default)
      w word count fuel m base:=by
  simp [mapLabelCfg,lensRenamedCfg,sparseShiftLeftLocalCfg,
    mapAlphabetCfg,mapAlphabetStacks,sparseBitEncode,shiftCfg,shiftStacks,
    cappedShiftCfg,cappedShiftStacks,cleanReturnCfg,shiftRoundBase,
    renamedStacks,shiftRoundRenaming,shiftRoundDecode]
  constructor
  · exact Or.inl ⟨.first,rfl,rfl⟩
  · constructor
    · rfl
    · funext k
      cases k <;> simp [shiftRoundBase,renamedStacks,shiftRoundRenaming,
        shiftRoundDecode,sparseShiftLeftLocalCfg,mapAlphabetCfg,
        mapAlphabetStacks,sparseBitEncode,shiftCfg,shiftStacks]

theorem cappedRight_start_bridge {N:Nat}
    (w word count:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    mapLabelCfg embedRightController
      (lensRenamedCfg shiftRoundRenaming FullInterpreterState.shiftLens
        (sparseShiftRightLocalCfg .discard (fixedBits w word) [] [])
        state (shiftRoundBase w word count fuel m base)) =
    cappedShiftCfg (.right (Sum.inl .discard))
      (FullInterpreterState.shiftLens.put state default)
      w word count fuel m base:=by
  simp [mapLabelCfg,lensRenamedCfg,sparseShiftRightLocalCfg,
    mapAlphabetCfg,mapAlphabetStacks,sparseBitEncode,
    shiftRightCfg,shiftStacks,cappedShiftCfg,cappedShiftStacks,
    cleanReturnCfg,shiftRoundBase,renamedStacks,shiftRoundRenaming,
    shiftRoundDecode]
  constructor
  · exact Or.inl ⟨.discard,rfl,rfl⟩
  · constructor
    · rfl
    · funext k
      cases k <;> simp [shiftRoundBase,renamedStacks,shiftRoundRenaming,
        shiftRoundDecode,sparseShiftRightLocalCfg,mapAlphabetCfg,
        mapAlphabetStacks,sparseBitEncode,shiftRightCfg,shiftStacks]

theorem cappedLeft_return_bridge {N:Nat}
    (w word count:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    mapLabelCfg embedLeftController
      (mapLabelCfg (fun l:ShiftLeftRoundTailLabel Unit => Sum.inr l)
        (mapLabelCfg (fun l:ShiftRoundFinalLabel Unit => Sum.inr l)
          (mapLabelCfg (fun l:Unit => Sum.inr l)
            (cleanReturnCfg () state
              (shiftRoundBase w word count fuel m base))))) =
    cappedShiftCfg (.left (Sum.inr (Sum.inr (Sum.inr ()))))
      state w word count fuel m base:=by
  rfl

theorem cappedRight_return_bridge {N:Nat}
    (w word count:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    mapLabelCfg embedRightController
      (mapLabelCfg (fun l:ShiftLeftRoundTailLabel Unit => Sum.inr l)
        (mapLabelCfg (fun l:ShiftRoundFinalLabel Unit => Sum.inr l)
          (mapLabelCfg (fun l:Unit => Sum.inr l)
            (cleanReturnCfg () state
              (shiftRoundBase w word count fuel m base))))) =
    cappedShiftCfg (.right (Sum.inr (Sum.inr (Sum.inr ()))))
      state w word count fuel m base:=by
  rfl

theorem cappedShift_left_return_step {N:Nat}
    (w word count:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    TM2.step (cappedShiftProgram false)
      (cappedShiftCfg (.left (Sum.inr (Sum.inr (Sum.inr ()))))
        state w word count fuel m base) =
    some (cappedShiftCfg (.countdown .scan)
      (FullInterpreterState.countdownLens.put state default)
      w word count fuel m base):=by
  rfl

theorem cappedShift_right_return_step {N:Nat}
    (w word count:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    TM2.step (cappedShiftProgram true)
      (cappedShiftCfg (.right (Sum.inr (Sum.inr (Sum.inr ()))))
        state w word count fuel m base) =
    some (cappedShiftCfg (.countdown .scan)
      (FullInterpreterState.countdownLens.put state default)
      w word count fuel m base):=by
  rfl

theorem shiftRoundBase_word_mod (w word count:Nat)
    (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):
    shiftRoundBase w word count fuel m base =
      shiftRoundBase w (word % 2 ^ w) count fuel m base:=by
  funext k
  cases k <;> simp [shiftRoundBase,fixedBits_mod_word]

theorem cappedShiftCfg_word_mod {N:Nat} (label:CappedShiftLabel)
    (state:FullInterpreterState N) (w word count:Nat)
    (fuel:List SparseSymbol) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):
    cappedShiftCfg label state w word count fuel m base =
      cappedShiftCfg label state w (word % 2 ^ w) count fuel m base:=by
  simp only [cappedShiftCfg,cappedShiftStacks]
  rw [shiftRoundBase_word_mod]

theorem cappedLeft_cycle_correct {N:Nat}
    (w word count:Nat) (hw:0 < w)
    (hcount0:0 < count) (hcount:count < 2 ^ w)
    (symbol:SparseSymbol) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N)
    (hcountdown:FullInterpreterState.countdownLens.get state=default):
    ∃ finalState,
      FullInterpreterState.countdownLens.get finalState=default∧
      ((fun x => x.bind (TM2.step (cappedShiftProgram false)))^[6 * w + 13])
        (some (cappedShiftCfg (.countdown .scan)
          state w word count (symbol::fuel) m base)) =
      some (cappedShiftCfg (.countdown .scan) finalState w
        ((2 * word) % 2 ^ w) (count - 1) fuel m base):=by
  rcases cappedCountdown_positive_correct false w count hcount0 hcount state
      (shiftRoundBase w word count (symbol::fuel) m base) with
    ⟨countState,hcountRun⟩
  rw [cappedCountdown_start_bridge w word count (symbol::fuel) m base state]
    at hcountRun
  rw [cappedCountdown_positive_bridge countState w word count (count - 1)
      (symbol::fuel) m base state] at hcountRun
  have hstate:FullInterpreterState.countdownLens.put state default=state:=by
    rw [← hcountdown]
    exact FullInterpreterState.countdownLens.put_get state
  rw [hstate] at hcountRun
  let afterCount:=FullInterpreterState.countdownLens.put state countState
  have hfuel:=cappedShift_fuel_left_step w word (count - 1) symbol fuel m
    base afterCount
  let roundState:=resetShiftControls afterCount
  rcases cappedLeftRound_correct w word (count - 1) hw fuel m base roundState
      (resetShiftControls_move afterCount) with ⟨afterRound,hround⟩
  rw [cappedLeft_start_bridge w word (count - 1) fuel m base roundState]
    at hround
  rw [show FullInterpreterState.shiftLens.put roundState default=roundState by
      rw [← resetShiftControls_shift afterCount]
      exact FullInterpreterState.shiftLens.put_get roundState] at hround
  rw [cappedLeft_return_bridge w (2 * word) (count - 1) fuel m base afterRound]
    at hround
  have hreturn:=cappedShift_left_return_step w (2 * word) (count - 1)
    fuel m base afterRound
  let cycleState:=FullInterpreterState.countdownLens.put afterRound default
  let stepO:=fun x:Option (TM2.Cfg
      (fun _:CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (cappedShiftProgram false))
  have hfuel':(stepO^[1])
      (some (cappedShiftCfg .fuel afterCount w word (count - 1)
        (symbol::fuel) m base)) =
      some (cappedShiftCfg (.left (Sum.inl .first)) roundState
        w word (count - 1) fuel m base):=by
    simpa [stepO,roundState] using hfuel
  have hreturn':(stepO^[1])
      (some (cappedShiftCfg (.left (Sum.inr (Sum.inr (Sum.inr ()))))
        afterRound w (2 * word) (count - 1) fuel m base)) =
      some (cappedShiftCfg (.countdown .scan) cycleState
        w (2 * word) (count - 1) fuel m base):=by
    simpa [stepO,cycleState] using hreturn
  have h₁:=chain_iterations stepO hcountRun hfuel'
  have h₂:=chain_iterations stepO h₁ hround
  have h₃:=chain_iterations stepO h₂ hreturn'
  rw [cappedShiftCfg_word_mod (.countdown .scan) cycleState w (2 * word)
    (count - 1) fuel m base] at h₃
  refine ⟨cycleState,FullInterpreterState.countdownLens.get_put _ _, ?_⟩
  simpa [stepO,afterCount,roundState,
    show (2 * w + 3) + 1 + (4 * w + 8) + 1=6 * w + 13 by omega]
    using h₃

theorem cappedRight_cycle_correct {N:Nat}
    (w word count:Nat) (hw:0 < w) (hword:word < 2 ^ w)
    (hcount0:0 < count) (hcount:count < 2 ^ w)
    (symbol:SparseSymbol) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N)
    (hcountdown:FullInterpreterState.countdownLens.get state=default):
    ∃ finalState,
      FullInterpreterState.countdownLens.get finalState=default∧
      ((fun x => x.bind (TM2.step (cappedShiftProgram true)))^[6 * w + 12])
        (some (cappedShiftCfg (.countdown .scan)
          state w word count (symbol::fuel) m base)) =
      some (cappedShiftCfg (.countdown .scan) finalState w
        (word / 2) (count - 1) fuel m base):=by
  rcases cappedCountdown_positive_correct true w count hcount0 hcount state
      (shiftRoundBase w word count (symbol::fuel) m base) with
    ⟨countState,hcountRun⟩
  rw [cappedCountdown_start_bridge w word count (symbol::fuel) m base state]
    at hcountRun
  rw [cappedCountdown_positive_bridge countState w word count (count - 1)
      (symbol::fuel) m base state] at hcountRun
  have hstate:FullInterpreterState.countdownLens.put state default=state:=by
    rw [← hcountdown]
    exact FullInterpreterState.countdownLens.put_get state
  rw [hstate] at hcountRun
  let afterCount:=FullInterpreterState.countdownLens.put state countState
  have hfuel:=cappedShift_fuel_right_step w word (count - 1) symbol fuel m
    base afterCount
  let roundState:=resetShiftControls afterCount
  rcases cappedRightRound_correct w word (count - 1) hw hword fuel m base
      roundState (resetShiftControls_move afterCount) with
    ⟨afterRound,hround⟩
  rw [cappedRight_start_bridge w word (count - 1) fuel m base roundState]
    at hround
  rw [show FullInterpreterState.shiftLens.put roundState default=roundState by
      rw [← resetShiftControls_shift afterCount]
      exact FullInterpreterState.shiftLens.put_get roundState] at hround
  rw [cappedRight_return_bridge w (word / 2) (count - 1) fuel m base
    afterRound] at hround
  have hreturn:=cappedShift_right_return_step w (word / 2) (count - 1)
    fuel m base afterRound
  let cycleState:=FullInterpreterState.countdownLens.put afterRound default
  let stepO:=fun x:Option (TM2.Cfg
      (fun _:CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (cappedShiftProgram true))
  have hfuel':(stepO^[1])
      (some (cappedShiftCfg .fuel afterCount w word (count - 1)
        (symbol::fuel) m base)) =
      some (cappedShiftCfg (.right (Sum.inl .discard)) roundState
        w word (count - 1) fuel m base):=by
    simpa [stepO,roundState] using hfuel
  have hreturn':(stepO^[1])
      (some (cappedShiftCfg (.right (Sum.inr (Sum.inr (Sum.inr ()))))
        afterRound w (word / 2) (count - 1) fuel m base)) =
      some (cappedShiftCfg (.countdown .scan) cycleState
        w (word / 2) (count - 1) fuel m base):=by
    simpa [stepO,cycleState] using hreturn
  have h₁:=chain_iterations stepO hcountRun hfuel'
  have h₂:=chain_iterations stepO h₁ hround
  have h₃:=chain_iterations stepO h₂ hreturn'
  refine ⟨cycleState,FullInterpreterState.countdownLens.get_put _ _, ?_⟩
  simpa [stepO,afterCount,roundState,
    show (2 * w + 3) + 1 + (4 * w + 7) + 1=6 * w + 12 by omega]
    using h₃

theorem cappedShift_cleanup_roundBase {N:Nat} (rightShift:Bool)
    (w word count:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram rightShift)))^[
          fuel.length + w + 3])
        (some (cappedShiftCfg .cleanupFuel state
          w word count fuel m base)) =
      some (controllerCfg .done finalState
        (operandBoundaryBase w word m base)):=by
  rcases cappedShift_cleanup_all rightShift fuel
      ((fixedBits w count).map SparseSymbol.bit) [] state
      (shiftRoundBase w word count fuel m base)
      (by rfl) (by rfl) (by rfl) with ⟨finalState,hrun⟩
  refine ⟨finalState, ?_⟩
  have htapes:
      Function.update
        (Function.update
          (Function.update (shiftRoundBase w word count fuel m base)
            .work1 []) .work3 []) .work4 [] =
      operandBoundaryBase w word m base:=by
    funext k
    cases k <;> simp [shiftRoundBase,operandBoundaryBase,Function.update]
  simpa [cappedShiftCfg,cappedShiftStacks,List.length_map,
    fixedBits_length,htapes] using! hrun

def zeroShiftCleanupBase (w word:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w word).map SparseSymbol.bit
  | .work1 => fuel
  | .work4 => List.replicate w (.bit true)
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work0 | .work2 | .work3 | .work5 | .work6 | .work7 => []
  | k => base k

theorem cappedCountdown_zero_bridge {N:Nat}
    (w word:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    mapLabelCfg embedCountdownController
      (mapLabelCfg Sum.inr
        (multiPhaseReturnCfg countdownCoreRenaming
          FullInterpreterState.countdownLens CappedShiftLabel.cleanupFuel id
          (sparseCountdownCfg .zero
            { held:=none,borrow:=true,positiveSeen:=false }
            [] (List.replicate w true)) state
          (shiftRoundBase w word 0 fuel m base))) =
    controllerCfg .cleanupFuel
      (FullInterpreterState.countdownLens.put state
        { held:=none,borrow:=true,positiveSeen:=false })
      (zeroShiftCleanupBase w word fuel m base):=by
  simp [mapLabelCfg,multiPhaseReturnCfg,sparseCountdownCfg,countdownCfg,
    mapAlphabetCfg,mapAlphabetStacks,sparseBitEncode,controllerCfg,
    cleanReturnCfg,zeroShiftCleanupBase,shiftRoundBase,renamedStacks,
    countdownCoreRenaming,countdownCoreDecode]
  constructor
  · rfl
  · funext k
    cases k <;> simp [zeroShiftCleanupBase,shiftRoundBase,renamedStacks,
      countdownCoreRenaming,countdownCoreDecode,countdownCfg,
      countdownStacks,mapAlphabetCfg,mapAlphabetStacks,sparseBitEncode]

theorem cappedShift_zero_finish {N:Nat} (rightShift:Bool)
    (w word:Nat) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N)
    (hcountdown:FullInterpreterState.countdownLens.get state=default):
    ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram rightShift)))^[
          fuel.length + 2 * w + 5])
        (some (cappedShiftCfg (.countdown .scan)
          state w word 0 fuel m base)) =
      some (controllerCfg .done finalState
        (operandBoundaryBase w word m base)):=by
  have hzero:=cappedCountdown_zero_correct rightShift w state
    (shiftRoundBase w word 0 fuel m base)
  rw [cappedCountdown_start_bridge w word 0 fuel m base state] at hzero
  rw [cappedCountdown_zero_bridge w word fuel m base state] at hzero
  have hstate:FullInterpreterState.countdownLens.put state default=state:=by
    rw [← hcountdown]
    exact FullInterpreterState.countdownLens.put_get state
  rw [hstate] at hzero
  let zeroState:=FullInterpreterState.countdownLens.put state
    { held:=none,borrow:=true,positiveSeen:=false }
  rcases cappedShift_cleanup_all rightShift fuel []
      (List.replicate w (.bit true)) zeroState
      (zeroShiftCleanupBase w word fuel m base)
      (by rfl) (by rfl) (by rfl) with ⟨finalState,hclean⟩
  have htapes:
      Function.update
        (Function.update
          (Function.update (zeroShiftCleanupBase w word fuel m base)
            .work1 []) .work3 []) .work4 [] =
      operandBoundaryBase w word m base:=by
    funext k
    cases k <;> simp [zeroShiftCleanupBase,operandBoundaryBase,
      Function.update]
  let stepO:=fun x:Option (TM2.Cfg
      (fun _:CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (cappedShiftProgram rightShift))
  rw [htapes] at hclean
  simp only [List.length_nil,List.length_replicate] at hclean
  have hall:=chain_iterations stepO hzero hclean
  refine ⟨finalState, ?_⟩
  change (stepO^[fuel.length + 2 * w + 5])
    (some (cappedShiftCfg (.countdown .scan)
      state w word 0 fuel m base))=_
  rw [show fuel.length + 2 * w + 5 =
    (w + 2) + (fuel.length + 0 + w + 3) by omega]
  exact hall

theorem cappedShift_positive_noFuel_finish {N:Nat} (rightShift:Bool)
    (w word count:Nat) (hcount0:0 < count)
    (hcount:count < 2 ^ w)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N)
    (hcountdown:FullInterpreterState.countdownLens.get state=default):
    ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram rightShift)))^[
          3 * w + 7])
        (some (cappedShiftCfg (.countdown .scan)
          state w word count [] m base)) =
      some (controllerCfg .done finalState
        (operandBoundaryBase w word m base)):=by
  rcases cappedCountdown_positive_correct rightShift w count hcount0 hcount state
      (shiftRoundBase w word count [] m base) with
    ⟨countState,hcountRun⟩
  rw [cappedCountdown_start_bridge w word count [] m base state] at hcountRun
  rw [cappedCountdown_positive_bridge countState w word count (count - 1)
      [] m base state] at hcountRun
  have hstate:FullInterpreterState.countdownLens.put state default=state:=by
    rw [← hcountdown]
    exact FullInterpreterState.countdownLens.put_get state
  rw [hstate] at hcountRun
  let afterCount:=FullInterpreterState.countdownLens.put state countState
  have hfuel:=cappedShift_fuel_empty_step rightShift w word (count - 1)
    m base afterCount
  let afterFuel:=FullInterpreterState.moveLens.put afterCount ⟨none⟩
  rcases cappedShift_cleanup_roundBase rightShift w word (count - 1) [] m base
      afterFuel with ⟨finalState,hclean⟩
  let stepO:=fun x:Option (TM2.Cfg
      (fun _:CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (cappedShiftProgram rightShift))
  have hfuel':(stepO^[1])
      (some (cappedShiftCfg .fuel afterCount w word (count - 1) [] m base)) =
      some (cappedShiftCfg .cleanupFuel afterFuel
        w word (count - 1) [] m base):=by
    simpa [stepO,afterFuel] using hfuel
  have h₁:=chain_iterations stepO hcountRun hfuel'
  have h₂:=chain_iterations stepO h₁ hclean
  refine ⟨finalState, ?_⟩
  change (stepO^[3 * w + 7])
    (some (cappedShiftCfg (.countdown .scan)
      state w word count [] m base))=_
  rw [show 3 * w + 7=(2 * w + 3) + 1 + (0 + w + 3) by omega]
  exact h₂

theorem fuel_le_cappedShiftLoopBound (w fuel:Nat):
    fuel <= cappedShiftLoopBound w fuel:=by
  induction fuel with
  | zero => simp [cappedShiftLoopBound]
  | succ fuel ih =>
      simp [cappedShiftLoopBound]
      omega

def cappedLeftValue (w word count:Nat):Nat -> Nat
  | 0 => word
  | fuel + 1 =>
      if count=0 then word
      else cappedLeftValue w ((2 * word) % 2 ^ w) (count - 1) fuel

def cappedRightValue (word count:Nat):Nat -> Nat
  | 0 => word
  | fuel + 1 =>
      if count=0 then word
      else cappedRightValue (word / 2) (count - 1) fuel

theorem min_succ_of_pos (count fuel:Nat) (hcount:0 < count):
    min count (fuel + 1)=min (count - 1) fuel + 1:=by
  omega

theorem cappedLeftValue_eq_min (w word count fuel:Nat)
    (hword:word < 2 ^ w):
    cappedLeftValue w word count fuel =
      word * 2 ^ min count fuel % 2 ^ w:=by
  induction fuel generalizing word count with
  | zero =>
      simp [cappedLeftValue,Nat.mod_eq_of_lt hword]
  | succ fuel ih =>
      by_cases hc0:count=0
      · subst count
        simp [cappedLeftValue,Nat.mod_eq_of_lt hword]
      · have hcpos:0 < count:=Nat.pos_of_ne_zero hc0
        let word':=2 * word % 2 ^ w
        have hword':word' < 2 ^ w:=Nat.mod_lt _ (by positivity)
        rw [cappedLeftValue]
        simp only [hc0, ↓reduceIte]
        rw [ih word' (count - 1) hword',min_succ_of_pos count fuel hcpos,
          pow_succ]
        dsimp [word']
        rw [Nat.mod_mul_mod]
        congr 1
        ring

theorem cappedRightValue_eq_min (word count fuel:Nat):
    cappedRightValue word count fuel=word / 2 ^ min count fuel:=by
  induction fuel generalizing word count with
  | zero => simp [cappedRightValue]
  | succ fuel ih =>
      by_cases hc0:count=0
      · subst count
        simp [cappedRightValue]
      · have hcpos:0 < count:=Nat.pos_of_ne_zero hc0
        rw [cappedRightValue]
        simp only [hc0, ↓reduceIte]
        rw [ih,min_succ_of_pos count fuel hcpos,pow_succ,
          Nat.div_div_eq_div_mul]
        rw [Nat.mul_comm 2 (2 ^ min (count - 1) fuel)]

theorem cappedLeftValue_width (w word count:Nat)
    (hword:word < 2 ^ w):
    cappedLeftValue w word count w=word * 2 ^ count % 2 ^ w:=by
  rw [cappedLeftValue_eq_min w word count w hword]
  by_cases hc:count <= w
  · rw [Nat.min_eq_left hc]
  · have hwc:w < count:=Nat.lt_of_not_ge hc
    rw [Nat.min_eq_right (Nat.le_of_lt hwc)]
    have hdvd:2 ^ w ∣ 2 ^ count:=Nat.pow_dvd_pow 2 (Nat.le_of_lt hwc)
    have hleft:word * 2 ^ w % 2 ^ w=0:=by simp
    have hright:word * 2 ^ count % 2 ^ w=0:=by
      exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdvd word)
    rw [hleft,hright]

theorem cappedRightValue_width (w word count:Nat)
    (hword:word < 2 ^ w):
    cappedRightValue word count w=word / 2 ^ count:=by
  rw [cappedRightValue_eq_min]
  by_cases hc:count <= w
  · rw [Nat.min_eq_left hc]
  · have hwc:w < count:=Nat.lt_of_not_ge hc
    rw [Nat.min_eq_right (Nat.le_of_lt hwc)]
    have hp:2 ^ w <= 2 ^ count:=Nat.pow_le_pow_right (by omega) hwc.le
    rw [Nat.div_eq_of_lt hword,Nat.div_eq_of_lt (lt_of_lt_of_le hword hp)]

theorem cappedLeft_loop_correct {N:Nat}
    (w word count:Nat) (hw:0 < w) (hword:word < 2 ^ w)
    (hcount:count < 2 ^ w) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N)
    (hcountdown:FullInterpreterState.countdownLens.get state=default):
    ∃ steps,steps <= cappedShiftLoopBound w fuel.length∧ ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram false)))^[steps])
        (some (cappedShiftCfg (.countdown .scan)
          state w word count fuel m base)) =
      some (controllerCfg .done finalState
        (operandBoundaryBase w
          (cappedLeftValue w word count fuel.length) m base)):=by
  induction fuel generalizing word count state with
  | nil =>
      by_cases hc0:count=0
      · subst count
        rcases cappedShift_zero_finish false w word [] m base state hcountdown with
          ⟨finalState,hrun⟩
        refine ⟨2 * w + 5, ?_,finalState, ?_⟩
        · simp [cappedShiftLoopBound]; omega
        · simpa [cappedLeftValue] using hrun
      · have hcpos:0 < count:=Nat.pos_of_ne_zero hc0
        rcases cappedShift_positive_noFuel_finish false w word count hcpos
            hcount m base state hcountdown with ⟨finalState,hrun⟩
        exact ⟨3 * w + 7,by rfl,finalState,by
          simpa [cappedShiftLoopBound,cappedLeftValue] using hrun⟩
  | cons symbol fuel ih =>
      by_cases hc0:count=0
      · subst count
        rcases cappedShift_zero_finish false w word (symbol::fuel) m base
            state hcountdown with ⟨finalState,hrun⟩
        refine ⟨(symbol::fuel).length + 2 * w + 5, ?_,finalState, ?_⟩
        · simp [cappedShiftLoopBound]
          have hb:=fuel_le_cappedShiftLoopBound w fuel.length
          omega
        · simpa [cappedLeftValue] using hrun
      · have hcpos:0 < count:=Nat.pos_of_ne_zero hc0
        rcases cappedLeft_cycle_correct w word count hw hcpos hcount symbol fuel
            m base state hcountdown with ⟨cycleState,hcycleCountdown,hcycle⟩
        let word':=(2 * word) % 2 ^ w
        have hword':word' < 2 ^ w:=by
          exact Nat.mod_lt _ (by positivity)
        have hcount':count - 1 < 2 ^ w:=lt_of_le_of_lt
          (Nat.sub_le count 1) hcount
        rcases ih word' (count - 1) hword' hcount' cycleState
            hcycleCountdown with ⟨restSteps,hrestBound,finalState,hrest⟩
        let stepO:=fun x:Option (TM2.Cfg
            (fun _:CoreStack => SparseSymbol) CappedShiftLabel
            (FullInterpreterState N)) =>
          x.bind (TM2.step (cappedShiftProgram false))
        have hall:=chain_iterations stepO hcycle hrest
        refine ⟨(6 * w + 13) + restSteps, ?_,finalState, ?_⟩
        · simp [cappedShiftLoopBound]
          omega
        · change (stepO^[(6 * w + 13) + restSteps])
            (some (cappedShiftCfg (.countdown .scan)
              state w word count (symbol::fuel) m base))=_
          simpa [cappedLeftValue,hc0,word'] using hall

theorem cappedRight_loop_correct {N:Nat}
    (w word count:Nat) (hw:0 < w) (hword:word < 2 ^ w)
    (hcount:count < 2 ^ w) (fuel:List SparseSymbol)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N)
    (hcountdown:FullInterpreterState.countdownLens.get state=default):
    ∃ steps,steps <= cappedShiftLoopBound w fuel.length∧ ∃ finalState,
      ((fun x => x.bind (TM2.step (cappedShiftProgram true)))^[steps])
        (some (cappedShiftCfg (.countdown .scan)
          state w word count fuel m base)) =
      some (controllerCfg .done finalState
        (operandBoundaryBase w
          (cappedRightValue word count fuel.length) m base)):=by
  induction fuel generalizing word count state with
  | nil =>
      by_cases hc0:count=0
      · subst count
        rcases cappedShift_zero_finish true w word [] m base state hcountdown with
          ⟨finalState,hrun⟩
        refine ⟨2 * w + 5, ?_,finalState, ?_⟩
        · simp [cappedShiftLoopBound]; omega
        · simpa [cappedRightValue] using hrun
      · have hcpos:0 < count:=Nat.pos_of_ne_zero hc0
        rcases cappedShift_positive_noFuel_finish true w word count hcpos
            hcount m base state hcountdown with ⟨finalState,hrun⟩
        exact ⟨3 * w + 7,by rfl,finalState,by
          simpa [cappedShiftLoopBound,cappedRightValue] using hrun⟩
  | cons symbol fuel ih =>
      by_cases hc0:count=0
      · subst count
        rcases cappedShift_zero_finish true w word (symbol::fuel) m base
            state hcountdown with ⟨finalState,hrun⟩
        refine ⟨(symbol::fuel).length + 2 * w + 5, ?_,finalState, ?_⟩
        · simp [cappedShiftLoopBound]
          have hb:=fuel_le_cappedShiftLoopBound w fuel.length
          omega
        · simpa [cappedRightValue] using hrun
      · have hcpos:0 < count:=Nat.pos_of_ne_zero hc0
        rcases cappedRight_cycle_correct w word count hw hword hcpos hcount
            symbol fuel m base state hcountdown with
          ⟨cycleState,hcycleCountdown,hcycle⟩
        have hword':word / 2 < 2 ^ w:=
          lt_of_le_of_lt (Nat.div_le_self word 2) hword
        have hcount':count - 1 < 2 ^ w:=lt_of_le_of_lt
          (Nat.sub_le count 1) hcount
        rcases ih (word / 2) (count - 1) hword' hcount' cycleState
            hcycleCountdown with ⟨restSteps,hrestBound,finalState,hrest⟩
        let stepO:=fun x:Option (TM2.Cfg
            (fun _:CoreStack => SparseSymbol) CappedShiftLabel
            (FullInterpreterState N)) =>
          x.bind (TM2.step (cappedShiftProgram true))
        have hall:=chain_iterations stepO hcycle hrest
        refine ⟨(6 * w + 12) + restSteps, ?_,finalState, ?_⟩
        · simp [cappedShiftLoopBound]
          omega
        · change (stepO^[(6 * w + 12) + restSteps])
            (some (cappedShiftCfg (.countdown .scan)
              state w word count (symbol::fuel) m base))=_
          simpa [cappedRightValue,hc0] using hall

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

theorem storeIndInstruction_correct {N:Nat} {R:Type}
    (address:Nat) (hN:address <= N)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator:Nat) (m:SparseMemory) (hm:m.Normalized w)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ steps,steps <= storeIndInstructionBound w m∧ ∃ finalState,
      ((fun o => o.bind (TM2.step
        (storeIndInstructionProgram address returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=StoreInstructionTailLabel R) (.mem address) hN
          w accumulator m state base)) =
      some (embedOperandReturnCfg (.mem address)
        (mapLabelCfg (fun l:FullStoreLabel R => Sum.inr l)
          (mapLabelCfg (fun l:StorePrependTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l:FullPrependLabel R => Sum.inr l)
              (mapLabelCfg (fun l:R => Sum.inr l)
                (cleanReturnCfg returnLabel finalState
                  (operandBoundaryBase w accumulator
                    (m.write w (m.read (address % 2 ^ w)) accumulator)
                    base))))))):=by
  rcases operandEval_correct (.mem address) hN w accumulator m hm
      (Sum.inl StoreResetLabel.reset)
      (storeInstructionTailProgram returnLabel right) state base with
    ⟨operandSteps,operandBound,operandState,hoperand⟩
  let wordAddress:=operandWordValue w (.mem address) m
  have hresetStep:=storeReset_step returnLabel right w wordAddress
    accumulator m base operandState
  have hreset:
      ((fun o => o.bind (TM2.step
        (storeInstructionTailProgram returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl StoreResetLabel.reset) operandState
          (operandResultBase w accumulator wordAddress m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg
          (copyCoreRenaming .accumulator .work1 .work7
            (by decide) (by decide) (by decide))
          FullInterpreterState.moveLens
          (copyCfg .scan ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
          operandState
          (operandResultBase w accumulator wordAddress m base))):=by
    simpa using hresetStep
  rcases fullStore_correct returnLabel right w wordAddress accumulator m base
      operandState with ⟨storeState,hstore⟩
  have htail:=chain_liftRightProgram storeResetProgram
    (fullStoreProgram returnLabel right) hreset hstore
  have hlift:=transport_iterate_operand_right (.mem address)
    (Sum.inl StoreResetLabel.reset)
    (storeInstructionTailProgram returnLabel right) htail
  have hchain:=chain_loadInstruction_iterations
    (fun o:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (StoreIndInstructionLabel address R) (FullInterpreterState N)) =>
        o.bind (TM2.step (storeIndInstructionProgram address returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (1 + (4 * w + 10)), ?_,storeState, ?_⟩
  · simp [storeIndInstructionBound]
    omega
  · have hwrite:m.write w wordAddress accumulator =
        m.write w (m.read (address % 2 ^ w)) accumulator:=by
      simp [wordAddress,SparseMemory.write_mod_address]
    rw [hwrite] at hchain
    simpa [storeIndInstructionProgram,storeInstructionTailProgram,
      wordAddress] using hchain

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

theorem sparseSubLocal_fixed_run (w a b:Nat)
    (ha:a < 2 ^ w) (hb:b < 2 ^ w):
    ((fun o => o.bind (TM2.step sparseSubCoreProgram))^[w + 1])
      (some (sparseSubLocalCfg false (fixedBits w a) (fixedBits w b) [])) =
    some (sparseSubLocalDoneCfg (decide (a < b))
      (subBits (fixedBits w a) (fixedBits w b) false).reverse):=by
  have hp:sparseSubCoreProgram=sparseSubProgram:=by
    funext l
    cases l <;> rfl
  rw [hp]
  have hrun:=subMachine_reaches_done false
    (fixedBits w a) (fixedBits w b) [] (by simp)
  rw [subBorrowOut_fixed_eq_decide_lt w a b ha hb] at hrun
  have hsparse:=transport_iterate_mapAlphabetProgram
    sparseBitEncode sparseBitDecode sparseBitDecode_encode subMachine.m hrun
  simpa [sparseSubLocalCfg,sparseSubLocalDoneCfg,sparseSubCfg,
    sparseSubDoneCfg,subCfg,subDoneCfg,subPartialDoneCfg,
    mapAlphabetCfg] using! hsparse

abbrev FullSubtractCoreLabel (R:Type):=Sum AddLabel R

def fullSubtractCoreProgram {N:Nat} {R:Type} (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)):
    FullSubtractCoreLabel R -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (FullSubtractCoreLabel R)
      (FullInterpreterState N):=
  liftRightProgram
    (lensPhaseLeft binaryCoreRenaming FullInterpreterState.subLens
      sparseSubCoreProgram .done returnLabel)
    right

def subtractCoreResultStacks (w a b:Nat)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol
  | .accumulator | .work1 => []
  | .work0 =>
      (subBits (fixedBits w a) (fixedBits w b) false).reverse.map SparseSymbol.bit
  | k => base k

theorem fullSubtractCore_return_bridge {N:Nat} {R:Type}
    (returnLabel:R) (w a b:Nat)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    phaseReturnCfg binaryCoreRenaming FullInterpreterState.subLens returnLabel
      (sparseSubLocalDoneCfg (decide (a < b))
        (subBits (fixedBits w a) (fixedBits w b) false).reverse)
      state base =
    cleanReturnCfg returnLabel
      (FullInterpreterState.subLens.put state
        ⟨decide (a < b),none,none⟩)
      (subtractCoreResultStacks w a b base):=by
  simp only [phaseReturnCfg,cleanReturnCfg,lensRenamedCfg,
    sparseSubLocalDoneCfg]
  have hs:renamedStacks binaryCoreRenaming
      (mapAlphabetStacks sparseBitEncode
        (addStackFamily [] []
          (subBits (fixedBits w a) (fixedBits w b) false).reverse))
      base=subtractCoreResultStacks w a b base:=by
    funext k
    cases k <;> simp [renamedStacks,binaryCoreRenaming,binaryCoreDecode,
      addStackFamily,mapAlphabetStacks,sparseBitEncode,
      subtractCoreResultStacks]
  rw [hs]

theorem fullSubtractCore_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b:Nat) (ha:a < 2 ^ w) (hb:b < 2 ^ w)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    ((fun o => o.bind (TM2.step
      (fullSubtractCoreProgram returnLabel right)))^[w + 2])
      (some (lensRenamedCfg binaryCoreRenaming FullInterpreterState.subLens
        (sparseSubLocalCfg false (fixedBits w a) (fixedBits w b) [])
        state base)) =
    some (mapLabelCfg Sum.inr
      (cleanReturnCfg returnLabel
        (FullInterpreterState.subLens.put state
          ⟨decide (a < b),none,none⟩)
        (subtractCoreResultStacks w a b base))):=by
  have h:=run_lensPhase_to_right binaryCoreRenaming
    FullInterpreterState.subLens sparseSubCoreProgram .done (by rfl)
    returnLabel right (sparseSubLocal_fixed_run w a b ha hb) rfl state base
  rw [fullSubtractCore_return_bridge returnLabel w a b base state] at h
  simpa [fullSubtractCoreProgram] using h

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

def conditionalInstallCfg {N:Nat} (label:ConditionalInstallLabel)
    (state:FullInterpreterState N) (source accumulator:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol) ConditionalInstallLabel
      (FullInterpreterState N) where
  l:=some label
  var:=state
  stk:=fun
    | .work0 => source
    | .accumulator => accumulator
    | k => base k

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

@[simp] theorem conditionalInstall_step_nil {N:Nat}
    (state:FullInterpreterState N) (accumulator:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol):
    TM2.step (conditionalInstallProgram N)
      (conditionalInstallCfg .loop state [] accumulator base) =
    some (conditionalInstallCfg .done
      (FullInterpreterState.moveLens.put state default) [] accumulator
      base):=by
  simp [conditionalInstallProgram,conditionalInstallCfg,TM2.step]
  simp [FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]

@[simp] theorem conditionalInstall_step_cons {N:Nat}
    (state:FullInterpreterState N) (x:SparseSymbol)
    (xs accumulator:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol):
    TM2.step (conditionalInstallProgram N)
      (conditionalInstallCfg .loop state (x::xs) accumulator base) =
    some (conditionalInstallCfg .loop
      (FullInterpreterState.moveLens.put state default) xs
      ((if subtractInstallZero state then .bit false else x)::
        accumulator) base):=by
  simp [conditionalInstallProgram,conditionalInstallCfg,TM2.step,
    Function.update,FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  congr 2
  funext k
  cases k <;> rfl

def conditionalInstalled (borrow:Bool) (source:List SparseSymbol):
    List SparseSymbol:=
  if borrow then List.replicate source.length (.bit false) else source.reverse

theorem conditionalInstall_iterate {N:Nat}
    (state:FullInterpreterState N) (source accumulator:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol)
    (hmove:FullInterpreterState.moveLens.get state=default):
    ((fun o => o.bind (TM2.step (conditionalInstallProgram N)))^[source.length])
      (some (conditionalInstallCfg .loop state source accumulator base)) =
    some (conditionalInstallCfg .loop
      (FullInterpreterState.moveLens.put state default) []
      (conditionalInstalled (subtractInstallZero state) source ++
        accumulator) base):=by
  induction source generalizing state accumulator base with
  | nil =>
      have hstate:FullInterpreterState.moveLens.put state default=state:=by
        rw [← hmove,FullInterpreterState.moveLens.put_get]
      simp [conditionalInstalled,hstate]
  | cons x xs ih =>
      rw [List.length_cons,Function.iterate_succ_apply]
      simp only [Option.bind_some,conditionalInstall_step_cons]
      rw [ih (FullInterpreterState.moveLens.put state default)
        ((if subtractInstallZero state then .bit false else x)::
          accumulator) base (FullInterpreterState.moveLens.get_put _ _)]
      simp [conditionalInstalled,List.replicate_succ,List.reverse_cons,
        List.append_assoc]
      by_cases h:subtractInstallZero state <;>
        simp [h,subLens_get_moveLens_put,List.append_assoc,
          FullInterpreterState.moveLens.put_put,
          replicate_append_same_cons]

theorem conditionalInstall_correct {N:Nat}
    (state:FullInterpreterState N) (source:List SparseSymbol)
    (base:CoreStack -> List SparseSymbol)
    (hmove:FullInterpreterState.moveLens.get state=default):
    ((fun o => o.bind (TM2.step (conditionalInstallProgram N)))^[source.length + 1])
      (some (conditionalInstallCfg .loop state source [] base)) =
    some (conditionalInstallCfg .done
      (FullInterpreterState.moveLens.put state default) []
      (conditionalInstalled (subtractInstallZero state) source)
      base):=by
  rw [Nat.add_comm,Function.iterate_add_apply,
    conditionalInstall_iterate state source [] base hmove]
  simp only [List.append_nil,Function.iterate_one,Option.bind_some,
    conditionalInstall_step_nil,FullInterpreterState.moveLens.put_put]

end Lax759944Proofs.RamToTM

end

section

namespace Lax759944Proofs.RamToTM

open Turing TM2

def subtractReadyStacks (w a b:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w a).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work1 => (fixedBits w b).map SparseSymbol.bit
  | .work0 | .work2 | .work3 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def subtractResultStacks (w a b:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):CoreStack -> List SparseSymbol:=
  operandBoundaryBase w (a - b) m base

theorem subtractMove_bridge {N:Nat} {R:Type}
    (w a b:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N)
    (hsub:FullInterpreterState.subLens.get state=default):
    phaseReturnCfg
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens
      (Sum.inl AddLabel.loop:FullSubtractTailLabel R)
      (symbolMoveLocalCfg .done [] ((fixedBits w b).map SparseSymbol.bit))
      state (operandResultBase w a b m base) =
    lensRenamedCfg binaryCoreRenaming FullInterpreterState.subLens
      (sparseSubLocalCfg false (fixedBits w a) (fixedBits w b) [])
      (FullInterpreterState.moveLens.put state default)
      (subtractReadyStacks w a b m base):=by
  simp [phaseReturnCfg,lensRenamedCfg,symbolMoveCoreRenaming,
    symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks,
    operandResultBase,subtractReadyStacks,sparseSubLocalCfg,
    sparseSubCfg,subCfg,addStackFamily,mapAlphabetStacks,
    sparseBitEncode,renamedStacks,binaryCoreRenaming,binaryCoreDecode]
  constructor
  · have hs:FullInterpreterState.subLens.get
        (FullInterpreterState.moveLens.put state default)=default:=by
      simpa using hsub
    symm
    calc
      FullInterpreterState.subLens.put
          (FullInterpreterState.moveLens.put state default) default =
        FullInterpreterState.subLens.put
          (FullInterpreterState.moveLens.put state default)
          (FullInterpreterState.subLens.get
            (FullInterpreterState.moveLens.put state default)):=by rw [hs]
      _=FullInterpreterState.moveLens.put state default:=
        FullInterpreterState.subLens.put_get _
  · funext k
    cases k <;> simp [operandResultBase,subtractReadyStacks,
      symbolMoveCoreRenaming,symbolMoveCoreDecode,symbolMoveLocalCfg,
      symbolMoveStacks,renamedStacks,binaryCoreRenaming,
      binaryCoreDecode,sparseSubLocalCfg,sparseSubCfg,subCfg,
      addStackFamily,mapAlphabetStacks,sparseBitEncode,
      List.map_reverse]

theorem subtractCore_install_bridge {N:Nat} {R:Type}
    (w a b:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N):
    cleanReturnCfg (Sum.inl ConditionalInstallLabel.loop:
        SubtractInstallPhaseLabel R)
      (FullInterpreterState.subLens.put state
        ⟨decide (a < b),none,none⟩)
      (subtractCoreResultStacks w a b (subtractReadyStacks w a b m base)) =
    mapLabelCfg Sum.inl (conditionalInstallCfg .loop
      (FullInterpreterState.subLens.put state
        ⟨decide (a < b),none,none⟩)
      ((subBits (fixedBits w a) (fixedBits w b) false).reverse.map
        SparseSymbol.bit) []
      (operandBoundaryBase w a m base)):=by
  simp [cleanReturnCfg,conditionalInstallCfg,subtractCoreResultStacks,
    subtractReadyStacks,operandBoundaryBase,mapLabelCfg]
  funext k
  cases k <;> simp [subtractCoreResultStacks,subtractReadyStacks,
    List.map_reverse]

theorem conditionalInstalled_subBits (w a b:Nat):
    conditionalInstalled (decide (a < b))
      ((subBits (fixedBits w a) (fixedBits w b) false).reverse.map
        SparseSymbol.bit) =
      (fixedBits w (a - b)).map SparseSymbol.bit:=by
  by_cases h:a < b
  · have hab:a - b=0:=Nat.sub_eq_zero_of_le (Nat.le_of_lt h)
    simp [conditionalInstalled,h,hab,subBits_length_fixed]
  · have hba:b≤ a:=Nat.le_of_not_gt h
    simp [conditionalInstalled,h,fixedBits_sub_of_le w hba,
      List.map_reverse]

theorem conditionalInstalled_subBits_or (force:Bool) (w a b:Nat):
    conditionalInstalled (decide (a < b) || force)
      ((subBits (fixedBits w a) (fixedBits w b) false).reverse.map
        SparseSymbol.bit) =
      (fixedBits w (if force then 0 else a - b)).map SparseSymbol.bit:=by
  cases force
  · simpa using conditionalInstalled_subBits w a b
  · simp [conditionalInstalled,subBits_length_fixed]

theorem subtractInstall_return_bridge {N:Nat} {R:Type}
    (returnLabel:R) (force:Bool) (w a b:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol) (state:FullInterpreterState N)
    (hborrow:subtractInstallZero state=(decide (a < b) || force)):
    phaseReturnCfg coreIdentityRenaming (fullStateIdentityLens N) returnLabel
      (conditionalInstallCfg .done
        (FullInterpreterState.moveLens.put state default) []
        (conditionalInstalled (subtractInstallZero state)
          ((subBits (fixedBits w a) (fixedBits w b) false).reverse.map
            SparseSymbol.bit))
        (operandBoundaryBase w a m base))
      state (operandBoundaryBase w a m base) =
    cleanReturnCfg returnLabel
      (FullInterpreterState.moveLens.put state default)
      (operandBoundaryBase w (if force then 0 else a - b) m base):=by
  simp [phaseReturnCfg,cleanReturnCfg,conditionalInstallCfg,
    fullStateIdentityLens,renamedStacks_coreIdentity,
    subtractReadyStacks]
  funext k
  cases k <;> simp [operandBoundaryBase,hborrow]
  simpa [List.map_reverse] using conditionalInstalled_subBits_or force w a b

theorem fullSubtract_correct {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b:Nat) (ha:a < 2 ^ w) (hb:b < 2 ^ w)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N)
    (hsub:FullInterpreterState.subLens.get state=default)
    (force:Bool) (hforce:state.subtractForceZero=force):
    ∃ finalState,
      ((fun o => o.bind (TM2.step
        (fullSubtractProgram returnLabel right)))^[3 * w + 6])
        (some (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .work1 (by decide))
          FullInterpreterState.moveLens
          (symbolMoveLocalCfg .loop
            ((fixedBits w b).reverse.map SparseSymbol.bit) [])
          state (operandResultBase w a b m base))) =
      some (mapLabelCfg (fun l:FullSubtractTailLabel R => Sum.inr l)
        (mapLabelCfg (fun l:SubtractInstallPhaseLabel R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w (if force then 0 else a - b) m base))))):=by
  have hmove:=run_lensPhase_to_right
    (symbolMoveCoreRenaming .work0 .work1 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl)
    (Sum.inl AddLabel.loop)
    (fullSubtractTailProgram returnLabel right)
    (symbolMoveLocal_correct
      ((fixedBits w b).reverse.map SparseSymbol.bit) []) rfl state
    (operandResultBase w a b m base)
  simp only [List.length_map,List.length_reverse,fixedBits_length,
    List.append_nil,List.map_reverse,List.reverse_reverse] at hmove
  rw [subtractMove_bridge w a b m base state hsub] at hmove
  let moveState:=FullInterpreterState.moveLens.put state default
  have hcore:=fullSubtractCore_correct
    (Sum.inl ConditionalInstallLabel.loop:SubtractInstallPhaseLabel R)
    (subtractInstallPhaseProgram returnLabel right)
    w a b ha hb (subtractReadyStacks w a b m base) moveState
  rw [subtractCore_install_bridge (R:=R) w a b m base moveState] at hcore
  let coreState:=FullInterpreterState.subLens.put moveState
    ⟨decide (a < b),none,none⟩
  have hinstallRaw:=run_lensPhase_to_right coreIdentityRenaming
    (fullStateIdentityLens N) (conditionalInstallProgram N) .done (by rfl)
    returnLabel right
    (conditionalInstall_correct coreState
      ((subBits (fixedBits w a) (fixedBits w b) false).reverse.map
        SparseSymbol.bit)
      (operandBoundaryBase w a m base) (by rfl)) rfl
    coreState (operandBoundaryBase w a m base)
  simp only [List.length_map,List.length_reverse,subBits_length_fixed]
    at hinstallRaw
  rw [subtractInstall_return_bridge returnLabel force w a b m base coreState
    (by
      change (decide (a < b) || state.subtractForceZero) =
        (decide (a < b) || force)
      rw [hforce])]
    at hinstallRaw
  have htail:=chain_liftRightProgram (m:=w + 2) (n:=w + 2)
    (lensPhaseLeft binaryCoreRenaming FullInterpreterState.subLens
      sparseSubCoreProgram .done (Sum.inl ConditionalInstallLabel.loop))
    (subtractInstallPhaseProgram returnLabel right) hcore hinstallRaw
  have htail':
      ((fun o => o.bind (TM2.step
        (fullSubtractTailProgram returnLabel right)))^[2 * w + 4])
        (some (lensRenamedCfg binaryCoreRenaming FullInterpreterState.subLens
          (sparseSubLocalCfg false (fixedBits w a) (fixedBits w b) [])
          moveState (subtractReadyStacks w a b m base))) =
      some (mapLabelCfg (fun l:SubtractInstallPhaseLabel R => Sum.inr l)
        (mapLabelCfg (fun l:R => Sum.inr l)
          (cleanReturnCfg returnLabel
            (FullInterpreterState.moveLens.put coreState default)
            (operandBoundaryBase w (if force then 0 else a - b) m base)))):=by
    simpa only [show w + 2 + (w + 2)=2 * w + 4 by omega] using! htail
  have hall:=chain_liftRightProgram (m:=w + 2) (n:=2 * w + 4)
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl AddLabel.loop))
    (fullSubtractTailProgram returnLabel right) hmove htail'
  refine ⟨FullInterpreterState.moveLens.put coreState default, ?_⟩
  have htime:3 * w + 6=(w + 2) + (2 * w + 4):=by omega
  rw [htime]
  simpa [fullSubtractProgram,moveState,coreState] using hall

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

theorem subtractReset_step {N:Nat} {R:Type}
    (o:Op)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a b:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    TM2.step (subtractInstructionTailProgram o returnLabel right)
      (cleanReturnCfg (Sum.inl SubtractResetLabel.reset)
        state (operandResultBase w a b m base)) =
    some (mapLabelCfg Sum.inr
      (lensRenamedCfg
        (symbolMoveCoreRenaming .work0 .work1 (by decide))
        FullInterpreterState.moveLens
        (symbolMoveLocalCfg .loop
          ((fixedBits w b).reverse.map SparseSymbol.bit) [])
        (FullInterpreterState.moveLens.put
          (FullInterpreterState.subLens.put
            { state with subtractForceZero:=operandForcesSubtractionZero o state }
            default) default)
        (operandResultBase w a b m base))):=by
  simp [subtractInstructionTailProgram,subtractResetProgram,
    cleanReturnCfg,mapLabelCfg,liftRightProgram,TM2.step,
    lensRenamedCfg]
  constructor
  · rfl
  · constructor
    · rfl
    · funext k
      cases k <;> simp [symbolMoveCoreRenaming,symbolMoveCoreDecode,
        symbolMoveLocalCfg,symbolMoveStacks,renamedStacks,
        operandResultBase,List.map_reverse]

theorem subtractInstruction_finish {N:Nat} {R:Type}
    (o:Op) (hN:operandArgument o <= N)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a:Nat) (ha:a < 2 ^ w)
    (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol)
    (state operandState:FullInterpreterState N)
    (operandSteps:Nat) (operandBound:operandSteps <= operandEvalBound w m)
    (hoperand:
      ((fun x => x.bind (TM2.step
        (operandEvalProgram o (Sum.inl SubtractResetLabel.reset)
          (subtractInstructionTailProgram o returnLabel right))))^[operandSteps])
        (some (operandEvalStartCfg
          (R:=SubtractInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (cleanReturnCfg (Sum.inl SubtractResetLabel.reset) operandState
          (operandResultBase w a (operandWordValue w o m) m base))))
    (force:Bool)
    (hforce:operandForcesSubtractionZero o operandState=force):
    ∃ steps,steps <= subtractInstructionBound w m∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (subtractInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=SubtractInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l:FullSubtractLabel R => Sum.inr l)
          (mapLabelCfg (fun l:FullSubtractTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l:SubtractInstallPhaseLabel R => Sum.inr l)
              (mapLabelCfg (fun l:R => Sum.inr l)
                (cleanReturnCfg returnLabel finalState
                  (operandBoundaryBase w
                    (if force then 0 else a - operandWordValue w o m)
                    m base))))))):=by
  let b:=operandWordValue w o m
  have hb:b < 2 ^ w:=operandWordValue_lt w o m
  have hresetStep:=subtractReset_step o returnLabel right w a b m base
    operandState
  have hreset:
      ((fun x => x.bind (TM2.step
        (subtractInstructionTailProgram o returnLabel right)))^[1])
        (some (cleanReturnCfg (Sum.inl SubtractResetLabel.reset)
          operandState (operandResultBase w a b m base))) =
      some (mapLabelCfg Sum.inr
        (lensRenamedCfg
          (symbolMoveCoreRenaming .work0 .work1 (by decide))
          FullInterpreterState.moveLens
          (symbolMoveLocalCfg .loop
            ((fixedBits w b).reverse.map SparseSymbol.bit) [])
          (FullInterpreterState.moveLens.put
          (FullInterpreterState.subLens.put
              { operandState with subtractForceZero:=
                operandForcesSubtractionZero o operandState } default) default)
          (operandResultBase w a b m base))):=by
    simpa using hresetStep
  rcases fullSubtract_correct returnLabel right w a b ha hb m base
      (FullInterpreterState.moveLens.put
        (FullInterpreterState.subLens.put
          { operandState with subtractForceZero:=
            operandForcesSubtractionZero o operandState } default) default)
      (by
        rw [subLens_get_moveLens_put,
          FullInterpreterState.subLens.get_put])
      force (by simpa using! hforce) with
    ⟨subtractState,hsubtract⟩
  have htail:=chain_liftRightProgram (subtractResetProgram o)
    (fullSubtractProgram returnLabel right) hreset hsubtract
  have hlift:=transport_iterate_operand_right o
    (Sum.inl SubtractResetLabel.reset)
    (subtractInstructionTailProgram o returnLabel right) htail
  have hchain:=chain_loadInstruction_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
        (SubtractInstructionLabel o R) (FullInterpreterState N)) =>
      x.bind (TM2.step (subtractInstructionProgram o returnLabel right)))
    hoperand hlift
  refine ⟨operandSteps + (1 + (3 * w + 6)), ?_,subtractState, ?_⟩
  · simp [subtractInstructionBound]
    omega
  · simpa [subtractInstructionProgram,subtractInstructionTailProgram,
      b,subtractResultStacks] using hchain

theorem subtractInstruction_correct_of_operand_lt {N:Nat} {R:Type}
    (o:Op) (hN:operandArgument o <= N)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a:Nat) (ha:a < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (hop:sparseValue w o m < 2 ^ w)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ steps,steps <= subtractInstructionBound w m∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (subtractInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=SubtractInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l:FullSubtractLabel R => Sum.inr l)
          (mapLabelCfg (fun l:FullSubtractTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l:SubtractInstallPhaseLabel R => Sum.inr l)
              (mapLabelCfg (fun l:R => Sum.inr l)
                (cleanReturnCfg returnLabel finalState
                  (operandBoundaryBase w (a - sparseValue w o m) m base))))))):=by
  cases o with
  | lit n =>
      change n <= N at hN
      let operandState:=FullInterpreterState.literalLens.put state
        ⟨none, ⟨n / 2 ^ w,by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
      have hoperand:=literalOperand_correct n hN w a m
        (Sum.inl SubtractResetLabel.reset)
        (subtractInstructionTailProgram (.lit n) returnLabel right) state base
      have hbound:2 * w + 3 <= operandEvalBound w m:=by
        simp [operandEvalBound]
        omega
      have hnlt:n < 2 ^ w:=by
        simpa [sparseValue,Op.value] using hop
      have hzero:n / 2 ^ w=0:=
        (literalWord_remaining_eq_zero_iff n w).2 hnlt
      have hfinish:=subtractInstruction_finish (.lit n) hN returnLabel right
        w a ha m base state operandState (2 * w + 3) hbound
        (by simpa [operandEvalProgram,operandEvalStartCfg,operandArgument,
          embedOperandReturnCfg,operandState] using! hoperand)
        false (by
          simp only [operandForcesSubtractionZero]
          change ((FullInterpreterState.literalLens.get operandState).remaining.val !=
            0)=false
          rw [show FullInterpreterState.literalLens.get operandState =
              ⟨none, ⟨n / 2 ^ w,by
                exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩ by
            exact FullInterpreterState.literalLens.get_put _ _]
          simp [hzero])
      simpa [sparseValue,Op.value,operandWordValue,
        Nat.mod_eq_of_lt hnlt] using hfinish
  | mem address =>
      rcases operandEval_correct (.mem address) hN w a m hm
          (Sum.inl SubtractResetLabel.reset)
          (subtractInstructionTailProgram (.mem address) returnLabel right)
          state base with ⟨steps,hsteps,operandState,hoperand⟩
      have hfinish:=subtractInstruction_finish (.mem address) hN
        returnLabel right w a ha m base state operandState steps hsteps hoperand
        false (by rfl)
      simpa [operandWordValue,Nat.mod_eq_of_lt hop] using hfinish
  | ind address =>
      rcases operandEval_correct (.ind address) hN w a m hm
          (Sum.inl SubtractResetLabel.reset)
          (subtractInstructionTailProgram (.ind address) returnLabel right)
          state base with ⟨steps,hsteps,operandState,hoperand⟩
      have hfinish:=subtractInstruction_finish (.ind address) hN
        returnLabel right w a ha m base state operandState steps hsteps hoperand
        false (by rfl)
      simpa [operandWordValue,Nat.mod_eq_of_lt hop] using hfinish

theorem subtractInstruction_correct {N:Nat} {R:Type}
    (o:Op) (hN:operandArgument o <= N)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w a:Nat) (ha:a < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ steps,steps <= subtractInstructionBound w m∧ ∃ finalState,
      ((fun x => x.bind (TM2.step
        (subtractInstructionProgram o returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=SubtractInstructionTailLabel R) o hN w a m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg (fun l:FullSubtractLabel R => Sum.inr l)
          (mapLabelCfg (fun l:FullSubtractTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l:SubtractInstallPhaseLabel R => Sum.inr l)
              (mapLabelCfg (fun l:R => Sum.inr l)
                (cleanReturnCfg returnLabel finalState
                  (operandBoundaryBase w (a - sparseValue w o m) m base))))))):=by
  cases o with
  | mem address =>
      exact subtractInstruction_correct_of_operand_lt (.mem address) hN
        returnLabel right w a ha m hm (sparseValue_mem_lt hm address)
        base state
  | ind address =>
      exact subtractInstruction_correct_of_operand_lt (.ind address) hN
        returnLabel right w a ha m hm (sparseValue_ind_lt hm address)
        base state
  | lit n =>
      by_cases hnlt:n < 2 ^ w
      · apply subtractInstruction_correct_of_operand_lt (.lit n) hN
          returnLabel right w a ha m hm
        simpa [sparseValue,Op.value] using hnlt
      · change n <= N at hN
        let operandState:=FullInterpreterState.literalLens.put state
          ⟨none, ⟨n / 2 ^ w,by
            exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
        have hoperand:=literalOperand_correct n hN w a m
          (Sum.inl SubtractResetLabel.reset)
          (subtractInstructionTailProgram (.lit n) returnLabel right) state base
        have hbound:2 * w + 3 <= operandEvalBound w m:=by
          simp [operandEvalBound]
          omega
        have hquot:n / 2 ^ w ≠ 0:=by
          intro hz
          exact hnlt ((literalWord_remaining_eq_zero_iff n w).1 hz)
        have hfinish:=subtractInstruction_finish (.lit n) hN returnLabel right
          w a ha m base state operandState (2 * w + 3) hbound
          (by simpa [operandEvalProgram,operandEvalStartCfg,operandArgument,
            embedOperandReturnCfg,operandState] using! hoperand)
          true (by
            simp only [operandForcesSubtractionZero]
            change ((FullInterpreterState.literalLens.get operandState).remaining.val !=
              0)=true
            rw [show FullInterpreterState.literalLens.get operandState =
                ⟨none, ⟨n / 2 ^ w,by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩ by
              exact FullInterpreterState.literalLens.get_put _ _]
            simp [hquot])
        have hle:a <= n:=le_trans (Nat.le_of_lt ha) (Nat.le_of_not_gt hnlt)
        have hsub:a - n=0:=Nat.sub_eq_zero_of_le hle
        simpa [sparseValue,Op.value,hsub] using hfinish

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

namespace Lax759944Proofs.RamToTM

open Turing TM2

def PreservesLiteral {N:Nat} {Λ:Type}
    (stmt:TM2.Stmt (fun _:CoreStack => SparseSymbol) Λ
      (FullInterpreterState N)):Prop:=
  ∀ state tapes,
    (TM2.stepAux stmt state tapes).var.literal=state.literal

def ProgramPreservesLiteral {N:Nat} {Λ:Type}
    (program:Λ -> TM2.Stmt (fun _:CoreStack => SparseSymbol) Λ
      (FullInterpreterState N)):Prop:=
  ∀ label,PreservesLiteral (program label)

theorem step_preservesLiteral {N:Nat} {Λ:Type}
    (program:Λ -> TM2.Stmt (fun _:CoreStack => SparseSymbol) Λ
      (FullInterpreterState N))
    (hprogram:ProgramPreservesLiteral program)
    (c d:TM2.Cfg (fun _:CoreStack => SparseSymbol) Λ
      (FullInterpreterState N))
    (hstep:TM2.step program c=some d):
    d.var.literal=c.var.literal:=by
  rcases c with ⟨label,state,tapes⟩
  cases label with
  | none => contradiction
  | some label =>
      simp only [TM2.step] at hstep
      have hd:=Option.some.inj hstep
      subst d
      exact hprogram label state tapes

theorem iterate_preservesLiteral {N:Nat} {Λ:Type}
    (program:Λ -> TM2.Stmt (fun _:CoreStack => SparseSymbol) Λ
      (FullInterpreterState N))
    (hprogram:ProgramPreservesLiteral program)
    {n:Nat}
    (c d:TM2.Cfg (fun _:CoreStack => SparseSymbol) Λ
      (FullInterpreterState N))
    (hrun:((fun x => x.bind (TM2.step program))^[n]) (some c)=some d):
    d.var.literal=c.var.literal:=by
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
          exact (ih c' hrun).trans (step_preservesLiteral program hprogram c c' hs)

theorem preservesLiteral_mapLabel {N:Nat} {Λ Λ':Type}
    (encode:Λ -> Λ')
    (stmt:TM2.Stmt (fun _:CoreStack => SparseSymbol) Λ
      (FullInterpreterState N))
    (h:PreservesLiteral stmt):
    PreservesLiteral (mapLabelStmt encode stmt):=by
  intro state tapes
  rw [stepAux_mapLabelStmt]
  exact h state tapes

theorem preservesLiteral_lensRename {N:Nat}
    {K Λ R σ:Type} [DecidableEq K]
    (stackMap:StackRenaming K CoreStack)
    (lens:StateLens σ (FullInterpreterState N))
    (hput:∀ state value, (lens.put state value).literal=state.literal)
    (stmt:TM2.Stmt (fun _:K => SparseSymbol) Λ σ):
    PreservesLiteral
      (lensRenameStmt (Λx:=R) stackMap lens stmt):=by
  induction stmt with
  | push k f stmt ih =>
      intro state tapes
      simp only [lensRenameStmt,TM2.stepAux]
      exact ih _ _
  | peek k f stmt ih =>
      intro state tapes
      simp only [lensRenameStmt,TM2.stepAux]
      rw [ih,hput]
  | pop k f stmt ih =>
      intro state tapes
      simp only [lensRenameStmt,TM2.stepAux]
      rw [ih,hput]
  | load f stmt ih =>
      intro state tapes
      simp only [lensRenameStmt,TM2.stepAux]
      rw [ih,hput]
  | branch f left right ihLeft ihRight =>
      intro state tapes
      simp only [lensRenameStmt,TM2.stepAux]
      by_cases h:f (lens.get state)
      · simp only [h]
        exact ihLeft state tapes
      · simp only [h]
        exact ihRight state tapes
  | goto f => intro state tapes; rfl
  | halt => intro state tapes; rfl

theorem preservesLiteral_lensPhase {N:Nat}
    {K Λ R σ:Type} [DecidableEq K] [DecidableEq Λ]
    (stackMap:StackRenaming K CoreStack)
    (lens:StateLens σ (FullInterpreterState N))
    (hput:∀ state value, (lens.put state value).literal=state.literal)
    (program:Λ -> TM2.Stmt (fun _:K => SparseSymbol) Λ σ)
    (done:Λ) (entry:R) (label:Λ):
    PreservesLiteral
      (lensPhaseLeft stackMap lens program done entry label):=by
  simp only [lensPhaseLeft]
  split
  · intro state tapes; rfl
  · exact preservesLiteral_lensRename stackMap lens hput (program label)

@[simp] theorem literal_move_put {N:Nat} (state:FullInterpreterState N)
    (value:SymbolMoveControl):
    (FullInterpreterState.moveLens.put state value).literal=state.literal:=by
  cases state <;> rfl

@[simp] theorem literal_shift_put {N:Nat} (state:FullInterpreterState N)
    (value:MoveControl):
    (FullInterpreterState.shiftLens.put state value).literal=state.literal:=by
  cases state <;> rfl

@[simp] theorem literal_countdown_put {N:Nat}
    (state:FullInterpreterState N) (value:CountdownControl):
    (FullInterpreterState.countdownLens.put state value).literal =
      state.literal:=by
  cases state <;> rfl

@[simp] theorem literal_resetShiftControls {N:Nat}
    (state:FullInterpreterState N):
    (resetShiftControls state).literal=state.literal:=by
  cases state <;> rfl

theorem preservesLiteral_shiftLeftRound {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (hright:∀ label,PreservesLiteral (right label))
    (label:ShiftLeftRoundLabel R):
    PreservesLiteral (shiftLeftRoundProgram returnLabel right label):=by
  rcases label with label | tail
  · exact preservesLiteral_lensPhase shiftRoundRenaming
      FullInterpreterState.shiftLens literal_shift_put
      sparseShiftLeftCoreProgram .done (Sum.inl SymbolMoveLabel.loop) label
  rcases tail with label | tail
  · apply preservesLiteral_mapLabel Sum.inr
    exact preservesLiteral_lensPhase
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens literal_move_put symbolMoveCoreProgram
      .done (Sum.inl SymbolMoveLabel.loop) label
  rcases tail with label | label
  · apply preservesLiteral_mapLabel Sum.inr
    apply preservesLiteral_mapLabel Sum.inr
    exact preservesLiteral_lensPhase
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens literal_move_put symbolMoveCoreProgram
      .done returnLabel label
  · apply preservesLiteral_mapLabel Sum.inr
    apply preservesLiteral_mapLabel Sum.inr
    exact preservesLiteral_mapLabel Sum.inr (right label) (hright label)

theorem preservesLiteral_shiftRightRound {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (hright:∀ label,PreservesLiteral (right label))
    (label:ShiftRightRoundLabel R):
    PreservesLiteral (shiftRightRoundProgram returnLabel right label):=by
  rcases label with label | tail
  · exact preservesLiteral_lensPhase shiftRoundRenaming
      FullInterpreterState.shiftLens literal_shift_put
      sparseShiftRightCoreProgram .done (Sum.inl SymbolMoveLabel.loop) label
  rcases tail with label | tail
  · apply preservesLiteral_mapLabel Sum.inr
    exact preservesLiteral_lensPhase
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens literal_move_put symbolMoveCoreProgram
      .done (Sum.inl SymbolMoveLabel.loop) label
  rcases tail with label | label
  · apply preservesLiteral_mapLabel Sum.inr
    apply preservesLiteral_mapLabel Sum.inr
    exact preservesLiteral_lensPhase
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens literal_move_put symbolMoveCoreProgram
      .done returnLabel label
  · apply preservesLiteral_mapLabel Sum.inr
    apply preservesLiteral_mapLabel Sum.inr
    exact preservesLiteral_mapLabel Sum.inr (right label) (hright label)

theorem preservesLiteral_countdownMultiLeft {N:Nat} {R:Type}
    (zeroLabel positiveLabel:R) (label:CountdownLabel):
    PreservesLiteral
      (countdownMultiLeft (N:=N) zeroLabel positiveLabel label):=by
  simp only [countdownMultiLeft,lensMultiPhaseLeft]
  split
  · intro state tapes
    simp [TM2.stepAux,countdownOnExit]
  · exact preservesLiteral_lensRename countdownCoreRenaming
      FullInterpreterState.countdownLens literal_countdown_put
      (sparseCountdownProgram label)

theorem preservesLiteral_cleanupStmt {N:Nat}
    (stack:CoreStack) (again next:CappedShiftLabel):
    PreservesLiteral (N:=N)
      (cappedShiftCleanupStmt stack again next):=by
  intro state tapes
  simp [cappedShiftCleanupStmt,TM2.stepAux,
    FullInterpreterState.moveLens.get_put,
    FullInterpreterState.moveLens.put_put]
  cases h:(tapes stack).head? <;>
    simp [h,literal_move_put]

theorem preservesLiteral_cappedShiftProgram {N:Nat}
    (rightShift:Bool) (label:CappedShiftLabel):
    PreservesLiteral (cappedShiftProgram (N:=N) rightShift label):=by
  cases label with
  | countdown label =>
      exact preservesLiteral_mapLabel embedCountdownController
        (countdownMultiLeft CappedShiftLabel.cleanupFuel CappedShiftLabel.fuel label)
        (preservesLiteral_countdownMultiLeft CappedShiftLabel.cleanupFuel
          CappedShiftLabel.fuel label)
  | fuel =>
      intro state tapes
      simp [cappedShiftProgram,TM2.stepAux,
        FullInterpreterState.moveLens.get_put,
        FullInterpreterState.moveLens.put_put,literal_resetShiftControls]
      cases h:(tapes CoreStack.work1).head? <;>
        simp [h,literal_move_put,literal_resetShiftControls]
  | left label =>
      rcases label with label | tail
      · exact preservesLiteral_mapLabel CappedShiftLabel.left
          (shiftLeftRoundProgram () (fun _ => .halt) (Sum.inl label))
          (preservesLiteral_shiftLeftRound () (fun _ => .halt)
            (fun _ => by intro state tapes; rfl) (Sum.inl label))
      rcases tail with label | tail
      · exact preservesLiteral_mapLabel CappedShiftLabel.left
          (shiftLeftRoundProgram () (fun _ => .halt)
            (Sum.inr (Sum.inl label)))
          (preservesLiteral_shiftLeftRound () (fun _ => .halt)
            (fun _ => by intro state tapes; rfl) (Sum.inr (Sum.inl label)))
      rcases tail with label | terminal
      · exact preservesLiteral_mapLabel CappedShiftLabel.left
          (shiftLeftRoundProgram () (fun _ => .halt)
            (Sum.inr (Sum.inr (Sum.inl label))))
          (preservesLiteral_shiftLeftRound () (fun _ => .halt)
            (fun _ => by intro state tapes; rfl)
            (Sum.inr (Sum.inr (Sum.inl label))))
      · cases terminal
        intro state tapes
        simp [cappedShiftProgram,TM2.stepAux]
  | right label =>
      rcases label with label | tail
      · exact preservesLiteral_mapLabel CappedShiftLabel.right
          (shiftRightRoundProgram () (fun _ => .halt) (Sum.inl label))
          (preservesLiteral_shiftRightRound () (fun _ => .halt)
            (fun _ => by intro state tapes; rfl) (Sum.inl label))
      rcases tail with label | tail
      · exact preservesLiteral_mapLabel CappedShiftLabel.right
          (shiftRightRoundProgram () (fun _ => .halt)
            (Sum.inr (Sum.inl label)))
          (preservesLiteral_shiftRightRound () (fun _ => .halt)
            (fun _ => by intro state tapes; rfl) (Sum.inr (Sum.inl label)))
      rcases tail with label | terminal
      · exact preservesLiteral_mapLabel CappedShiftLabel.right
          (shiftRightRoundProgram () (fun _ => .halt)
            (Sum.inr (Sum.inr (Sum.inl label))))
          (preservesLiteral_shiftRightRound () (fun _ => .halt)
            (fun _ => by intro state tapes; rfl)
            (Sum.inr (Sum.inr (Sum.inl label))))
      · cases terminal
        intro state tapes
        simp [cappedShiftProgram,TM2.stepAux]
  | cleanupFuel =>
      exact preservesLiteral_cleanupStmt .work1 .cleanupFuel .cleanupCount
  | cleanupCount =>
      exact preservesLiteral_cleanupStmt .work3 .cleanupCount .cleanupTemp
  | cleanupTemp =>
      exact preservesLiteral_cleanupStmt .work4 .cleanupTemp .done
  | done => intro state tapes; rfl

end Lax759944Proofs.RamToTM

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

def shiftCountBase (w accumulator count:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):
    CoreStack -> List SparseSymbol
  | .accumulator => (fixedBits w accumulator).map SparseSymbol.bit
  | .work3 => (fixedBits w count).map SparseSymbol.bit
  | .memory => encodeSparseMemory w m ++ [.memoryEnd]
  | .work0 | .work1 | .work2 | .work4 | .work5 | .work6 | .work7 => []
  | k => base k

def shiftSetupStartCfg {N:Nat} (state:FullInterpreterState N)
    (w accumulator count:Nat) (m:SparseMemory)
    (base:CoreStack -> List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol) ShiftSetupLabel
      (FullInterpreterState N):=
  cleanReturnCfg .initializeState state
    (operandResultBase w accumulator count m base)

def shiftSetupMoveSource {N:Nat}:
    Sum SymbolMoveLabel Unit -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (Sum SymbolMoveLabel Unit)
      (FullInterpreterState N):=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work3 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done ())
    (fun _ => .halt)

theorem shiftSetupMoveSource_embeds {N:Nat} (rightShift:Bool)
    (label:Sum SymbolMoveLabel Unit)
    (hn:shiftSetupMoveSource (N:=N) label ≠ .halt):
    shiftSetupProgram (N:=N) rightShift (embedSetupMove label) =
      mapLabelStmt embedSetupMove (shiftSetupMoveSource label):=by
  cases label with
  | inl label => rfl
  | inr unit =>
      cases unit
      exact False.elim (hn rfl)

def shiftSetupCopySource {N:Nat}:
    Sum CopyLabel Unit -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (Sum CopyLabel Unit)
      (FullInterpreterState N):=
  liftRightProgram
    (lensPhaseLeft
      (copyCoreRenaming .accumulator .work1 .work7
        (by decide) (by decide) (by decide))
      FullInterpreterState.moveLens copyProgram .done ())
    (fun _ => .halt)

theorem shiftSetupCopySource_embeds {N:Nat} (rightShift:Bool)
    (label:Sum CopyLabel Unit)
    (hn:shiftSetupCopySource (N:=N) label ≠ .halt):
    shiftSetupProgram (N:=N) rightShift (embedSetupCopy label) =
      mapLabelStmt embedSetupCopy (shiftSetupCopySource label):=by
  cases label with
  | inl label => rfl
  | inr unit =>
      cases unit
      exact False.elim (hn rfl)

theorem shiftSetup_initialize_step {N:Nat} (rightShift:Bool)
    (state:FullInterpreterState N) (w accumulator count:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    TM2.step (shiftSetupProgram rightShift)
      (shiftSetupStartCfg state w accumulator count m base) =
    some (cleanReturnCfg (.move .loop) (resetShiftControls state)
      (operandResultBase w accumulator count m base)):=by
  rfl

theorem shiftSetup_move_start_bridge {N:Nat}
    (state:FullInterpreterState N) (w accumulator count:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    mapLabelCfg embedSetupMove
      (lensRenamedCfg
        (symbolMoveCoreRenaming .work0 .work3 (by decide))
        FullInterpreterState.moveLens
        (symbolMoveLocalCfg .loop
          ((fixedBits w count).reverse.map SparseSymbol.bit) [])
        state (operandResultBase w accumulator count m base)) =
    cleanReturnCfg (.move .loop)
      (FullInterpreterState.moveLens.put state default)
      (operandResultBase w accumulator count m base):=by
  simp [mapLabelCfg,lensRenamedCfg,symbolMoveLocalCfg,symbolMoveStacks,
    operandResultBase,cleanReturnCfg,renamedStacks,
    symbolMoveCoreRenaming,symbolMoveCoreDecode]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks,symbolMoveCoreRenaming,
      symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks,
      operandResultBase]

theorem shiftSetup_move_return_bridge {N:Nat}
    (state:FullInterpreterState N) (w accumulator count:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    mapLabelCfg embedSetupMove
      (mapLabelCfg Sum.inr
        (phaseReturnCfg
          (symbolMoveCoreRenaming .work0 .work3 (by decide))
          FullInterpreterState.moveLens ()
          (symbolMoveLocalCfg .done []
            (((fixedBits w count).reverse.map SparseSymbol.bit).reverse))
          state (operandResultBase w accumulator count m base))) =
    cleanReturnCfg (.copy .scan)
      (FullInterpreterState.moveLens.put state default)
      (shiftCountBase w accumulator count m base):=by
  simp [mapLabelCfg,phaseReturnCfg,lensRenamedCfg,symbolMoveLocalCfg,
    symbolMoveStacks,operandResultBase,cleanReturnCfg,renamedStacks,
    symbolMoveCoreRenaming,symbolMoveCoreDecode,shiftCountBase,
    List.map_reverse]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks,symbolMoveCoreRenaming,
      symbolMoveCoreDecode,symbolMoveLocalCfg,symbolMoveStacks,
      operandResultBase,shiftCountBase,List.map_reverse]

theorem shiftSetup_copy_start_bridge {N:Nat}
    (state:FullInterpreterState N) (w accumulator count:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    mapLabelCfg embedSetupCopy
      (lensRenamedCfg
        (copyCoreRenaming .accumulator .work1 .work7
          (by decide) (by decide) (by decide))
        FullInterpreterState.moveLens
        (copyCfg .scan ((fixedBits w accumulator).map SparseSymbol.bit) [] [])
        state (shiftCountBase w accumulator count m base)) =
    cleanReturnCfg (.copy .scan)
      (FullInterpreterState.moveLens.put state default)
      (shiftCountBase w accumulator count m base):=by
  simp [mapLabelCfg,lensRenamedCfg,copyCfg,copyCfgState,copyStacks,
    cleanReturnCfg,renamedStacks,copyCoreRenaming,shiftCountBase]
  constructor
  · rfl
  · funext k
    cases k <;> simp [renamedStacks,copyCoreRenaming,copyCfg,
      copyCfgState,copyStacks,shiftCountBase]

theorem shiftSetup_copy_return_bridge {N:Nat}
    (state:FullInterpreterState N) (w accumulator count:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    mapLabelCfg embedSetupCopy
      (mapLabelCfg Sum.inr
        (cleanReturnCfg () state
          (copyAccumulatorStacks
            ((fixedBits w accumulator).map SparseSymbol.bit)
            (shiftCountBase w accumulator count m base)))) =
    cleanReturnCfg (.controller (.countdown .scan)) state
      (shiftRoundBase w accumulator count
        (((fixedBits w accumulator).map SparseSymbol.bit).reverse)
        m base):=by
  simp [mapLabelCfg,cleanReturnCfg]
  constructor
  · rfl
  · funext k
    cases k <;> simp [copyAccumulatorStacks,shiftCountBase,shiftRoundBase]

theorem shiftSetupController_embeds {N:Nat} (rightShift:Bool)
    (label:CappedShiftLabel):
    shiftSetupProgram (N:=N) rightShift (.controller label) =
      mapLabelStmt ShiftSetupLabel.controller
        (cappedShiftProgram rightShift label):=by
  rfl

theorem shiftSetup_correct {N:Nat} (rightShift:Bool)
    (state:FullInterpreterState N) (w accumulator count:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    ((fun x => x.bind (TM2.step (shiftSetupProgram rightShift)))^[
        shiftSetupBound w])
      (some (shiftSetupStartCfg state w accumulator count m base)) =
    some (cleanReturnCfg (.controller (.countdown .scan))
      (resetShiftControls state)
      (shiftRoundBase w accumulator count
        (((fixedBits w accumulator).map SparseSymbol.bit).reverse)
        m base)):=by
  let resetState:=resetShiftControls state
  have hinit:=shiftSetup_initialize_step rightShift state w accumulator count
    m base
  let countBits:=(fixedBits w count).reverse.map SparseSymbol.bit
  have hmoveLocal:=symbolMoveLocal_correct countBits []
  have hmoveSource:=run_lensPhase_to_right
    (symbolMoveCoreRenaming .work0 .work3 (by decide))
    FullInterpreterState.moveLens symbolMoveCoreProgram .done (by rfl) ()
    (fun _:Unit => .halt) hmoveLocal rfl resetState
    (operandResultBase w accumulator count m base)
  have hmove:=iterate_mapLabelProgram_until_exit
    shiftSetupMoveSource (shiftSetupProgram rightShift) embedSetupMove
    (shiftSetupMoveSource_embeds rightShift) hmoveSource (by rfl)
  dsimp [countBits] at hmove
  simp only [List.length_map,List.length_reverse,fixedBits_length,
    List.append_nil] at hmove
  rw [shiftSetup_move_start_bridge resetState w accumulator count m base]
    at hmove
  rw [show FullInterpreterState.moveLens.put resetState default=resetState by
      rw [← resetShiftControls_move state]
      exact FullInterpreterState.moveLens.put_get resetState] at hmove
  rw [shiftSetup_move_return_bridge resetState w accumulator count m base]
    at hmove
  have hresetMove:FullInterpreterState.moveLens.put resetState default =
      resetState:=by
    rw [← resetShiftControls_move state]
    exact FullInterpreterState.moveLens.put_get resetState
  rw [hresetMove] at hmove
  have hcopySource:=fullCopyAccumulator_generic_correct ()
    (fun _:Unit => .halt)
    ((fixedBits w accumulator).map SparseSymbol.bit)
    (shiftCountBase w accumulator count m base) resetState
  have hcopy:=iterate_mapLabelProgram_until_exit
    shiftSetupCopySource (shiftSetupProgram rightShift) embedSetupCopy
    (shiftSetupCopySource_embeds rightShift) hcopySource (by rfl)
  rw [shiftSetup_copy_start_bridge resetState w accumulator count m base]
    at hcopy
  rw [show FullInterpreterState.moveLens.put resetState default=resetState by
      rw [← resetShiftControls_move state]
      exact FullInterpreterState.moveLens.put_get resetState] at hcopy
  rw [shiftSetup_copy_return_bridge resetState w accumulator count m base]
    at hcopy
  rw [show 2 * ((fixedBits w accumulator).map SparseSymbol.bit).length + 3 =
    2 * w + 3 by simp] at hcopy
  let stepO:=fun x:Option (TM2.Cfg
      (fun _:CoreStack => SparseSymbol) ShiftSetupLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (shiftSetupProgram rightShift))
  have hinit':(stepO^[1])
      (some (shiftSetupStartCfg state w accumulator count m base)) =
      some (cleanReturnCfg (.move .loop) resetState
        (operandResultBase w accumulator count m base)):=by
    simpa [stepO,resetState] using hinit
  have hmove':(stepO^[w + 2])
      (some (cleanReturnCfg (.move .loop) resetState
        (operandResultBase w accumulator count m base))) =
      some (cleanReturnCfg (.copy .scan) resetState
        (shiftCountBase w accumulator count m base)):=by
    rw [show w + 2=Nat.succ (Nat.succ w) by omega,
      Function.iterate_succ_apply,Function.iterate_succ_apply]
    exact hmove
  have h₁:=chain_iterations stepO hinit' hmove'
  have h₂:=chain_iterations stepO h₁ hcopy
  change (stepO^[shiftSetupBound w])
    (some (shiftSetupStartCfg state w accumulator count m base))=_
  rw [show shiftSetupBound w=1 + (w + 2) + (2 * w + 3) by
    simp [shiftSetupBound]; omega]
  exact h₂

theorem preservesLiteral_shiftSetupProgram {N:Nat}
    (rightShift:Bool):
    ProgramPreservesLiteral (shiftSetupProgram (N:=N) rightShift):=by
  intro label
  cases label with
  | «initializeState» =>
      intro state tapes
      simp [shiftSetupProgram,TM2.stepAux,literal_resetShiftControls]
  | move label =>
      exact preservesLiteral_mapLabel embedSetupMove
        (lensPhaseLeft
          (symbolMoveCoreRenaming .work0 .work3 (by decide))
          FullInterpreterState.moveLens symbolMoveCoreProgram .done () label)
        (preservesLiteral_lensPhase
          (symbolMoveCoreRenaming .work0 .work3 (by decide))
          FullInterpreterState.moveLens literal_move_put
          symbolMoveCoreProgram .done () label)
  | copy label =>
      exact preservesLiteral_mapLabel embedSetupCopy
        (lensPhaseLeft
          (copyCoreRenaming .accumulator .work1 .work7
            (by decide) (by decide) (by decide))
          FullInterpreterState.moveLens copyProgram .done () label)
        (preservesLiteral_lensPhase
          (copyCoreRenaming .accumulator .work1 .work7
            (by decide) (by decide) (by decide))
          FullInterpreterState.moveLens literal_move_put
          copyProgram .done () label)
  | controller label =>
      exact preservesLiteral_mapLabel ShiftSetupLabel.controller
        (cappedShiftProgram rightShift label)
        (preservesLiteral_cappedShiftProgram rightShift label)

theorem shiftLeftCore_correct {N:Nat}
    (state:FullInterpreterState N) (w accumulator count:Nat)
    (hw:0 < w) (hacc:accumulator < 2 ^ w)
    (hcount:count < 2 ^ w)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    ∃ steps,steps <= shiftCoreBound w∧ ∃ finalState,
      ((fun x => x.bind (TM2.step (shiftSetupProgram false)))^[steps])
        (some (shiftSetupStartCfg state w accumulator count m base)) =
      some (cleanReturnCfg (.controller .done) finalState
        (operandBoundaryBase w
          (cappedLeftValue w accumulator count w) m base)):=by
  have hsetup:=shiftSetup_correct false state w accumulator count m base
  let resetState:=resetShiftControls state
  let fuel:=((fixedBits w accumulator).map SparseSymbol.bit).reverse
  have hfuelLength:fuel.length=w:=by
    simp [fuel]
  rcases cappedLeft_loop_correct w accumulator count hw hacc hcount fuel m base
      resetState (resetShiftControls_countdown state) with
    ⟨loopSteps,hloopBound,loopState,hloop⟩
  rw [hfuelLength] at hloopBound
  have hloopEmbedded:=iterate_mapLabelProgram_until_exit
    (cappedShiftProgram false) (shiftSetupProgram false)
    ShiftSetupLabel.controller (fun label _ => shiftSetupController_embeds false label)
    hloop (by rfl)
  have hstart:
      mapLabelCfg ShiftSetupLabel.controller
        (cappedShiftCfg (.countdown .scan) resetState
          w accumulator count fuel m base) =
      cleanReturnCfg (.controller (.countdown .scan)) resetState
        (shiftRoundBase w accumulator count fuel m base):=by
    rfl
  rw [hstart] at hloopEmbedded
  have hend:
      mapLabelCfg ShiftSetupLabel.controller
        (controllerCfg .done loopState
          (operandBoundaryBase w
            (cappedLeftValue w accumulator count fuel.length) m base)) =
      cleanReturnCfg (.controller .done) loopState
        (operandBoundaryBase w
          (cappedLeftValue w accumulator count w) m base):=by
    simp [mapLabelCfg,controllerCfg,cleanReturnCfg,hfuelLength]
  rw [hend] at hloopEmbedded
  let stepO:=fun x:Option (TM2.Cfg
      (fun _:CoreStack => SparseSymbol) ShiftSetupLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (shiftSetupProgram false))
  have hall:=chain_iterations stepO hsetup hloopEmbedded
  refine ⟨shiftSetupBound w + loopSteps, ?_,loopState, ?_⟩
  · simp [shiftCoreBound]
    omega
  · exact hall

theorem shiftRightCore_correct {N:Nat}
    (state:FullInterpreterState N) (w accumulator count:Nat)
    (hw:0 < w) (hacc:accumulator < 2 ^ w)
    (hcount:count < 2 ^ w)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    ∃ steps,steps <= shiftCoreBound w∧ ∃ finalState,
      ((fun x => x.bind (TM2.step (shiftSetupProgram true)))^[steps])
        (some (shiftSetupStartCfg state w accumulator count m base)) =
      some (cleanReturnCfg (.controller .done) finalState
        (operandBoundaryBase w
          (cappedRightValue accumulator count w) m base)):=by
  have hsetup:=shiftSetup_correct true state w accumulator count m base
  let resetState:=resetShiftControls state
  let fuel:=((fixedBits w accumulator).map SparseSymbol.bit).reverse
  have hfuelLength:fuel.length=w:=by
    simp [fuel]
  rcases cappedRight_loop_correct w accumulator count hw hacc hcount fuel m base
      resetState (resetShiftControls_countdown state) with
    ⟨loopSteps,hloopBound,loopState,hloop⟩
  rw [hfuelLength] at hloopBound
  have hloopEmbedded:=iterate_mapLabelProgram_until_exit
    (cappedShiftProgram true) (shiftSetupProgram true)
    ShiftSetupLabel.controller (fun label _ => shiftSetupController_embeds true label)
    hloop (by rfl)
  have hstart:
      mapLabelCfg ShiftSetupLabel.controller
        (cappedShiftCfg (.countdown .scan) resetState
          w accumulator count fuel m base) =
      cleanReturnCfg (.controller (.countdown .scan)) resetState
        (shiftRoundBase w accumulator count fuel m base):=by
    rfl
  rw [hstart] at hloopEmbedded
  have hend:
      mapLabelCfg ShiftSetupLabel.controller
        (controllerCfg .done loopState
          (operandBoundaryBase w
            (cappedRightValue accumulator count fuel.length) m base)) =
      cleanReturnCfg (.controller .done) loopState
        (operandBoundaryBase w
          (cappedRightValue accumulator count w) m base):=by
    simp [mapLabelCfg,controllerCfg,cleanReturnCfg,hfuelLength]
  rw [hend] at hloopEmbedded
  let stepO:=fun x:Option (TM2.Cfg
      (fun _:CoreStack => SparseSymbol) ShiftSetupLabel
      (FullInterpreterState N)) =>
    x.bind (TM2.step (shiftSetupProgram true))
  have hall:=chain_iterations stepO hsetup hloopEmbedded
  refine ⟨shiftSetupBound w + loopSteps, ?_,loopState, ?_⟩
  · simp [shiftCoreBound]
    omega
  · exact hall

theorem fullShiftLeft_embeds {N:Nat} {R:Type} (o:Op)
    (rightShift:Bool) (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (label:ShiftSetupLabel)
    (hn:shiftSetupProgram (N:=N) rightShift label ≠ .halt):
    fullShiftProgram (N:=N) o rightShift returnLabel right (Sum.inl label) =
      mapLabelStmt Sum.inl (shiftSetupProgram rightShift label):=by
  cases label with
  | «initializeState» => rfl
  | move label => rfl
  | copy label => rfl
  | controller label =>
      cases label with
      | countdown label => rfl
      | fuel => rfl
      | left label => rfl
      | right label => rfl
      | cleanupFuel => rfl
      | cleanupCount => rfl
      | cleanupTemp => rfl
      | done => exact False.elim (hn rfl)

def fullShiftPostStartCfg {N:Nat} {R:Type}
    (state:FullInterpreterState N) (w value:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    TM2.Cfg (fun _:CoreStack => SparseSymbol) (FullShiftLabel R)
      (FullInterpreterState N):=
  mapLabelCfg Sum.inr <|
    lensRenamedCfg coreIdentityRenaming (fullStateIdentityLens N)
      (conditionalZeroCfg .rewrite state
        ((fixedBits w value).map SparseSymbol.bit) []
        (operandBoundaryBase w value m base))
      state (operandBoundaryBase w value m base)

theorem fullShift_to_post_step {N:Nat} {R:Type} (o:Op)
    (rightShift:Bool) (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N) (w value:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    TM2.step (fullShiftProgram o rightShift returnLabel right)
      (mapLabelCfg Sum.inl
        (cleanReturnCfg (.controller .done) state
          (operandBoundaryBase w value m base))) =
    some (fullShiftPostStartCfg (R:=R)
      (FullInterpreterState.moveLens.put state default)
      w value m base):=by
  simp [fullShiftProgram,liftRightProgram,fullShiftLeft,
    fullShiftPostStartCfg,mapLabelCfg,lensRenamedCfg,
    coreIdentityRenaming,renamedStacks_coreIdentity,fullStateIdentityLens,
    conditionalZeroCfg,cleanReturnCfg,TM2.step,TM2.stepAux]
  funext k
  cases k <;> simp [renamedStacks,coreIdentityRenaming,
    conditionalZeroCfg,operandBoundaryBase]

theorem fullShift_finish {N:Nat} {R:Type} (o:Op)
    (rightShift:Bool) (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N) (w accumulator count value:Nat)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (coreSteps:Nat) (hcoreBound:coreSteps <= shiftCoreBound w)
    (coreState:FullInterpreterState N)
    (hcore:
      ((fun x => x.bind (TM2.step (shiftSetupProgram rightShift)))^[coreSteps])
        (some (shiftSetupStartCfg state w accumulator count m base)) =
      some (cleanReturnCfg (.controller .done) coreState
        (operandBoundaryBase w value m base))):
    ∃ steps,steps <= fullShiftBound w∧ ∃ finalState,
      ((fun x => x.bind
        (TM2.step (fullShiftProgram o rightShift returnLabel right)))^[steps])
        (some (mapLabelCfg Sum.inl
          (shiftSetupStartCfg state w accumulator count m base))) =
      some (mapLabelCfg Sum.inr
        (mapLabelCfg (fun l:ConditionalZeroTailLabel R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w
                (if operandLiteralOversized o
                    (FullInterpreterState.moveLens.put coreState default)
                  then 0 else value) m base))))):=by
  have hcoreEmbedded:=iterate_mapLabelProgram_until_exit
    (shiftSetupProgram rightShift)
    (fullShiftProgram o rightShift returnLabel right) Sum.inl
    (fullShiftLeft_embeds o rightShift returnLabel right) hcore (by rfl)
  let postState:=FullInterpreterState.moveLens.put coreState default
  have htransition:=fullShift_to_post_step o rightShift returnLabel right
    coreState w value m base
  rcases conditionalZeroPhase_correct o returnLabel right w value m base
      postState (FullInterpreterState.moveLens.get_put _ _) with
    ⟨finalState,hpost⟩
  have hpostLift:=transport_iterate_liftRightProgram
    (fullShiftLeft (R:=R) rightShift)
    (conditionalZeroPhaseProgram o returnLabel right) hpost
  let stepO:=fun x:Option (TM2.Cfg
      (fun _:CoreStack => SparseSymbol) (FullShiftLabel R)
      (FullInterpreterState N)) =>
    x.bind (TM2.step (fullShiftProgram o rightShift returnLabel right))
  have htransition':(stepO^[1])
      (some (mapLabelCfg Sum.inl
        (cleanReturnCfg (.controller .done) coreState
          (operandBoundaryBase w value m base)))) =
      some (fullShiftPostStartCfg (R:=R) postState w value m base):=by
    simpa [stepO,postState] using htransition
  have h₁:=chain_iterations stepO hcoreEmbedded htransition'
  have h₂:=chain_iterations stepO h₁ hpostLift
  refine ⟨coreSteps + 1 + (2 * w + 4), ?_,finalState, ?_⟩
  · simp [fullShiftBound]
    omega
  · simpa [stepO,fullShiftProgram,postState] using h₂

theorem operandLiteralOversized_eq_of_literal {N:Nat} (o:Op)
    (first second:FullInterpreterState N)
    (h:first.literal=second.literal):
    operandLiteralOversized o first=operandLiteralOversized o second:=by
  cases o with
  | lit n =>
      exact congrArg (fun value:BoundedLiteralControl N =>
        value.remaining.val != 0) h
  | mem n => rfl
  | ind n => rfl

theorem fullShiftLeft_correct {N:Nat} {R:Type} (o:Op)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N) (w accumulator count:Nat)
    (hw:0 < w) (hacc:accumulator < 2 ^ w)
    (hcount:count < 2 ^ w)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    ∃ steps,steps <= fullShiftBound w∧ ∃ finalState,
      ((fun x => x.bind
        (TM2.step (fullShiftProgram o false returnLabel right)))^[steps])
        (some (mapLabelCfg Sum.inl
          (shiftSetupStartCfg state w accumulator count m base))) =
      some (mapLabelCfg Sum.inr
        (mapLabelCfg (fun l:ConditionalZeroTailLabel R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w
                (if operandLiteralOversized o state
                  then 0 else cappedLeftValue w accumulator count w) m base))))):=by
  rcases shiftLeftCore_correct state w accumulator count hw hacc hcount m base with
    ⟨coreSteps,hbound,coreState,hcore⟩
  have hliteral:=iterate_preservesLiteral (shiftSetupProgram false)
    (preservesLiteral_shiftSetupProgram false)
    (shiftSetupStartCfg state w accumulator count m base)
    (cleanReturnCfg (.controller .done) coreState
      (operandBoundaryBase w (cappedLeftValue w accumulator count w) m base))
    hcore
  have hover:operandLiteralOversized o
      (FullInterpreterState.moveLens.put coreState default) =
      operandLiteralOversized o state:=by
    rw [operandLiteralOversized_move_put]
    exact operandLiteralOversized_eq_of_literal o coreState state hliteral
  rcases fullShift_finish o false returnLabel right state w accumulator count
      (cappedLeftValue w accumulator count w) m base coreSteps hbound coreState
      hcore with ⟨steps,hsteps,finalState,hrun⟩
  refine ⟨steps,hsteps,finalState, ?_⟩
  simpa [hover] using hrun

theorem fullShiftRight_correct {N:Nat} {R:Type} (o:Op)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (state:FullInterpreterState N) (w accumulator count:Nat)
    (hw:0 < w) (hacc:accumulator < 2 ^ w)
    (hcount:count < 2 ^ w)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol):
    ∃ steps,steps <= fullShiftBound w∧ ∃ finalState,
      ((fun x => x.bind
        (TM2.step (fullShiftProgram o true returnLabel right)))^[steps])
        (some (mapLabelCfg Sum.inl
          (shiftSetupStartCfg state w accumulator count m base))) =
      some (mapLabelCfg Sum.inr
        (mapLabelCfg (fun l:ConditionalZeroTailLabel R => Sum.inr l)
          (mapLabelCfg (fun l:R => Sum.inr l)
            (cleanReturnCfg returnLabel finalState
              (operandBoundaryBase w
                (if operandLiteralOversized o state
                  then 0 else cappedRightValue accumulator count w) m base))))):=by
  rcases shiftRightCore_correct state w accumulator count hw hacc hcount m base with
    ⟨coreSteps,hbound,coreState,hcore⟩
  have hliteral:=iterate_preservesLiteral (shiftSetupProgram true)
    (preservesLiteral_shiftSetupProgram true)
    (shiftSetupStartCfg state w accumulator count m base)
    (cleanReturnCfg (.controller .done) coreState
      (operandBoundaryBase w (cappedRightValue accumulator count w) m base))
    hcore
  have hover:operandLiteralOversized o
      (FullInterpreterState.moveLens.put coreState default) =
      operandLiteralOversized o state:=by
    rw [operandLiteralOversized_move_put]
    exact operandLiteralOversized_eq_of_literal o coreState state hliteral
  rcases fullShift_finish o true returnLabel right state w accumulator count
      (cappedRightValue accumulator count w) m base coreSteps hbound coreState
      hcore with ⟨steps,hsteps,finalState,hrun⟩
  refine ⟨steps,hsteps,finalState, ?_⟩
  simpa [hover] using hrun

theorem shiftLeftInstruction_finish {N:Nat} {R:Type}
    (o:Op) (hN:operandArgument o <= N)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator:Nat) (hacc:accumulator < 2 ^ w) (hw:0 < w)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state operandState:FullInterpreterState N)
    (operandSteps:Nat) (hoperandBound:operandSteps <= operandEvalBound w m)
    (hoperand:
      ((fun x => x.bind
        (TM2.step (shiftInstructionProgram o false returnLabel right)))^[
          operandSteps])
        (some (operandEvalStartCfg
          (R:=FullShiftLabel R) o hN w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg Sum.inl
          (shiftSetupStartCfg operandState w accumulator
            (operandWordValue w o m) m base))))
    (hsemantic:
      (if operandLiteralOversized o operandState then 0
        else accumulator * 2 ^ operandWordValue w o m % 2 ^ w) =
      accumulator * 2 ^ sparseValue w o m % 2 ^ w):
    ∃ steps,steps <= shiftInstructionBound w m∧ ∃ finalState,
      ((fun x => x.bind
        (TM2.step (shiftInstructionProgram o false returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=FullShiftLabel R) o hN w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg Sum.inr
          (mapLabelCfg (fun l:ConditionalZeroTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l:R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w
                  (accumulator * 2 ^ sparseValue w o m % 2 ^ w)
                  m base)))))):=by
  have hcount:=operandWordValue_lt w o m
  rcases fullShiftLeft_correct o returnLabel right operandState w accumulator
      (operandWordValue w o m) hw hacc hcount m base with
    ⟨shiftSteps,hshiftBound,finalState,hshift⟩
  rw [cappedLeftValue_width w accumulator (operandWordValue w o m) hacc]
    at hshift
  have hshiftLift:=transport_iterate_operand_right o
    (Sum.inl ShiftSetupLabel.initializeState)
    (fullShiftProgram o false returnLabel right) hshift
  have hall:=chain_iterations
    (fun x:Option (TM2.Cfg
      (fun _:CoreStack => SparseSymbol) (ShiftInstructionLabel o R)
      (FullInterpreterState N)) =>
      x.bind (TM2.step (shiftInstructionProgram o false returnLabel right)))
    hoperand hshiftLift
  refine ⟨operandSteps + shiftSteps, ?_,finalState, ?_⟩
  · simp [shiftInstructionBound]
    omega
  · simpa [shiftInstructionProgram,hsemantic] using hall

theorem shiftLeftInstruction_correct {N:Nat} {R:Type}
    (o:Op) (hN:operandArgument o <= N)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator:Nat) (hw:0 < w) (hacc:accumulator < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ steps,steps <= shiftInstructionBound w m∧ ∃ finalState,
      ((fun x => x.bind
        (TM2.step (shiftInstructionProgram o false returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=FullShiftLabel R) o hN w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg Sum.inr
          (mapLabelCfg (fun l:ConditionalZeroTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l:R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w
                  (accumulator * 2 ^ sparseValue w o m % 2 ^ w)
                  m base)))))):=by
  cases o with
  | mem address =>
      rcases operandEval_correct (.mem address) hN w accumulator m hm
          (Sum.inl ShiftSetupLabel.initializeState)
          (fullShiftProgram (.mem address) false returnLabel right)
          state base with ⟨operandSteps,hbound,operandState,hoperand⟩
      apply shiftLeftInstruction_finish (.mem address) hN returnLabel right
        w accumulator hacc hw m base state operandState operandSteps hbound
      · simpa [shiftInstructionProgram,shiftSetupStartCfg] using! hoperand
      · simp [operandLiteralOversized,operandWordValue,
          Nat.mod_eq_of_lt (sparseValue_mem_lt hm address)]
  | ind address =>
      rcases operandEval_correct (.ind address) hN w accumulator m hm
          (Sum.inl ShiftSetupLabel.initializeState)
          (fullShiftProgram (.ind address) false returnLabel right)
          state base with ⟨operandSteps,hbound,operandState,hoperand⟩
      apply shiftLeftInstruction_finish (.ind address) hN returnLabel right
        w accumulator hacc hw m base state operandState operandSteps hbound
      · simpa [shiftInstructionProgram,shiftSetupStartCfg] using! hoperand
      · simp [operandLiteralOversized,operandWordValue,
          Nat.mod_eq_of_lt (sparseValue_ind_lt hm address)]
  | lit n =>
      change n <= N at hN
      let operandState:=FullInterpreterState.literalLens.put state
        ⟨none, ⟨n / 2 ^ w,by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
      have hoperand:=literalOperand_correct n hN w accumulator m
        (Sum.inl ShiftSetupLabel.initializeState)
        (fullShiftProgram (.lit n) false returnLabel right) state base
      have hbound:2 * w + 3 <= operandEvalBound w m:=by
        simp [operandEvalBound]
        omega
      apply shiftLeftInstruction_finish (.lit n) hN returnLabel right
        w accumulator hacc hw m base state operandState (2 * w + 3) hbound
      · simpa [shiftInstructionProgram,operandEvalStartCfg,operandArgument,
          embedOperandReturnCfg,shiftSetupStartCfg,operandState] using! hoperand
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
          have hover:operandLiteralOversized (.lit n) operandState=true:=by
            simp only [operandLiteralOversized]
            rw [show FullInterpreterState.literalLens.get operandState =
                ⟨none, ⟨n / 2 ^ w,by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩ by
              exact FullInterpreterState.literalLens.get_put _ _]
            simp [hquot]
          have hwn:w <= n:=le_trans Nat.lt_two_pow_self.le
            (Nat.le_of_not_gt hnlt)
          have hdvd:2 ^ w ∣ 2 ^ n:=Nat.pow_dvd_pow 2 hwn
          have hresult:accumulator * 2 ^ n % 2 ^ w=0:=
            Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdvd accumulator)
          simp [hover,sparseValue,Op.value,hresult]

theorem shiftRightInstruction_finish {N:Nat} {R:Type}
    (o:Op) (hN:operandArgument o <= N)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator:Nat) (hacc:accumulator < 2 ^ w) (hw:0 < w)
    (m:SparseMemory) (base:CoreStack -> List SparseSymbol)
    (state operandState:FullInterpreterState N)
    (operandSteps:Nat) (hoperandBound:operandSteps <= operandEvalBound w m)
    (hoperand:
      ((fun x => x.bind
        (TM2.step (shiftInstructionProgram o true returnLabel right)))^[
          operandSteps])
        (some (operandEvalStartCfg
          (R:=FullShiftLabel R) o hN w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg Sum.inl
          (shiftSetupStartCfg operandState w accumulator
            (operandWordValue w o m) m base))))
    (hsemantic:
      (if operandLiteralOversized o operandState then 0
        else accumulator / 2 ^ operandWordValue w o m) =
      accumulator / 2 ^ sparseValue w o m % 2 ^ w):
    ∃ steps,steps <= shiftInstructionBound w m∧ ∃ finalState,
      ((fun x => x.bind
        (TM2.step (shiftInstructionProgram o true returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=FullShiftLabel R) o hN w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg Sum.inr
          (mapLabelCfg (fun l:ConditionalZeroTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l:R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w
                  (accumulator / 2 ^ sparseValue w o m % 2 ^ w)
                  m base)))))):=by
  have hcount:=operandWordValue_lt w o m
  rcases fullShiftRight_correct o returnLabel right operandState w accumulator
      (operandWordValue w o m) hw hacc hcount m base with
    ⟨shiftSteps,hshiftBound,finalState,hshift⟩
  rw [cappedRightValue_width w accumulator (operandWordValue w o m) hacc]
    at hshift
  have hshiftLift:=transport_iterate_operand_right o
    (Sum.inl ShiftSetupLabel.initializeState)
    (fullShiftProgram o true returnLabel right) hshift
  have hall:=chain_iterations
    (fun x:Option (TM2.Cfg
      (fun _:CoreStack => SparseSymbol) (ShiftInstructionLabel o R)
      (FullInterpreterState N)) =>
      x.bind (TM2.step (shiftInstructionProgram o true returnLabel right)))
    hoperand hshiftLift
  refine ⟨operandSteps + shiftSteps, ?_,finalState, ?_⟩
  · simp [shiftInstructionBound]
    omega
  · simpa [shiftInstructionProgram,hsemantic] using hall

theorem shiftRightInstruction_correct {N:Nat} {R:Type}
    (o:Op) (hN:operandArgument o <= N)
    (returnLabel:R)
    (right:R -> TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N))
    (w accumulator:Nat) (hw:0 < w) (hacc:accumulator < 2 ^ w)
    (m:SparseMemory) (hm:m.Normalized w)
    (base:CoreStack -> List SparseSymbol)
    (state:FullInterpreterState N):
    ∃ steps,steps <= shiftInstructionBound w m∧ ∃ finalState,
      ((fun x => x.bind
        (TM2.step (shiftInstructionProgram o true returnLabel right)))^[steps])
        (some (operandEvalStartCfg
          (R:=FullShiftLabel R) o hN w accumulator m state base)) =
      some (embedOperandReturnCfg o
        (mapLabelCfg Sum.inr
          (mapLabelCfg (fun l:ConditionalZeroTailLabel R => Sum.inr l)
            (mapLabelCfg (fun l:R => Sum.inr l)
              (cleanReturnCfg returnLabel finalState
                (operandBoundaryBase w
                  (accumulator / 2 ^ sparseValue w o m % 2 ^ w)
                  m base)))))):=by
  cases o with
  | mem address =>
      rcases operandEval_correct (.mem address) hN w accumulator m hm
          (Sum.inl ShiftSetupLabel.initializeState)
          (fullShiftProgram (.mem address) true returnLabel right)
          state base with ⟨operandSteps,hbound,operandState,hoperand⟩
      apply shiftRightInstruction_finish (.mem address) hN returnLabel right
        w accumulator hacc hw m base state operandState operandSteps hbound
      · simpa [shiftInstructionProgram,shiftSetupStartCfg] using! hoperand
      · have hv:=sparseValue_mem_lt hm address
        simp [operandLiteralOversized,operandWordValue,
          Nat.mod_eq_of_lt hv,
          Nat.mod_eq_of_lt (lt_of_le_of_lt
            (Nat.div_le_self accumulator (2 ^ sparseValue w (.mem address) m))
            hacc)]
  | ind address =>
      rcases operandEval_correct (.ind address) hN w accumulator m hm
          (Sum.inl ShiftSetupLabel.initializeState)
          (fullShiftProgram (.ind address) true returnLabel right)
          state base with ⟨operandSteps,hbound,operandState,hoperand⟩
      apply shiftRightInstruction_finish (.ind address) hN returnLabel right
        w accumulator hacc hw m base state operandState operandSteps hbound
      · simpa [shiftInstructionProgram,shiftSetupStartCfg] using! hoperand
      · have hv:=sparseValue_ind_lt hm address
        simp [operandLiteralOversized,operandWordValue,
          Nat.mod_eq_of_lt hv,
          Nat.mod_eq_of_lt (lt_of_le_of_lt
            (Nat.div_le_self accumulator (2 ^ sparseValue w (.ind address) m))
            hacc)]
  | lit n =>
      change n <= N at hN
      let operandState:=FullInterpreterState.literalLens.put state
        ⟨none, ⟨n / 2 ^ w,by
          exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩
      have hoperand:=literalOperand_correct n hN w accumulator m
        (Sum.inl ShiftSetupLabel.initializeState)
        (fullShiftProgram (.lit n) true returnLabel right) state base
      have hbound:2 * w + 3 <= operandEvalBound w m:=by
        simp [operandEvalBound]
        omega
      apply shiftRightInstruction_finish (.lit n) hN returnLabel right
        w accumulator hacc hw m base state operandState (2 * w + 3) hbound
      · simpa [shiftInstructionProgram,operandEvalStartCfg,operandArgument,
          embedOperandReturnCfg,shiftSetupStartCfg,operandState] using! hoperand
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
          have hdivlt:accumulator / 2 ^ n < 2 ^ w:=
            lt_of_le_of_lt (Nat.div_le_self _ _) hacc
          simp [hover,operandWordValue,sparseValue,Op.value,
            Nat.mod_eq_of_lt hnlt,Nat.mod_eq_of_lt hdivlt]
        · have hquot:n / 2 ^ w ≠ 0:=by
            intro hz
            exact hnlt ((literalWord_remaining_eq_zero_iff n w).1 hz)
          have hover:operandLiteralOversized (.lit n) operandState=true:=by
            simp only [operandLiteralOversized]
            rw [show FullInterpreterState.literalLens.get operandState =
                ⟨none, ⟨n / 2 ^ w,by
                  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩⟩ by
              exact FullInterpreterState.literalLens.get_put _ _]
            simp [hquot]
          have hpow:2 ^ w <= 2 ^ n:=Nat.pow_le_pow_right (by omega)
            (le_trans Nat.lt_two_pow_self.le (Nat.le_of_not_gt hnlt))
          have hzeroResult:accumulator / 2 ^ n=0:=
            Nat.div_eq_of_lt (lt_of_lt_of_le hacc hpow)
          simp [hover,sparseValue,Op.value,hzeroResult]

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

theorem finite_step_load_entry {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (pc:BoundedPC p) (o:Op)
    (hfetch:pc.fetch=some (.load o))
    (state:FullInterpreterState N) (tapes:CoreStack -> List SparseSymbol):
    let harg:operandArgument o <= N:=
      (instrArgument_le_of_boundedFetch pc hfetch).trans hbound
    let bo:=BoundedOp.ofOp o harg
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data pc .load)) state tapes) =
    some (finiteInterpreterCfg
      (encodeLoadLabel pc bo (by simpa [bo] using operandEvalStartLabel o))
      (FullInterpreterState.literalLens.put state
        (BoundedLiteralControl.initial harg)) tapes):=by
  dsimp only
  change some (TM2.stepAux (finitePrepareEntry p N hbound pc) state tapes)=_
  rw [finitePrepareEntry_of_fetch hbound pc (.load o) hfetch]
  simp [finitePrepareInstr,
    finiteInitializeEntry,instrArgument,finiteInterpreterCfg,TM2.stepAux]

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

theorem fullLoadProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (fullLoadProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft coreIdentityRenaming
      FullInterpreterState.macroLens (by intros; rfl)
      closedAccInstallProgram closedAccInstallDone
      (Sum.inl DiscardLabel.loop)
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft
        (discardCoreRenaming .work7) FullInterpreterState.moveLens
        (by intros; rfl) discardProgram .done returnLabel
    · exact hright

theorem loadResetProgram_preservesDispatch {N:Nat} {R:Type}:
    ProgramPreservesDispatch (loadResetProgram (N:=N) (R:=R)):=by
  intro label
  cases label
  intro state tapes
  rfl

theorem loadInstructionTailProgram_preservesDispatch
    {N:Nat} {R:Type} (returnLabel:R):
    ProgramPreservesDispatch
      (loadInstructionTailProgram (N:=N) returnLabel (fun _ => .halt)):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact loadResetProgram_preservesDispatch
  · exact fullLoadProgram_preservesDispatch returnLabel _
      haltProgram_preservesDispatch

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

theorem fullAddPhaseProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R) (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (fullAddPhaseProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft coreIdentityRenaming
      FullInterpreterState.macroLens (by intros; rfl)
      closedAddPipelineProgram closedAddDone returnLabel
  · exact hright

theorem addInstructionTailProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R) (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (addInstructionTailProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label; cases label; intro state tapes; rfl
  · exact fullAddPhaseProgram_preservesDispatch returnLabel right hright

theorem fullCopyProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R) (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (fullCopyProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft
      (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide) (by decide))
      FullInterpreterState.moveLens (by intros; rfl) copyProgram .done returnLabel
  · exact hright

theorem fullPrependProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R) (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (fullPrependProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft prependCoreRenaming
      FullInterpreterState.prependLens (by intros; rfl)
      prependCoreProgram .done returnLabel
  · exact hright

theorem storeInstructionTailProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R) (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (storeInstructionTailProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label; cases label; intro state tapes; rfl
  · apply fullCopyProgram_preservesDispatch
    apply ProgramPreservesDispatch.liftRightProgram
    · intro label; cases label; intro state tapes; rfl
    · exact fullPrependProgram_preservesDispatch returnLabel right hright

theorem readTransferProgram_preservesDispatch {N:Nat} {R:Type}
    (exhaustedLabel returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (readTransferProgram exhaustedLabel returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label
    apply StmtPreservesDispatch.sound
    cases label <;>
      simp [StmtPreservesDispatch,readTransferLeftProgram,
        FullInterpreterState.moveLens,FullInterpreterState.prependLens,
        FullInterpreterState.dispatchLens,FullInterpreterState.macroLens,
        InterpreterMacroState.moveLens,InterpreterMacroState.prependLens,
        StateLens.comp]
  · exact fullPrependProgram_preservesDispatch returnLabel right hright

theorem writeTailProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R) (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (writeTailProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label; cases label; intro state tapes; rfl
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft
        (symbolMoveCoreRenaming .work0 .work1 (by decide))
        FullInterpreterState.moveLens (by intros; rfl)
        symbolMoveCoreProgram .done (Sum.inl SymbolMoveLabel.loop)
    · apply ProgramPreservesDispatch.liftRightProgram
      · exact ProgramPreservesDispatch.lensPhaseLeft
          (symbolMoveCoreRenaming .work1 .output (by decide))
          FullInterpreterState.moveLens (by intros; rfl)
          symbolMoveCoreProgram .done (Sum.inl WriteFinishLabel.finish)
      · apply ProgramPreservesDispatch.liftRightProgram
        · intro label; cases label; intro state tapes; rfl
        · exact hright

theorem fullSubtractProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R) (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (fullSubtractProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens (by intros; rfl)
      symbolMoveCoreProgram .done (Sum.inl AddLabel.loop)
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft binaryCoreRenaming
        FullInterpreterState.subLens (by intros; rfl)
        sparseSubCoreProgram .done (Sum.inl ConditionalInstallLabel.loop)
    · apply ProgramPreservesDispatch.liftRightProgram
      · intro label state tapes
        cases label
        · simp [lensPhaseLeft,lensRenameStmt,conditionalInstallProgram,
            fullStateIdentityLens,coreIdentityRenaming,TM2.stepAux]
          generalize
            (FullInterpreterState.moveLens.get
              (FullInterpreterState.moveLens.put state
                { held:=(tapes .work0).head? })).held.isNone=b
          cases b <;> rfl
        · rfl
      · exact hright

theorem subtractInstructionTailProgram_preservesDispatch {N:Nat} {R:Type}
    (o:Op) (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (subtractInstructionTailProgram o returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label; cases label; intro state tapes; rfl
  · exact fullSubtractProgram_preservesDispatch returnLabel right hright

theorem zipInstructionTailProgram_preservesDispatch {N:Nat} {R:Type}
    (f:Bool→ Bool→ Bool) (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (zipInstructionTailProgram f returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label; cases label; intro state tapes; rfl
  · apply ProgramPreservesDispatch.liftRightProgram
    · exact ProgramPreservesDispatch.lensPhaseLeft coreIdentityRenaming
        FullInterpreterState.macroLens (by intros; rfl)
        (closedZipProgram f) closedZipDone returnLabel
    · exact hright

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

theorem shiftRoundFinalProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (shiftRoundFinalProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens (by intros; rfl)
      symbolMoveCoreProgram .done returnLabel
  · exact hright

theorem shiftLeftRoundTailProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (shiftLeftRoundTailProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens (by intros; rfl)
      symbolMoveCoreProgram .done (Sum.inl SymbolMoveLabel.loop)
  · exact shiftRoundFinalProgram_preservesDispatch returnLabel right hright

theorem shiftLeftRoundProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (shiftLeftRoundProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft shiftRoundRenaming
      FullInterpreterState.shiftLens (by intros; rfl)
      sparseShiftLeftCoreProgram .done (Sum.inl SymbolMoveLabel.loop)
  · exact shiftLeftRoundTailProgram_preservesDispatch returnLabel right hright

theorem shiftRightRoundProgram_preservesDispatch {N:Nat} {R:Type}
    (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (shiftRightRoundProgram returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · exact ProgramPreservesDispatch.lensPhaseLeft shiftRoundRenaming
      FullInterpreterState.shiftLens (by intros; rfl)
      sparseShiftRightCoreProgram .done (Sum.inl SymbolMoveLabel.loop)
  · exact shiftLeftRoundTailProgram_preservesDispatch returnLabel right hright

theorem fullShiftProgram_preservesDispatch {N:Nat} {R:Type}
    (o:Op) (rightShift:Bool) (returnLabel:R)
    (right:R→ TM2.Stmt (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N)) (hright:ProgramPreservesDispatch right):
    ProgramPreservesDispatch (fullShiftProgram o rightShift returnLabel right):=by
  apply ProgramPreservesDispatch.liftRightProgram
  · intro label
    cases label
    · apply PreservesDispatch.mapLabelStmt Sum.inl
      apply StmtPreservesDispatch.sound
      simp [StmtPreservesDispatch,shiftSetupProgram,resetShiftControls,
        FullInterpreterState.dispatchLens,FullInterpreterState.macroLens,
        FullInterpreterState.moveLens,FullInterpreterState.shiftLens,
        FullInterpreterState.countdownLens,
        InterpreterMacroState.dispatchLens,InterpreterMacroState.moveLens,
        StateLens.comp]
    · rename_i label
      apply PreservesDispatch.mapLabelStmt Sum.inl
      apply PreservesDispatch.mapLabelStmt embedSetupMove
      exact PreservesDispatch.lensPhaseLeft
        (symbolMoveCoreRenaming .work0 .work3 (by decide))
        FullInterpreterState.moveLens (by intros; rfl)
        symbolMoveCoreProgram .done () label
    · rename_i label
      apply PreservesDispatch.mapLabelStmt Sum.inl
      apply PreservesDispatch.mapLabelStmt embedSetupCopy
      exact PreservesDispatch.lensPhaseLeft
        (copyCoreRenaming .accumulator .work1 .work7
          (by decide) (by decide) (by decide))
        FullInterpreterState.moveLens (by intros; rfl)
        copyProgram .done () label
    · rename_i label
      cases label with
      | countdown label =>
          simp only [fullShiftLeft,shiftSetupProgram,cappedShiftProgram]
          apply PreservesDispatch.mapLabelStmt Sum.inl
          apply PreservesDispatch.mapLabelStmt ShiftSetupLabel.controller
          apply PreservesDispatch.mapLabelStmt embedCountdownController
          exact (ProgramPreservesDispatch.lensMultiPhaseLeft
            countdownCoreRenaming FullInterpreterState.countdownLens
            (by intros; rfl) sparseCountdownProgram
            (countdownExit CappedShiftLabel.cleanupFuel CappedShiftLabel.fuel)
            countdownOnExit (by intros; rfl)) label
      | left label =>
        by_cases h:label=Sum.inr (Sum.inr (Sum.inr ()))
        · subst label
          apply StmtPreservesDispatch.sound
          simp [StmtPreservesDispatch,fullShiftLeft,shiftSetupProgram,
            cappedShiftProgram,mapLabelStmt,FullInterpreterState.countdownLens,
            FullInterpreterState.dispatchLens,FullInterpreterState.macroLens,
            StateLens.comp]
        · simp only [fullShiftLeft,shiftSetupProgram,cappedShiftProgram,h]
          apply PreservesDispatch.mapLabelStmt Sum.inl
          apply PreservesDispatch.mapLabelStmt ShiftSetupLabel.controller
          apply PreservesDispatch.mapLabelStmt CappedShiftLabel.left
          exact shiftLeftRoundProgram_preservesDispatch () (fun _ => .halt)
            (by intro u; cases u; intro state tapes; rfl) label
      | right label =>
        by_cases h:label=Sum.inr (Sum.inr (Sum.inr ()))
        · subst label
          apply StmtPreservesDispatch.sound
          simp [StmtPreservesDispatch,fullShiftLeft,shiftSetupProgram,
            cappedShiftProgram,mapLabelStmt,FullInterpreterState.countdownLens,
            FullInterpreterState.dispatchLens,FullInterpreterState.macroLens,
            StateLens.comp]
        · simp only [fullShiftLeft,shiftSetupProgram,cappedShiftProgram,h]
          apply PreservesDispatch.mapLabelStmt Sum.inl
          apply PreservesDispatch.mapLabelStmt ShiftSetupLabel.controller
          apply PreservesDispatch.mapLabelStmt CappedShiftLabel.right
          exact shiftRightRoundProgram_preservesDispatch () (fun _ => .halt)
            (by intro u; cases u; intro state tapes; rfl) label
      | fuel | cleanupFuel | cleanupCount | cleanupTemp | done =>
        apply StmtPreservesDispatch.sound
        simp [StmtPreservesDispatch,fullShiftLeft,shiftSetupProgram,
          cappedShiftProgram,cappedShiftCleanupStmt,resetShiftControls,mapLabelStmt,
          countdownMultiLeft,lensMultiPhaseLeft,lensRenameStmt,
          sparseCountdownProgram,countdownExit,countdownOnExit,
          FullInterpreterState.dispatchLens,FullInterpreterState.macroLens,
          FullInterpreterState.moveLens,FullInterpreterState.shiftLens,
          FullInterpreterState.countdownLens,
          InterpreterMacroState.dispatchLens,InterpreterMacroState.moveLens,
          StateLens.comp]
  · exact conditionalZeroPhaseProgram_preservesDispatch o returnLabel right hright

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

theorem operandBoundaryBase_coreStacks_withMemory (w value:Nat)
    (m:SparseMemory) (s:SparseState):
    operandBoundaryBase w value m (coreStacks w s) =
      coreStacks w {s with acc:=value,mem:=m}:=by
  funext k
  cases k <;> rfl

theorem transport_finiteLocal_cfg_to_fetch_selective
    {p:Program} {N n:Nat} {L:Type} [Fintype L]
    (encode:L→ FiniteInterpreterLabel p N) (next:BoundedPC p)
    (program:L→ TM2.Stmt (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N))
    (target:FiniteInterpreterLabel p N→ TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N))
    (hnonhalt:∀ label,program label ≠ .halt→
      target (encode label)=mapLabelStmt encode (program label))
    {c d:TM2.Cfg (fun _:CoreStack => SparseSymbol) L
      (FullInterpreterState N)}
    (hrun:((fun x => x.bind (TM2.step program))^[n]) (some c)=some d)
    (hd:d.l.isSome) (hhalt:program (d.l.get hd)=.halt)
    (hfinal:target (encode (d.l.get hd))=.goto (fun _ => .fetch next)):
    ((fun x => x.bind (TM2.step target))^[n + 1])
      (some (finiteEmbedCfg encode c)) =
      some (finiteInterpreterCfg (.fetch next) d.var d.stk):=by
  have htransport:=iterate_mapLabelProgram_until_exit program target encode
    hnonhalt hrun hd
  have hembed:finiteEmbedCfg encode d =
      finiteInterpreterCfg (encode (d.l.get hd)) d.var d.stk:=by
    rcases d with ⟨label,state,tapes⟩
    cases label with
    | none => simp at hd
    | some label => rfl
  have htransport':
      ((fun x => x.bind (TM2.step target))^[n])
        (some (finiteEmbedCfg encode c)) =
      some (finiteInterpreterCfg (encode (d.l.get hd)) d.var d.stk):=by
    exact htransport.trans (congrArg some hembed)
  have hexit:
      ((fun x => x.bind (TM2.step target))^[1])
        (some (finiteInterpreterCfg (encode (d.l.get hd)) d.var d.stk)) =
      some (finiteInterpreterCfg (.fetch next) d.var d.stk):=by
    simp [hfinal,finiteInterpreterCfg,TM2.step]
  exact chain_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N)) =>
      x.bind (TM2.step target)) htransport' hexit

theorem loadInstructionProgram_preservesDispatch {N:Nat} {R:Type}
    (o:Op) (returnLabel:R):
    ProgramPreservesDispatch
      (loadInstructionProgram (N:=N) o returnLabel (fun _ => .halt)):=by
  exact operandEvalProgram_preservesDispatch o _ _
    (loadInstructionTailProgram_preservesDispatch returnLabel)

theorem addInstructionProgram_preservesDispatch {N:Nat} {R:Type}
    (o:Op) (returnLabel:R):
    ProgramPreservesDispatch
      (addInstructionProgram (N:=N) o returnLabel (fun _ => .halt)):=by
  exact operandEvalProgram_preservesDispatch o _ _
    (addInstructionTailProgram_preservesDispatch returnLabel _
      haltProgram_preservesDispatch)

theorem writeInstructionProgram_preservesDispatch {N:Nat} {R:Type}
    (o:Op) (returnLabel:R):
    ProgramPreservesDispatch
      (writeInstructionProgram (N:=N) o returnLabel (fun _ => .halt)):=by
  exact operandEvalProgram_preservesDispatch o _ _
    (writeTailProgram_preservesDispatch returnLabel _
      haltProgram_preservesDispatch)

theorem storeInstructionProgram_preservesDispatch {N:Nat} {R:Type}
    (address:Nat) (returnLabel:R):
    ProgramPreservesDispatch
      (storeInstructionProgram (N:=N) address returnLabel (fun _ => .halt)):=by
  exact operandEvalProgram_preservesDispatch (.lit address) _ _
    (storeInstructionTailProgram_preservesDispatch returnLabel _
      haltProgram_preservesDispatch)

theorem storeIndInstructionProgram_preservesDispatch {N:Nat} {R:Type}
    (address:Nat) (returnLabel:R):
    ProgramPreservesDispatch
      (storeIndInstructionProgram (N:=N) address returnLabel
        (fun _ => .halt)):=by
  exact operandEvalProgram_preservesDispatch (.mem address) _ _
    (storeInstructionTailProgram_preservesDispatch returnLabel _
      haltProgram_preservesDispatch)

theorem readInstructionProgram_preservesDispatch {N:Nat} {R:Type}
    (address:Nat) (exhaustedLabel returnLabel:R):
    ProgramPreservesDispatch
      (readInstructionProgram (N:=N) address exhaustedLabel returnLabel
        (fun _ => .halt)):=by
  exact operandEvalProgram_preservesDispatch (.lit address) _ _
    (readTransferProgram_preservesDispatch exhaustedLabel returnLabel _
      haltProgram_preservesDispatch)

theorem subtractInstructionProgram_preservesDispatch {N:Nat} {R:Type}
    (o:Op) (returnLabel:R):
    ProgramPreservesDispatch
      (subtractInstructionProgram (N:=N) o returnLabel (fun _ => .halt)):=by
  exact operandEvalProgram_preservesDispatch o _ _
    (subtractInstructionTailProgram_preservesDispatch o returnLabel _
      haltProgram_preservesDispatch)

theorem bitwiseInstructionProgram_preservesDispatch {N:Nat} {R:Type}
    (kind:BitwiseKind) (o:Op) (returnLabel:R):
    ProgramPreservesDispatch
      (bitwiseInstructionProgram (N:=N) kind o returnLabel
        (fun _ => .halt)):=by
  exact operandEvalProgram_preservesDispatch o _ _
    (zipInstructionTailProgram_preservesDispatch kind.boolFn returnLabel _
      haltProgram_preservesDispatch)

theorem shiftInstructionProgram_preservesDispatch {N:Nat} {R:Type}
    (rightShift:Bool) (o:Op) (returnLabel:R):
    ProgramPreservesDispatch
      (shiftInstructionProgram (N:=N) o rightShift returnLabel
        (fun _ => .halt)):=by
  exact operandEvalProgram_preservesDispatch o _ _
    (fullShiftProgram_preservesDispatch o rightShift returnLabel _
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

theorem finite_load_to_fetch {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (pc:BoundedPC p)
    (o:BoundedOp N) (w:Nat) (s:SparseState) (hm:s.mem.Normalized w)
    (state:FullInterpreterState N):
    ∃ steps,steps <= loadInstructionBound w s.mem + 1∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeLoadLabel pc o)
          (operandEvalStartCfg
            (R:=LoadInstructionTailLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc:=operandWordValue w o.toOp s.mem})):=by
  let haltRight:BoundedPC p -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N):=fun _ => .halt
  rcases loadInstruction_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc s.mem hm
      (coreStacks w s) state with
    ⟨steps,hsteps,finalState,hrun⟩
  let finalCfg:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (LoadInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N):=
    embedOperandReturnCfg o.toOp
    (mapLabelCfg (fun l:FullLoadLabel (BoundedPC p) => Sum.inr l)
      (mapLabelCfg (fun l:FullLoadFinishLabel (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l:BoundedPC p => Sum.inr l)
          (cleanReturnCfg (nextPC p pc) finalState
            (operandBoundaryBase w (operandWordValue w o.toOp s.mem)
              s.mem (coreStacks w s))))))
  have hfinal:finalCfg.l.isSome:=by
    cases o <;> rfl
  have hhalt:
      loadInstructionProgram o.toOp (nextPC p pc) haltRight
        (finalCfg.l.get hfinal)=.halt:=by
    cases o <;> rfl
  have hglobal:=transport_finiteLocal_cfg_to_fetch
    (encodeLoadLabel pc o) (nextPC p pc)
    (loadInstructionProgram o.toOp (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label; simp [finiteInterpreterProgram,encodeLoadLabel,haltRight])
    (d:=finalCfg) hrun hfinal hhalt
  have hpres:=iterate_preservesDispatch
    (loadInstructionProgram o.toOp (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      loadInstructionProgram_preservesDispatch (N:=N) o.toOp (nextPC p pc))
    _ finalCfg hrun
  have hdispatch:FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state:=by
    cases o <;>
      simpa [finalCfg,operandEvalStartCfg,literalOperandStartCfg,
        lensRenamedCfg,FullInterpreterState.dispatchLens,
        FullInterpreterState.literalLens,FullInterpreterState.macroLens,
        InterpreterMacroState.dispatchLens,StateLens.comp]
        using! hpres
  refine ⟨steps + 1,by omega,finalState,hdispatch, ?_⟩
  cases o <;>
    simpa [finalCfg,operandBoundaryBase_coreStacks,
      Function.iterate_succ_apply,embedOperandReturnCfg,
      embedDirectReturnCfg,embedIndirectReturnCfg,
      embedIndirectTransferReturnCfg,embedDirectTailReturnCfg]
      using! hglobal

theorem finite_load_instruction {p:Program} {N pc w:Nat}
    (hbound:programArgumentBound p <= N) (o:Op)
    (hfetch:p[pc]?=some (.load o))
    (s:SparseState) (hm:s.mem.Normalized w)
    (state:FullInterpreterState N):
    let harg:operandArgument o <= N:=
      (instrArgument_le_programArgumentBound hfetch).trans hbound
    let bo:=BoundedOp.ofOp o harg
    ∃ steps,steps <= loadInstructionBound w s.mem + 3∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc:=operandWordValue w o s.mem})):=by
  dsimp only
  let harg:operandArgument o <= N:=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo:=BoundedOp.ofOp o harg
  have hfetchStep:=finite_step_fetch_data hbound hfetch (by simp) (by simp)
    state (coreStacks w s)
  have hfetchIter:
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[1])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg
        (.control (.data (boundPC p pc) .load)) state (coreStacks w s)):=by
    simpa using! hfetchStep
  have hentryStep:=finite_step_load_entry hbound (boundPC p pc) o
    (by simpa [fetch_boundPC] using hfetch) state (coreStacks w s)
  have hstartEq:
      finiteEmbedCfg (encodeLoadLabel (boundPC p pc) bo)
        (operandEvalStartCfg
          (R:=LoadInstructionTailLabel (BoundedPC p)) bo.toOp
          bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s)) =
      finiteInterpreterCfg
        (encodeLoadLabel (boundPC p pc) bo
          (by simpa [bo] using operandEvalStartLabel o))
        (FullInterpreterState.literalLens.put state
          (BoundedLiteralControl.initial harg)) (coreStacks w s):=by
    rw [operandEvalStartCfg_coreStacks]
    cases o <;> rfl
  have hentryIter:
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[1])
        (some (finiteInterpreterCfg
          (.control (.data (boundPC p pc) .load)) state (coreStacks w s))) =
      some (finiteEmbedCfg (encodeLoadLabel (boundPC p pc) bo)
        (operandEvalStartCfg
          (R:=LoadInstructionTailLabel (BoundedPC p)) bo.toOp
          bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))):=by
    rw [hstartEq]
    simpa using hentryStep
  rcases finite_load_to_fetch hbound (boundPC p pc) bo w s hm state with
    ⟨localSteps,hlocalBound,finalState,hdispatch,hlocal⟩
  have hprefix:=chain_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N)) =>
      x.bind (TM2.step (finiteInterpreterProgram p N hbound)))
    hfetchIter hentryIter
  have hall:=chain_iterations
    (fun x:Option (TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (FiniteInterpreterLabel p N) (FullInterpreterState N)) =>
      x.bind (TM2.step (finiteInterpreterProgram p N hbound)))
    hprefix hlocal
  refine ⟨2 + localSteps,by omega,finalState,hdispatch, ?_⟩
  simpa [bo] using hall

theorem finite_add_to_fetch {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (pc:BoundedPC p)
    (o:BoundedOp N) (w:Nat) (s:SparseState) (hm:s.mem.Normalized w)
    (state:FullInterpreterState N):
    ∃ steps,steps <= addInstructionBound w s.mem + 1∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeAddLabel pc o)
          (operandEvalStartCfg
            (R:=AddInstructionTailLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc:=
          (s.acc + operandWordValue w o.toOp s.mem) % 2 ^ w})):=by
  let haltRight:BoundedPC p -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N):=fun _ => .halt
  rcases addInstruction_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc s.mem hm
      (coreStacks w s) state with
    ⟨steps,hsteps,finalState,hrun⟩
  let finalCfg:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (AddInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N):=
    embedOperandReturnCfg o.toOp
      (mapLabelCfg (fun l:FullAddPhaseLabel (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l:BoundedPC p => Sum.inr l)
          (cleanReturnCfg (nextPC p pc) finalState
            (operandBoundaryBase w
              ((s.acc + operandWordValue w o.toOp s.mem) % 2 ^ w)
              s.mem (coreStacks w s)))))
  have hfinal:finalCfg.l.isSome:=by cases o <;> rfl
  have hhalt:addInstructionProgram o.toOp (nextPC p pc) haltRight
      (finalCfg.l.get hfinal)=.halt:=by cases o <;> rfl
  have hglobal:=transport_finiteLocal_cfg_to_fetch
    (encodeAddLabel pc o) (nextPC p pc)
    (addInstructionProgram o.toOp (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label; simp [finiteInterpreterProgram,encodeAddLabel,haltRight])
    (d:=finalCfg) hrun hfinal hhalt
  have hpres:=iterate_preservesDispatch
    (addInstructionProgram o.toOp (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      addInstructionProgram_preservesDispatch (N:=N) o.toOp (nextPC p pc))
    _ finalCfg hrun
  have hdispatch:FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state:=by
    cases o <;>
      simpa [finalCfg,operandEvalStartCfg,literalOperandStartCfg,
        lensRenamedCfg,FullInterpreterState.dispatchLens,
        FullInterpreterState.literalLens,FullInterpreterState.macroLens,
        InterpreterMacroState.dispatchLens,StateLens.comp] using! hpres
  refine ⟨steps + 1,by omega,finalState,hdispatch, ?_⟩
  cases o <;>
    simpa [finalCfg,operandBoundaryBase_coreStacks,
      Function.iterate_succ_apply,embedOperandReturnCfg,
      embedDirectReturnCfg,embedIndirectReturnCfg,
      embedIndirectTransferReturnCfg,embedDirectTailReturnCfg]
      using! hglobal

set_option maxHeartbeats 1000000 in
theorem finite_add_instruction {p:Program} {N pc w:Nat}
    (hbound:programArgumentBound p <= N) (o:Op)
    (hfetch:p[pc]?=some (.add o))
    (s:SparseState) (hm:s.mem.Normalized w)
    (state:FullInterpreterState N):
    ∃ steps,steps <= addInstructionBound w s.mem + 3∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc:=
          (s.acc + sparseValue w o s.mem) % 2 ^ w})):=by
  let harg:operandArgument o <= N:=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo:=BoundedOp.ofOp o harg
  let localCfg:=finiteEmbedCfg (encodeAddLabel (boundPC p pc) bo)
    (operandEvalStartCfg
      (R:=AddInstructionTailLabel (BoundedPC p)) bo.toOp
      bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))
  have hprepare:=finite_step_prepare_entry hbound (boundPC p pc) (.add o)
    .add (by simpa [fetch_boundPC] using hfetch) rfl state (coreStacks w s)
  have hentry:TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .add))
        state (coreStacks w s))=some localCfg:=by
    rw [hprepare]
    simp [finitePrepareInstr,finiteInitializeEntry,instrArgument,
      localCfg,operandEvalStartCfg_coreStacks,finiteEmbedCfg,
      mapLabelCfg,finiteInterpreterCfg]
    cases o <;> simp [bo,BoundedOp.ofOp] <;> constructor <;> congr
  rcases finite_add_to_fetch hbound (boundPC p pc) bo w s hm state with
    ⟨localSteps,hlocalBound,finalState,hdispatch,hlocal⟩
  have hall:=finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with acc:=
        (s.acc + operandWordValue w bo.toOp s.mem) % 2 ^ w}))
    hentry hlocal
  refine ⟨2 + localSteps,by omega,finalState,hdispatch, ?_⟩
  simpa [bo,sparseValue,operandWordValue] using hall

theorem finite_bitwise_to_fetch {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (pc:BoundedPC p)
    (kind:BitwiseKind) (o:BoundedOp N) (w:Nat) (s:SparseState)
    (hm:s.mem.Normalized w) (state:FullInterpreterState N):
    ∃ steps,steps <= zipInstructionBound w s.mem + 1∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeBitwiseLabel pc kind o)
          (operandEvalStartCfg
            (R:=ZipInstructionTailLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc:=
          (kind.natFn w s.acc (operandWordValue w o.toOp s.mem) % 2 ^ w)})):=by
  let haltRight:BoundedPC p -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N):=fun _ => .halt
  rcases bitwiseInstruction_correct kind o.toOp o.operandArgument_toOp
      w s.acc s.mem hm (nextPC p pc) haltRight
      (coreStacks w s) state with
    ⟨steps,hsteps,finalState,hrun⟩
  let finalCfg:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (ZipInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N):=
    embedOperandReturnCfg o.toOp
      (mapLabelCfg (fun l:FullZipPhaseLabel (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l:BoundedPC p => Sum.inr l)
          (cleanReturnCfg (nextPC p pc) finalState
            (operandBoundaryBase w
              (kind.natFn w s.acc (operandWordValue w o.toOp s.mem) % 2 ^ w)
              s.mem (coreStacks w s)))))
  have hfinal:finalCfg.l.isSome:=by cases o <;> rfl
  have hhalt:bitwiseInstructionProgram kind o.toOp (nextPC p pc) haltRight
      (finalCfg.l.get hfinal)=.halt:=by cases o <;> rfl
  have hglobal:=transport_finiteLocal_cfg_to_fetch
    (encodeBitwiseLabel pc kind o) (nextPC p pc)
    (bitwiseInstructionProgram kind o.toOp (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label
        simp [finiteInterpreterProgram,encodeBitwiseLabel,haltRight])
    (d:=finalCfg) hrun hfinal hhalt
  have hpres:=iterate_preservesDispatch
    (bitwiseInstructionProgram kind o.toOp (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (bitwiseInstructionProgram_preservesDispatch
        (N:=N) kind o.toOp (nextPC p pc))) _ finalCfg hrun
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
      embedIndirectTransferReturnCfg,embedDirectTailReturnCfg]
      using! hglobal

theorem finite_sub_to_fetch {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (pc:BoundedPC p)
    (o:BoundedOp N) (w:Nat) (s:SparseState) (hacc:s.acc < 2 ^ w)
    (hm:s.mem.Normalized w) (state:FullInterpreterState N):
    ∃ steps,steps <= subtractInstructionBound w s.mem + 1∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeSubLabel pc o)
          (operandEvalStartCfg
            (R:=SubtractInstructionTailLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc:=s.acc - sparseValue w o.toOp s.mem})):=by
  let haltRight:BoundedPC p -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N):=fun _ => .halt
  rcases subtractInstruction_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc hacc s.mem hm
      (coreStacks w s) state with
    ⟨steps,hsteps,finalState,hrun⟩
  let finalCfg:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (SubtractInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N):=
    embedOperandReturnCfg o.toOp
      (mapLabelCfg (fun l:FullSubtractLabel (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l:FullSubtractTailLabel (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l:SubtractInstallPhaseLabel (BoundedPC p) => Sum.inr l)
            (mapLabelCfg (fun l:BoundedPC p => Sum.inr l)
              (cleanReturnCfg (nextPC p pc) finalState
                (operandBoundaryBase w (s.acc - sparseValue w o.toOp s.mem)
                  s.mem (coreStacks w s)))))))
  have hfinal:finalCfg.l.isSome:=by cases o <;> rfl
  have hhalt:subtractInstructionProgram o.toOp (nextPC p pc) haltRight
      (finalCfg.l.get hfinal)=.halt:=by cases o <;> rfl
  have hglobal:=transport_finiteLocal_cfg_to_fetch
    (encodeSubLabel pc o) (nextPC p pc)
    (subtractInstructionProgram o.toOp (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label; simp [finiteInterpreterProgram,encodeSubLabel,haltRight])
    (d:=finalCfg) hrun hfinal hhalt
  have hpres:=iterate_preservesDispatch
    (subtractInstructionProgram o.toOp (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (subtractInstructionProgram_preservesDispatch
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
      embedIndirectTransferReturnCfg,embedDirectTailReturnCfg]
      using! hglobal

set_option maxHeartbeats 1000000 in
theorem finite_shiftLeft_to_fetch {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (pc:BoundedPC p)
    (o:BoundedOp N) (w:Nat) (hw:0 < w) (s:SparseState)
    (hacc:s.acc < 2 ^ w) (hm:s.mem.Normalized w)
    (state:FullInterpreterState N):
    ∃ steps,steps <= shiftInstructionBound w s.mem + 1∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeShiftLabel pc false o)
          (operandEvalStartCfg
            (R:=FullShiftLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc:=
          (s.acc * 2 ^ sparseValue w o.toOp s.mem) % 2 ^ w})):=by
  let haltRight:BoundedPC p -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N):=fun _ => .halt
  rcases shiftLeftInstruction_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc hw hacc s.mem hm
      (coreStacks w s) state with
    ⟨steps,hsteps,finalState,hrun⟩
  let finalCfg:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (ShiftInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N):=
    embedOperandReturnCfg o.toOp
      (mapLabelCfg Sum.inr
        (mapLabelCfg (fun l:ConditionalZeroTailLabel (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l:BoundedPC p => Sum.inr l)
            (cleanReturnCfg (nextPC p pc) finalState
              (operandBoundaryBase w
                (s.acc * 2 ^ sparseValue w o.toOp s.mem % 2 ^ w)
                s.mem (coreStacks w s))))))
  have hfinal:finalCfg.l.isSome:=by cases o <;> rfl
  have hhalt:shiftInstructionProgram o.toOp false (nextPC p pc) haltRight
      (finalCfg.l.get hfinal)=.halt:=by cases o <;> rfl
  have hglobal:=transport_finiteLocal_cfg_to_fetch
    (encodeShiftLabel pc false o) (nextPC p pc)
    (shiftInstructionProgram o.toOp false (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label
        simp [finiteInterpreterProgram,encodeShiftLabel,haltRight])
    (d:=finalCfg) hrun hfinal hhalt
  have hpres:=iterate_preservesDispatch
    (shiftInstructionProgram o.toOp false (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (shiftInstructionProgram_preservesDispatch
        (N:=N) false o.toOp (nextPC p pc))) _ finalCfg hrun
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
      embedIndirectTransferReturnCfg,embedDirectTailReturnCfg]
      using! hglobal

set_option maxHeartbeats 1000000 in
theorem finite_shiftRight_to_fetch {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (pc:BoundedPC p)
    (o:BoundedOp N) (w:Nat) (hw:0 < w) (s:SparseState)
    (hacc:s.acc < 2 ^ w) (hm:s.mem.Normalized w)
    (state:FullInterpreterState N):
    ∃ steps,steps <= shiftInstructionBound w s.mem + 1∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeShiftLabel pc true o)
          (operandEvalStartCfg
            (R:=FullShiftLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with acc:=
          (s.acc / 2 ^ sparseValue w o.toOp s.mem) % 2 ^ w})):=by
  let haltRight:BoundedPC p -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N):=fun _ => .halt
  rcases shiftRightInstruction_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc hw hacc s.mem hm
      (coreStacks w s) state with
    ⟨steps,hsteps,finalState,hrun⟩
  let finalCfg:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (ShiftInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N):=
    embedOperandReturnCfg o.toOp
      (mapLabelCfg Sum.inr
        (mapLabelCfg (fun l:ConditionalZeroTailLabel (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l:BoundedPC p => Sum.inr l)
            (cleanReturnCfg (nextPC p pc) finalState
              (operandBoundaryBase w
                (s.acc / 2 ^ sparseValue w o.toOp s.mem % 2 ^ w)
                s.mem (coreStacks w s))))))
  have hfinal:finalCfg.l.isSome:=by cases o <;> rfl
  have hhalt:shiftInstructionProgram o.toOp true (nextPC p pc) haltRight
      (finalCfg.l.get hfinal)=.halt:=by cases o <;> rfl
  have hglobal:=transport_finiteLocal_cfg_to_fetch
    (encodeShiftLabel pc true o) (nextPC p pc)
    (shiftInstructionProgram o.toOp true (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label
        simp [finiteInterpreterProgram,encodeShiftLabel,haltRight])
    (d:=finalCfg) hrun hfinal hhalt
  have hpres:=iterate_preservesDispatch
    (shiftInstructionProgram o.toOp true (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (shiftInstructionProgram_preservesDispatch
        (N:=N) true o.toOp (nextPC p pc))) _ finalCfg hrun
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
      embedIndirectTransferReturnCfg,embedDirectTailReturnCfg]
      using! hglobal

set_option maxHeartbeats 1000000 in
theorem finite_write_to_fetch {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (pc:BoundedPC p)
    (o:BoundedOp N) (w:Nat) (s:SparseState) (hm:s.mem.Normalized w)
    (state:FullInterpreterState N):
    ∃ steps,steps <= writeInstructionBound w s.mem + 1∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeWriteLabel pc o)
          (operandEvalStartCfg
            (R:=WriteTailLabel (BoundedPC p)) o.toOp
            o.operandArgument_toOp w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with out:=
          s.out ++ [operandWordValue w o.toOp s.mem]})):=by
  let haltRight:BoundedPC p -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N):=fun _ => .halt
  rcases writeInstruction_correct o.toOp o.operandArgument_toOp
      (nextPC p pc) haltRight w s.acc s.mem hm
      (coreStacks w s) state with
    ⟨steps,hsteps,finalState,hrun⟩
  let finalCfg:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (WriteInstructionLabel o.toOp (BoundedPC p)) (FullInterpreterState N):=
    embedOperandReturnCfg o.toOp
      (mapLabelCfg (fun l:WriteMove1Label (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l:WriteMove2Label (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l:WriteAfterLabel (BoundedPC p) => Sum.inr l)
            (mapLabelCfg (fun l:BoundedPC p => Sum.inr l)
              (cleanReturnCfg (nextPC p pc) finalState
                (writeResultBase w s.acc (operandWordValue w o.toOp s.mem)
                  s.mem (coreStacks w s)))))))
  have hfinal:finalCfg.l.isSome:=by cases o <;> rfl
  have hhalt:writeInstructionProgram o.toOp (nextPC p pc) haltRight
      (finalCfg.l.get hfinal)=.halt:=by cases o <;> rfl
  have hglobal:=transport_finiteLocal_cfg_to_fetch
    (encodeWriteLabel pc o) (nextPC p pc)
    (writeInstructionProgram o.toOp (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label; simp [finiteInterpreterProgram,encodeWriteLabel,haltRight])
    (d:=finalCfg) hrun hfinal hhalt
  have hpres:=iterate_preservesDispatch
    (writeInstructionProgram o.toOp (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (writeInstructionProgram_preservesDispatch
        (N:=N) o.toOp (nextPC p pc))) _ finalCfg hrun
  have hdispatch:FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state:=by
    cases o <;> simpa [finalCfg,operandEvalStartCfg,literalOperandStartCfg,
      lensRenamedCfg,FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens,FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens,StateLens.comp] using! hpres
  refine ⟨steps + 1,by omega,finalState,hdispatch, ?_⟩
  cases o <;>
    simpa [finalCfg,writeResultBase_coreStacks,
      Function.iterate_succ_apply,embedOperandReturnCfg,
      embedDirectReturnCfg,embedIndirectReturnCfg,
      embedIndirectTransferReturnCfg,embedDirectTailReturnCfg]
      using! hglobal

set_option maxHeartbeats 1000000 in
theorem finite_store_to_fetch {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (pc:BoundedPC p)
    (address:Fin (N + 1)) (w:Nat) (s:SparseState)
    (hm:s.mem.Normalized w) (state:FullInterpreterState N):
    ∃ steps,steps <= storeInstructionBound w s.mem + 1∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeStoreLabel pc address)
          (operandEvalStartCfg
            (R:=StoreInstructionTailLabel (BoundedPC p)) (.lit address.val)
            (Nat.le_of_lt_succ address.isLt) w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with mem:=
          (s.mem.write w address.val s.acc)})):=by
  let haltRight:BoundedPC p -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N):=fun _ => .halt
  have haddress:address.val <= N:=by omega
  rcases storeInstruction_correct address.val haddress
      (nextPC p pc) haltRight w s.acc s.mem hm
      (coreStacks w s) state with
    ⟨steps,hsteps,finalState,hrun⟩
  let finalCfg:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (StoreInstructionLabel address.val (BoundedPC p))
      (FullInterpreterState N):=
    embedOperandReturnCfg (.lit address.val)
      (mapLabelCfg (fun l:FullStoreLabel (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l:StorePrependTailLabel (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l:FullPrependLabel (BoundedPC p) => Sum.inr l)
            (mapLabelCfg (fun l:BoundedPC p => Sum.inr l)
              (cleanReturnCfg (nextPC p pc) finalState
                (operandBoundaryBase w s.acc
                  (s.mem.write w address.val s.acc) (coreStacks w s)))))))
  have hfinal:finalCfg.l.isSome:=by rfl
  have hhalt:storeInstructionProgram address.val (nextPC p pc) haltRight
      (finalCfg.l.get hfinal)=.halt:=by rfl
  have hglobal:=transport_finiteLocal_cfg_to_fetch
    (encodeStoreLabel pc address) (nextPC p pc)
    (storeInstructionProgram address.val (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label; simp [finiteInterpreterProgram,encodeStoreLabel,haltRight])
    (d:=finalCfg) hrun hfinal hhalt
  have hpres:=iterate_preservesDispatch
    (storeInstructionProgram address.val (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (storeInstructionProgram_preservesDispatch
        (N:=N) address.val (nextPC p pc))) _ finalCfg hrun
  have hdispatch:FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state:=by
    simpa [finalCfg,operandEvalStartCfg,literalOperandStartCfg,
      lensRenamedCfg,FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens,FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens,StateLens.comp] using! hpres
  refine ⟨steps + 1,by omega,finalState,hdispatch, ?_⟩
  simpa [finalCfg,operandBoundaryBase_coreStacks_withMemory,
    Function.iterate_succ_apply,embedOperandReturnCfg]
    using! hglobal

set_option maxHeartbeats 1000000 in
theorem finite_storeInd_to_fetch {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (pc:BoundedPC p)
    (address:Fin (N + 1)) (w:Nat) (s:SparseState)
    (hm:s.mem.Normalized w) (state:FullInterpreterState N):
    ∃ steps,steps <= storeIndInstructionBound w s.mem + 1∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeStoreIndLabel pc address)
          (operandEvalStartCfg
            (R:=StoreInstructionTailLabel (BoundedPC p)) (.mem address.val)
            (Nat.le_of_lt_succ address.isLt) w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with mem:=(s.mem.write w
          (s.mem.read (address.val % 2 ^ w)) s.acc)})):=by
  let haltRight:BoundedPC p -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) (BoundedPC p)
      (FullInterpreterState N):=fun _ => .halt
  have haddress:address.val <= N:=by omega
  rcases storeIndInstruction_correct address.val haddress
      (nextPC p pc) haltRight w s.acc s.mem hm
      (coreStacks w s) state with
    ⟨steps,hsteps,finalState,hrun⟩
  let finalCfg:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (StoreIndInstructionLabel address.val (BoundedPC p))
      (FullInterpreterState N):=
    embedOperandReturnCfg (.mem address.val)
      (mapLabelCfg (fun l:FullStoreLabel (BoundedPC p) => Sum.inr l)
        (mapLabelCfg (fun l:StorePrependTailLabel (BoundedPC p) => Sum.inr l)
          (mapLabelCfg (fun l:FullPrependLabel (BoundedPC p) => Sum.inr l)
            (mapLabelCfg (fun l:BoundedPC p => Sum.inr l)
              (cleanReturnCfg (nextPC p pc) finalState
                (operandBoundaryBase w s.acc
                  (s.mem.write w (s.mem.read (address.val % 2 ^ w)) s.acc)
                  (coreStacks w s)))))))
  have hfinal:finalCfg.l.isSome:=by rfl
  have hhalt:storeIndInstructionProgram address.val (nextPC p pc) haltRight
      (finalCfg.l.get hfinal)=.halt:=by rfl
  have hglobal:=transport_finiteLocal_cfg_to_fetch
    (encodeStoreIndLabel pc address) (nextPC p pc)
    (storeIndInstructionProgram address.val (nextPC p pc) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by intro label
        simp [finiteInterpreterProgram,encodeStoreIndLabel,haltRight])
    (d:=finalCfg) hrun hfinal hhalt
  have hpres:=iterate_preservesDispatch
    (storeIndInstructionProgram address.val (nextPC p pc) haltRight)
    (by simpa [haltRight] using
      (storeIndInstructionProgram_preservesDispatch
        (N:=N) address.val (nextPC p pc))) _ finalCfg hrun
  have hdispatch:FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state:=by
    simpa [finalCfg,operandEvalStartCfg,literalOperandStartCfg,
      lensRenamedCfg,FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens,FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens,StateLens.comp] using! hpres
  refine ⟨steps + 1,by omega,finalState,hdispatch, ?_⟩
  simpa [finalCfg,operandBoundaryBase_coreStacks_withMemory,
    Function.iterate_succ_apply,embedOperandReturnCfg,
    embedDirectReturnCfg]
    using! hglobal

set_option maxHeartbeats 1000000 in
theorem finite_read_to_fetch {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N) (pc:BoundedPC p)
    (address:Fin (N + 1)) (w value:Nat) (inputTail:List Nat)
    (s:SparseState) (hinp:s.inp=value::inputTail)
    (hm:s.mem.Normalized w) (state:FullInterpreterState N):
    ∃ steps,steps <= readInstructionBound w s.mem + 1∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteEmbedCfg (encodeReadLabel pc address)
          (operandEvalStartCfg
            (R:=ReadTailLabel (Sum (BoundedPC p) Unit)) (.lit address.val)
            (Nat.le_of_lt_succ address.isLt) w s.acc s.mem state (coreStacks w s)))) =
      some (finiteInterpreterCfg (.fetch (nextPC p pc)) finalState
        (coreStacks w {s with
          mem:=s.mem.write w address.val value,
          inp:=inputTail})):=by
  let R:=Sum (BoundedPC p) Unit
  let haltRight:R -> TM2.Stmt
      (fun _:CoreStack => SparseSymbol) R
      (FullInterpreterState N):=fun _ => .halt
  have haddress:address.val <= N:=by omega
  have hinput:(coreStacks w s) .input =
      encodeFixedWord w value ++ encodeInputStack w inputTail:=by
    simp [coreStacks,encodeInputStack,encodeWordList,hinp,
      encodeFixedWord,List.append_assoc]
  rcases readInstruction_correct address.val haddress
      (Sum.inr ()) (Sum.inl (nextPC p pc)) haltRight
      w s.acc value (encodeInputStack w inputTail)
      s.mem hm (coreStacks w s) hinput state with
    ⟨steps,hsteps,finalState,hrun⟩
  let finalCfg:TM2.Cfg (fun _:CoreStack => SparseSymbol)
      (ReadInstructionLabel address.val R)
      (FullInterpreterState N):=
    embedOperandReturnCfg (.lit address.val)
      (mapLabelCfg Sum.inr (mapLabelCfg Sum.inr
        (cleanReturnCfg (Sum.inl (nextPC p pc)) finalState
          (prependResultStacks w address.val value s.mem
            (readTransferStacks (encodeInputStack w inputTail)
              ((fixedBits w value).reverse.map SparseSymbol.bit)
              (operandResultBase w s.acc
                (operandWordValue w (.lit address.val) s.mem)
                s.mem (coreStacks w s)))))))
  have hfinal:finalCfg.l.isSome:=by rfl
  have hhalt:readInstructionProgram address.val (Sum.inr ())
      (Sum.inl (nextPC p pc)) haltRight
      (finalCfg.l.get hfinal)=.halt:=by rfl
  have hglobal:=transport_finiteLocal_cfg_to_fetch_selective
    (encodeReadLabel pc address) (nextPC p pc)
    (readInstructionProgram address.val (Sum.inr ()) (Sum.inl (nextPC p pc)) haltRight)
    (finiteInterpreterProgram p N hbound)
    (by
      intro label hn
      cases label with
      | inl l =>
          simpa [finiteInterpreterProgram,encodeReadLabel] using
            (wrapFiniteLocal_encode_nonhalt (encodeReadLabel pc address)
              (nextPC p pc)
              (readInstructionProgram address.val (Sum.inr ())
                (Sum.inl (nextPC p pc)) haltRight) (Sum.inl l) hn)
      | inr l =>
          cases l with
          | inl l =>
              simpa [finiteInterpreterProgram,encodeReadLabel] using
                (wrapFiniteLocal_encode_nonhalt (encodeReadLabel pc address)
                  (nextPC p pc)
                  (readInstructionProgram address.val (Sum.inr ())
                    (Sum.inl (nextPC p pc)) haltRight)
                  (Sum.inr (Sum.inl l)) hn)
          | inr l =>
              cases l with
              | inl l =>
                  simpa [finiteInterpreterProgram,encodeReadLabel] using
                    (wrapFiniteLocal_encode_nonhalt (encodeReadLabel pc address)
                      (nextPC p pc)
                      (readInstructionProgram address.val (Sum.inr ())
                        (Sum.inl (nextPC p pc)) haltRight)
                      (Sum.inr (Sum.inr (Sum.inl l))) hn)
              | inr l =>
                  cases l with
                  | inl returnPC =>
                      simpa [finiteInterpreterProgram,encodeReadLabel] using
                        (wrapFiniteLocal_encode_nonhalt (encodeReadLabel pc address)
                          (nextPC p pc)
                          (readInstructionProgram address.val (Sum.inr ())
                            (Sum.inl (nextPC p pc)) haltRight)
                          (Sum.inr (Sum.inr (Sum.inr (Sum.inl returnPC)))) hn)
                  | inr u =>
                      cases u
                      exact False.elim (hn rfl))
    (d:=finalCfg) hrun hfinal hhalt
    (by
      have hlabel:finalCfg.l.get hfinal =
          Sum.inr (Sum.inr (Sum.inr (Sum.inl (nextPC p pc)))):=by rfl
      rw [hlabel]
      simp [finiteInterpreterProgram,encodeReadLabel,wrapFiniteLocal,
        readInstructionProgram,haltRight,stmtIsHalt]
      intro hnonhalt
      change stmtIsHalt
        (readInstructionProgram address.val (Sum.inr ())
          (Sum.inl (nextPC p pc)) haltRight
          (finalCfg.l.get hfinal))=false at hnonhalt
      rw [hhalt] at hnonhalt
      simp [stmtIsHalt] at hnonhalt)
  have hpres:=iterate_preservesDispatch
    (readInstructionProgram address.val (Sum.inr ()) (Sum.inl (nextPC p pc)) haltRight)
    (by simpa [haltRight] using
      (readInstructionProgram_preservesDispatch
        (N:=N) address.val (Sum.inr ()) (Sum.inl (nextPC p pc)))) _ finalCfg hrun
  have hdispatch:FullInterpreterState.dispatchLens.get finalState =
      FullInterpreterState.dispatchLens.get state:=by
    simpa [finalCfg,operandEvalStartCfg,literalOperandStartCfg,
      lensRenamedCfg,FullInterpreterState.dispatchLens,
      FullInterpreterState.literalLens,FullInterpreterState.macroLens,
      InterpreterMacroState.dispatchLens,StateLens.comp] using! hpres
  refine ⟨steps + 1,by omega,finalState,hdispatch, ?_⟩
  convert hglobal using 1 <;>
    simp [finalCfg,Function.iterate_succ_apply,embedOperandReturnCfg,cleanReturnCfg,
      operandWordValue,sparseValue,Op.value,readResultStacks_coreStacks]
  exact congrArg
    (finiteInterpreterCfg (FiniteInterpreterLabel.fetch (nextPC p pc)) finalState)
    (by simpa [List.map_reverse] using!
      (readResultStacks_coreStacks w address.val value s inputTail).symm)

set_option maxHeartbeats 1000000 in
theorem finite_write_instruction {p:Program} {N pc w:Nat}
    (hbound:programArgumentBound p <= N) (o:Op)
    (hfetch:p[pc]?=some (.write o))
    (s:SparseState) (hm:s.mem.Normalized w)
    (state:FullInterpreterState N):
    ∃ steps,steps <= writeInstructionBound w s.mem + 3∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with out:=
          s.out ++ [sparseValue w o s.mem % 2 ^ w]})):=by
  let harg:operandArgument o <= N:=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo:=BoundedOp.ofOp o harg
  let localCfg:=finiteEmbedCfg (encodeWriteLabel (boundPC p pc) bo)
    (operandEvalStartCfg
      (R:=WriteTailLabel (BoundedPC p)) bo.toOp
      bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))
  have hprepare:=finite_step_prepare_entry hbound (boundPC p pc) (.write o)
    .write (by simpa [fetch_boundPC] using hfetch) rfl state (coreStacks w s)
  have hentry:TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .write))
        state (coreStacks w s))=some localCfg:=by
    rw [hprepare]
    simp [finitePrepareInstr,finiteInitializeEntry,instrArgument,
      localCfg,operandEvalStartCfg_coreStacks,finiteEmbedCfg,
      mapLabelCfg,finiteInterpreterCfg]
    cases o <;> simp [bo,BoundedOp.ofOp] <;> constructor <;> congr
  rcases finite_write_to_fetch hbound (boundPC p pc) bo w s hm state with
    ⟨localSteps,hlocalBound,finalState,hdispatch,hlocal⟩
  have hall:=finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with out:=
        s.out ++ [operandWordValue w bo.toOp s.mem]}))
    hentry hlocal
  refine ⟨2 + localSteps,by omega,finalState,hdispatch, ?_⟩
  simpa [bo,operandWordValue] using hall

set_option maxHeartbeats 1200000 in
theorem finite_sub_instruction {p:Program} {N pc w:Nat}
    (hbound:programArgumentBound p <= N) (o:Op)
    (hfetch:p[pc]?=some (.sub o)) (s:SparseState)
    (hacc:s.acc < 2 ^ w) (hm:s.mem.Normalized w)
    (state:FullInterpreterState N):
    ∃ steps,steps <= subtractInstructionBound w s.mem + 3∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc:=
          (s.acc - sparseValue w o s.mem) % 2 ^ w})):=by
  let harg:operandArgument o <= N:=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo:=BoundedOp.ofOp o harg
  let localCfg:=finiteEmbedCfg (encodeSubLabel (boundPC p pc) bo)
    (operandEvalStartCfg
      (R:=SubtractInstructionTailLabel (BoundedPC p)) bo.toOp
      bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))
  have hprepare:=finite_step_prepare_entry hbound (boundPC p pc) (.sub o)
    .sub (by simpa [fetch_boundPC] using hfetch) rfl state (coreStacks w s)
  have hentry:TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .sub))
        state (coreStacks w s))=some localCfg:=by
    rw [hprepare]
    simp [finitePrepareInstr,finiteInitializeEntry,instrArgument,
      localCfg,operandEvalStartCfg_coreStacks,finiteEmbedCfg,
      mapLabelCfg,finiteInterpreterCfg]
    cases o <;> simp [bo,BoundedOp.ofOp] <;> constructor <;> congr
  rcases finite_sub_to_fetch hbound (boundPC p pc) bo w s hacc hm state with
    ⟨localSteps,hlocalBound,finalState,hdispatch,hlocal⟩
  have hall:=finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with acc:=s.acc - sparseValue w bo.toOp s.mem}))
    hentry hlocal
  refine ⟨2 + localSteps,by omega,finalState,hdispatch, ?_⟩
  have hlt:s.acc - sparseValue w o s.mem < 2 ^ w:=
    lt_of_le_of_lt (Nat.sub_le _ _) hacc
  simpa [bo,Nat.mod_eq_of_lt hlt] using hall

set_option maxHeartbeats 1000000 in
theorem finite_store_instruction {p:Program} {N pc w:Nat}
    (hbound:programArgumentBound p <= N) (address:Nat)
    (hfetch:p[pc]?=some (.store address)) (s:SparseState)
    (hm:s.mem.Normalized w) (state:FullInterpreterState N):
    ∃ steps,steps <= storeInstructionBound w s.mem + 3∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with mem:=(s.mem.write w address s.acc)})):=by
  let harg:address <= N:=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let ba:=boundedAddress address harg
  let localCfg:=finiteEmbedCfg (encodeStoreLabel (boundPC p pc) ba)
    (operandEvalStartCfg
      (R:=StoreInstructionTailLabel (BoundedPC p)) (.lit ba.val)
      (Nat.le_of_lt_succ ba.isLt) w s.acc s.mem state (coreStacks w s))
  have hprepare:=finite_step_prepare_entry hbound (boundPC p pc)
    (.store address) .store (by simpa [fetch_boundPC] using hfetch) rfl
    state (coreStacks w s)
  have hentry:TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .store))
        state (coreStacks w s))=some localCfg:=by
    rw [hprepare]
    simp [finitePrepareInstr,finiteInitializeEntry,instrArgument,
      localCfg,operandEvalStartCfg_coreStacks,finiteEmbedCfg,
      mapLabelCfg,finiteInterpreterCfg,ba,harg,boundedAddress] <;>
      constructor <;> congr
  rcases finite_store_to_fetch hbound (boundPC p pc) ba w s hm state with
    ⟨localSteps,hlocalBound,finalState,hdispatch,hlocal⟩
  have hall:=finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with mem:=s.mem.write w ba.val s.acc}))
    hentry hlocal
  refine ⟨2 + localSteps,by omega,finalState,hdispatch, ?_⟩
  simpa [ba,boundedAddress] using hall

set_option maxHeartbeats 1000000 in
theorem finite_storeInd_instruction {p:Program} {N pc w:Nat}
    (hbound:programArgumentBound p <= N) (address:Nat)
    (hfetch:p[pc]?=some (.storeInd address)) (s:SparseState)
    (hm:s.mem.Normalized w) (state:FullInterpreterState N):
    ∃ steps,steps <= storeIndInstructionBound w s.mem + 3∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with mem:=(s.mem.write w
          (s.mem.read (address % 2 ^ w)) s.acc)})):=by
  let harg:address <= N:=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let ba:=boundedAddress address harg
  let localCfg:=finiteEmbedCfg (encodeStoreIndLabel (boundPC p pc) ba)
    (operandEvalStartCfg
      (R:=StoreInstructionTailLabel (BoundedPC p)) (.mem ba.val)
      (Nat.le_of_lt_succ ba.isLt) w s.acc s.mem state (coreStacks w s))
  have hprepare:=finite_step_prepare_entry hbound (boundPC p pc)
    (.storeInd address) .storeInd (by simpa [fetch_boundPC] using hfetch) rfl
    state (coreStacks w s)
  have hentry:TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.control (.data (boundPC p pc) .storeInd))
        state (coreStacks w s))=some localCfg:=by
    rw [hprepare]
    simp [finitePrepareInstr,finiteInitializeEntry,instrArgument,
      localCfg,operandEvalStartCfg_coreStacks,finiteEmbedCfg,
      mapLabelCfg,finiteInterpreterCfg,ba,harg,boundedAddress] <;>
      constructor <;> congr
  rcases finite_storeInd_to_fetch hbound (boundPC p pc) ba w s hm state with
    ⟨localSteps,hlocalBound,finalState,hdispatch,hlocal⟩
  have hall:=finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with mem:=(s.mem.write w
        (s.mem.read (ba.val % 2 ^ w)) s.acc)}))
    hentry hlocal
  refine ⟨2 + localSteps,by omega,finalState,hdispatch, ?_⟩
  simpa [ba,boundedAddress] using hall

set_option maxHeartbeats 1200000 in
theorem finite_read_instruction {p:Program} {N pc w:Nat}
    (hbound:programArgumentBound p <= N) (address value:Nat)
    (inputTail:List Nat) (hfetch:p[pc]?=some (.read address))
    (s:SparseState) (hinp:s.inp=value::inputTail)
    (hm:s.mem.Normalized w) (state:FullInterpreterState N):
    ∃ steps,steps <= readInstructionBound w s.mem + 3∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with
          mem:=s.mem.write w address value,
          inp:=inputTail})):=by
  let harg:address <= N:=
    (instrArgument_le_programArgumentBound hfetch).trans hbound
  let ba:=boundedAddress address harg
  let localCfg:=finiteEmbedCfg (encodeReadLabel (boundPC p pc) ba)
    (operandEvalStartCfg
      (R:=ReadTailLabel (Sum (BoundedPC p) Unit)) (.lit ba.val)
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
  rcases finite_read_to_fetch hbound (boundPC p pc) ba w value inputTail
      s hinp hm state with
    ⟨localSteps,hlocalBound,finalState,hdispatch,hlocal⟩
  have hall:=finite_data_prefix hbound hfetch (by simp) (by simp)
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with
        mem:=s.mem.write w ba.val value,
        inp:=inputTail}))
    hentry hlocal
  refine ⟨2 + localSteps,by omega,finalState,hdispatch, ?_⟩
  simpa [ba,boundedAddress] using hall

def bitwiseInstr:BitwiseKind -> Op -> Instr
  | .and => .and
  | .or => .or
  | .xor => .xor
  | .compl => .compl

set_option maxHeartbeats 1500000 in
theorem finite_bitwise_instruction {p:Program} {N pc w:Nat}
    (hbound:programArgumentBound p <= N) (kind:BitwiseKind) (o:Op)
    (hfetch:p[pc]?=some (bitwiseInstr kind o))
    (s:SparseState) (hm:s.mem.Normalized w)
    (state:FullInterpreterState N):
    ∃ steps,steps <= zipInstructionBound w s.mem + 3∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc:=
          (kind.natFn w s.acc (sparseValue w o s.mem) % 2 ^ w)})):=by
  have hargument:instrArgument (bitwiseInstr kind o)=operandArgument o:=by
    cases kind <;> rfl
  let harg:operandArgument o <= N:=by
    rw [← hargument]
    exact (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo:=BoundedOp.ofOp o harg
  let localCfg:=finiteEmbedCfg (encodeBitwiseLabel (boundPC p pc) kind bo)
    (operandEvalStartCfg
      (R:=ZipInstructionTailLabel (BoundedPC p)) bo.toOp
      bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))
  have hprepare:=finite_step_prepare_entry hbound (boundPC p pc)
    (bitwiseInstr kind o) (instrClass (bitwiseInstr kind o))
    (by simpa [fetch_boundPC] using hfetch) rfl state (coreStacks w s)
  have hentry:TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg
        (.control (.data (boundPC p pc) (instrClass (bitwiseInstr kind o))))
        state (coreStacks w s))=some localCfg:=by
    rw [hprepare]
    cases kind <;>
      simp [bitwiseInstr,finitePrepareInstr,finiteInitializeEntry,
        instrArgument,localCfg,operandEvalStartCfg_coreStacks,
        finiteEmbedCfg,mapLabelCfg,finiteInterpreterCfg]
    all_goals cases o <;> simp [bo,BoundedOp.ofOp] <;>
      constructor <;> congr
  rcases finite_bitwise_to_fetch hbound (boundPC p pc) kind bo w s hm state with
    ⟨localSteps,hlocalBound,finalState,hdispatch,hlocal⟩
  have hall:=finite_data_prefix hbound hfetch (by cases kind <;> simp [bitwiseInstr])
    (by cases kind <;> simp [bitwiseInstr]) state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with acc:=
        (kind.natFn w s.acc (operandWordValue w bo.toOp s.mem) % 2 ^ w)}))
    hentry hlocal
  refine ⟨2 + localSteps,by omega,finalState,hdispatch, ?_⟩
  have hword:operandWordValue w o s.mem=sparseValue w o s.mem % 2 ^ w:=rfl
  have hnat:kind.natFn w s.acc (operandWordValue w o s.mem) % 2 ^ w =
      kind.natFn w s.acc (sparseValue w o s.mem) % 2 ^ w:=by
    have hbits:fixedBits w (kind.natFn w s.acc (operandWordValue w o s.mem)) =
        fixedBits w (kind.natFn w s.acc (sparseValue w o s.mem)):=by
      rw [fixedBits_bitwiseKind,fixedBits_bitwiseKind,hword,
        fixedBits_mod_word]
    simpa only [bitsValue_fixedBits] using congrArg bitsValue hbits
  simpa [bo,hnat] using hall

def shiftInstr (rightShift:Bool) (o:Op):Instr:=
  if rightShift then .shiftr o else .shiftl o

def shiftValue (rightShift:Bool) (w accumulator count:Nat):Nat:=
  if rightShift then accumulator / 2 ^ count % 2 ^ w
  else accumulator * 2 ^ count % 2 ^ w

set_option maxHeartbeats 1800000 in
theorem finite_shift_instruction {p:Program} {N pc w:Nat}
    (hbound:programArgumentBound p <= N) (rightShift:Bool) (o:Op)
    (hfetch:p[pc]?=some (shiftInstr rightShift o))
    (hw:0 < w) (s:SparseState) (hacc:s.acc < 2 ^ w)
    (hm:s.mem.Normalized w) (state:FullInterpreterState N):
    ∃ steps,steps <= shiftInstructionBound w s.mem + 3∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc:=
          (shiftValue rightShift w s.acc (sparseValue w o s.mem))})):=by
  have hargument:instrArgument (shiftInstr rightShift o)=operandArgument o:=by
    cases rightShift <;> rfl
  let harg:operandArgument o <= N:=by
    rw [← hargument]
    exact (instrArgument_le_programArgumentBound hfetch).trans hbound
  let bo:=BoundedOp.ofOp o harg
  let localCfg:=finiteEmbedCfg
    (encodeShiftLabel (boundPC p pc) rightShift bo)
    (operandEvalStartCfg
      (R:=FullShiftLabel (BoundedPC p)) bo.toOp
      bo.operandArgument_toOp w s.acc s.mem state (coreStacks w s))
  have hprepare:=finite_step_prepare_entry hbound (boundPC p pc)
    (shiftInstr rightShift o) (instrClass (shiftInstr rightShift o))
    (by simpa [fetch_boundPC] using hfetch) rfl state (coreStacks w s)
  have hentry:TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg
        (.control (.data (boundPC p pc) (instrClass (shiftInstr rightShift o))))
        state (coreStacks w s))=some localCfg:=by
    rw [hprepare]
    cases rightShift <;>
      simp [shiftInstr,finitePrepareInstr,finiteInitializeEntry,
        instrArgument,localCfg,operandEvalStartCfg_coreStacks,
        finiteEmbedCfg,mapLabelCfg,finiteInterpreterCfg]
    all_goals cases o <;> simp [bo,BoundedOp.ofOp] <;>
      constructor <;> congr
  have hlocal:∃ localSteps,
      localSteps <= shiftInstructionBound w s.mem + 1∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[localSteps])
        (some localCfg) =
      some (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
        (coreStacks w {s with acc:=(shiftValue rightShift w s.acc
          (sparseValue w bo.toOp s.mem))})):=by
    cases rightShift
    · simpa [localCfg,shiftValue] using
        finite_shiftLeft_to_fetch hbound (boundPC p pc) bo w hw s hacc hm state
    · simpa [localCfg,shiftValue] using
        finite_shiftRight_to_fetch hbound (boundPC p pc) bo w hw s hacc hm state
  rcases hlocal with
    ⟨localSteps,hlocalBound,finalState,hdispatch,hlocalRun⟩
  have hall:=finite_data_prefix hbound hfetch
    (by cases rightShift <;> simp [shiftInstr])
    (by cases rightShift <;> simp [shiftInstr])
    state (coreStacks w s) localCfg
    (finiteInterpreterCfg (.fetch (nextPC p (boundPC p pc))) finalState
      (coreStacks w {s with acc:=(shiftValue rightShift w s.acc
        (sparseValue w bo.toOp s.mem))})) hentry hlocalRun
  refine ⟨2 + localSteps,by omega,finalState,hdispatch, ?_⟩
  simpa [bo] using hall

theorem readInstructionBound_le_finiteDataStepBound (w:Nat) (m:SparseMemory):
    readInstructionBound w m + 3 <= finiteDataStepBound w m:=by
  simp [finiteDataStepBound]
  omega

theorem writeInstructionBound_le_finiteDataStepBound (w:Nat) (m:SparseMemory):
    writeInstructionBound w m + 3 <= finiteDataStepBound w m:=by
  simp [finiteDataStepBound]
  omega

theorem loadInstructionBound_le_finiteDataStepBound (w:Nat) (m:SparseMemory):
    loadInstructionBound w m + 3 <= finiteDataStepBound w m:=by
  simp [finiteDataStepBound]
  omega

theorem storeInstructionBound_le_finiteDataStepBound (w:Nat) (m:SparseMemory):
    storeInstructionBound w m + 3 <= finiteDataStepBound w m:=by
  simp [finiteDataStepBound]
  omega

theorem storeIndInstructionBound_le_finiteDataStepBound (w:Nat)
    (m:SparseMemory):
    storeIndInstructionBound w m + 3 <= finiteDataStepBound w m:=by
  simp [finiteDataStepBound]
  omega

theorem addInstructionBound_le_finiteDataStepBound (w:Nat) (m:SparseMemory):
    addInstructionBound w m + 3 <= finiteDataStepBound w m:=by
  simp [finiteDataStepBound]
  omega

theorem subtractInstructionBound_le_finiteDataStepBound (w:Nat)
    (m:SparseMemory):
    subtractInstructionBound w m + 3 <= finiteDataStepBound w m:=by
  simp [finiteDataStepBound]
  omega

theorem mulInstructionBound_le_finiteDataStepBound (w:Nat) (m:SparseMemory):
    mulInstructionBound w m + 3 <= finiteDataStepBound w m:=by
  simp [finiteDataStepBound]
  omega

theorem divideInstructionBound_le_finiteDataStepBound (w:Nat)
    (m:SparseMemory):
    divideInstructionTotalBound w m + 3 <= finiteDataStepBound w m:=by
  simp [finiteDataStepBound]
  omega

theorem zipInstructionBound_le_finiteDataStepBound (w:Nat) (m:SparseMemory):
    zipInstructionBound w m + 3 <= finiteDataStepBound w m:=by
  simp [finiteDataStepBound]
  omega

theorem shiftInstructionBound_le_finiteDataStepBound (w:Nat)
    (m:SparseMemory):
    shiftInstructionBound w m + 3 <= finiteDataStepBound w m:=by
  simp [finiteDataStepBound]
  omega

theorem finite_jump_instruction {p:Program} {N pc target:Nat}
    (hbound:programArgumentBound p <= N)
    (hfetch:p[pc]?=some (.jump target))
    (state:FullInterpreterState N) (tapes:CoreStack -> List SparseSymbol):
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteInterpreterCfg (.fetch (boundPC p pc)) state tapes) =
    some (finiteInterpreterCfg (.fetch (jumpPC p target)) state tapes):=by
  have hpc:pc < p.length:=fetch_some_pc_lt hfetch
  have hget:p[pc]=.jump target:=by
    simpa [List.getElem?_eq_getElem hpc] using hfetch
  simp [finiteInterpreterProgram,finiteControlStmt,finiteInterpreterCfg,
    controlDispatchMachine,fetch_boundPC,hfetch,hget,mapLabelStmt,
    lensRenameStmt,coreIdentityRenaming,FullInterpreterState.dispatchLens,
    FullInterpreterState.macroLens,InterpreterMacroState.dispatchLens,
    StateLens.comp,TM2.step,finiteEmbedControlLabel]

def finiteControlCfg {p:Program} {N:Nat}
    (c:(controlDispatchMachine p).Cfg) (ambient:FullInterpreterState N):
    TM2.Cfg (fun _:CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) where
  l:=c.l.map finiteEmbedControlLabel
  var:=FullInterpreterState.dispatchLens.put ambient c.var
  stk:=c.stk

set_option maxHeartbeats 1000000 in
theorem finiteControl_step_of_some {p:Program} {N:Nat}
    (hbound:programArgumentBound p <= N)
    (c d:(controlDispatchMachine p).Cfg)
    (ambient:FullInterpreterState N)
    (hstep:(controlDispatchMachine p).step c=some d)
    (hdlabel:d.l.isSome):
    TM2.step (finiteInterpreterProgram p N hbound)
      (finiteControlCfg c ambient)=some (finiteControlCfg d ambient):=by
  rcases c with ⟨label,control,tapes⟩
  cases label with
  | none => simp [TM2.step] at hstep
  | some label =>
      have liftControl
          (hprogram:finiteInterpreterProgram p N hbound
            (finiteEmbedControlLabel label)=finiteControlStmt label):
          TM2.step (finiteInterpreterProgram p N hbound)
            (finiteControlCfg ⟨some label,control,tapes⟩ ambient) =
              some (finiteControlCfg d ambient):=by
        have hd:TM2.stepAux ((controlDispatchMachine p).m label) control tapes=d:=by
          exact Option.some.inj hstep
        change some (TM2.stepAux
          (finiteInterpreterProgram p N hbound (finiteEmbedControlLabel label))
          (FullInterpreterState.dispatchLens.put ambient control) tapes) =
            some (finiteControlCfg d ambient)
        subst d
        rw [hprogram]
        simp only [finiteControlStmt,stepAux_mapLabelStmt]
        have htapes:renamedStacks coreIdentityRenaming tapes tapes=tapes:=by
          funext k
          simp [renamedStacks,coreIdentityRenaming]
        have hlens:=stepAux_lensRenameStmt
          (Λx:=Empty) coreIdentityRenaming FullInterpreterState.dispatchLens
          ((controlDispatchMachine p).m label) control ambient tapes tapes
        have hlens':TM2.stepAux
            (lensRenameStmt (Λx:=Empty) coreIdentityRenaming
              FullInterpreterState.dispatchLens ((controlDispatchMachine p).m label))
            (FullInterpreterState.dispatchLens.put ambient control) tapes =
          lensRenamedCfg coreIdentityRenaming FullInterpreterState.dispatchLens
            (TM2.stepAux ((controlDispatchMachine p).m label) control tapes)
            ambient tapes:=by
          simpa only [htapes] using hlens
        rw [hlens']
        generalize he:TM2.stepAux ((controlDispatchMachine p).m label)
          control tapes=e
        rcases e with ⟨elabel,econtrol,estacks⟩
        apply congrArg some
        have hestacks:renamedStacks coreIdentityRenaming estacks tapes=estacks:=by
          funext k
          simp [renamedStacks,coreIdentityRenaming]
        cases elabel with
        | none =>
            simp [finiteControlCfg,lensRenamedCfg,mapLabelCfg,hestacks,
              FullInterpreterState.dispatchLens] <;> rfl
        | some elabel =>
            cases elabel <;>
              simp [finiteControlCfg,lensRenamedCfg,mapLabelCfg,hestacks,
                FullInterpreterState.dispatchLens,finiteEmbedControlLabel] <;> rfl
      cases label with
      | fetch pc => exact liftControl rfl
      | scanAccumulator pc target z => exact liftControl rfl
      | restoreAccumulator pc target z => exact liftControl rfl
      | data pc kind =>
          have hdnone:d.l=none:=by
            have:=congrArg (fun x => x.l) (Option.some.inj hstep)
            simpa [controlDispatchMachine,TM2.step] using! this.symm
          rw [hdnone] at hdlabel
          simp at hdlabel
      | stopped =>
          have hdnone:d.l=none:=by
            have:=congrArg (fun x => x.l) (Option.some.inj hstep)
            simpa [controlDispatchMachine,TM2.step] using! this.symm
          rw [hdnone] at hdlabel
          simp at hdlabel

theorem finiteControl_run_of_some {p:Program} {N n:Nat}
    (hbound:programArgumentBound p <= N)
    (c d:(controlDispatchMachine p).Cfg)
    (ambient:FullInterpreterState N)
    (hrun:((fun x:Option (controlDispatchMachine p).Cfg =>
      x.bind (controlDispatchMachine p).step)^[n]) (some c)=some d)
    (hdlabel:d.l.isSome):
    ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[n])
      (some (finiteControlCfg c ambient)) =
    some (finiteControlCfg d ambient):=by
  induction n generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply] at hrun ⊢
      cases hrun
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      simp only [Option.bind_some] at hrun ⊢
      cases hs:(controlDispatchMachine p).step c with
      | none =>
          change ((fun x:Option (controlDispatchMachine p).Cfg =>
            x.bind (controlDispatchMachine p).step)^[n])
              ((controlDispatchMachine p).step c)=some d at hrun
          rw [hs,iterate_optionBind_none] at hrun
          contradiction
      | some c' =>
          have hc'label:c'.l.isSome:=by
            cases n with
            | zero =>
                simp only [Function.iterate_zero_apply] at hrun
                rw [hs] at hrun
                cases hrun
                exact hdlabel
            | succ n =>
                rw [hs] at hrun
                rcases c' with ⟨none | label,control,tapes⟩
                · change ((fun x:Option (controlDispatchMachine p).Cfg =>
                    x.bind (controlDispatchMachine p).step)^[n + 1])
                      (some ⟨none,control,tapes⟩)=some d at hrun
                  rw [Function.iterate_succ_apply] at hrun
                  change ((fun x:Option (controlDispatchMachine p).Cfg =>
                    x.bind (controlDispatchMachine p).step)^[n]) none=some d at hrun
                  rw [iterate_optionBind_none] at hrun
                  contradiction
                · rfl
          rw [finiteControl_step_of_some hbound c c' ambient hs hc'label]
          rw [hs] at hrun
          exact ih c' hrun

theorem finiteControlCfg_boundary {p:Program} {N pc w:Nat}
    (s:SparseState) (state:FullInterpreterState N)
    (hdispatch:FullInterpreterState.dispatchLens.get state=default):
    finiteControlCfg (controlBoundaryCfg p pc w s) state =
      finiteInterpreterCfg (.fetch (boundPC p pc)) state (coreStacks w s):=by
  unfold finiteControlCfg controlBoundaryCfg controlDispatchCfg
  unfold finiteInterpreterCfg
  rw [← hdispatch,FullInterpreterState.dispatchLens.put_get]
  rfl

theorem finite_jzero_instruction {p:Program} {N pc target w:Nat}
    (hbound:programArgumentBound p <= N)
    (hfetch:p[pc]?=some (.jzero target))
    (s:SparseState) (hacc:s.acc < 2 ^ w)
    (state:FullInterpreterState N)
    (hdispatch:FullInterpreterState.dispatchLens.get state=default):
    let next:=if s.acc=0 then target else pc + 1
    ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[2 * w + 3])
      (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
        (coreStacks w s))) =
    some (finiteInterpreterCfg (.fetch (boundPC p next)) state
      (coreStacks w {s with pc:=next})):=by
  dsimp only
  have hrun:=control_jzero_correct hfetch hacc
  have hlift:=finiteControl_run_of_some hbound
    (controlBoundaryCfg p pc w s)
    (controlBoundaryCfg p (if s.acc=0 then target else pc + 1) w
      {s with pc:=if s.acc=0 then target else pc + 1}) state hrun
    (by rfl)
  rw [finiteControlCfg_boundary s state hdispatch] at hlift
  rw [finiteControlCfg_boundary
    {s with pc:=if s.acc=0 then target else pc + 1} state hdispatch] at hlift
  exact hlift

theorem finite_jgtz_instruction {p:Program} {N pc target w:Nat}
    (hbound:programArgumentBound p <= N)
    (hfetch:p[pc]?=some (.jgtz target))
    (s:SparseState) (hacc:s.acc < 2 ^ w)
    (state:FullInterpreterState N)
    (hdispatch:FullInterpreterState.dispatchLens.get state=default):
    let next:=if 0 < s.acc then target else pc + 1
    ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[2 * w + 3])
      (some (finiteInterpreterCfg (.fetch (boundPC p pc)) state
        (coreStacks w s))) =
    some (finiteInterpreterCfg (.fetch (boundPC p next)) state
      (coreStacks w {s with pc:=next})):=by
  dsimp only
  have hrun:=control_jgtz_correct hfetch hacc
  have hlift:=finiteControl_run_of_some hbound
    (controlBoundaryCfg p pc w s)
    (controlBoundaryCfg p (if 0 < s.acc then target else pc + 1) w
      {s with pc:=if 0 < s.acc then target else pc + 1}) state hrun
    (by rfl)
  rw [finiteControlCfg_boundary s state hdispatch] at hlift
  rw [finiteControlCfg_boundary
    {s with pc:=if 0 < s.acc then target else pc + 1} state hdispatch] at hlift
  exact hlift

def isDataInstr:Instr -> Prop
  | .jump _ | .jzero _ | .jgtz _ | .halt => False
  | _ => True

set_option maxHeartbeats 0 in
theorem finite_data_effect {p:Program} {N w:Nat}
    (hbound:programArgumentBound p <= N) (hw:0 < w)
    (s:SparseState) (hacc:s.acc < 2 ^ w) (hm:s.mem.Normalized w)
    (i:Instr) (hfetch:p[s.pc]?=some i) (hdata:isDataInstr i)
    {s':SparseState} (heffect:sparseEffect w i s=some s')
    (state:FullInterpreterState N):
    ∃ steps,steps <= finiteDataStepBound w s.mem∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p s.pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (boundPC p s'.pc)) finalState
        (coreStacks w s')):=by
  have hpc:s.pc < p.length:=fetch_some_pc_lt hfetch
  have hnext:nextPC p (boundPC p s.pc)=boundPC p (s.pc + 1):=
    nextPC_boundPC_of_lt hpc
  cases i with
  | read address =>
      cases hin:s.inp with
      | nil => simp [sparseEffect,hin] at heffect
      | cons value inputTail =>
          simp [sparseEffect,hin] at heffect
          subst s'
          rcases finite_read_instruction hbound address value inputTail hfetch
              s hin hm state with
            ⟨steps,hs,finalState,hdispatch,hrun⟩
          refine ⟨steps,hs.trans (readInstructionBound_le_finiteDataStepBound _ _),
            finalState,hdispatch, ?_⟩
          simpa [hnext,coreStacks] using! hrun
  | write o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_write_instruction hbound o hfetch s hm state with
        ⟨steps,hs,finalState,hdispatch,hrun⟩
      refine ⟨steps,hs.trans (writeInstructionBound_le_finiteDataStepBound _ _),
        finalState,hdispatch, ?_⟩
      simpa [hnext,coreStacks] using! hrun
  | load o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_load_instruction hbound o hfetch s hm state with
        ⟨steps,hs,finalState,hdispatch,hrun⟩
      refine ⟨steps,hs.trans (loadInstructionBound_le_finiteDataStepBound _ _),
        finalState,hdispatch, ?_⟩
      simpa [hnext,operandWordValue,coreStacks] using! hrun
  | store address =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_store_instruction hbound address hfetch s hm state with
        ⟨steps,hs,finalState,hdispatch,hrun⟩
      refine ⟨steps,hs.trans (storeInstructionBound_le_finiteDataStepBound _ _),
        finalState,hdispatch, ?_⟩
      simpa [hnext,coreStacks] using! hrun
  | storeInd address =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_storeInd_instruction hbound address hfetch s hm state with
        ⟨steps,hs,finalState,hdispatch,hrun⟩
      refine ⟨steps,hs.trans (storeIndInstructionBound_le_finiteDataStepBound _ _),
        finalState,hdispatch, ?_⟩
      simpa [hnext,coreStacks] using! hrun
  | add o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_add_instruction hbound o hfetch s hm state with
        ⟨steps,hs,finalState,hdispatch,hrun⟩
      refine ⟨steps,hs.trans (addInstructionBound_le_finiteDataStepBound _ _),
        finalState,hdispatch, ?_⟩
      simpa [hnext,coreStacks] using! hrun
  | sub o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_sub_instruction hbound o hfetch s hacc hm state with
        ⟨steps,hs,finalState,hdispatch,hrun⟩
      refine ⟨steps,hs.trans (subtractInstructionBound_le_finiteDataStepBound _ _),
        finalState,hdispatch, ?_⟩
      simpa [hnext,coreStacks] using! hrun
  | mul o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_mul_instruction hbound o hfetch hw s hm state with
        ⟨steps,hs,finalState,hdispatch,hrun⟩
      refine ⟨steps,hs.trans (mulInstructionBound_le_finiteDataStepBound _ _),
        finalState,hdispatch, ?_⟩
      simpa [hnext,coreStacks] using! hrun
  | div o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_div_instruction hbound o hfetch s hacc hm state with
        ⟨steps,hs,finalState,hdispatch,hrun⟩
      refine ⟨steps,hs.trans (divideInstructionBound_le_finiteDataStepBound _ _),
        finalState,hdispatch, ?_⟩
      simpa [hnext,coreStacks] using! hrun
  | and o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_bitwise_instruction hbound .and o hfetch s hm state with
        ⟨steps,hs,finalState,hdispatch,hrun⟩
      refine ⟨steps,hs.trans (zipInstructionBound_le_finiteDataStepBound _ _),
        finalState,hdispatch, ?_⟩
      simpa [bitwiseInstr,BitwiseKind.natFn,hnext,coreStacks] using! hrun
  | or o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_bitwise_instruction hbound .or o hfetch s hm state with
        ⟨steps,hs,finalState,hdispatch,hrun⟩
      refine ⟨steps,hs.trans (zipInstructionBound_le_finiteDataStepBound _ _),
        finalState,hdispatch, ?_⟩
      simpa [bitwiseInstr,BitwiseKind.natFn,hnext,coreStacks] using! hrun
  | xor o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_bitwise_instruction hbound .xor o hfetch s hm state with
        ⟨steps,hs,finalState,hdispatch,hrun⟩
      refine ⟨steps,hs.trans (zipInstructionBound_le_finiteDataStepBound _ _),
        finalState,hdispatch, ?_⟩
      simpa [bitwiseInstr,BitwiseKind.natFn,hnext,coreStacks] using! hrun
  | compl o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_bitwise_instruction hbound .compl o hfetch s hm state with
        ⟨steps,hs,finalState,hdispatch,hrun⟩
      refine ⟨steps,hs.trans (zipInstructionBound_le_finiteDataStepBound _ _),
        finalState,hdispatch, ?_⟩
      simpa [bitwiseInstr,BitwiseKind.natFn,hnext,coreStacks] using! hrun
  | shiftl o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_shift_instruction hbound false o hfetch hw s hacc hm state with
        ⟨steps,hs,finalState,hdispatch,hrun⟩
      refine ⟨steps,hs.trans (shiftInstructionBound_le_finiteDataStepBound _ _),
        finalState,hdispatch, ?_⟩
      simpa [shiftInstr,shiftValue,hnext,coreStacks] using! hrun
  | shiftr o =>
      simp [sparseEffect] at heffect
      subst s'
      rcases finite_shift_instruction hbound true o hfetch hw s hacc hm state with
        ⟨steps,hs,finalState,hdispatch,hrun⟩
      refine ⟨steps,hs.trans (shiftInstructionBound_le_finiteDataStepBound _ _),
        finalState,hdispatch, ?_⟩
      simpa [shiftInstr,shiftValue,hnext,coreStacks] using! hrun
  | jump _ | jzero _ | jgtz _ | halt => simp [isDataInstr] at hdata

set_option maxHeartbeats 0 in
theorem finite_sparseStep_correct {p:Program} {N w:Nat}
    (hbound:programArgumentBound p <= N) (hw:0 < w)
    (s s':SparseState) (hacc:s.acc < 2 ^ w)
    (hm:s.mem.Normalized w) (hstep:sparseStep w p s=some s')
    (state:FullInterpreterState N)
    (hdispatch:FullInterpreterState.dispatchLens.get state=default):
    ∃ steps,steps <= finiteStepBound w s.mem∧ ∃ finalState,
      FullInterpreterState.dispatchLens.get finalState =
        FullInterpreterState.dispatchLens.get state∧
      ((fun x => x.bind (TM2.step (finiteInterpreterProgram p N hbound)))^[steps])
        (some (finiteInterpreterCfg (.fetch (boundPC p s.pc)) state
          (coreStacks w s))) =
      some (finiteInterpreterCfg (.fetch (boundPC p s'.pc)) finalState
        (coreStacks w s')):=by
  unfold sparseStep at hstep
  cases hfetch:p[s.pc]? with
  | none => simp [hfetch] at hstep
  | some i =>
      simp [hfetch] at hstep
      by_cases hdata:isDataInstr i
      · rcases finite_data_effect (p:=p) (N:=N) (w:=w)
            hbound hw s hacc hm i hfetch hdata hstep state with
          ⟨steps,hs,finalState,hfinalDispatch,hrun⟩
        refine ⟨steps, ?_,finalState,hfinalDispatch,hrun⟩
        exact hs.trans (by unfold finiteStepBound; omega)
      · cases i with
        | jump target =>
            simp [sparseEffect] at hstep
            subst s'
            refine ⟨1, ?_,state,rfl, ?_⟩
            · unfold finiteStepBound
              omega
            have hjump:=finite_jump_instruction hbound hfetch state
              (coreStacks w s)
            simpa [jumpPC,coreStacks,Function.iterate_one] using hjump
        | jzero target =>
            simp [sparseEffect] at hstep
            subst s'
            refine ⟨2 * w + 3,by simp [finiteStepBound]; omega,
              state,rfl, ?_⟩
            simpa [coreStacks] using
              finite_jzero_instruction hbound hfetch s hacc state hdispatch
        | jgtz target =>
            simp [sparseEffect] at hstep
            subst s'
            refine ⟨2 * w + 3,by simp [finiteStepBound]; omega,
              state,rfl, ?_⟩
            simpa [coreStacks] using
              finite_jgtz_instruction hbound hfetch s hacc state hdispatch
        | halt => simp [sparseEffect] at hstep
        | read _ => simp [isDataInstr] at hdata
        | write _ => simp [isDataInstr] at hdata
        | load _ => simp [isDataInstr] at hdata
        | store _ => simp [isDataInstr] at hdata
        | storeInd _ => simp [isDataInstr] at hdata
        | add _ => simp [isDataInstr] at hdata
        | sub _ => simp [isDataInstr] at hdata
        | mul _ => simp [isDataInstr] at hdata
        | div _ => simp [isDataInstr] at hdata
        | and _ => simp [isDataInstr] at hdata
        | or _ => simp [isDataInstr] at hdata
        | xor _ => simp [isDataInstr] at hdata
        | compl _ => simp [isDataInstr] at hdata
        | shiftl _ => simp [isDataInstr] at hdata
        | shiftr _ => simp [isDataInstr] at hdata

end

end Lax759944Proofs.RamToTM

end

theorem solution:∀ {p:Lax759944Proofs.Microcode.Program} {N w:ℕ} (hbound:Lax759944Proofs.RamToTM.programArgumentBound p≤ N),
  0 < w→
    ∀ (s s':Lax759944Proofs.RamToTM.SparseState),
      s.acc < 2 ^ w→
        Lax759944Proofs.RamToTM.SparseMemory.Normalized w s.mem→
          Lax759944Proofs.RamToTM.sparseStep w p s=Option.some s'→
            ∀ (state:Lax759944Proofs.RamToTM.FullInterpreterState N),
              Lax759944Proofs.RamToTM.FullInterpreterState.dispatchLens.get state=Inhabited.default→
                ∃ steps≤ Lax759944Proofs.RamToTM.finiteStepBound w s.mem,
                  ∃ (finalState:Lax759944Proofs.RamToTM.FullInterpreterState N),
                    Lax759944Proofs.RamToTM.FullInterpreterState.dispatchLens.get finalState =
                        Lax759944Proofs.RamToTM.FullInterpreterState.dispatchLens.get state∧
                      (fun
                                (x:
                                  Option
                                    (Turing.TM2.Cfg
                                      (fun (x:Lax759944Proofs.RamToTM.CoreStack) =>
                                        Lax759944Proofs.RamToTM.SparseSymbol)
                                      (Lax759944Proofs.RamToTM.FiniteInterpreterLabel p N)
                                      (Lax759944Proofs.RamToTM.FullInterpreterState N))) =>
                              x.bind
                                (Turing.TM2.step (Lax759944Proofs.RamToTM.finiteInterpreterProgram p N hbound)))^[steps]
                          (Option.some
                            (Lax759944Proofs.RamToTM.finiteInterpreterCfg
                              (Lax759944Proofs.RamToTM.FiniteInterpreterLabel.fetch
                                (Lax759944Proofs.RamToTM.boundPC p s.pc))
                              state (Lax759944Proofs.RamToTM.coreStacks w s))) =
                        Option.some
                          (Lax759944Proofs.RamToTM.finiteInterpreterCfg
                            (Lax759944Proofs.RamToTM.FiniteInterpreterLabel.fetch
                              (Lax759944Proofs.RamToTM.boundPC p s'.pc))
                            finalState (Lax759944Proofs.RamToTM.coreStacks w s')):= @Lax759944Proofs.RamToTM.finite_sparseStep_correct
