-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.theorem_6_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T07:15:16.196026+00:00
-- url     : https://prove2.me/submissions/8087bb4c-aed7-495d-ab8d-0b05dcc646c4

import Mathlib
import Definitions.Def_BooneHigman
import Definitions.Def_BooneHigman_MonoidWordProblem
import Definitions.Def_BooneHigman_PMonoid
import Definitions.Def_BooneHigman_TMonoid
import Definitions.Def_OAIFAE000
import Definitions.Def_OAIFAE001
import Definitions.Def_OAIFAE002
import Definitions.Def_OAIFAE003
import Definitions.Def_OAIFAE004

attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000

open OAI.FiniteAlgebraicEnvelopes

universe u

noncomputable section

namespace OAI.FiniteAlgebraicEnvelopes.PElemCoding
theorem primrec_pow2 : Primrec (fun n : ℕ => 2 ^ n) :=
  (Primrec.nat_rec₁ 1 (Primrec.nat_mul.comp Primrec.snd (Primrec.const 2)).to₂).of_eq
    (by intro n; induction n <;> simp_all [pow_succ])

abbrev URat := ℕ × ℕ × ℕ
instance instPrimcodableURat : Primcodable URat := inferInstance

namespace URat

def val (a : URat) : ℚ := ((a.1 : ℚ) - (a.2.1 : ℚ)) / ((a.2.2 : ℚ) + 1)
def zero : URat := (0, 0, 0)
def one : URat := (1, 0, 0)
def neg (a : URat) : URat := (a.2.1, a.1, a.2.2)

def add (a b : URat) : URat :=
  (a.1 * (b.2.2 + 1) + b.1 * (a.2.2 + 1),
   a.2.1 * (b.2.2 + 1) + b.2.1 * (a.2.2 + 1),
   a.2.2 * b.2.2 + a.2.2 + b.2.2)

def mul (a b : URat) : URat :=
  (a.1 * b.1 + a.2.1 * b.2.1,
   a.1 * b.2.1 + a.2.1 * b.1,
   a.2.2 * b.2.2 + a.2.2 + b.2.2)

def le (a b : URat) : Bool :=
  decide (a.1 * (b.2.2 + 1) + b.2.1 * (a.2.2 + 1) ≤ b.1 * (a.2.2 + 1) + a.2.1 * (b.2.2 + 1))

def eq (a b : URat) : Bool := le a b && le b a
def max (a b : URat) : URat := if le a b then b else a

def ofRat (q : ℚ) : URat := (q.num.toNat, (-q.num).toNat, q.den - 1)

theorem den_pos (a : URat) : (0 : ℚ) < (a.2.2 : ℚ) + 1 := by positivity

@[simp] theorem val_zero : val zero = 0 := by norm_num [val, zero]
@[simp] theorem val_one : val one = 1 := by norm_num [val, one]
@[simp] theorem val_neg (a : URat) : val (neg a) = -val a := by simp [val, neg]; ring

@[simp] theorem val_add (a b : URat) : val (add a b) = val a + val b := by
  have ha := (den_pos a).ne'
  have hb := (den_pos b).ne'
  have hab : ((a.2.2 * b.2.2 + a.2.2 + b.2.2 : ℕ) : ℚ) + 1 = ((a.2.2 : ℚ) + 1) * ((b.2.2 : ℚ) + 1) := by
    push_cast; ring
  simp only [val, add]
  rw [hab]
  push_cast
  field_simp
  ring

@[simp] theorem val_mul (a b : URat) : val (mul a b) = val a * val b := by
  have ha := (den_pos a).ne'
  have hb := (den_pos b).ne'
  have hab : ((a.2.2 * b.2.2 + a.2.2 + b.2.2 : ℕ) : ℚ) + 1 = ((a.2.2 : ℚ) + 1) * ((b.2.2 : ℚ) + 1) := by
    push_cast; ring
  simp only [val, mul]
  rw [hab]
  push_cast
  field_simp
  ring

@[simp] theorem le_correct (a b : URat) : le a b = true ↔ val a ≤ val b := by
  rw [val, val, div_le_div_iff₀ (den_pos a) (den_pos b)]
  simp only [le, decide_eq_true_eq]
  rw [← Nat.cast_le (α := ℚ)]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  constructor <;> intro h <;> nlinarith

@[simp] theorem eq_correct (a b : URat) : eq a b = true ↔ val a = val b := by
  rw [eq, Bool.and_eq_true, le_correct, le_correct]
  exact le_antisymm_iff.symm

@[simp] theorem val_max (a b : URat) : val (max a b) = Max.max (val a) (val b) := by
  unfold max
  split
  next h => exact (max_eq_right ((le_correct a b).mp h)).symm
  next h => exact (max_eq_left (le_of_not_ge fun hh => h ((le_correct a b).mpr hh))).symm

@[simp] theorem val_ofRat (q : ℚ) : val (ofRat q) = q := by
  simp only [val, ofRat]
  have hnum : ((q.num.toNat : ℚ) - ((-q.num).toNat : ℚ)) = (q.num : ℚ) := by
    exact_mod_cast (show (q.num.toNat : ℤ) - ((-q.num).toNat : ℤ) = q.num by omega)
  have hden : ((q.den - 1 : ℕ) : ℚ) + 1 = (q.den : ℚ) := by
    have hd : 1 ≤ q.den := q.den_pos
    exact_mod_cast Nat.sub_add_cancel hd
  rw [hnum, hden, Rat.num_div_den]

theorem primrec_neg : Primrec neg :=
  (Primrec.fst.comp Primrec.snd).pair (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))

theorem primrec_add : Primrec₂ add := by
  have ap : Primrec (fun p : URat × URat => p.1.1) := Primrec.fst.comp Primrec.fst
  have an : Primrec (fun p : URat × URat => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ak : Primrec (fun p : URat × URat => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bp : Primrec (fun p : URat × URat => p.2.1) := Primrec.fst.comp Primrec.snd
  have bn : Primrec (fun p : URat × URat => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have bk : Primrec (fun p : URat × URat => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have ak1 : Primrec (fun p : URat × URat => p.1.2.2 + 1) := Primrec.nat_add.comp ak (Primrec.const 1)
  have bk1 : Primrec (fun p : URat × URat => p.2.2.2 + 1) := Primrec.nat_add.comp bk (Primrec.const 1)
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp ap bk1) (Primrec.nat_mul.comp bp ak1)).pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp an bk1) (Primrec.nat_mul.comp bn ak1)).pair
      (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp ak bk) ak) bk))).to₂

theorem primrec_mul : Primrec₂ mul := by
  have ap : Primrec (fun p : URat × URat => p.1.1) := Primrec.fst.comp Primrec.fst
  have an : Primrec (fun p : URat × URat => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ak : Primrec (fun p : URat × URat => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bp : Primrec (fun p : URat × URat => p.2.1) := Primrec.fst.comp Primrec.snd
  have bn : Primrec (fun p : URat × URat => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have bk : Primrec (fun p : URat × URat => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp ap bp) (Primrec.nat_mul.comp an bn)).pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp ap bn) (Primrec.nat_mul.comp an bp)).pair
      (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp ak bk) ak) bk))).to₂

theorem primrec_le : Primrec₂ le := by
  have ap : Primrec (fun p : URat × URat => p.1.1) := Primrec.fst.comp Primrec.fst
  have an : Primrec (fun p : URat × URat => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ak : Primrec (fun p : URat × URat => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bp : Primrec (fun p : URat × URat => p.2.1) := Primrec.fst.comp Primrec.snd
  have bn : Primrec (fun p : URat × URat => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have bk : Primrec (fun p : URat × URat => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have ak1 : Primrec (fun p : URat × URat => p.1.2.2 + 1) := Primrec.nat_add.comp ak (Primrec.const 1)
  have bk1 : Primrec (fun p : URat × URat => p.2.2.2 + 1) := Primrec.nat_add.comp bk (Primrec.const 1)
  exact ((Primrec.nat_le.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp ap bk1) (Primrec.nat_mul.comp bn ak1))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp bp ak1) (Primrec.nat_mul.comp an bk1))).decide).to₂

theorem primrec_eq : Primrec₂ eq :=
  (Primrec.and.comp (primrec_le.comp Primrec.fst Primrec.snd)
    (primrec_le.comp Primrec.snd Primrec.fst)).to₂

theorem primrec_max : Primrec₂ max :=
  (Primrec.ite (Primrec.eq.comp primrec_le (Primrec.const true)) Primrec.snd Primrec.fst).to₂

end URat

abbrev USlope := ℕ × ℕ
instance instPrimcodableUSlope : Primcodable USlope := inferInstance

namespace USlope

def val (a : USlope) : ℤ := (a.1 : ℤ) - (a.2 : ℤ)
def urat (a : USlope) : URat := (2 ^ a.1, 0, 2 ^ a.2 - 1)
def mul (a b : USlope) : USlope := (a.1 + b.1, a.2 + b.2)
def inv (a : USlope) : USlope := (a.2, a.1)
def eq (a b : USlope) : Bool := decide (a.1 + b.2 = b.1 + a.2)
def ofInt (m : ℤ) : USlope := (m.toNat, (-m).toNat)

@[simp] theorem val_urat (a : USlope) : URat.val (urat a) = (2 : ℚ) ^ (val a) := by
  simp only [urat, URat.val, val]
  have hpow : ((2 ^ a.2 - 1 : ℕ) : ℚ) + 1 = (2 : ℚ) ^ a.2 := by
    have h1 : 1 ≤ 2 ^ a.2 := Nat.one_le_two_pow
    exact_mod_cast Nat.sub_add_cancel h1
  rw [hpow, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast, zpow_natCast]
  push_cast
  ring

@[simp] theorem val_mul (a b : USlope) : val (mul a b) = val a + val b := by
  simp only [val, mul, Nat.cast_add]; ring

@[simp] theorem val_inv (a : USlope) : val (inv a) = -val a := by
  simp only [val, inv]; ring

@[simp] theorem eq_correct (a b : USlope) : eq a b = true ↔ val a = val b := by
  simp only [eq, val, decide_eq_true_eq]
  omega

@[simp] theorem val_ofInt (m : ℤ) : val (ofInt m) = m := by
  simp only [val, ofInt]; omega

theorem primrec_urat : Primrec urat :=
  (primrec_pow2.comp Primrec.fst).pair ((Primrec.const 0).pair
    (Primrec.nat_sub.comp (primrec_pow2.comp Primrec.snd) (Primrec.const 1)))

theorem primrec_mul : Primrec₂ mul :=
  ((Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂

theorem primrec_inv : Primrec inv := Primrec.snd.pair Primrec.fst

theorem primrec_eq : Primrec₂ eq :=
  ((Primrec.eq.comp
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))).decide).to₂

end USlope

namespace UBound

def val : Option URat → WithBot ℚ
  | none => ⊥
  | some r => (URat.val r : WithBot ℚ)

def sup : Option URat → Option URat → Option URat
  | none, b => b
  | a, none => a
  | some a, some b => some (URat.max a b)

def shift (r : Option URat) (b : URat) (m : USlope) : Option URat :=
  r.map (fun r0 => URat.mul (USlope.urat (USlope.inv m)) (URat.add r0 (URat.neg b)))

def eq : Option URat → Option URat → Bool
  | none, none => true
  | some a, some b => URat.eq a b
  | _, _ => false

def ofWithBot : WithBot ℚ → Option URat
  | ⊥ => none
  | (q : ℚ) => some (URat.ofRat q)

@[simp] theorem val_sup (a b : Option URat) : val (sup a b) = Max.max (val a) (val b) := by
  cases a <;> cases b <;> simp [sup, val, URat.val_max]

@[simp] theorem val_shift (r : Option URat) (b : URat) (m : USlope) :
    val (shift r b m) = PElem.shiftedBound (val r) (URat.val b) ((2 : ℚ) ^ (USlope.val m)) := by
  cases r with
  | none => rfl
  | some r0 =>
    simp only [shift, Option.map_some, val, PElem.shiftedBound_coe, WithBot.coe_eq_coe,
      URat.val_mul, USlope.val_urat, USlope.val_inv, URat.val_add, URat.val_neg, zpow_neg]
    ring

@[simp] theorem eq_correct (a b : Option URat) : eq a b = true ↔ val a = val b := by
  cases a <;> cases b <;> simp [eq, val, URat.eq_correct]

@[simp] theorem val_ofWithBot (r : WithBot ℚ) : val (ofWithBot r) = r := by
  cases r with
  | bot => rfl
  | coe q => simp [ofWithBot, val]

theorem primrec_sup : Primrec₂ sup := by
  have hh : Primrec (fun p : Option URat × Option URat =>
      (Option.casesOn p.1 p.2 (fun a => Option.casesOn p.2 (some a) (fun b => some (URat.max a b))) : Option URat)) := by
    apply Primrec.option_casesOn Primrec.fst Primrec.snd
    exact (Primrec.option_casesOn (Primrec.snd.comp Primrec.fst)
      (Primrec.option_some.comp Primrec.snd)
      (Primrec.option_some.comp (URat.primrec_max.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂).to₂
  exact hh.of_eq (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)

theorem primrec_eq : Primrec₂ eq := by
  have hh : Primrec (fun p : Option URat × Option URat =>
      (Option.casesOn p.1 (Option.casesOn p.2 true (fun _ => false))
        (fun a => Option.casesOn p.2 false (fun b => URat.eq a b)) : Bool)) := by
    apply Primrec.option_casesOn Primrec.fst
    · exact Primrec.option_casesOn Primrec.snd (Primrec.const true) (Primrec.const false).to₂
    · exact (Primrec.option_casesOn (Primrec.snd.comp Primrec.fst) (Primrec.const false)
        (URat.primrec_eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact hh.of_eq (by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl)

theorem primrec_shift {X : Type*} [Primcodable X]
    {r : X → Option URat} {b : X → URat} {m : X → USlope}
    (hr : Primrec r) (hb : Primrec b) (hm : Primrec m) :
    Primrec (fun x => shift (r x) (b x) (m x)) :=
  Primrec.option_map hr
    ((URat.primrec_mul.comp (USlope.primrec_urat.comp (USlope.primrec_inv.comp (hm.comp Primrec.fst)))
      (URat.primrec_add.comp Primrec.snd (URat.primrec_neg.comp (hb.comp Primrec.fst)))).to₂)

end UBound

def UData := USlope × URat × Option URat
instance instPrimcodableOptionURat : Primcodable (Option URat) := inferInstance
instance instPrimcodableUData : Primcodable UData := inferInstanceAs (Primcodable (USlope × URat × Option URat))

namespace UData

def toPElem (d : UData) : PElem := ⟨USlope.val d.1, URat.val d.2.1, UBound.val d.2.2⟩
def ofPElem (p : PElem) : UData := (USlope.ofInt p.m, URat.ofRat p.b, UBound.ofWithBot p.r)
def one : UData := ((0, 0), URat.zero, none)

def mul (a b : UData) : UData :=
  (USlope.mul a.1 b.1,
   URat.add (URat.mul (USlope.urat a.1) b.2.1) a.2.1,
   UBound.sup b.2.2 (UBound.shift a.2.2 b.2.1 b.1))

def eq (a b : UData) : Bool :=
  USlope.eq a.1 b.1 && URat.eq a.2.1 b.2.1 && UBound.eq a.2.2 b.2.2

@[simp] theorem toPElem_ofPElem (p : PElem) : toPElem (ofPElem p) = p := by
  cases p; simp [toPElem, ofPElem]

@[simp] theorem toPElem_one : toPElem one = 1 := by
  simp [toPElem, one, PElem.one_def, USlope.val, UBound.val]

@[simp] theorem toPElem_mul (a b : UData) : toPElem (mul a b) = toPElem a * toPElem b := by
  simp [toPElem, mul, PElem.mul_def]

@[simp] theorem eq_correct (a b : UData) : eq a b = true ↔ toPElem a = toPElem b := by
  simp only [eq, Bool.and_eq_true, USlope.eq_correct, URat.eq_correct, UBound.eq_correct,
    toPElem, PElem.mk.injEq, and_assoc]

theorem primrec_mul : Primrec₂ mul := by
  have ac : Primrec (fun p : UData × UData => p.1.1) := Primrec.fst.comp Primrec.fst
  have ad : Primrec (fun p : UData × UData => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ar : Primrec (fun p : UData × UData => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have bc : Primrec (fun p : UData × UData => p.2.1) := Primrec.fst.comp Primrec.snd
  have bd : Primrec (fun p : UData × UData => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have br : Primrec (fun p : UData × UData => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((USlope.primrec_mul.comp ac bc).pair
    ((URat.primrec_add.comp (URat.primrec_mul.comp (USlope.primrec_urat.comp ac) bd) ad).pair
      (UBound.primrec_sup.comp br (UBound.primrec_shift ar bd bc)))).to₂

theorem primrec_eq : Primrec₂ eq :=
  (Primrec.and.comp
    (Primrec.and.comp
      (USlope.primrec_eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (URat.primrec_eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
    (UBound.primrec_eq.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂

end UData

def decodeNat (n : ℕ) : UData := (Encodable.decode (α := UData) n).getD UData.one

theorem primrec_decodeNat : Primrec decodeNat :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const UData.one)

@[simp] theorem decodeNat_encode (d : UData) : decodeNat (Encodable.encode d) = d := by
  rw [decodeNat, Encodable.encodek]; rfl

attribute [irreducible] UData UData.toPElem UData.ofPElem UData.one UData.mul UData.eq decodeNat

abbrev PTag := Bool ⊕ ℕ
abbrev PState := PElem × List (PTag × PElem)
abbrev UState := UData × List (PTag × UData)
instance instPrimcodablePTag : Primcodable PTag := inferInstance
instance instPrimcodablePTagUData : Primcodable (PTag × UData) := inferInstance
instance instPrimcodableListPTagUData : Primcodable (List (PTag × UData)) := inferInstance
instance instPrimcodableUState : Primcodable UState := inferInstance

def uStateToPState (s : UState) : PState :=
  (UData.toPElem s.1, s.2.map (fun x => (x.1, UData.toPElem x.2)))

def pPrependElem (p : PElem) (s : PState) : PState := (p * s.1, s.2)
def uPrependElem (d : UData) (s : UState) : UState := (UData.mul d s.1, s.2)

def pStepTag : PTag → PState → PState
  | .inl false, s =>
      if s.1 = 1 then
        match s.2 with
        | (.inr n, p1) :: rest => (UData.toPElem (decodeNat n) * p1, rest)
        | _ => (1, (.inl false, s.1) :: s.2)
      else (1, (.inl false, s.1) :: s.2)
  | .inl true, s =>
      if s.1 = 1 then
        match s.2 with
        | (.inr n, p1) :: rest => (1, (.inr (n + 1), p1) :: rest)
        | _ => (1, (.inl true, s.1) :: s.2)
      else (1, (.inl true, s.1) :: s.2)
  | .inr n, s => (1, (.inr n, s.1) :: s.2)

def uStepTag : PTag → UState → UState
  | .inl false, s =>
      if UData.eq s.1 UData.one then
        match s.2 with
        | (.inr n, d1) :: rest => (UData.mul (decodeNat n) d1, rest)
        | _ => (UData.one, (.inl false, s.1) :: s.2)
      else (UData.one, (.inl false, s.1) :: s.2)
  | .inl true, s =>
      if UData.eq s.1 UData.one then
        match s.2 with
        | (.inr n, d1) :: rest => (UData.one, (.inr (n + 1), d1) :: rest)
        | _ => (UData.one, (.inl true, s.1) :: s.2)
      else (UData.one, (.inl true, s.1) :: s.2)
  | .inr n, s => (UData.one, (.inr n, s.1) :: s.2)

theorem uStateToPState_uPrependElem (d : UData) (s : UState) :
    uStateToPState (uPrependElem d s) = pPrependElem (UData.toPElem d) (uStateToPState s) := by
  simp [uStateToPState, uPrependElem, pPrependElem]

theorem uStateToPState_uStepTag (t : PTag) (s : UState) :
    uStateToPState (uStepTag t s) = pStepTag t (uStateToPState s) := by
  rcases s with ⟨d0, rest⟩
  have h1 : UData.eq d0 UData.one = decide (UData.toPElem d0 = 1) := by
    rw [Bool.eq_iff_iff, UData.eq_correct, UData.toPElem_one, decide_eq_true_eq]
  rcases t with (⟨⟩ | ⟨⟩) | n
  · simp only [uStepTag, pStepTag, uStateToPState, h1]
    by_cases hd0 : UData.toPElem d0 = 1
    · simp only [hd0, decide_true, ↓reduceIte]
      cases rest with
      | nil => simp [uStateToPState, hd0]
      | cons x rest' =>
        rcases x with ⟨(⟨⟩ | ⟨⟩) | m, d1⟩ <;> simp [uStateToPState, hd0]
    · simp [hd0, uStateToPState]
  · simp only [uStepTag, pStepTag, uStateToPState, h1]
    by_cases hd0 : UData.toPElem d0 = 1
    · simp only [hd0, decide_true, ↓reduceIte]
      cases rest with
      | nil => simp [uStateToPState, hd0]
      | cons x rest' =>
        rcases x with ⟨(⟨⟩ | ⟨⟩) | m, d1⟩ <;> simp [uStateToPState, hd0]
    · simp [hd0, uStateToPState]
  · simp [uStepTag, pStepTag, uStateToPState]

def pEvalList (l : List (PTag × PElem)) (s : PState) : PState :=
  l.foldr (fun x acc => pStepTag x.1 (pPrependElem x.2 acc)) s

def pEvalState (u s : PState) : PState :=
  pPrependElem u.1 (pEvalList u.2 s)

@[simp] theorem pPrependElem_one (s : PState) : pPrependElem 1 s = s := by
  cases s; simp [pPrependElem]

@[simp] theorem pEvalState_pPrependElem (p : PElem) (u s : PState) :
    pEvalState (pPrependElem p u) s = pPrependElem p (pEvalState u s) := by
  simp [pEvalState, pPrependElem, mul_assoc]

@[simp] theorem pEvalState_pStepTag (t : PTag) (u s : PState) :
    pEvalState (pStepTag t u) s = pStepTag t (pEvalState u s) := by
  rcases u with ⟨p0, rest⟩
  rcases t with (⟨⟩ | ⟨⟩) | n
  · by_cases hp0 : p0 = 1
    · subst hp0
      cases rest with
      | nil => simp [pStepTag, pEvalState, pEvalList, pPrependElem]
      | cons x rest' =>
        rcases x with ⟨(⟨⟩ | ⟨⟩) | m, p1⟩ <;>
          simp [pStepTag, pEvalState, pEvalList, pPrependElem, mul_assoc]
    · rw [pStepTag, if_neg hp0]
      simp only [pEvalState, pEvalList, List.foldr_cons, pPrependElem_one]
  · by_cases hp0 : p0 = 1
    · subst hp0
      cases rest with
      | nil => simp [pStepTag, pEvalState, pEvalList, pPrependElem]
      | cons x rest' =>
        rcases x with ⟨(⟨⟩ | ⟨⟩) | m, p1⟩ <;>
          simp [pStepTag, pEvalState, pEvalList, pPrependElem]
    · rw [pStepTag, if_neg hp0]
      simp only [pEvalState, pEvalList, List.foldr_cons, pPrependElem_one]
  · simp [pStepTag, pEvalState, pEvalList, pPrependElem]

abbrev Letter := Fin 6

def letterTag (i : Letter) : PTag :=
  if i = 0 then .inl false else if i = 2 then .inr 0 else .inl true

def pEvalWord (w : List Letter) (s : PState) : PState :=
  w.foldr (fun i acc => pStepTag (letterTag i) acc) s

def uEvalWord (w : List Letter) (s : UState) : UState :=
  w.foldr (fun i acc => uStepTag (letterTag i) acc) s

def pValue (w : List Letter) : PState := pEvalWord w (1, [])
def uEvaluate (w : List Letter) : UState := uEvalWord w (UData.one, [])

theorem uStateToPState_uEvalWord (w : List Letter) (s : UState) :
    uStateToPState (uEvalWord w s) = pEvalWord w (uStateToPState s) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change uStateToPState (uStepTag (letterTag i) (uEvalWord w s)) =
      pStepTag (letterTag i) (pEvalWord w (uStateToPState s))
    rw [uStateToPState_uStepTag, ih]

theorem uStateToPState_uEvaluate (w : List Letter) :
    uStateToPState (uEvaluate w) = pValue w := by
  simpa [uEvaluate, pValue, uStateToPState] using uStateToPState_uEvalWord w (UData.one, [])

theorem pEvalState_pValue (w : List Letter) (s : PState) :
    pEvalState (pValue w) s = pEvalWord w s := by
  induction w with
  | nil => simp [pValue, pEvalWord, pEvalState, pEvalList, pPrependElem]
  | cons i w ih =>
    simp only [pValue, pEvalWord, List.foldr_cons] at ih ⊢
    rw [pEvalState_pStepTag, ih]

@[simp] theorem pEvalWord_append (u v : List Letter) (s : PState) :
    pEvalWord (u ++ v) s = pEvalWord u (pEvalWord v s) := by
  simp [pEvalWord, List.foldr_append]

theorem pValue_append (u v : List Letter) :
    pValue (u ++ v) = pEvalState (pValue u) (pValue v) := by
  rw [pValue, pEvalWord_append, ← pEvalState_pValue]
  rfl

theorem pValue_context {u v : List Letter} (h : pValue u = pValue v) (a b : List Letter) :
    pValue (a ++ u ++ b) = pValue (a ++ v ++ b) := by
  simp only [pValue_append, h]

def encodePElem (p : PElem) : List Letter :=
  [0] ++ List.replicate (Encodable.encode (UData.ofPElem p)) 1 ++ [2]

theorem pEvalWord_replicate_one (n m : ℕ) (p1 : PElem) (rest : List (PTag × PElem)) :
    pEvalWord (List.replicate n 1) (1, (.inr m, p1) :: rest) = (1, (.inr (n + m), p1) :: rest) := by
  induction n with
  | zero => simp [pEvalWord]
  | succ n ih =>
    rw [List.replicate_succ, pEvalWord, List.foldr_cons]
    change pStepTag (letterTag 1) (pEvalWord (List.replicate n 1) (1, (.inr m, p1) :: rest)) = _
    rw [ih]
    have htag : letterTag 1 = .inl true := rfl
    rw [htag]
    simp only [pStepTag, ↓reduceIte]
    rw [Nat.succ_add]

@[simp] theorem pValue_nil : pValue [] = (1, []) := rfl

@[simp] theorem pValue_encodePElem (p : PElem) : pValue (encodePElem p) = (p, []) := by
  simp only [encodePElem, pValue, pEvalWord, List.append_assoc, List.singleton_append,
    List.foldr_cons, List.foldr_append, List.foldr_nil]
  have h2 : pStepTag (letterTag 2) (1, []) = (1, [(.inr 0, 1)]) := rfl
  rw [h2]
  change pStepTag (letterTag 0) (pEvalWord (List.replicate (Encodable.encode (UData.ofPElem p)) 1) (1, [(.inr 0, 1)])) = (p, [])
  rw [pEvalWord_replicate_one, Nat.add_zero]
  have h0 : letterTag 0 = .inl false := rfl
  rw [h0]
  simp [pStepTag]

theorem pValue_encodePElem_one : pValue (encodePElem 1) = pValue [] := by
  rw [pValue_encodePElem, pValue_nil]

theorem pValue_encodePElem_mul (p1 p2 : PElem) :
    pValue (encodePElem (p1 * p2)) = pValue (encodePElem p1 ++ encodePElem p2) := by
  rw [pValue_append, pValue_encodePElem, pValue_encodePElem, pValue_encodePElem]
  simp [pEvalState, pEvalList, pPrependElem]

theorem pValue_encodePElem_injective : Function.Injective (fun p => pValue (encodePElem p)) := by
  intro p1 p2 h
  simpa [pValue_encodePElem] using h

def uListEqStep (st : Bool ⊕ List (PTag × UData)) (x : PTag × UData) : Bool ⊕ List (PTag × UData) :=
  match st with
  | .inl b => .inl b
  | .inr [] => .inl false
  | .inr (y :: v) => if decide (x.1 = y.1) && UData.eq x.2 y.2 then .inr v else .inl false

def uListEqFinish : Bool ⊕ List (PTag × UData) → Bool := Sum.elim id List.isEmpty

def uListEq (u v : List (PTag × UData)) : Bool :=
  uListEqFinish (u.foldl uListEqStep (.inr v))

theorem uListEq_fold (u : List (PTag × UData)) (st : Bool ⊕ List (PTag × UData)) :
    uListEqFinish (u.foldl uListEqStep st) =
      st.elim id (fun v => decide (u.map (fun x => (x.1, UData.toPElem x.2)) = v.map (fun x => (x.1, UData.toPElem x.2)))) := by
  induction u generalizing st with
  | nil =>
    cases st with
    | inl b => rfl
    | inr v => cases v <;> rfl
  | cons x u ih =>
    rw [List.foldl_cons, ih]
    cases st with
    | inl b => rfl
    | inr v =>
      cases v with
      | nil => rfl
      | cons y v =>
        simp only [uListEqStep, Sum.elim_inr, List.map_cons, List.cons.injEq, Prod.mk.injEq]
        by_cases h1 : x.1 = y.1
        · by_cases h2 : UData.eq x.2 y.2 = true
          · have h2' : UData.toPElem x.2 = UData.toPElem y.2 := (UData.eq_correct _ _).mp h2
            simp [h1, h2, h2']
          · have h2' : UData.toPElem x.2 ≠ UData.toPElem y.2 := by
              intro hc; exact h2 ((UData.eq_correct _ _).mpr hc)
            simp [h1, h2, h2']
        · simp [h1]

theorem uListEq_correct (u v : List (PTag × UData)) :
    uListEq u v = true ↔ u.map (fun x => (x.1, UData.toPElem x.2)) = v.map (fun x => (x.1, UData.toPElem x.2)) := by
  rw [uListEq, uListEq_fold, Sum.elim_inr, decide_eq_true_eq]

def uStateEq (u v : UState) : Bool :=
  UData.eq u.1 v.1 && uListEq u.2 v.2

theorem uStateEq_correct (u v : UState) :
    uStateEq u v = true ↔ uStateToPState u = uStateToPState v := by
  simp only [uStateEq, Bool.and_eq_true, UData.eq_correct, uListEq_correct, uStateToPState, Prod.mk.injEq]

theorem primrec_uPrependElem : Primrec₂ uPrependElem :=
  ((UData.primrec_mul.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.snd.comp Primrec.snd)).to₂

abbrev UX := PTag × UState
abbrev UY := UX × ((PTag × UData) × List (PTag × UData))
instance instPrimcodableUX : Primcodable UX := inferInstance
instance instPrimcodableUY : Primcodable UY := inferInstance

theorem primrec_uStepTag : Primrec₂ uStepTag := by
  let X := UX
  have hs : Primrec (fun x : X => x.2) := Primrec.snd
  have hd0 : Primrec (fun x : X => x.2.1) := Primrec.fst.comp hs
  have hrest : Primrec (fun x : X => x.2.2) := Primrec.snd.comp hs
  have hcond : Primrec (fun x : X => UData.eq x.2.1 UData.one) :=
    UData.primrec_eq.comp hd0 (Primrec.const UData.one)
  have hpush (t : X → PTag) (ht : Primrec t) : Primrec (fun x : X =>
      (UData.one, (t x, x.2.1) :: x.2.2)) :=
    (Primrec.const UData.one).pair (Primrec.list_cons.comp (ht.pair hd0) hrest)
  have hfalse_cons : Primrec₂ (fun (x : X) (p : (PTag × UData) × List (PTag × UData)) =>
      match p.1.1 with
      | .inl _ => (UData.one, ((Sum.inl false : PTag), x.2.1) :: x.2.2)
      | .inr n => (UData.mul (decodeNat n) p.1.2, p.2)) := by
    let Y := UY
    have htag : Primrec (fun y : Y => y.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
    have hd1 : Primrec (fun y : Y => y.2.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have hr' : Primrec (fun y : Y => y.2.2) := Primrec.snd.comp Primrec.snd
    have hinl : Primrec₂ (fun (y : Y) (_ : Bool) =>
        (UData.one, ((Sum.inl false : PTag), y.1.2.1) :: y.1.2.2)) :=
      ((hpush (fun _ => Sum.inl false) (Primrec.const (Sum.inl false : PTag))).comp
        (Primrec.fst.comp Primrec.fst)).to₂
    have hinr : Primrec₂ (fun (y : Y) (n : ℕ) =>
        (UData.mul (decodeNat n) y.2.1.2, y.2.2)) :=
      ((UData.primrec_mul.comp (primrec_decodeNat.comp Primrec.snd)
        (hd1.comp Primrec.fst)).pair (hr'.comp Primrec.fst)).to₂
    exact (Primrec.sumCasesOn htag hinl hinr).to₂.of_eq fun x p => by
      rcases p with ⟨⟨(⟨⟩ | ⟨⟩) | n, d1⟩, r⟩ <;> rfl
  have hfalse : Primrec (fun x : X => uStepTag (.inl false) x.2) := by
    refine (Primrec.cond hcond
      (Primrec.list_casesOn hrest
        (hpush (fun _ => Sum.inl false) (Primrec.const (Sum.inl false : PTag)))
        hfalse_cons)
      (hpush (fun _ => Sum.inl false) (Primrec.const (Sum.inl false : PTag)))).of_eq fun x => by
        rcases x with ⟨_, d0, rest⟩
        dsimp only [uStepTag]
        cases UData.eq d0 UData.one with
        | false => rfl
        | true =>
          cases rest with
          | nil => rfl
          | cons hd tl => rcases hd with ⟨(⟨⟩ | ⟨⟩) | n, d1⟩ <;> rfl
  have htrue_cons : Primrec₂ (fun (x : X) (p : (PTag × UData) × List (PTag × UData)) =>
      match p.1.1 with
      | .inl _ => (UData.one, ((Sum.inl true : PTag), x.2.1) :: x.2.2)
      | .inr n => (UData.one, ((Sum.inr (n + 1) : PTag), p.1.2) :: p.2)) := by
    let Y := UY
    have htag : Primrec (fun y : Y => y.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
    have hd1 : Primrec (fun y : Y => y.2.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have hr' : Primrec (fun y : Y => y.2.2) := Primrec.snd.comp Primrec.snd
    have hinl : Primrec₂ (fun (y : Y) (_ : Bool) =>
        (UData.one, ((Sum.inl true : PTag), y.1.2.1) :: y.1.2.2)) :=
      ((hpush (fun _ => Sum.inl true) (Primrec.const (Sum.inl true : PTag))).comp
        (Primrec.fst.comp Primrec.fst)).to₂
    have hinr : Primrec₂ (fun (y : Y) (n : ℕ) =>
        (UData.one, ((Sum.inr (n + 1) : PTag), y.2.1.2) :: y.2.2)) :=
      ((Primrec.const UData.one).pair (Primrec.list_cons.comp
        ((Primrec.sumInr.comp (Primrec.succ.comp Primrec.snd)).pair (hd1.comp Primrec.fst))
        (hr'.comp Primrec.fst))).to₂
    exact (Primrec.sumCasesOn htag hinl hinr).to₂.of_eq fun x p => by
      rcases p with ⟨⟨(⟨⟩ | ⟨⟩) | n, d1⟩, r⟩ <;> rfl
  have htrue : Primrec (fun x : X => uStepTag (.inl true) x.2) := by
    refine (Primrec.cond hcond
      (Primrec.list_casesOn hrest
        (hpush (fun _ => Sum.inl true) (Primrec.const (Sum.inl true : PTag)))
        htrue_cons)
      (hpush (fun _ => Sum.inl true) (Primrec.const (Sum.inl true : PTag)))).of_eq fun x => by
        rcases x with ⟨_, d0, rest⟩
        dsimp only [uStepTag]
        cases UData.eq d0 UData.one with
        | false => rfl
        | true =>
          cases rest with
          | nil => rfl
          | cons hd tl => rcases hd with ⟨(⟨⟩ | ⟨⟩) | n, d1⟩ <;> rfl
  have hinl_top : Primrec₂ (fun (x : X) (b : Bool) => uStepTag (.inl b) x.2) := by
    refine (Primrec.cond Primrec.snd (htrue.comp Primrec.fst) (hfalse.comp Primrec.fst)).to₂.of_eq ?_
    intro x b; cases b <;> rfl
  have hinr_top : Primrec₂ (fun (x : X) (n : ℕ) => uStepTag (.inr n) x.2) :=
    ((Primrec.const UData.one).pair (Primrec.list_cons.comp
      ((Primrec.sumInr.comp Primrec.snd).pair (hd0.comp Primrec.fst))
      (hrest.comp Primrec.fst))).to₂
  exact (Primrec.sumCasesOn Primrec.fst hinl_top hinr_top).to₂.of_eq fun t s => by
    cases t <;> rfl

theorem primrec_uEvaluate : Primrec uEvaluate :=
  Primrec.list_foldr Primrec.id (Primrec.const (UData.one, []))
    (primrec_uStepTag.comp ((Primrec.dom_finite letterTag).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

abbrev UListSt := Bool ⊕ List (PTag × UData)
abbrev UListP := UListSt × (PTag × UData)
abbrev UListQ := (UListP × List (PTag × UData)) × ((PTag × UData) × List (PTag × UData))
instance instPrimcodableUListSt : Primcodable UListSt := inferInstance
instance instPrimcodableUListP : Primcodable UListP := inferInstance
instance instPrimcodableUListQ : Primcodable UListQ := inferInstance

theorem primrec_listIsEmpty {α : Type*} [Primcodable α] : Primrec (@List.isEmpty α) :=
  (Primrec.list_casesOn Primrec.id (Primrec.const true) (Primrec.const false).to₂).of_eq fun l => by
    cases l <;> rfl

theorem primrec_uListEq : Primrec₂ uListEq := by
  have hinr : Primrec₂ (fun (p : UListP)
      (v : List (PTag × UData)) =>
      match v with
      | [] => (Sum.inl false : UListSt)
      | y :: v => if decide (p.2.1 = y.1) && UData.eq p.2.2 y.2 then .inr v else .inl false) := by
    have hp : Primrec (fun q : UListQ => q.1.1) := Primrec.fst.comp Primrec.fst
    have hcond : Primrec (fun q : UListQ =>
        decide (q.1.1.2.1 = q.2.1.1) && UData.eq q.1.1.2.2 q.2.1.2) :=
      Primrec.and.comp
        (Primrec.eq.decide.comp (Primrec.fst.comp (Primrec.snd.comp hp))
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (UData.primrec_eq.comp (Primrec.snd.comp (Primrec.snd.comp hp))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
    exact (Primrec.list_casesOn Primrec.snd (Primrec.const (Sum.inl false : UListSt))
      (Primrec.cond hcond
        (Primrec.sumInr.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.const (Sum.inl false : UListSt))).to₂).to₂.of_eq fun p v => by
          cases v with
          | nil => rfl
          | cons y v =>
            dsimp only
            cases decide (p.2.1 = y.1) && UData.eq p.2.2 y.2 <;> rfl
  have hstep : Primrec₂ uListEqStep :=
    (Primrec.sumCasesOn Primrec.fst (Primrec.sumInl.comp Primrec.snd).to₂ hinr).to₂.of_eq fun st x => by
      cases st with
      | inl b => rfl
      | inr v => cases v <;> rfl
  have hfin : Primrec uListEqFinish :=
    (Primrec.sumCasesOn Primrec.id Primrec.snd.to₂
      (primrec_listIsEmpty.comp Primrec.snd).to₂).of_eq fun s => by cases s <;> rfl
  exact (hfin.comp (Primrec.list_foldl Primrec.fst (Primrec.sumInr.comp Primrec.snd)
    (hstep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)).to₂

theorem primrec_uStateEq : Primrec₂ uStateEq :=
  (Primrec.and.comp
    (UData.primrec_eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (primrec_uListEq.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂

theorem primrec_pValue_eq : PrimrecPred (fun p : List Letter × List Letter => pValue p.1 = pValue p.2) := by
  have hh : PrimrecPred (fun p : List Letter × List Letter => uStateEq (uEvaluate p.1) (uEvaluate p.2) = true) :=
    Primrec.eq.comp (primrec_uStateEq.comp (primrec_uEvaluate.comp Primrec.fst)
      (primrec_uEvaluate.comp Primrec.snd)) (Primrec.const true)
  exact hh.of_eq fun p => by
    rw [uStateEq_correct, uStateToPState_uEvaluate, uStateToPState_uEvaluate]

def pCon : Con (FreeMonoid Letter) where
  r u v := pValue u.toList = pValue v.toList
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  mul' := by
    intro u v x y huv hxy
    change pValue (u.toList ++ x.toList) = pValue (v.toList ++ y.toList)
    rw [pValue_append, pValue_append, huv, hxy]

abbrev pMonoid := pCon.Quotient

def pWordValue (w : List Letter) : pMonoid := pCon.mk' (FreeMonoid.ofList w)

@[simp] theorem pWordValue_nil : pWordValue [] = 1 := rfl

@[simp] theorem pWordValue_append (u v : List Letter) :
    pWordValue (u ++ v) = pWordValue u * pWordValue v := rfl

theorem pWordValue_surjective : Function.Surjective pWordValue := by
  intro x
  induction x using Con.induction_on with
  | H w => exact ⟨w.toList, rfl⟩

def embedP : PElem →* pMonoid where
  toFun p := pWordValue (encodePElem p)
  map_one' := (pCon.eq).mpr pValue_encodePElem_one
  map_mul' p1 p2 := (pCon.eq).mpr (pValue_encodePElem_mul p1 p2)

theorem embedP_injective : Function.Injective embedP := by
  intro p1 p2 h
  exact pValue_encodePElem_injective ((pCon.eq).mp h)


theorem pWordValue_eq_iff (u v : List Letter) :
    pWordValue u = pWordValue v ↔ pValue u = pValue v :=
  pCon.eq

noncomputable def testedClass : List Letter → List Letter :=
  Bootstrap.Canonical.least (r := fun a b : Letter => a < b) wellFounded_lt pValue

theorem testedClass_eq_iff (u v : List Letter) :
    testedClass u = testedClass v ↔ pValue u = pValue v := by
  classical
  exact Bootstrap.Canonical.least_eq_iff _ _

theorem testedClass_context {u v : List Letter} (h : testedClass u = testedClass v) (a b : List Letter) :
    testedClass (a ++ u ++ b) = testedClass (a ++ v ++ b) :=
  (testedClass_eq_iff _ _).mpr (pValue_context ((testedClass_eq_iff _ _).mp h) a b)

theorem computable_testedClass : Computable testedClass := by
  classical
  apply Bootstrap.Canonical.computable_least
  · exact Bootstrap.Search.primrec_shortlex ⟨inferInstance, Primrec.dom_finite _⟩
  · exact ⟨inferInstance, primrec_pValue_eq.decide.to_comp⟩

end OAI.FiniteAlgebraicEnvelopes.PElemCoding

namespace OAI

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H B T K : Type*}

namespace Literal
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path

theorem rule_length (table : Table H B T) (m : H → K) {u v : List (Letter (B × T) K)}
    (h : Rule table m u v) : u.length = 2 ∧ v.length = 2 := by
  cases h with
  | cell q b t i h =>
    cases hd : table.direction q <;> cases hc : i.cross <;>
      simp [headed, inLeft, inRight, outLeft, outRight]
  | left => simp
  | right => simp

end Literal
end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Word
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

theorem ordinary_length {u v : List (Letter S Γ Q)} (h : Ordinary A M u v) :
    u.length ≤ 4 ∧ v.length ≤ 4 := by
  cases h with
  | internal h => obtain ⟨h₁, h₂⟩ := Scan.Literal.rule_length _ _ h; omega
  | clean c => cases he : Cleanup.emit c <;> simp
  | raw => simp
  | merge => simp
  | quota => simp
  | entry => simp
  | finish => simp

theorem rule_length {u v : List (Letter S Γ Q)} (h : Rule A M u v) :
    u.length ≤ 4 ∧ v.length ≤ 4 := by
  cases h with
  | ordinary h => exact ordinary_length A M h
  | zero h => cases h; simp
  | exit => simp

theorem rules_finite [Fintype S] [Fintype Γ] [Fintype Q] :
    {p : List (Letter S Γ Q) × List (Letter S Γ Q) | Rule A M p.1 p.2}.Finite := by
  apply ((List.finite_length_le (Letter S Γ Q) 4).prod
    (List.finite_length_le (Letter S Γ Q) 4)).subset
  rintro ⟨u, v⟩ h
  exact rule_length A M h

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Bootstrap.Quotient
open Relation
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n, GoodTable (r := r) T n)
  (stable : ∀ k n, k ≤ n → ∀ rk ∈ T k, ∀ rn ∈ T n, Selectors.BoundedEq rk rn k)
include wf good stable

theorem representative_injective : Function.Injective (representative T) := by
  intro x y he
  rw [← present_representative T wf good stable x, ← present_representative T wf good stable y, he]

theorem present_nil_ne_zero (z : S)
    (hshort : ∀ n rs, rs ∈ T n → ∀ p ∈ rs, 1 < p.1.length) :
    (1 : Mon T) ≠ present T [z] := by
  obtain ⟨r0, hr0, _⟩ := good 0
  obtain ⟨r1, hr1, _⟩ := good 1
  have h0 : normal T [] = [] := normal_eq_self T wf good stable hr0
    (irreducible_of_short (fun p hp => by simpa using Nat.lt_trans Nat.zero_lt_one (hshort 0 r0 hr0 p hp)))
  have h1 : normal T [z] = [z] := normal_eq_self T wf good stable hr1
    (irreducible_of_short (fun p hp => hshort 1 r1 hr1 p hp))
  intro he
  have hh := (present_eq_iff T wf good stable [] [z]).mp he
  rw [h0, h1] at hh
  simp at hh

variable {Γ Q : Type*} [Fintype S] [Fintype Γ] [Fintype Q]
  [DecidableEq Γ] [DecidableEq Q] [LinearOrder (Compiler.Control.Sector S Γ Q)]
variable (A : Compiler.Simulator.Alphabet S Γ) (M : Compiler.Simulator.Machine Q Γ)
variable (hdecode : ∀ g a, A.output g = some a → g = A.input a)
variable (hr : Compiler.Word.Realizes A M (tableNormal T))
include hdecode hr

theorem rawMap_injective : Function.Injective (rawMap T wf good stable A M hdecode hr) := by
  intro x y hxy
  have hn := (Compiler.Word.present_eq_iff_normal A M hdecode
    (fun n => (budget T wf good stable n).totalize)
    (fun n => Compiler.Word.Realizes.computesAt A M hr (budget T wf good stable n)) _ _).mp hxy
  simp only [Compiler.Word.normal_raw] at hn
  have he := congrArg Compiler.Word.rawLetters hn
  simp only [Compiler.Word.rawLetters_raw] at he
  exact representative_injective T wf good stable he

theorem rawMap_ne_zero (x : Mon T) :
    rawMap T wf good stable A M hdecode hr x ≠ Compiler.Word.present A M [.zero] := by
  intro hx
  have hn := (Compiler.Word.present_eq_iff_normal A M hdecode
    (fun n => (budget T wf good stable n).totalize)
    (fun n => Compiler.Word.Realizes.computesAt A M hr (budget T wf good stable n))
    (Compiler.Word.raw A.blank (representative T x)) [.zero]).mp hx
  simp only [Compiler.Word.normal_raw, Compiler.Word.normal_omega] at hn
  simp [Compiler.Word.raw, Compiler.Word.encode, Compiler.Surface.raw, Compiler.Scan.literal,
    Compiler.Path.encode, Compiler.Path.headed] at hn

theorem rawMap_ne_one (x : Mon T) :
    rawMap T wf good stable A M hdecode hr x ≠ 1 := by
  intro hx
  have hn := (Compiler.Word.present_eq_iff_normal A M hdecode
    (fun n => (budget T wf good stable n).totalize)
    (fun n => Compiler.Word.Realizes.computesAt A M hr (budget T wf good stable n))
    (Compiler.Word.raw A.blank (representative T x)) []).mp hx
  simp only [Compiler.Word.normal_raw, Compiler.Word.normal_nil] at hn
  simp [Compiler.Word.raw, Compiler.Word.encode, Compiler.Surface.raw, Compiler.Scan.literal,
    Compiler.Path.encode, Compiler.Path.headed] at hn

omit wf good stable hdecode hr in
theorem descendCode_injective {A_1 M_1 : Type*} [Monoid M_1]
    {T_1 : ℕ → Part (List (List S × List S))} (C : BlockCode A_1 S)
    (e : FreeMonoid A_1 →* M_1) (he : Function.Surjective e)
    (hc : ∀ u v : List A_1, present T_1 (C.encode u) = present T_1 (C.encode v) ↔
      e (FreeMonoid.ofList u) = e (FreeMonoid.ofList v)) :
    Function.Injective (descendCode C e he hc) := by
  intro x y hxy
  rw [← (he x).choose_spec, ← (he y).choose_spec]
  exact (hc (he x).choose.toList (he y).choose.toList).mp hxy

end FiniteAlgebraicEnvelopes.Bootstrap.Quotient

namespace FiniteAlgebraicEnvelopes.Bootstrap.Tested
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec

variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable T] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool × Γ))

noncomputable def pFamily (f : ℕ × List T → Part (List T)) (n : ℕ) (w : List (Y T Γ Q)) :
    Part (Option (Class T Γ Q)) :=
  (codedNormal A M p B f (n, Projection.left w)).map
    (fun o => combine (o, PElemCoding.testedClass (Projection.right w)))

theorem partrec_pFamily {f : ℕ × List T → Part (List T)} (hf : Partrec f) :
    Partrec₂ (pFamily A M p B f) := by
  have hh : Partrec (fun x : ℕ × List (Y T Γ Q) =>
      codedNormal A M p B f (x.1, Projection.left x.2)) :=
    (partrec_codedNormal A M p B hf).comp
    (Computable.fst.pair ((Projection.primrec_left (A := X T Γ Q) (B := PartialAffine.Letter)).to_comp.comp Computable.snd))
  exact (hh.map (primrec_combine.to_comp.comp
    (Computable.snd.pair (PElemCoding.computable_testedClass.comp
      (Projection.primrec_right.to_comp.comp (Computable.snd.comp Computable.fst))))).to₂).to₂

end FiniteAlgebraicEnvelopes.Bootstrap.Tested

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec

variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

local instance instDecidableEqXSigma_p : DecidableEq (Tested.X Sigma Γ Q) := inferInstance
local instance instDecidableEqY_p : DecidableEq (Y (Γ := Γ) (Q := Q)) := inferInstance
local instance instFintypeLetterSigmaProdBoolState_p (n : ℕ) : Fintype (Word.Letter Sigma (Bool × Γ) (ParameterMachine.State Q n)) := inferInstance
local instance instDecidableEqLetterSigmaProdBoolState_p (n : ℕ) : DecidableEq (Word.Letter Sigma (Bool × Γ) (ParameterMachine.State Q n)) := inferInstance
local instance instDecidableEqFiniteY_p (n : ℕ) : DecidableEq (FiniteY (Γ := Γ) (Q := Q) n) := inferInstance
local instance instLinearOrderSectorSigmaProdBoolState_p (n : ℕ) : LinearOrder (Compiler.Control.Sector Sigma (Bool × Γ) (ParameterMachine.State Q n)) :=
  finiteOrder (T := Sigma) (Γ := Γ) (Q := Q) n

noncomputable def pTestT (n : ℕ) : List (Y (Γ := Γ) (Q := Q)) → Part (Option (Tested.Class Sigma Γ Q)) :=
  Tested.pFamily A M (.inr ()) (UniversalMachine.restrict (ParameterMachine.alphabet A))
    (fun p => raw p.1 p.2) n

noncomputable def pTables (n : ℕ) : ℕ → Part (List (List Sigma × List Sigma)) :=
  Uniform.tables markers (yLetters n) (zLetters k) (codeT (k := k) n) (codeG (Γ := Γ) (Q := Q) n)
    (Rank.less (yLetters n)) (Rank.less (zLetters k))
    (width (Γ := Γ) (Q := Q) k n + 1) (width (Γ := Γ) (Q := Q) k n + 1) (pTestT A M n) (testG s n)

noncomputable def pFiniteTest (n : ℕ) (w : List (FiniteY (Γ := Γ) (Q := Q) n)) :=
  pTestT A M n (w.map (includeY n))

noncomputable def pFiniteTables (n : ℕ) :=
  Uniform.fullTables (r := relT n) (s := relG k) markers (finiteCodeT (Γ := Γ) (Q := Q) k n) (finiteCodeG (Γ := Γ) (Q := Q) k n)
    (finiteLetters n) (zLetters k) (pFiniteTest A M n) (testG s n)

omit [Primcodable Γ] in
theorem pTables_eq_finite (n : ℕ) : pTables s A M n = pFiniteTables s A M n := by
  have hT (j : ℕ) : Uniform.compute (yLetters n) (codeT (k := k) n) (Rank.less (yLetters n)) markers.zero (pTestT A M n) j =
      Uniform.compute (finiteLetters n) (finiteCodeT (Γ := Γ) (Q := Q) k n).encode (fun u v => decide (List.Shortlex (relT n) u v))
        markers.zero (pFiniteTest A M n) j := by
    simpa only [map_finiteLetters] using Uniform.compute_map (includeY n) _ _ (lessT_map n) _ _ (fun w => (finiteCodeT_encode k n w).symm)
      markers.zero (finiteLetters n) (pFiniteTest A M n) (pTestT A M n) (fun _ => rfl) j
  have hG : codeG (Γ := Γ) (Q := Q) (k := k) n = (finiteCodeG (Γ := Γ) (Q := Q) k n).encode :=
    funext (fun w => (finiteCodeG_encode k n w).symm)
  have hlG : Rank.less (zLetters k) = (fun u v => decide (List.Shortlex (relG k) u v)) :=
    funext (fun u => funext (lessG_eq k u))
  funext j
  simp only [pTables, pFiniteTables, Uniform.fullTables, Uniform.tables, Uniform.bases, hT, hG, hlG]
  rfl

omit [Primcodable Γ] in
theorem pStable (n : ℕ) {a b : ℕ} (hab : a ≤ b) {ra rb : List (List Sigma × List Sigma)}
    (ha : ra ∈ pTables s A M n a) (hb : rb ∈ pTables s A M n b) : Selectors.BoundedEq ra rb a := by
  rw [pTables_eq_finite] at ha hb
  exact Uniform.stable_support markers (finiteCodeT (Γ := Γ) (Q := Q) k n) (finiteCodeG (Γ := Γ) (Q := Q) k n) (wf_relT n) (wf_relG k)
    (finiteLetters n) (zLetters k) (mem_finiteLetters n) (by intro x; simp [zLetters, Static.letters])
    (pFiniteTest A M n) (testG s n) hab ha hb

omit [Primcodable Γ] in
theorem pGood_of_tests (n j : ℕ)
    (hf : ∀ w : List (FiniteY (Γ := Γ) (Q := Q) n), w.length ≤ j / (width (Γ := Γ) (Q := Q) k n + 1) → (pFiniteTest A M n w).Dom)
    (hf0 : Search.value (pFiniteTest A M n) [] ≠ none)
    (hfc : Static.Contextual (Search.value (pFiniteTest A M n)) (j / (width (Γ := Γ) (Q := Q) k n + 1)))
    (hfi : Static.ZeroIdeal (Search.value (pFiniteTest A M n)) (j / (width (Γ := Γ) (Q := Q) k n + 1)))
    (hg0 : Search.value (testG s n) [] ≠ none)
    (hgc : Static.Contextual (Search.value (testG s n)) (j / (width (Γ := Γ) (Q := Q) k n + 1)))
    (hgi : Static.ZeroIdeal (Search.value (testG s n)) (j / (width (Γ := Γ) (Q := Q) k n + 1))) :
    GoodTable (r := fun u v : Sigma => u < v) (pTables s A M n) j := by
  rw [pTables_eq_finite]
  apply Uniform.good_support markers (finiteCodeT (Γ := Γ) (Q := Q) k n) (finiteCodeG (Γ := Γ) (Q := Q) k n) (wf_relT n) (wf_relG k)
    (finiteLetters n) (zLetters k) (mem_finiteLetters n) (by intro x; simp [zLetters, Static.letters])
    (pFiniteTest A M n) (testG s n)
  · change 1 < width (Γ := Γ) (Q := Q) k n + 1; unfold width; omega
  · change 1 < width (Γ := Γ) (Q := Q) k n + 1; unfold width; omega
  · exact codeT_order k n
  · exact codeG_order k n
  · exact codeT_avoid k n
  · exact codeG_avoid k n
  · exact codes_disjoint k n
  · exact hf
  · intro w hw; trivial
  · exact hf0
  · exact hg0
  · exact hfc
  · exact hfi
  · exact hgc
  · exact hgi

noncomputable def pFiniteClass (n : ℕ) (w : List (FiniteY (Γ := Γ) (Q := Q) n)) :=
  ZeroProduct.test [.zero] (finiteValue A M n) (fun w => PElemCoding.testedClass (Projection.right w)) w

omit [Primcodable Γ] in
theorem pFiniteTest_eq (n j : ℕ) (h : PartialBudget (raw n) (2 * j))
    (w : List (FiniteY (Γ := Γ) (Q := Q) n)) (hw : w.length ≤ j) :
    pFiniteTest A M n w = Part.some (pFiniteClass A M n w) := by
  have hg := (projection_grade n w).trans (Nat.mul_le_mul_left 2 hw)
  simp only [pFiniteTest, pTestT, Tested.pFamily, includeY, Projection.left_map, Projection.right_map, List.map_id]
  rw [codedNormal_map, Word.partialNormal_eq_some _ _ h _ hg]
  simp only [Part.map_some, pFiniteClass, ZeroProduct.test, finiteValue, Tested.combine,
    terminalAlphabet, terminalMachine]
  rfl

omit [Primcodable Γ] in
theorem pFiniteClass_context (n j : ℕ) (h : PartialBudget (raw n) (2 * j))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a, (terminalAlphabet A).output g = some a → g = (terminalAlphabet A).input a) :
    Static.Contextual (pFiniteClass A M n) j := by
  apply ZeroProduct.contextual
  · exact finiteValue_context A M n j h hr hd
  · exact finiteValue_ideal A M n j h hr hd
  · intro a b u v he
    simpa only [Projection.right_append] using PElemCoding.testedClass_context he (Projection.right a) (Projection.right b)

omit [Primcodable Γ] in
theorem pFiniteClass_ideal (n j : ℕ) (h : PartialBudget (raw n) (2 * j))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a, (terminalAlphabet A).output g = some a → g = (terminalAlphabet A).input a) :
    Static.ZeroIdeal (pFiniteClass A M n) j :=
  ZeroProduct.ideal _ _ _ _ (finiteValue_ideal A M n j h hr hd)

omit [Primcodable Γ] in
theorem pFiniteClass_nil (n : ℕ) : pFiniteClass A M n [] ≠ none := by
  simp [pFiniteClass, ZeroProduct.test, finiteValue, Projection.left]

omit [Primcodable Γ] in
theorem pSearch_value_eq (n j : ℕ) (h : PartialBudget (raw n) (2 * j))
    (w : List (FiniteY (Γ := Γ) (Q := Q) n)) (hw : w.length ≤ j) :
    Search.value (pFiniteTest A M n) w = pFiniteClass A M n w := by
  have hh := pFiniteTest_eq A M n j h w hw
  have hd : (pFiniteTest A M n w).Dom := by rw [hh]; trivial
  have hm := Search.value_mem hd
  simpa only [hh, Part.mem_some_iff] using hm

omit [Primcodable Γ] in
theorem pTests_bounded (n j : ℕ) (h : PartialBudget (raw n) (2 * j))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a, (terminalAlphabet A).output g = some a → g = (terminalAlphabet A).input a) :
    (∀ w : List (FiniteY (Γ := Γ) (Q := Q) n), w.length ≤ j → (pFiniteTest A M n w).Dom) ∧
      Search.value (pFiniteTest A M n) [] ≠ none ∧
      Static.Contextual (Search.value (pFiniteTest A M n)) j ∧
      Static.ZeroIdeal (Search.value (pFiniteTest A M n)) j := by
  refine ⟨fun w hw => ?_, ?_, ?_, ?_⟩
  · rw [pFiniteTest_eq A M n j h w hw]; trivial
  · rw [pSearch_value_eq A M n j h [] (by simp)]
    exact pFiniteClass_nil A M n
  · intro a b u v hu hv he
    have hul : u.length ≤ j := by simp only [List.length_append] at hu; omega
    have hvl : v.length ≤ j := by simp only [List.length_append] at hv; omega
    rw [pSearch_value_eq A M n j h u hul, pSearch_value_eq A M n j h v hvl] at he
    rw [pSearch_value_eq A M n j h _ hu, pSearch_value_eq A M n j h _ hv]
    exact pFiniteClass_context A M n j h hr hd a b u v hu hv he
  · intro a b u hu he
    have hul : u.length ≤ j := by simp only [List.length_append] at hu; omega
    rw [pSearch_value_eq A M n j h u hul] at he
    rw [pSearch_value_eq A M n j h _ hu]
    exact pFiniteClass_ideal A M n j h hr hd a b u hu he

omit [Primcodable Γ] in
theorem pFiniteTest_nil (n : ℕ) : pFiniteTest A M n [] = Part.some (pFiniteClass A M n []) := by
  simp only [pFiniteTest, pTestT, Tested.pFamily, includeY, List.map_nil, Projection.left]
  have hh := codedNormal_map A M (.inr ()) (terminalAlphabet A) n (fun p => raw p.1 p.2) ([] : List (Word.Letter Sigma (Bool × Γ) (ParameterMachine.State Q n)))
  simp only [List.map_nil, Word.partialNormal_nil, Part.map_some] at hh
  simp only [List.filterMap_nil]
  rw [hh]
  simp [pFiniteClass, ZeroProduct.test, finiteValue, Projection.left, Projection.right, Tested.combine]

omit [Primcodable Γ] in
theorem pFinite_search_nil (n : ℕ) : Search.value (pFiniteTest A M n) [] = pFiniteClass A M n [] := by
  have hd : (pFiniteTest A M n []).Dom := by rw [pFiniteTest_nil]; trivial
  simpa only [pFiniteTest_nil, Part.mem_some_iff] using Search.value_mem hd

omit [Primcodable Γ] in
theorem pTests_zero (n : ℕ) :
    (∀ w : List (FiniteY (Γ := Γ) (Q := Q) n), w.length ≤ 0 → (pFiniteTest A M n w).Dom) ∧
      Search.value (pFiniteTest A M n) [] ≠ none ∧
      Static.Contextual (Search.value (pFiniteTest A M n)) 0 ∧
      Static.ZeroIdeal (Search.value (pFiniteTest A M n)) 0 := by
  refine ⟨?_, ?_, Static.contextual_zero _, Static.zeroIdeal_zero _⟩
  · intro w hw
    have hw : w = [] := by simpa using hw
    subst w
    rw [pFiniteTest_nil]; trivial
  · rw [pFinite_search_nil]
    exact pFiniteClass_nil A M n

theorem partrec_pTestT : Partrec₂ (pTestT A M) :=
  Tested.partrec_pFamily A M (.inr ()) (UniversalMachine.restrict (ParameterMachine.alphabet A)) partrec_raw

theorem partrec_pTables (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => FiniteAlgebraicEnvelopes.evalWord s w = 1)) :
    Partrec₂ (pTables s A M) := by
  have hg : Partrec₂ (testG s) :=
    (Primrec.option_some.to_comp.comp ((WordProblem.computable_testedClass s h).comp Computable.snd)).partrec
  exact Uniform.partrec_tables markers yLetters (fun _ => zLetters k)
    codeT (codeG (Γ := Γ) (Q := Q)) (fun n => Rank.less (yLetters n)) (fun _ => Rank.less (zLetters k))
    (fun n => width (Γ := Γ) (Q := Q) k n + 1) (fun n => width (Γ := Γ) (Q := Q) k n + 1) (pTestT A M) (testG s)
    Tested.primrec_letters (Primrec.const _) primrec_codeT primrec_codeG
    (Rank.primrec_less _ Tested.primrec_letters) (Rank.primrec_less _ (Primrec.const _))
    (Primrec.nat_add.comp primrec_width (Primrec.const 1))
    (Primrec.nat_add.comp primrec_width (Primrec.const 1)) (partrec_pTestT A M) hg

theorem exists_pFixed_point (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => FiniteAlgebraicEnvelopes.evalWord s w = 1)) :
    ∃ n, raw n = tableNormal (pTables s A M n) := by
  have hh := partrec_tableNormal_parameter (partrec_pTables s A M h)
  have hc : Partrec₂ (fun c : Nat.Partrec.Code => tableNormal (pTables s A M (Encodable.encode c))) :=
    hh.comp (Computable.encode.comp Computable.fst) Computable.snd
  obtain ⟨c, hc⟩ := WordProgramming.fixed_point hc
  exact ⟨Encodable.encode c, (raw_encode c).trans hc⟩

omit [Primcodable Γ] in
theorem all_pBudgets (n : ℕ) (fixed : raw n = tableNormal (pTables s A M n))
    (hr : Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a, (terminalAlphabet A).output g = some a → g = (terminalAlphabet A).input a) :
    ∀ j, GoodTable (r := fun a b : Sigma => a < b) (pTables s A M n) j ∧ PartialBudget (raw n) j := by
  apply bootstrap_length_induction (r := fun a b : Sigma => a < b)
    (InvImage.wf Fin.val Nat.lt_wfRel.wf) (pTables s A M n) (raw n) fixed
  · intro j m hjm rk hrk rn hrn
    exact pStable s A M n hjm hrk hrn
  · intro j ih
    have ht :
        (∀ w : List (FiniteY (Γ := Γ) (Q := Q) n), w.length ≤ j / (width (Γ := Γ) (Q := Q) k n + 1) → (pFiniteTest A M n w).Dom) ∧
          Search.value (pFiniteTest A M n) [] ≠ none ∧
          Static.Contextual (Search.value (pFiniteTest A M n)) (j / (width (Γ := Γ) (Q := Q) k n + 1)) ∧
          Static.ZeroIdeal (Search.value (pFiniteTest A M n)) (j / (width (Γ := Γ) (Q := Q) k n + 1)) := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simpa using pTests_zero A M n
      · exact pTests_bounded A M n _ (ih _ (quota_smaller k n j hj)) hr hd
    have hg := group_tests s n (j / (width (Γ := Γ) (Q := Q) k n + 1))
    exact pGood_of_tests s A M n j ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hg.1 hg.2.1 hg.2.2

theorem exists_total_pFixed_point
    (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w = 1))
    (hr : ∀ n, Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n))
    (hd : ∀ g a, (terminalAlphabet A).output g = some a → g = (terminalAlphabet A).input a) :
    ∃ n, raw n = tableNormal (pTables s A M n) ∧
      ∀ j, GoodTable (r := fun a b : Sigma => a < b) (pTables s A M n) j ∧ PartialBudget (raw n) j := by
  obtain ⟨n, hn⟩ := exists_pFixed_point s A M h
  exact ⟨n, hn, all_pBudgets s A M n hn (hr n) hd⟩

noncomputable def pBase (n j : ℕ) : List (List Sigma × List Sigma) :=
  Base.table (finiteCodeT (Γ := Γ) (Q := Q) k n) (finiteCodeG (Γ := Γ) (Q := Q) k n)
    (wf_relT n) (wf_relG k) (Search.value (pFiniteTest A M n)) (Search.value (testG s n)) markers.zero j

omit [Primcodable Γ] in
theorem pTables_members (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs ∈ pTables s A M n j) :
    RulesEq rs (Selectors.process (a := markers) (pBase s A M n j) (Selectors.stages markers.zero) j j) := by
  rw [pTables_eq_finite] at hrs
  exact Uniform.tables_members_support markers (finiteCodeT (Γ := Γ) (Q := Q) k n) (finiteCodeG (Γ := Γ) (Q := Q) k n)
    (wf_relT n) (wf_relG k) (finiteLetters n) (zLetters k) (mem_finiteLetters n)
    (by intro x; simp [zLetters, Static.letters]) (pFiniteTest A M n) (testG s n) hrs

omit [Primcodable Γ] in
theorem pTables_absorb (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs ∈ pTables s A M n j) :
    Absorbs rs markers.zero := by
  have hh := Selectors.process_contains (a := markers) (pBase s A M n j) (Selectors.stages markers.zero) j j
  have hz := Base.absorbs (finiteCodeT (Γ := Γ) (Q := Q) k n) (finiteCodeG (Γ := Γ) (Q := Q) k n)
    (wf_relT n) (wf_relG k) (Search.value (pFiniteTest A M n)) (Search.value (testG s n)) markers.zero j
  intro b
  exact ⟨(pTables_members s A M n j hrs _).mpr (hh _ (hz b).1),
    (pTables_members s A M n j hrs _).mpr (hh _ (hz b).2)⟩

omit [Primcodable Γ] in
theorem pTables_short (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs ∈ pTables s A M n j) :
    ∀ p ∈ rs, 1 < p.1.length := by
  intro p hp
  have hp := (pTables_members s A M n j hrs p).mp hp
  rcases Selectors.process_members hp with hp | ⟨i, hi, hp⟩
  · rcases (Base.mem_table _ _ (wf_relT n) (wf_relG k) _ _ markers.zero).mp hp with hp | hp | hp
    · obtain ⟨b, (he | he), _⟩ := (Base.mem_absorption markers.zero).mp hp <;> rw [he] <;> simp
    · apply Static.table_short _ (wf_relT n) _ _ _ hp
      change 1 < width (Γ := Γ) (Q := Q) k n + 1; unfold width; omega
    · apply Static.table_short _ (wf_relG k) _ _ _ hp
      change 1 < width (Γ := Γ) (Q := Q) k n + 1; unfold width; omega
  · obtain ⟨w, _, he, _⟩ := (Selectors.mem_rules markers).mp hp
    rw [he]
    simp only [Selectors.Markers.wrap, Envelopes.length_frame]
    omega

omit [Primcodable Γ] in
theorem pTables_isolateT (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs ∈ pTables s A M n j) :
    ∀ p ∈ rs, p ∈ Static.table (finiteCodeT (Γ := Γ) (Q := Q) k n) (wf_relT n)
      (Search.value (pFiniteTest A M n)) markers.zero j ∨ ∃ b ∈ p.1, b ∉ (finiteCodeT (Γ := Γ) (Q := Q) k n).Alphabet := by
  intro p hp
  apply Selectors.process_isolate markers _ (wf_relT n) (Search.value (pFiniteTest A M n))
    (fun p hp => Base.isolate_left (finiteCodeT (Γ := Γ) (Q := Q) k n) (finiteCodeG (Γ := Γ) (Q := Q) k n) (wf_relT n) (wf_relG k) (Search.value (pFiniteTest A M n)) (Search.value (testG s n)) markers.zero
      (codeT_avoid (Γ := Γ) (Q := Q) k n _ (by simp)) (codes_disjoint (Γ := Γ) (Q := Q) k n) hp)
    (codeT_avoid (Γ := Γ) (Q := Q) k n _ (by simp)) _ _ _
  exact (pTables_members s A M n j hrs p).mp hp

omit [Primcodable Γ] in
theorem pTables_staticT (n j : ℕ) {rs : List (List Sigma × List Sigma)}
    (hrs : rs ∈ pTables s A M n ((width (Γ := Γ) (Q := Q) k n + 1) * j)) :
    ∀ p ∈ Static.table (finiteCodeT (Γ := Γ) (Q := Q) k n) (wf_relT n)
      (Search.value (pFiniteTest A M n)) markers.zero j, p ∈ rs := by
  intro p hp
  apply (pTables_members s A M n _ hrs p).mpr
  apply Selectors.process_contains
  apply (Base.mem_table _ _ (wf_relT n) (wf_relG k) _ _ markers.zero).mpr
  apply Or.inr; apply Or.inl
  change p ∈ Static.table (finiteCodeT (Γ := Γ) (Q := Q) k n) (wf_relT n)
    (Search.value (pFiniteTest A M n)) markers.zero (((width (Γ := Γ) (Q := Q) k n + 1) * j) / (width (Γ := Γ) (Q := Q) k n + 1))
  simpa using hp

omit [Primcodable Γ] in
theorem pTables_isolateG (n j : ℕ) {rs : List (List Sigma × List Sigma)} (hrs : rs ∈ pTables s A M n j) :
    ∀ p ∈ rs, p ∈ Static.table (finiteCodeG (Γ := Γ) (Q := Q) k n) (wf_relG k)
      (Search.value (testG s n)) markers.zero j ∨ ∃ b ∈ p.1, b ∉ (finiteCodeG (Γ := Γ) (Q := Q) k n).Alphabet := by
  intro p hp
  apply Selectors.process_isolate markers _ (wf_relG k) (Search.value (testG s n)) ?_
    (codeG_avoid (Γ := Γ) (Q := Q) k n _ (by simp)) _ _ _ ((pTables_members s A M n j hrs p).mp hp)
  intro p hp
  rcases (Base.mem_table _ _ (wf_relT n) (wf_relG k) _ _ markers.zero).mp hp with hp | hp | hp
  · obtain ⟨b, hb, _⟩ := (Base.mem_absorption markers.zero).mp hp
    exact Or.inr ⟨markers.zero, by rcases hb with h | h <;> simp [h], codeG_avoid (Γ := Γ) (Q := Q) k n _ (by simp)⟩
  · obtain ⟨hn, hs⟩ := Static.table_support _ (wf_relT n) _ _ hp
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ hn
    exact Or.inr ⟨b, hb, fun hc => Set.disjoint_left.mp (codes_disjoint (Γ := Γ) (Q := Q) k n) (hs b hb) hc⟩
  · exact Or.inl (Static.table_mono _ (wf_relG k) _ _ (Nat.div_le_self j _) hp)

omit [Primcodable Γ] in
theorem pTables_staticG (n j : ℕ) {rs : List (List Sigma × List Sigma)}
    (hrs : rs ∈ pTables s A M n ((width (Γ := Γ) (Q := Q) k n + 1) * j)) :
    ∀ p ∈ Static.table (finiteCodeG (Γ := Γ) (Q := Q) k n) (wf_relG k)
      (Search.value (testG s n)) markers.zero j, p ∈ rs := by
  intro p hp
  apply (pTables_members s A M n _ hrs p).mpr
  apply Selectors.process_contains
  apply (Base.mem_table _ _ (wf_relT n) (wf_relG k) _ _ markers.zero).mpr
  apply Or.inr; apply Or.inr
  change p ∈ Static.table (finiteCodeG (Γ := Γ) (Q := Q) k n) (wf_relG k)
    (Search.value (testG s n)) markers.zero (((width (Γ := Γ) (Q := Q) k n + 1) * j) / (width (Γ := Γ) (Q := Q) k n + 1))
  simpa using hp

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization MachineRealization.ParameterCode
open scoped Compiler.HeadCodec

attribute [instance] Family.finiteΓ Family.finiteQ Family.decΓ Family.decQ Family.codeΓ Family.codeQ

variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)

theorem pSource_bootstrap
    (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w = 1)) :
    ∃ n, raw n = tableNormal (pTables s family.A family.M n) ∧
      ∀ j, GoodTable (r := fun a b : Sigma => a < b) (pTables s family.A family.M n) j ∧ PartialBudget (raw n) j :=
  exists_total_pFixed_point s family.A family.M h family.realizes family.decode

variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w = 1))

noncomputable def pIndex : ℕ := (pSource_bootstrap s h).choose
abbrev pProcessor := pTables s family.A family.M (pIndex s h)

theorem pIndex_fixed : raw (pIndex s h) = tableNormal (pProcessor s h) := (pSource_bootstrap s h).choose_spec.1

theorem pIndex_good (j : ℕ) : GoodTable (r := fun a b : Sigma => a < b) (pProcessor s h) j :=
  ((pSource_bootstrap s h).choose_spec.2 j).1

theorem pIndex_budget (j : ℕ) : PartialBudget (raw (pIndex s h)) j :=
  ((pSource_bootstrap s h).choose_spec.2 j).2

theorem pIndex_stable : ∀ j m : ℕ, j ≤ m → ∀ rs ∈ pProcessor s h j, ∀ rt ∈ pProcessor s h m, Selectors.BoundedEq rs rt j := by
  intro j m hjm rs hrs rt hrt
  exact pStable s family.A family.M (pIndex s h) hjm hrs hrt

abbrev pH := Quotient.Mon (pProcessor s h)

noncomputable instance pHMonoidWithZero : MonoidWithZero (pH s h) :=
  Quotient.monoidWithZero (pProcessor s h) markers.zero (pIndex_good s h 2).choose_spec.1
    (pTables_absorb s family.A family.M (pIndex s h) 2 (pIndex_good s h 2).choose_spec.1)

theorem zero_pH : (0 : pH s h) = Quotient.present (pProcessor s h) [markers.zero] := rfl

theorem pGroup_code_eq_iff (u v : List (Z k)) :
    Quotient.present (pProcessor s h) ((finiteCodeG (Γ := family.Γ) (Q := family.Q) k (pIndex s h)).encode u) =
      Quotient.present (pProcessor s h) ((finiteCodeG (Γ := family.Γ) (Q := family.Q) k (pIndex s h)).encode v) ↔
        evalWord s u = evalWord s v := by
  have hh := Quotient.present_encode_iff (pProcessor s h) wf_sigma (pIndex_good s h) (pIndex_stable s h)
    (finiteCodeG (Γ := family.Γ) (Q := family.Q) k (pIndex s h)) (wf_relG k)
    (Search.value (testG s (pIndex s h))) markers.zero
    (fun j rs hrs => pTables_short s family.A family.M (pIndex s h) j hrs)
    (fun j rs hrs => pTables_isolateG s family.A family.M (pIndex s h) j hrs)
    (fun j rs hrs => pTables_staticG s family.A family.M (pIndex s h) j hrs)
    (fun j => (group_tests s (pIndex s h) j).2.1)
    (fun j => (group_tests s (pIndex s h) j).2.2)
    (group_tests s (pIndex s h) 0).1
    (codeG_avoid (Γ := family.Γ) (Q := family.Q) k (pIndex s h) _ (by simp)) u v
  simpa only [group_search_value, Option.some.injEq, WordProblem.testedClass_eq_iff] using hh

noncomputable def pGroupEmbedding (hs : Subgroup.closure (Set.range s) = ⊤) : G →* pH s h :=
  Quotient.descendCode (finiteCodeG (Γ := family.Γ) (Q := family.Q) k (pIndex s h)) (groupEval s)
    (groupEval_surjective s hs) (pGroup_code_eq_iff s h)

noncomputable abbrev pKMachine := terminalMachine family.A family.M (pIndex s h)
abbrev pK := Word.Presentation KAlphabet (pKMachine s h)

local instance instLinearOrderSector_p : LinearOrder (Control.Sector Sigma (Bool × family.Γ) (ParameterMachine.State family.Q (pIndex s h))) :=
  finiteOrder (T := Sigma) (Γ := family.Γ) (Q := family.Q) (pIndex s h)

noncomputable instance pKMonoidWithZero : MonoidWithZero (pK s h) := Word.monoidWithZero KAlphabet (pKMachine s h)

theorem zero_pK : (0 : pK s h) = Word.present KAlphabet (pKMachine s h) [.zero] := rfl

theorem realizes_pProcessor : Word.Realizes KAlphabet (pKMachine s h) (tableNormal (pProcessor s h)) :=
  pIndex_fixed s h ▸ family.realizes (pIndex s h)

noncomputable def pCopyEmbedding : pH s h →ₙ* pK s h :=
  Quotient.rawMap (pProcessor s h) wf_sigma (pIndex_good s h) (pIndex_stable s h)
    KAlphabet (pKMachine s h) family.decode (realizes_pProcessor s h)

instance pHFG : Monoid.FG (pH s h) :=
  Monoid.fg_of_surjective (PresentedMonoid.mk (Quotient.Rel (pProcessor s h))) PresentedMonoid.surjective_mk

instance pKFG : Monoid.FG (pK s h) :=
  Monoid.fg_of_surjective (PresentedMonoid.mk (Word.Rel KAlphabet (pKMachine s h))) PresentedMonoid.surjective_mk

abbrev pT := FiniteAlgebraicEnvelopes.ZeroProduct.Mon (pK s h) PElemCoding.pMonoid
abbrev pTLetter := FiniteY (Γ := family.Γ) (Q := family.Q) (pIndex s h)
abbrev pTCode := finiteCodeT (Γ := family.Γ) (Q := family.Q) k (pIndex s h)
abbrev pTClass := pFiniteClass family.A family.M (pIndex s h)
abbrev pTTest := Search.value (pFiniteTest family.A family.M (pIndex s h))

local instance instDecidableEqXSigmaΓFamilyQ_p : DecidableEq (Tested.X Sigma family.Γ family.Q) := inferInstance
local instance instDecidableEqLetter_p : DecidableEq (Word.Letter Sigma (Bool × family.Γ) (ParameterMachine.State family.Q (pIndex s h))) := inferInstance
local instance instDecidableEqPTLetter_p : DecidableEq (pTLetter s h) := inferInstance
local instance instFintypePTLetter_p : Fintype (pTLetter s h) := inferInstance

noncomputable def pTPairEval : FreeMonoid (pTLetter s h) →* pK s h × PElemCoding.pMonoid where
  toFun w := (Word.present KAlphabet (pKMachine s h) (Projection.left w.toList), PElemCoding.pWordValue (Projection.right w.toList))
  map_one' := rfl
  map_mul' u v := by
    apply Prod.ext
    · simp only [FreeMonoid.toList_mul, Projection.left_append]
      rfl
    · simp only [FreeMonoid.toList_mul, Projection.right_append, PElemCoding.pWordValue_append]
      rfl

noncomputable def pTEval : FreeMonoid (pTLetter s h) →* pT s h :=
  (FiniteAlgebraicEnvelopes.ZeroProduct.pair (pK s h) PElemCoding.pMonoid).comp (pTPairEval s h)

theorem pTPairEval_surjective : Function.Surjective (pTPairEval s h) := by
  rintro ⟨x, y⟩
  obtain ⟨u, rfl⟩ := Word.present_surjective KAlphabet (pKMachine s h) x
  obtain ⟨v, rfl⟩ := PElemCoding.pWordValue_surjective y
  refine ⟨FreeMonoid.ofList (u.map Sum.inl ++ v.map Sum.inr), ?_⟩
  simp [pTPairEval, Projection.left, Projection.right, List.filterMap_map]

theorem pTEval_surjective : Function.Surjective (pTEval s h) :=
  (FiniteAlgebraicEnvelopes.ZeroProduct.pair_surjective _ _).comp (pTPairEval_surjective s h)

theorem pFiniteValue_eq_iff (u v : List (pTLetter s h)) :
    finiteValue family.A family.M (pIndex s h) u = finiteValue family.A family.M (pIndex s h) v ↔
      Word.present KAlphabet (pKMachine s h) (Projection.left u) = Word.present KAlphabet (pKMachine s h) (Projection.left v) := by
  rw [finiteValue, finiteValue, (List.map_injective_iff.mpr (Word.letterMap_injective _ (MachineRealization.ParameterCode.encode_injective (pIndex s h)))).eq_iff]
  exact (Word.present_eq_iff_normal KAlphabet (pKMachine s h) family.decode
    (fun j => (pIndex_budget s h j).totalize)
    (fun j => (family.realizes (pIndex s h)).computesAt KAlphabet (pKMachine s h) (pIndex_budget s h j)) _ _).symm

theorem pFiniteValue_eq_zero (w : List (pTLetter s h)) :
    finiteValue family.A family.M (pIndex s h) w = [.zero] ↔
      Word.present KAlphabet (pKMachine s h) (Projection.left w) = (0 : pK s h) := by
  rw [finiteValue_zero, zero_pK, Word.present_eq_iff_normal KAlphabet (pKMachine s h) family.decode
    (fun j => (pIndex_budget s h j).totalize)
    (fun j => (family.realizes (pIndex s h)).computesAt KAlphabet (pKMachine s h) (pIndex_budget s h j)), Word.normal_omega]

theorem pTClass_eq_iff (u v : List (pTLetter s h)) :
    pTClass s h u = pTClass s h v ↔ pTEval s h (FreeMonoid.ofList u) = pTEval s h (FreeMonoid.ofList v) := by
  change ZeroProduct.test _ _ _ u = ZeroProduct.test _ _ _ v ↔
    FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _ = FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _
  rw [FiniteAlgebraicEnvelopes.ZeroProduct.pair_eq_iff]
  change ZeroProduct.test _ _ _ u = ZeroProduct.test _ _ _ v ↔
    (Word.present KAlphabet (pKMachine s h) (Projection.left u), PElemCoding.pWordValue (Projection.right u)) =
      (Word.present KAlphabet (pKMachine s h) (Projection.left v), PElemCoding.pWordValue (Projection.right v)) ∨
       Word.present KAlphabet (pKMachine s h) (Projection.left u) = 0 ∧ Word.present KAlphabet (pKMachine s h) (Projection.left v) = 0
  rw [Prod.ext_iff, ← pFiniteValue_eq_iff s h, ← pFiniteValue_eq_zero s h, ← pFiniteValue_eq_zero s h]
  have hp : PElemCoding.pWordValue (Projection.right u) = PElemCoding.pWordValue (Projection.right v) ↔
      PElemCoding.testedClass (Projection.right u) = PElemCoding.testedClass (Projection.right v) :=
    (PElemCoding.pWordValue_eq_iff _ _).trans (PElemCoding.testedClass_eq_iff _ _).symm
  rw [hp]
  by_cases hu : finiteValue family.A family.M (pIndex s h) u = [Path.Letter.zero] <;>
    by_cases hv : finiteValue family.A family.M (pIndex s h) v = [Path.Letter.zero] <;>
    simp [ZeroProduct.test, hu, hv]
  aesop

theorem pTClass_eq_none (w : List (pTLetter s h)) : pTClass s h w = none ↔ pTEval s h (FreeMonoid.ofList w) = 0 := by
  change ZeroProduct.test _ _ _ w = none ↔ FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _ = 0
  rw [FiniteAlgebraicEnvelopes.ZeroProduct.pair_eq_zero]
  change ZeroProduct.test _ _ _ w = none ↔ Word.present KAlphabet (pKMachine s h) (Projection.left w) = 0
  rw [← pFiniteValue_eq_zero s h]
  simp [ZeroProduct.test]

theorem pTTest_eq_class (w : List (pTLetter s h)) : pTTest s h w = pTClass s h w :=
  pSearch_value_eq family.A family.M (pIndex s h) w.length (pIndex_budget s h (2 * w.length)) w le_rfl

theorem pTTest_properties (j : ℕ) : pTTest s h [] ≠ none ∧ Static.Contextual (pTTest s h) j ∧ Static.ZeroIdeal (pTTest s h) j :=
  (pTests_bounded family.A family.M (pIndex s h) j (pIndex_budget s h (2 * j))
    (family.realizes (pIndex s h)) family.decode).2

theorem pT_code_eq_iff (u v : List (pTLetter s h)) :
    Quotient.present (pProcessor s h) ((pTCode s h).encode u) = Quotient.present (pProcessor s h) ((pTCode s h).encode v) ↔
      pTEval s h (FreeMonoid.ofList u) = pTEval s h (FreeMonoid.ofList v) := by
  rw [Quotient.present_encode_iff (pProcessor s h) wf_sigma (pIndex_good s h) (pIndex_stable s h)
    (pTCode s h) (wf_relT (pIndex s h)) (pTTest s h) markers.zero
    (fun j _ hrs => pTables_short s family.A family.M (pIndex s h) j hrs)
    (fun j _ hrs => pTables_isolateT s family.A family.M (pIndex s h) j hrs)
    (fun j _ hrs => pTables_staticT s family.A family.M (pIndex s h) j hrs)
    (fun j => (pTTest_properties s h j).2.1) (fun j => (pTTest_properties s h j).2.2)
    (pTTest_properties s h 0).1 (codeT_avoid (Γ := family.Γ) (Q := family.Q) k (pIndex s h) _ (by simp))]
  rw [pTTest_eq_class, pTTest_eq_class, pTClass_eq_iff]

noncomputable def pKappa : pT s h →* pH s h :=
  Quotient.descendCode (pTCode s h) (pTEval s h) (pTEval_surjective s h) (pT_code_eq_iff s h)

theorem pKappa_word (w : List (pTLetter s h)) : pKappa s h (pTEval s h (FreeMonoid.ofList w)) =
    Quotient.present (pProcessor s h) ((pTCode s h).encode w) :=
  Quotient.descendCode_apply (pTCode s h) (pTEval s h) (pTEval_surjective s h) (pT_code_eq_iff s h) w

theorem pT_normal (w : List (pTLetter s h)) :
    Quotient.normal (pProcessor s h) ((pTCode s h).encode w) =
      Static.output (pTCode s h) (wf_relT (pIndex s h)) (pTTest s h) markers.zero w :=
  Quotient.normal_encode (pProcessor s h) wf_sigma (pIndex_good s h) (pIndex_stable s h)
    (pTCode s h) (wf_relT (pIndex s h)) (pTTest s h) markers.zero
    (fun j _ hrs => pTables_short s family.A family.M (pIndex s h) j hrs)
    (fun j _ hrs => pTables_isolateT s family.A family.M (pIndex s h) j hrs)
    (fun j _ hrs => pTables_staticT s family.A family.M (pIndex s h) j hrs)
    (fun j => (pTTest_properties s h j).2.1) (fun j => (pTTest_properties s h j).2.2)
    (pTTest_properties s h 0).1 w

theorem pTTest_eq_none (w : List (pTLetter s h)) :
    pTTest s h w = none ↔ pTEval s h (FreeMonoid.ofList w) = 0 := by
  rw [pTTest_eq_class, pTClass_eq_none]

theorem pKappa_zero : pKappa s h 0 = 0 := by
  obtain ⟨w, hw⟩ := pTEval_surjective s h 0
  have hq : pTTest s h w.toList = none := (pTTest_eq_none s h w.toList).mpr hw
  rw [← hw]
  change pKappa s h (pTEval s h (FreeMonoid.ofList w.toList)) = 0
  rw [pKappa_word, Quotient.present_normal (pProcessor s h) wf_sigma (pIndex_good s h) (pIndex_stable s h), pT_normal]
  simp only [Static.output, hq, ite_true]
  rfl

def pSeparator : pH s h := Quotient.present (pProcessor s h) [6]

theorem pSeparator_avoid_T : (6 : Sigma) ∉ (pTCode s h).Alphabet := by
  intro hh
  have hh := codeT_alphabet (Γ := family.Γ) (Q := family.Q) k (pIndex s h) hh
  norm_num [Fin.ext_iff] at hh

theorem pSeparator_avoid_G : (6 : Sigma) ∉ (finiteCodeG (Γ := family.Γ) (Q := family.Q) k (pIndex s h)).Alphabet := by
  intro hh
  have hh := codeG_alphabet (Γ := family.Γ) (Q := family.Q) k (pIndex s h) hh
  norm_num [Fin.ext_iff] at hh

theorem pTables_isolate_separator (j : ℕ) {rs : List (List Sigma × List Sigma)}
    (hrs : rs ∈ pProcessor s h j) :
    ∀ p ∈ rs, p ∈ Static.table (pTCode s h) (wf_relT (pIndex s h)) (pTTest s h) markers.zero j ∨
      ∃ b ∈ p.1, b ∉ (pTCode s h).Alphabet ∧ b ≠ 6 := by
  intro p hp
  apply Selectors.process_isolate_separator markers (pTCode s h) (wf_relT (pIndex s h)) (pTTest s h) 6 ?_
    (codeT_avoid (Γ := family.Γ) (Q := family.Q) k (pIndex s h) _ (by simp)) (by decide) _ _ _
    ((pTables_members s family.A family.M (pIndex s h) j hrs p).mp hp)
  intro p hp
  exact Base.isolate_separator (pTCode s h) (finiteCodeG (Γ := family.Γ) (Q := family.Q) k (pIndex s h))
    (wf_relT (pIndex s h)) (wf_relG k) (pTTest s h) (Search.value (testG s (pIndex s h))) markers.zero (6 : Sigma)
    (codeT_avoid (Γ := family.Γ) (Q := family.Q) k (pIndex s h) _ (by simp)) (by decide)
    (pSeparator_avoid_G s h)
    (codes_disjoint (Γ := family.Γ) (Q := family.Q) k (pIndex s h)) hp

theorem pSeparator_word (u v : List (pTLetter s h)) :
    pKappa s h (pTEval s h (FreeMonoid.ofList u)) * pSeparator s h * pKappa s h (pTEval s h (FreeMonoid.ofList v)) =
      Quotient.present (pProcessor s h) ((pTCode s h).encode u ++ 6 :: (pTCode s h).encode v) := by
  rw [pKappa_word, pKappa_word]
  simp only [pSeparator, ← Quotient.present_append, List.append_assoc, List.singleton_append]

theorem pSeparator_nonzero (x y : pT s h) (hx : x ≠ 0) (hy : y ≠ 0) :
    pKappa s h x * pSeparator s h * pKappa s h y ≠ 0 := by
  obtain ⟨u, rfl⟩ := pTEval_surjective s h x
  obtain ⟨v, rfl⟩ := pTEval_surjective s h y
  change pKappa s h (pTEval s h (FreeMonoid.ofList u.toList)) * pSeparator s h * pKappa s h (pTEval s h (FreeMonoid.ofList v.toList)) ≠ 0
  rw [pSeparator_word, zero_pH]
  exact Quotient.present_separator_ne_zero (pProcessor s h) wf_sigma (pIndex_good s h) (pIndex_stable s h)
    (pTCode s h) (wf_relT (pIndex s h)) (pTTest s h) markers.zero (6 : Sigma)
    (fun j rs hrs => pTables_short s family.A family.M (pIndex s h) j hrs)
    (fun j rs hrs => pTables_isolate_separator s h j hrs)
    (fun j rs hrs => pTables_staticT s family.A family.M (pIndex s h) j hrs)
    (fun j => (pTTest_properties s h j).2.1) (fun j => (pTTest_properties s h j).2.2)
    (pTTest_properties s h 0).1
    (pSeparator_avoid_T s h)
    (codeT_avoid (Γ := family.Γ) (Q := family.Q) k (pIndex s h) _ (by simp)) (by decide)
    (fun he => hx ((pTTest_eq_none s h _).mp he)) (fun he => hy ((pTTest_eq_none s h _).mp he))

theorem append_sep_inj {S : Type*} {u1 v1 u2 v2 : List S} {sep : S}
    (hu1 : sep ∉ u1) (hu2 : sep ∉ u2)
    (h : u1 ++ sep :: v1 = u2 ++ sep :: v2) : u1 = u2 ∧ v1 = v2 := by
  induction u1 generalizing u2 with
  | nil =>
    cases u2 with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨rfl, h⟩
    | cons b u2 =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact False.elim (hu2 (h.1 ▸ List.mem_cons_self))
  | cons a u1 ih =>
    cases u2 with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact False.elim (hu1 (h.1.symm ▸ List.mem_cons_self))
    | cons b u2 =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h'⟩ := h
      obtain ⟨rfl, rfl⟩ := ih (fun hm => hu1 (List.mem_cons_of_mem _ hm))
        (fun hm => hu2 (List.mem_cons_of_mem _ hm)) h'
      exact ⟨rfl, rfl⟩

theorem pSeparator_inj (x1 y1 x2 y2 : pT s h)
    (hx1 : x1 ≠ 0) (hy1 : y1 ≠ 0) (hx2 : x2 ≠ 0) (hy2 : y2 ≠ 0)
    (heq : pKappa s h x1 * pSeparator s h * pKappa s h y1 =
           pKappa s h x2 * pSeparator s h * pKappa s h y2) :
    x1 = x2 ∧ y1 = y2 := by
  obtain ⟨u1, rfl⟩ := pTEval_surjective s h x1
  obtain ⟨v1, rfl⟩ := pTEval_surjective s h y1
  obtain ⟨u2, rfl⟩ := pTEval_surjective s h x2
  obtain ⟨v2, rfl⟩ := pTEval_surjective s h y2
  change pKappa s h (pTEval s h (FreeMonoid.ofList u1.toList)) * pSeparator s h *
      pKappa s h (pTEval s h (FreeMonoid.ofList v1.toList)) =
    pKappa s h (pTEval s h (FreeMonoid.ofList u2.toList)) * pSeparator s h *
      pKappa s h (pTEval s h (FreeMonoid.ofList v2.toList)) at heq
  rw [pSeparator_word, pSeparator_word] at heq
  have hn := (Quotient.present_eq_iff (pProcessor s h) wf_sigma (pIndex_good s h) (pIndex_stable s h) _ _).mp heq
  have hu1 : pTTest s h u1.toList ≠ none := fun he => hx1 ((pTTest_eq_none s h _).mp he)
  have hv1 : pTTest s h v1.toList ≠ none := fun he => hy1 ((pTTest_eq_none s h _).mp he)
  have hu2 : pTTest s h u2.toList ≠ none := fun he => hx2 ((pTTest_eq_none s h _).mp he)
  have hv2 : pTTest s h v2.toList ≠ none := fun he => hy2 ((pTTest_eq_none s h _).mp he)
  rw [Quotient.normal_separator (pProcessor s h) wf_sigma (pIndex_good s h) (pIndex_stable s h)
      (pTCode s h) (wf_relT (pIndex s h)) (pTTest s h) markers.zero (6 : Sigma)
      (fun j rs hrs => pTables_short s family.A family.M (pIndex s h) j hrs)
      (fun j rs hrs => pTables_isolate_separator s h j hrs)
      (fun j rs hrs => pTables_staticT s family.A family.M (pIndex s h) j hrs)
      (fun j => (pTTest_properties s h j).2.1) (fun j => (pTTest_properties s h j).2.2)
      (pTTest_properties s h 0).1 (pSeparator_avoid_T s h) hu1 hv1,
    Quotient.normal_separator (pProcessor s h) wf_sigma (pIndex_good s h) (pIndex_stable s h)
      (pTCode s h) (wf_relT (pIndex s h)) (pTTest s h) markers.zero (6 : Sigma)
      (fun j rs hrs => pTables_short s family.A family.M (pIndex s h) j hrs)
      (fun j rs hrs => pTables_isolate_separator s h j hrs)
      (fun j rs hrs => pTables_staticT s family.A family.M (pIndex s h) j hrs)
      (fun j => (pTTest_properties s h j).2.1) (fun j => (pTTest_properties s h j).2.2)
      (pTTest_properties s h 0).1 (pSeparator_avoid_T s h) hu2 hv2] at hn
  obtain ⟨hl, hr⟩ := append_sep_inj
    (fun hm => pSeparator_avoid_T s h ((pTCode s h).mem_alphabet hm))
    (fun hm => pSeparator_avoid_T s h ((pTCode s h).mem_alphabet hm)) hn
  have hle1 := (Canonical.least_eq_iff (wf_relT (pIndex s h)) (pTTest s h)).mp ((pTCode s h).encode_injective hl)
  have hle2 := (Canonical.least_eq_iff (wf_relT (pIndex s h)) (pTTest s h)).mp ((pTCode s h).encode_injective hr)
  rw [pTTest_eq_class, pTTest_eq_class, pTClass_eq_iff] at hle1 hle2
  simpa only [FreeMonoid.ofList_toList] using And.intro hle1 hle2

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.Bootstrap

section SelectorHelpers
variable {S : Type*} [DecidableEq S]

theorem process_mono (a : Selectors.Markers S) (base : List (List S × List S))
    (stages : ℕ → Selectors.Stage S) (n : ℕ) {j m : ℕ} (hjm : j ≤ m) :
    ∀ p ∈ Selectors.process (a := a) base stages n j,
      p ∈ Selectors.process (a := a) base stages n m := by
  induction m, hjm using Nat.le_induction with
  | base => exact fun _ h => h
  | succ k hk ih => exact fun p h => Selectors.choose_contains (a := a) _ _ _ p (ih p h)

theorem irreducible_mono {rs rt : List (List S × List S)} (hsub : ∀ p ∈ rs, p ∈ rt)
    {w : List S} (h : Irreducible (Step rt) w) : Irreducible (Step rs) w := by
  intro v hv
  cases hv with
  | @apply u v' hp x y => exact h (x ++ v' ++ y) (Step.apply (hsub _ hp) x y)

variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n, GoodTable (r := r) T n)
  (stable : ∀ k n, k ≤ n → ∀ rk ∈ T k, ∀ rn ∈ T n, Selectors.BoundedEq rk rn k)
include wf good stable

theorem representative_irreducible (x : Quotient.Mon T) {m : ℕ}
    (hm : (Quotient.representative T x).length ≤ m)
    {rm : List (List S × List S)} (hrm : rm ∈ T m) :
    Irreducible (Step rm) (Quotient.representative T x) := by
  have hmem := Quotient.normal_mem T wf good stable (Quotient.representative T x)
  rw [Quotient.representative, Quotient.normal_idempotent T wf good stable] at hmem
  change Quotient.representative T x ∈ tableNormal T (Quotient.representative T x) at hmem
  rw [tableNormal_at wf (fun _ _ => good _) (fun k hk => stable k m hk) hrm hm] at hmem
  exact (evaluate_sound hmem).2

variable (a : Selectors.Markers S)
  (habsorb : ∀ n rs, rs ∈ T n → Absorbs rs a.zero)
include habsorb

theorem zero_not_mem_representative {x : Quotient.Mon T}
    (hx : x ≠ Quotient.present T [a.zero]) :
    a.zero ∉ Quotient.representative T x := by
  intro hu
  obtain ⟨u1, u2, heq⟩ := List.append_of_mem hu
  have heq' : Quotient.representative T x = u1 ++ [a.zero] ++ u2 := by simp [heq]
  obtain ⟨rm, hrm, _⟩ := good (Quotient.representative T x).length
  have hI := representative_irreducible T wf good stable x le_rfl hrm
  have hsteps := absorbs_context (habsorb _ rm hrm) u1 u2
  rw [← heq'] at hsteps
  have hrep : Quotient.representative T x = [a.zero] :=
    irreducible_reaches (Step rm) hI hsteps
  apply hx
  rw [← Quotient.present_representative T wf good stable x, hrep]

variable [Primcodable S] (base : ℕ → List (List S × List S))
  (hmembers : ∀ n rs, rs ∈ T n →
    RulesEq rs (Selectors.process (a := a) (base n) (Selectors.stages a.zero) n n))
include hmembers

theorem selector_property (d : ℕ) (hd : Fin (d + 1) → Quotient.Mon T)
    (hinj : Function.Injective hd)
    (hnez : ∀ i, hd i ≠ Quotient.present T [a.zero]) :
    ∃ L R : Quotient.Mon T,
      L * hd 0 * R = 1 ∧
      ∀ i : Fin (d + 1), i ≠ 0 → L * hd i * R = Quotient.present T [a.zero] := by
  let w : Fin (d + 1) → List S := fun i => Quotient.representative T (hd i)
  have hw_inj : Function.Injective w :=
    (Quotient.representative_injective T wf good stable).comp hinj
  let ws : List (List S) := (List.finRange (d + 1)).map w
  have hws_ne : ws ≠ [] := by simp [ws]
  have hws_nodup : ws.Nodup := (List.nodup_finRange (d + 1)).map hw_inj
  have hws_zero : ∀ u ∈ ws, a.zero ∉ u := by
    intro u hu
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hu
    exact zero_not_mem_representative T wf good stable a habsorb (hnez i)
  let idx : ℕ := Encodable.encode ws
  have htuples : Selectors.tuples a.zero idx = ws := by
    unfold Selectors.tuples
    rw [Encodable.encodek]
    dsimp only [Option.getD_some]
    exact if_pos ⟨hws_ne, hws_nodup, hws_zero⟩
  let N : ℕ := Selectors.sizes a.zero idx
  let n : ℕ := Selectors.sizes a.zero (idx + 1)
  have hidx_lt_N : idx < N := Selectors.index_lt_size a.zero idx
  have hstep : 2 * N + 2 + Selectors.maxLength (Selectors.tuples a.zero idx) < n :=
    Selectors.sizes_step a.zero idx
  have hN_le_n : N ≤ n := by omega
  have hidx_le_n : idx + 1 ≤ n := by omega
  obtain ⟨rn, hrn, _⟩ := good n
  have hrn_eq := hmembers n rn hrn
  let rs_idx := Selectors.process (a := a) (base n) (Selectors.stages a.zero) n idx
  have hrs_sub : ∀ p ∈ rs_idx, p ∈ rn := fun p hp =>
    (hrn_eq p).mpr (process_mono a (base n) (Selectors.stages a.zero) n (by omega) p hp)
  have hallowed : Selectors.allowed rs_idx (Selectors.stages a.zero idx) = true := by
    rw [Selectors.allowed_iff]
    intro u hu
    change u ∈ Selectors.tuples a.zero idx at hu
    have hu_len : u.length < N := Selectors.body_lt_size a.zero idx hu
    rw [htuples] at hu
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hu
    have hwi_len : (Quotient.representative T (hd i)).length ≤ n := by
      change (w i).length ≤ n
      omega
    exact irreducible_mono hrs_sub
      (representative_irreducible T wf good stable (hd i) hwi_len hrn)
  have hchoose : Selectors.process (a := a) (base n) (Selectors.stages a.zero) n (idx + 1) =
      rs_idx ++ Selectors.rules a N ws := by
    change Selectors.choose (a := a) rs_idx (Selectors.stages a.zero idx) n = _
    unfold Selectors.choose
    have hsize : (Selectors.stages a.zero idx).size ≤ n := hN_le_n
    rw [if_pos ⟨hsize, hallowed⟩]
    simp [Selectors.stages, N, htuples]
  have hrules_in_rn : ∀ p ∈ Selectors.rules a N ws, p ∈ rn := by
    intro p hp
    apply (hrn_eq p).mpr
    apply process_mono a (base n) (Selectors.stages a.zero) n hidx_le_n
    rw [hchoose]
    exact List.mem_append_right _ hp
  let L : Quotient.Mon T := Quotient.present T (a.d :: List.replicate N a.l)
  let R : Quotient.Mon T := Quotient.present T (List.replicate N a.r ++ [a.h])
  have hhead : ws.head? = some (w 0) := by
    simp [ws, List.finRange_succ]
  have hLR (i : Fin (d + 1)) :
      L * hd i * R = Quotient.present T (if ws.head? = some (w i) then [] else [a.zero]) := by
    have hw_mem : w i ∈ ws := List.mem_map_of_mem (List.mem_finRange i)
    have hrule_i : (a.wrap N (w i), if ws.head? = some (w i) then [] else [a.zero]) ∈ rn :=
      hrules_in_rn _ (List.mem_map_of_mem hw_mem)
    have hlen_i : (a.wrap N (w i)).length ≤ n := by
      have hw_max := Selectors.length_le_maxLength (w := w i) (htuples ▸ hw_mem)
      simp only [Selectors.Markers.wrap, Envelopes.length_frame]
      omega
    have hwrap_eq : (a.d :: List.replicate N a.l) ++ w i ++ (List.replicate N a.r ++ [a.h]) =
        a.wrap N (w i) := by
      simp [Selectors.Markers.wrap, Envelopes.frame, List.append_assoc]
    calc
      L * hd i * R
        = Quotient.present T (a.d :: List.replicate N a.l) *
            Quotient.present T (w i) *
            Quotient.present T (List.replicate N a.r ++ [a.h]) := by
          change L * hd i * R = L * Quotient.present T (Quotient.representative T (hd i)) * R
          rw [Quotient.present_representative T wf good stable (hd i)]
      _ = Quotient.present T (a.wrap N (w i)) := by
          rw [← Quotient.present_append, ← Quotient.present_append, hwrap_eq]
      _ = Quotient.present T (if ws.head? = some (w i) then [] else [a.zero]) :=
          PresentedMonoid.mk_eq_mk_of_rel ⟨n, rn, hrn, hrule_i, hlen_i⟩
  refine ⟨L, R, ?_, ?_⟩
  · rw [hLR 0, hhead, if_pos rfl, Quotient.present_nil]
  · intro i hi
    rw [hLR i, hhead]
    have hne : some (w 0) ≠ some (w i) := fun h => hi (hw_inj (Option.some.inj h)).symm
    rw [if_neg hne]

end SelectorHelpers

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes

section ULiftAndPresentationHelpers

instance instMonoidULift (N : Type) [Monoid N] : Monoid (ULift.{u} N) where
  mul a b := ⟨a.down * b.down⟩
  one := ⟨1⟩
  mul_assoc a b c := ULift.ext _ _ (mul_assoc a.down b.down c.down)
  one_mul a := ULift.ext _ _ (one_mul a.down)
  mul_one a := ULift.ext _ _ (mul_one a.down)
  npow n a := ⟨a.down ^ n⟩
  npow_zero a := ULift.ext _ _ (Monoid.npow_zero a.down)
  npow_succ n a := ULift.ext _ _ (Monoid.npow_succ n a.down)

instance instMonoidWithZeroULift (M : Type) [MonoidWithZero M] : MonoidWithZero (ULift.{u} M) where
  __ := instMonoidULift M
  zero := ⟨0⟩
  zero_mul a := ULift.ext _ _ (zero_mul a.down)
  mul_zero a := ULift.ext _ _ (mul_zero a.down)

instance instNontrivialULift (M : Type) [MonoidWithZero M] [Nontrivial M] : Nontrivial (ULift.{u} M) :=
  ⟨⟨1⟩, ⟨0⟩, fun h => one_ne_zero (congrArg ULift.down h)⟩

def uliftMulEquiv (N : Type) [Monoid N] : ULift.{u} N ≃* N where
  toFun := ULift.down
  invFun := ULift.up
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

instance instFGULift (N : Type) [Monoid N] [Monoid.FG N] : Monoid.FG (ULift.{u} N) :=
  Monoid.fg_of_surjective (uliftMulEquiv.{u} N).symm.toMonoidHom (uliftMulEquiv.{u} N).symm.surjective

theorem freeMonoid_lift_of_comp {α β : Type*} (rel : FreeMonoid β → FreeMonoid β → Prop)
    (f : α → β) (w : FreeMonoid α) :
    FreeMonoid.lift (fun x => PresentedMonoid.of rel (f x)) w =
      PresentedMonoid.mk rel (FreeMonoid.map f w) := by
  have h : FreeMonoid.lift (fun x => PresentedMonoid.of rel (f x)) =
      (PresentedMonoid.mk rel).comp (FreeMonoid.map f) :=
    FreeMonoid.hom_eq (fun _ => rfl)
  exact DFunLike.congr_fun h w

theorem freeMonoid_map_equiv_symm {α β : Type*} (e : α ≃ β) (w : FreeMonoid α) :
    FreeMonoid.map e.symm (FreeMonoid.map e w) = w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | of_mul x w ih =>
    simp only [map_mul, FreeMonoid.map_of, e.symm_apply_apply, ih]

theorem finitelyPresented_of_finite_rel {α : Type} [Fintype α]
    {rel : FreeMonoid α → FreeMonoid α → Prop}
    (hfin : {p : List α × List α | rel (FreeMonoid.ofList p.1) (FreeMonoid.ofList p.2)}.Finite) :
    IsFinitelyPresentedMonoid (ULift.{u} (PresentedMonoid rel)) := by
  classical
  let n := Fintype.card α
  let e : α ≃ Fin n := Fintype.equivFin α
  let toPair : List α × List α → FreeMonoid (Fin n) × FreeMonoid (Fin n) :=
    fun p => (FreeMonoid.map e (FreeMonoid.ofList p.1), FreeMonoid.map e (FreeMonoid.ofList p.2))
  have hfin' : {q : FreeMonoid (Fin n) × FreeMonoid (Fin n) |
      rel (FreeMonoid.map e.symm q.1) (FreeMonoid.map e.symm q.2)}.Finite := by
    apply (hfin.image toPair).subset
    rintro ⟨u, v⟩ huv
    refine ⟨((FreeMonoid.map e.symm u).toList, (FreeMonoid.map e.symm v).toList), ?_, ?_⟩
    · change rel (FreeMonoid.ofList (FreeMonoid.map e.symm u).toList)
        (FreeMonoid.ofList (FreeMonoid.map e.symm v).toList)
      rw [FreeMonoid.ofList_toList, FreeMonoid.ofList_toList]
      exact huv
    · simp only [toPair, FreeMonoid.ofList_toList, Prod.mk.injEq]
      exact ⟨freeMonoid_map_equiv_symm e.symm u, freeMonoid_map_equiv_symm e.symm v⟩
  let rels : Finset (FreeMonoid (Fin n) × FreeMonoid (Fin n)) := hfin'.toFinset
  let rel2 : FreeMonoid (Fin n) → FreeMonoid (Fin n) → Prop := fun a b => (a, b) ∈ rels
  have hrel2 (a b : FreeMonoid (Fin n)) :
      rel2 a b ↔ rel (FreeMonoid.map e.symm a) (FreeMonoid.map e.symm b) :=
    hfin'.mem_toFinset
  let φ : PresentedMonoid rel →* PresentedMonoid rel2 :=
    PresentedMonoid.lift (fun x => PresentedMonoid.of rel2 (e x)) (by
      intro u v huv
      rw [freeMonoid_lift_of_comp, freeMonoid_lift_of_comp]
      apply PresentedMonoid.mk_eq_mk_of_rel
      rw [hrel2, freeMonoid_map_equiv_symm, freeMonoid_map_equiv_symm]
      exact huv)
  let ψ : PresentedMonoid rel2 →* PresentedMonoid rel :=
    PresentedMonoid.lift (fun y => PresentedMonoid.of rel (e.symm y)) (by
      intro a b hab
      rw [freeMonoid_lift_of_comp, freeMonoid_lift_of_comp]
      exact PresentedMonoid.mk_eq_mk_of_rel ((hrel2 a b).mp hab))
  have hψφ : ψ.comp φ = MonoidHom.id _ := by
    apply PresentedMonoid.ext
    intro x
    simp [φ, ψ]
  have hφψ : φ.comp ψ = MonoidHom.id _ := by
    apply PresentedMonoid.ext
    intro y
    simp [φ, ψ]
  let iso0 : PresentedMonoid rel ≃* PresentedMonoid rel2 :=
    { φ with
      invFun := ψ
      left_inv := DFunLike.congr_fun hψφ
      right_inv := DFunLike.congr_fun hφψ }
  exact ⟨n, rels, (uliftMulEquiv.{u} (PresentedMonoid rel)).trans iso0, trivial⟩

variable (K : Type) [MonoidWithZero K] [DecidableEq K] [Nontrivial K]

noncomputable def embedTElemULiftFun : TElem (ULift.{u} K) → ZeroProduct.Mon K PElemCoding.pMonoid
  | .zero => 0
  | .pair k _ p => ZeroProduct.pair K PElemCoding.pMonoid (k.down, PElemCoding.embedP p)

noncomputable def embedTElemULift : TElem (ULift.{u} K) →* ZeroProduct.Mon K PElemCoding.pMonoid where
  toFun := embedTElemULiftFun K
  map_one' := by
    change ZeroProduct.pair K PElemCoding.pMonoid (1, PElemCoding.embedP 1) = 1
    rw [map_one]
    exact map_one (ZeroProduct.pair K PElemCoding.pMonoid)
  map_mul' x y := by
    cases x with
    | zero =>
      change (0 : ZeroProduct.Mon K PElemCoding.pMonoid) = 0 * embedTElemULiftFun K y
      rw [zero_mul]
    | pair k1 h1 p1 =>
      cases y with
      | zero =>
        change (0 : ZeroProduct.Mon K PElemCoding.pMonoid) = embedTElemULiftFun K (.pair k1 h1 p1) * 0
        rw [mul_zero]
      | pair k2 h2 p2 =>
        rw [TElem.pair_mul_pair]
        by_cases hk : k1 * k2 = 0
        · rw [dif_pos hk]
          have hk' : k1.down * k2.down = 0 := congrArg ULift.down hk
          change (0 : ZeroProduct.Mon K PElemCoding.pMonoid) =
            ZeroProduct.pair K PElemCoding.pMonoid (k1.down, PElemCoding.embedP p1) *
              ZeroProduct.pair K PElemCoding.pMonoid (k2.down, PElemCoding.embedP p2)
          rw [← map_mul]
          exact ((ZeroProduct.pair_eq_zero K PElemCoding.pMonoid _).mpr hk').symm
        · rw [dif_neg hk]
          change ZeroProduct.pair K PElemCoding.pMonoid (k1.down * k2.down, PElemCoding.embedP (p1 * p2)) =
            ZeroProduct.pair K PElemCoding.pMonoid (k1.down, PElemCoding.embedP p1) *
              ZeroProduct.pair K PElemCoding.pMonoid (k2.down, PElemCoding.embedP p2)
          rw [PElemCoding.embedP.map_mul, ← (ZeroProduct.pair K PElemCoding.pMonoid).map_mul]
          rfl

theorem embedTElemULift_zero : embedTElemULift.{u} K TElem.zero = 0 := rfl

theorem embedTElemULift_eq_zero_iff (t : TElem (ULift.{u} K)) :
    embedTElemULift.{u} K t = 0 ↔ t = TElem.zero := by
  cases t with
  | zero => simp [embedTElemULift_zero]
  | pair k hk p =>
    change ZeroProduct.pair K PElemCoding.pMonoid (k.down, PElemCoding.embedP p) = 0 ↔ _
    rw [ZeroProduct.pair_eq_zero]
    have hk' : k.down ≠ 0 := fun h => hk (ULift.ext _ _ h)
    simp [hk']

theorem embedTElemULift_injective : Function.Injective (embedTElemULift.{u} K) := by
  intro x y hxy
  cases x with
  | zero =>
    exact ((embedTElemULift_eq_zero_iff.{u} K y).mp hxy.symm).symm
  | pair k1 h1 p1 =>
    cases y with
    | zero =>
      exact (embedTElemULift_eq_zero_iff.{u} K (.pair k1 h1 p1)).mp hxy
    | pair k2 h2 p2 =>
      change ZeroProduct.pair K PElemCoding.pMonoid (k1.down, PElemCoding.embedP p1) =
        ZeroProduct.pair K PElemCoding.pMonoid (k2.down, PElemCoding.embedP p2) at hxy
      rw [ZeroProduct.pair_eq_iff] at hxy
      rcases hxy with hxy | ⟨hk1, _⟩
      · cases Prod.mk.inj hxy with
        | intro hk hp =>
          have hk' : k1 = k2 := ULift.ext _ _ hk
          subst hk'
          rw [PElemCoding.embedP_injective hp]
      · exact False.elim (h1 (ULift.ext _ _ hk1))

theorem evalMonoidWord_present (T : ℕ → Part (List (List Bootstrap.Source.Sigma × List Bootstrap.Source.Sigma)))
    (w : List Bootstrap.Source.Sigma) :
    evalMonoidWord (fun a : Bootstrap.Source.Sigma => Bootstrap.Quotient.present T [a]) w =
      Bootstrap.Quotient.present T w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change Bootstrap.Quotient.present T [a] *
        evalMonoidWord (fun a : Bootstrap.Source.Sigma => Bootstrap.Quotient.present T [a]) w =
      Bootstrap.Quotient.present T ([a] ++ w)
    rw [ih, Bootstrap.Quotient.present_append]

theorem hasDecidableWordProblem_of_tableNormal
    (T' : ℕ → Part (List (List Bootstrap.Source.Sigma × List Bootstrap.Source.Sigma)))
    (good : ∀ n, Bootstrap.GoodTable (r := fun a b : Bootstrap.Source.Sigma => a < b) T' n)
    (stable : ∀ k n, k ≤ n → ∀ rk ∈ T' k, ∀ rn ∈ T' n, Bootstrap.Selectors.BoundedEq rk rn k)
    (ht : Partrec (Bootstrap.tableNormal T')) :
    HasDecidableWordProblemMonoid (ULift.{u} (Bootstrap.Quotient.Mon T')) := by
  classical
  let gen0 : Fin 12 → Bootstrap.Quotient.Mon T' := fun a => Bootstrap.Quotient.present T' [a]
  let gen : Fin 12 → ULift.{u} (Bootstrap.Quotient.Mon T') := fun a => ⟨gen0 a⟩
  have heval (w : List Bootstrap.Source.Sigma) :
      (evalMonoidWord gen w).down = Bootstrap.Quotient.present T' w := by
    rw [← evalMonoidWord_present T' w]
    induction w with
    | nil => rfl
    | cons a w ih =>
      change (gen a * evalMonoidWord gen w).down = gen0 a * evalMonoidWord gen0 w
      exact congrArg (gen0 a * ·) ih
  refine ⟨12, gen, ?_, ?_⟩
  · rw [eq_top_iff]
    rintro ⟨x⟩ -
    obtain ⟨w, rfl⟩ := Bootstrap.Quotient.present_surjective T' x
    have hw : (⟨Bootstrap.Quotient.present T' w⟩ : ULift.{u} (Bootstrap.Quotient.Mon T')) =
        evalMonoidWord gen w :=
      ULift.ext _ _ (heval w).symm
    rw [hw]
    exact Submonoid.list_prod_mem _ (fun y hy => by
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
      exact Submonoid.subset_closure (Set.mem_range_self a))
  · have hnorm : Computable (Bootstrap.Quotient.normal T') :=
      ht.of_eq_tot (Bootstrap.Quotient.normal_mem T' Bootstrap.Source.wf_sigma good stable)
    have hdec : Computable (fun p : List Bootstrap.Source.Sigma × List Bootstrap.Source.Sigma =>
        decide (evalMonoidWord gen p.1 = evalMonoidWord gen p.2)) := by
      apply (Primrec.eq.decide.to_comp.comp
        (hnorm.comp Computable.fst) (hnorm.comp Computable.snd)).of_eq
      rintro ⟨u, v⟩
      simp only [decide_eq_decide]
      rw [ULift.ext_iff, heval u, heval v,
        Bootstrap.Quotient.present_eq_iff T' Bootstrap.Source.wf_sigma good stable]
    exact ⟨inferInstance, hdec⟩

end ULiftAndPresentationHelpers

end FiniteAlgebraicEnvelopes

end OAI

end

attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.Family.finiteΓ
attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.Family.finiteQ
attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.Family.decΓ
attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.Family.decQ
attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.Family.codeΓ
attribute [local instance] OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.Family.codeQ

theorem solution {Ghat : Type u} [Group Ghat] [Group.FG Ghat]
    (hGhat : HasDecidableWordProblem Ghat) :
    ∃ (K : Type u) (_ : MonoidWithZero K) (_ : DecidableEq K) (_ : Nontrivial K),
      IsFinitelyPresentedMonoid K ∧
    ∃ (H : Type u) (_ : MonoidWithZero H) (_ : Nontrivial H) (_ : Monoid.FG H),
      HasDecidableWordProblemMonoid H ∧
      (∃ ι : Ghat →* Hˣ, Function.Injective ι) ∧
      (∃ κ : TElem K →* H, Function.Injective κ ∧ κ TElem.zero = 0) ∧
      (∀ (d : ℕ) (h : Fin (d + 1) → H), Function.Injective h → (∀ i, h i ≠ 0) →
        ∃ L R : H, L * h 0 * R = 1 ∧ ∀ i : Fin (d + 1), i ≠ 0 → L * h i * R = 0) ∧
      (∃ c : H → K, (∀ x y, c (x * y) = c x * c y) ∧ Function.Injective c ∧
        ∀ h, c h ≠ 1 ∧ c h ≠ 0) ∧
      (∃ (κ : TElem K →* H) (z : H),
        (∀ τ τ' : TElem K, τ ≠ TElem.zero → τ' ≠ TElem.zero → κ τ * z * κ τ' ≠ 0) ∧
        ∀ τ1 τ1' τ2 τ2' : TElem K, τ1 ≠ TElem.zero → τ1' ≠ TElem.zero →
          τ2 ≠ TElem.zero → τ2' ≠ TElem.zero →
          κ τ1 * z * κ τ1' = κ τ2 * z * κ τ2' → τ1 = τ2 ∧ τ1' = τ2') := by
  classical
  obtain ⟨k, s, hs, h⟩ := hGhat
  let K0 := Bootstrap.Source.pK s h
  let H0 := Bootstrap.Source.pH s h
  let _ : LinearOrder (Compiler.Control.Sector Bootstrap.Source.Sigma
      (Bool × Bootstrap.Source.family.Γ)
      (MachineRealization.ParameterMachine.State Bootstrap.Source.family.Q (Bootstrap.Source.pIndex s h))) :=
    MachineRealization.ParameterCode.finiteOrder
      (T := Bootstrap.Source.Sigma) (Γ := Bootstrap.Source.family.Γ) (Q := Bootstrap.Source.family.Q)
      (Bootstrap.Source.pIndex s h)
  have hK0_nontriv : Nontrivial K0 :=
    ⟨Bootstrap.Source.pCopyEmbedding s h 1, 0,
      Bootstrap.Quotient.rawMap_ne_zero (Bootstrap.Source.pProcessor s h) Bootstrap.Source.wf_sigma
        (Bootstrap.Source.pIndex_good s h) (Bootstrap.Source.pIndex_stable s h)
        Bootstrap.Source.KAlphabet (Bootstrap.Source.pKMachine s h) Bootstrap.Source.family.decode
        (Bootstrap.Source.realizes_pProcessor s h) 1⟩
  have hH0_nontriv : Nontrivial H0 :=
    ⟨1, 0,
      Bootstrap.Quotient.present_nil_ne_zero (Bootstrap.Source.pProcessor s h) Bootstrap.Source.wf_sigma
        (Bootstrap.Source.pIndex_good s h) (Bootstrap.Source.pIndex_stable s h)
        Bootstrap.Source.markers.zero
        (fun j rs hrs => Bootstrap.Source.pTables_short s Bootstrap.Source.family.A Bootstrap.Source.family.M
          (Bootstrap.Source.pIndex s h) j hrs)⟩
  let K : Type u := ULift.{u} K0
  let H : Type u := ULift.{u} H0
  let instMZ_K : MonoidWithZero K := instMonoidWithZeroULift K0
  let instDE_K : DecidableEq K := inferInstance
  let instNT_K : Nontrivial K := @instNontrivialULift K0 _ hK0_nontriv
  let instMZ_H : MonoidWithZero H := instMonoidWithZeroULift H0
  let instNT_H : Nontrivial H := @instNontrivialULift H0 _ hH0_nontriv
  let instFG_H : Monoid.FG H := instFGULift H0
  refine ⟨K, instMZ_K, instDE_K, instNT_K, ?_, H, instMZ_H, instNT_H, instFG_H, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- IsFinitelyPresentedMonoid K
    exact finitelyPresented_of_finite_rel
      (Compiler.Word.rules_finite Bootstrap.Source.KAlphabet (Bootstrap.Source.pKMachine s h))
  · -- HasDecidableWordProblemMonoid H
    have hpart : Partrec (Bootstrap.tableNormal (Bootstrap.Source.pProcessor s h)) :=
      Bootstrap.Source.pIndex_fixed s h ▸
        Bootstrap.Source.partrec_raw.comp (Computable.const (Bootstrap.Source.pIndex s h)) Computable.id
    exact hasDecidableWordProblem_of_tableNormal (Bootstrap.Source.pProcessor s h)
      (Bootstrap.Source.pIndex_good s h) (Bootstrap.Source.pIndex_stable s h) hpart
  · -- (i) Injective group homomorphism Ghat →* Hˣ
    let ι0 : Ghat →* H :=
      (uliftMulEquiv.{u} H0).symm.toMonoidHom.comp (Bootstrap.Source.pGroupEmbedding s h hs)
    have hginj : Function.Injective (Bootstrap.Source.pGroupEmbedding s h hs) :=
      Bootstrap.Quotient.descendCode_injective _ _ _ _
    have hι0_inj : Function.Injective ι0 :=
      (uliftMulEquiv.{u} H0).symm.injective.comp hginj
    refine ⟨ι0.toHomUnits, ?_⟩
    intro g1 g2 hg
    exact hι0_inj (congrArg Units.val hg)
  · -- (ii) Injective unital monoid homomorphism κ : TElem K →* H with κ(0_T) = 0
    let eT : TElem K →* Bootstrap.Source.pT s h := @embedTElemULift.{u} K0 _ _ hK0_nontriv
    let κ : TElem K →* H :=
      ((uliftMulEquiv.{u} H0).symm.toMonoidHom.comp (Bootstrap.Source.pKappa s h)).comp eT
    have hκ_inj : Function.Injective κ :=
      ((uliftMulEquiv.{u} H0).symm.injective.comp
        (Bootstrap.Quotient.descendCode_injective _ _ _ _)).comp
        (@embedTElemULift_injective.{u} K0 _ _ hK0_nontriv)
    have hκ_zero : κ TElem.zero = 0 := by
      change ULift.up (Bootstrap.Source.pKappa s h (eT TElem.zero)) = ⟨0⟩
      rw [@embedTElemULift_zero.{u} K0 _ _ hK0_nontriv, Bootstrap.Source.pKappa_zero]
    exact ⟨κ, hκ_inj, hκ_zero⟩
  · -- (iii) Finite-tuple selector property
    intro d hd hinj hnez
    let hd0 : Fin (d + 1) → H0 := fun i => (hd i).down
    have hinj0 : Function.Injective hd0 := fun i j hij => hinj (ULift.ext _ _ hij)
    have hnez0 : ∀ i, hd0 i ≠ Bootstrap.Quotient.present (Bootstrap.Source.pProcessor s h)
        [Bootstrap.Source.markers.zero] := by
      intro i h0
      exact hnez i (ULift.ext _ _ h0)
    obtain ⟨L0, R0, h0, hi⟩ := Bootstrap.selector_property (Bootstrap.Source.pProcessor s h)
      Bootstrap.Source.wf_sigma (Bootstrap.Source.pIndex_good s h) (Bootstrap.Source.pIndex_stable s h)
      Bootstrap.Source.markers
      (fun j rs hrs => Bootstrap.Source.pTables_absorb s Bootstrap.Source.family.A Bootstrap.Source.family.M
        (Bootstrap.Source.pIndex s h) j hrs)
      (fun j => Bootstrap.Source.pBase s Bootstrap.Source.family.A Bootstrap.Source.family.M
        (Bootstrap.Source.pIndex s h) j)
      (fun j rs hrs => Bootstrap.Source.pTables_members s Bootstrap.Source.family.A Bootstrap.Source.family.M
        (Bootstrap.Source.pIndex s h) j hrs)
      d hd0 hinj0 hnez0
    refine ⟨⟨L0⟩, ⟨R0⟩, ULift.ext _ _ h0, fun i hne => ULift.ext _ _ (hi i hne)⟩
  · -- (iv) Injective multiplicative map c : H → K avoiding {1, 0}
    let c : H → K := fun x => ⟨Bootstrap.Source.pCopyEmbedding s h x.down⟩
    refine ⟨c, ?_, ?_, ?_⟩
    · intro x y
      exact ULift.ext _ _ ((Bootstrap.Source.pCopyEmbedding s h).map_mul x.down y.down)
    · intro x y hxy
      exact ULift.ext _ _ (Bootstrap.Quotient.rawMap_injective
        (Bootstrap.Source.pProcessor s h) Bootstrap.Source.wf_sigma
        (Bootstrap.Source.pIndex_good s h) (Bootstrap.Source.pIndex_stable s h)
        Bootstrap.Source.KAlphabet (Bootstrap.Source.pKMachine s h) Bootstrap.Source.family.decode
        (Bootstrap.Source.realizes_pProcessor s h) (congrArg ULift.down hxy))
    · intro x
      refine ⟨fun h1 => ?_, fun h0 => ?_⟩
      · exact Bootstrap.Quotient.rawMap_ne_one
          (Bootstrap.Source.pProcessor s h) Bootstrap.Source.wf_sigma
          (Bootstrap.Source.pIndex_good s h) (Bootstrap.Source.pIndex_stable s h)
          Bootstrap.Source.KAlphabet (Bootstrap.Source.pKMachine s h) Bootstrap.Source.family.decode
          (Bootstrap.Source.realizes_pProcessor s h) x.down (congrArg ULift.down h1)
      · exact Bootstrap.Quotient.rawMap_ne_zero
          (Bootstrap.Source.pProcessor s h) Bootstrap.Source.wf_sigma
          (Bootstrap.Source.pIndex_good s h) (Bootstrap.Source.pIndex_stable s h)
          Bootstrap.Source.KAlphabet (Bootstrap.Source.pKMachine s h) Bootstrap.Source.family.decode
          (Bootstrap.Source.realizes_pProcessor s h) x.down (congrArg ULift.down h0)
  · -- (v) Separator z ∈ H making (τ, τ') ↦ κ(τ) z κ(τ') injective into H \ {0}
    let eT : TElem K →* Bootstrap.Source.pT s h := @embedTElemULift.{u} K0 _ _ hK0_nontriv
    let κ : TElem K →* H :=
      ((uliftMulEquiv.{u} H0).symm.toMonoidHom.comp (Bootstrap.Source.pKappa s h)).comp eT
    let z : H := ⟨Bootstrap.Source.pSeparator s h⟩
    refine ⟨κ, z, ?_, ?_⟩
    · intro τ τ' hτ hτ'
      have hτ0 : eT τ ≠ 0 := fun h0 => hτ ((@embedTElemULift_eq_zero_iff.{u} K0 _ _ hK0_nontriv τ).mp h0)
      have hτ'0 : eT τ' ≠ 0 := fun h0 => hτ' ((@embedTElemULift_eq_zero_iff.{u} K0 _ _ hK0_nontriv τ').mp h0)
      intro hz
      exact Bootstrap.Source.pSeparator_nonzero s h (eT τ) (eT τ') hτ0 hτ'0 (congrArg ULift.down hz)
    · intro τ1 τ1' τ2 τ2' hτ1 hτ1' hτ2 hτ2' heq
      have h1 : eT τ1 ≠ 0 := fun h0 => hτ1 ((@embedTElemULift_eq_zero_iff.{u} K0 _ _ hK0_nontriv τ1).mp h0)
      have h1' : eT τ1' ≠ 0 := fun h0 => hτ1' ((@embedTElemULift_eq_zero_iff.{u} K0 _ _ hK0_nontriv τ1').mp h0)
      have h2 : eT τ2 ≠ 0 := fun h0 => hτ2 ((@embedTElemULift_eq_zero_iff.{u} K0 _ _ hK0_nontriv τ2).mp h0)
      have h2' : eT τ2' ≠ 0 := fun h0 => hτ2' ((@embedTElemULift_eq_zero_iff.{u} K0 _ _ hK0_nontriv τ2').mp h0)
      obtain ⟨he1, he2⟩ := Bootstrap.Source.pSeparator_inj s h (eT τ1) (eT τ1') (eT τ2) (eT τ2')
        h1 h1' h2 h2' (congrArg ULift.down heq)
      exact ⟨@embedTElemULift_injective.{u} K0 _ _ hK0_nontriv τ1 τ2 he1,
        @embedTElemULift_injective.{u} K0 _ _ hK0_nontriv τ1' τ2' he2⟩

