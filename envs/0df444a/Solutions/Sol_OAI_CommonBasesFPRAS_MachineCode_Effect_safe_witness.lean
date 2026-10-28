-- Prove2me | solution 1 for OAI.CommonBasesFPRAS.MachineCode.Effect.safe_witness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T01:34:01.127681+00:00
-- url     : https://prove2.me/submissions/91f47358-625d-4907-b1c2-528a4aca1f8e

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_OAIQ2Mt000
import Theorems.Thm_OAI_CommonBasesFPRAS_MachineCode_Effect_safe_positiveTest
import Theorems.Thm_OAI_CommonBasesFPRAS_MachineCode_Effect_safe_restartRepeat

section
-- module Solutions.OAIQ2_Mat.MatroidCounting_CommonBases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

section
open scoped RealInnerProductSpace BigOperators Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

open scoped BigOperators Classical

open Set

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance101 : Fintype X]
universe u

omit sectionInstance101 in
lemma Sample.toList_length [Fintype X] {k : ℕ} (v : Sample X k) : v.toList.length=k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ (ih v.2)
end FiniteChain
open scoped BigOperators Classical

end

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

open scoped Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

section
namespace DrawTree
open scoped BigOperators Classical
variable {A B : Type*}

lemma Reindexed.refl (t : DrawTree A) : Reindexed t t := by
  induction t with
  | leaf a => exact .leaf a
  | draw v k ih => exact .draw v k k (Equiv.refl _) ih
lemma Reindexed.all {t u : DrawTree A} (h : Reindexed t u) (P : A → Prop)
    (ht : All P t) : All P u := by
  induction h with
  | leaf a => exact ht
  | draw v k l e h ih =>
    intro i
    simpa using ih (e.symm i) (ht (e.symm i))
end DrawTree

open scoped BigOperators Classical

end

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

section

variable {k n : ℕ}
lemma wordGreedy_length (W : List Bool → Bool) (xs ps : List Bool) :
    (wordGreedy W xs ps).length=xs.length+ps.length := by
  induction xs generalizing ps with
  | nil => simp [wordGreedy]
  | cons b xs ih => simp [wordGreedy,ih,Nat.add_comm,Nat.add_left_comm]

end

section

variable {k n : ℕ}
lemma incrementBits_length (ys : List Bool) : (incrementBits ys).length≤ys.length+1 := by
  induction ys with
  | nil => simp [incrementBits,leadingOnes,carryTail]
  | cons b ys ih =>
    cases b <;> simp only [incrementBits,leadingOnes,carryTail,List.length_append,List.length_replicate,
      List.length_cons] at * <;> omega

end

section

variable {k n : ℕ}

lemma binaryValue_append (xs ys : List Bool) :
    binaryValue (xs++ys)=binaryValue xs+2^xs.length*binaryValue ys := by
  induction xs with
  | nil => simp [binaryValue]
  | cons x xs ih =>
    simp only [List.cons_append,binaryValue,ih,List.length_cons,pow_succ]
    ring

end

variable {k n : ℕ}
lemma bitFrame_length (bs : List Bool) : (bitFrame bs).length=2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [bitFrame,ih]; omega

end

namespace MachineCode

@[simp] lemma pair_length (x y : Word) : (pair x y).length=2*x.length+1+y.length := by
  simp [pair,bitFrame_length]

lemma strip_length (x : Word) : (stripZeros x).length≤x.length := by
  induction x with
  | nil => rfl
  | cons b xs ih => cases b <;> simp only [stripZeros,List.length_cons] <;> omega
lemma strip_append (x y : Word) : stripZeros (x++y)=if stripZeros x=[] then stripZeros y else stripZeros x++y := by
  induction x with
  | nil => simp [stripZeros]
  | cons b xs ih =>
    cases b <;> simp [stripZeros,ih]
    rfl

lemma normal_length (x : Word) : (normalWord x).length≤x.length := by
  simpa only [normalWord,List.length_reverse] using strip_length x.reverse
lemma normalWord_cons (b : Bool) (xs : Word) :
    normalWord (b::xs)=if normalWord xs=[] then (if b then [true] else []) else b::normalWord xs := by
  simp only [normalWord,List.reverse_cons,strip_append]
  by_cases h : stripZeros xs.reverse=[]
  · simp [h]; cases b <;> rfl
  · simp [h,List.reverse_eq_nil_iff]

lemma binaryValue_bits (n : ℕ) : binaryValue n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [binaryValue,ih,Nat.bit]
    omega
lemma normalWord_eq_bits (xs : Word) : normalWord xs=(binaryValue xs).bits := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rw [normalWord_cons,ih]
    by_cases hz : binaryValue xs=0
    · cases b <;> simp [binaryValue,hz]
    · have hb : (binaryValue xs).bits≠[] := by
        intro h
        have he := binaryValue_bits (binaryValue xs)
        rw [h] at he
        exact hz he.symm
      cases b with
      | false => simp [binaryValue,hb,Nat.bit0_bits _ hz]
      | true =>
        simp only [ite_true,ite_eq_right hb,binaryValue]
        rw [Nat.add_comm 1, Nat.bit1_bits]
@[simp] lemma normalWord_bits (n : ℕ) : normalWord n.bits=n.bits := by
  rw [normalWord_eq_bits,binaryValue_bits]

lemma popcountBits_length (xs ys : Word) : (popcountBits xs ys).length≤xs.length+ys.length := by
  induction xs generalizing ys with
  | nil => simp [popcountBits]
  | cons b xs ih =>
    cases b with
    | false => simpa only [popcountBits,Bool.false_eq_true,ite_false,List.length_cons] using
        (ih ys).trans (by omega)
    | true =>
      have h := ih (incrementBits ys)
      have hi := incrementBits_length ys
      simp only [popcountBits,ite_true,List.length_cons]
      omega
lemma rankBits_length {n : ℕ} (O : IndependenceOracle n) (which : Bool) (x : Word) :
    (rankBits which O x).length≤x.length := by
  simpa only [rankBits,wordGreedy_length,List.length_nil,Nat.add_zero] using
    popcountBits_length (wordGreedy (wordOracle which O) x []) []


lemma foldValue_eq_foldl {a b : DataType} (f : Value (.prod a b) → Option (Value b))
    (g : Value b → Value a → Value b) (hf : ∀ x z, f (x,z)=some (g z x))
    (xs : List (Value a)) (z : Value b) : foldValue f xs z=some (xs.foldl g z) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih => simp [foldValue,hf,ih]

namespace Expression
variable {n : ℕ} (O : IndependenceOracle n)
lemma run_listReverse {a : DataType} (xs : List (Value a)) :
    run O listReverse xs=some xs.reverse := by
  simp only [listReverse,run]
  have h := foldValue_eq_foldl (fun p : Value (.prod a (.list a)) => some (p.1::p.2))
    (fun zs x => x::zs) (fun _ _ => rfl) xs []
  simpa using h
lemma run_mapStep {a b c : DataType} (p : Expression (.prod a c) b)
    (f : Value a → Value c → Value b) (hp : ∀ x z, run O p (x,z)=some (f x z))
    (x : Value a) (xs : List (Value b)) (z : Value c) :
    run O (mapStep p) (x,(xs,z))=some (f x z::xs,z) := by
  simp [mapStep,run,hp]
lemma run_mapWith {a b c : DataType} (p : Expression (.prod a c) b)
    (f : Value a → Value c → Value b) (hp : ∀ x z, run O p (x,z)=some (f x z))
    (xs : List (Value a)) (z : Value c) :
    run O (mapWith p) (xs,z)=some (xs.map (fun x => f x z)) := by
  have hf : ∀ (ys : List (Value a)) (acc : List (Value b)),
      foldValue (run O (mapStep p)) ys (acc,z)=some ((ys.map (fun x => f x z)).reverse++acc,z) := by
    intro ys
    induction ys with
    | nil => intro acc; rfl
    | cons x ys ih => intro acc; simp [foldValue,run_mapStep O p f hp,ih,List.append_assoc]
  simp [mapWith,run,hf,run_listReverse]
lemma run_listLength {a : DataType} (xs : List (Value a)) :
    run O listLength xs=some xs.length := by
  have hf : ∀ (ys : List (Value a)) (z : ℕ),
      foldValue (fun p : Value (.prod a .nat) => some (p.2+1)) ys z=some (z+ys.length) := by
    intro ys
    induction ys with
    | nil => intro z; simp [foldValue]
    | cons x ys ih => intro z; simpa [foldValue,ih] using congrArg some (by omega : z+1+ys.length=z+(ys.length+1))
  simp [listLength,run,hf]
lemma run_wordLength (xs : Word) : run O wordLength xs=some xs.length := by
  simp [wordLength,run,run_listLength]
lemma run_wordRepeatStep (b : Bool) (w : Word) :
    run O wordRepeatStep (b,w)=some (if b then false::(w++w) else w++w) := by
  cases b <;> rfl
lemma unary_value (xs : List Bool) (w : Word) :
    ∃ out, foldValue (run O wordRepeatStep) xs.reverse w=some out ∧
      out.length=2^xs.length*w.length+binaryValue xs := by
  induction xs generalizing w with
  | nil => exact ⟨w,rfl,by simp [binaryValue]⟩
  | cons b xs ih =>
    obtain ⟨u,hu,hl⟩ := ih w
    have happ : ∀ (ys zs : List Bool) v,
        foldValue (run O wordRepeatStep) (ys++zs) v=
          (foldValue (run O wordRepeatStep) ys v).bind (foldValue (run O wordRepeatStep) zs) := by
      intro ys
      induction ys with
      | nil => intros; rfl
      | cons y ys ih => intros; simp [foldValue,ih,Option.bind_assoc]
    refine ⟨(if b then false::(u++u) else u++u),?_,?_⟩
    · rw [List.reverse_cons,happ,hu]
      simp only [Option.bind_some,foldValue]
      rw [run_wordRepeatStep]; rfl
    · cases b <;> simp [List.length_append,hl,binaryValue,Nat.pow_succ] <;> ring
lemma run_unary (m : ℕ) : ∃ w,run O unary m=some w ∧ w.length=m := by
  obtain ⟨w,hw,hlen⟩ := unary_value O m.bits []
  refine ⟨w,?_,?_⟩
  · simpa [unary,run] using hw
  · simpa [binaryValue_bits] using hlen
end Expression

@[simp] lemma width_pair {a b : DataType} (x : Value a) (y : Value b) :
    width (a:=.prod a b) (x,y)=2*width x+1+width y := by simp [width,encode]
@[simp] lemma width_cons {a : DataType} (x : Value a) (xs : List (Value a)) :
    width (a:=.list a) (x::xs)=2*width x+2+width (a:=.list a) xs := by
  simp [width,encode,words]; omega
lemma list_length_le_width {a : DataType} (xs : List (Value a)) :
    xs.length≤width (a:=.list a) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.length_cons,width_cons]; omega

lemma safe_input {n S : ℕ} {O : IndependenceOracle n} {a b : DataType}
    {p : Expression a b} {x : Value a} (h : Safe O S p x) : width x≤S := by
  cases p <;> exact h.1
lemma safe_output {n S : ℕ} {O : IndependenceOracle n} {a b : DataType}
    {p : Expression a b} {x : Value a} (h : Safe O S p x) {y : Value b}
    (hr : run O p x=some y) : width y≤S := by
  cases p <;> exact h.2.1 y hr

lemma foldSafe_mono {A B : Type*} (p q : A×B → Prop) (f : A×B → Option B)
    (hpq : ∀ x,p x → q x) (xs : List A) (z : B) (h : FoldSafe p f xs z) :
    FoldSafe q f xs z := by
  induction xs generalizing z with
  | nil => trivial
  | cons x xs ih => exact ⟨hpq _ h.1,fun y hy => ih y (h.2 y hy)⟩
lemma safe_mono {n S T : ℕ} {O : IndependenceOracle n} {a b : DataType}
    (p : Expression a b) (x : Value a) (h : Safe O S p x) (hST : S≤T) : Safe O T p x := by
  induction p with
  | compose p q ihp ihq =>
    exact ⟨h.1.trans hST,fun y hy => (h.2.1 y hy).trans hST,
      ihp _ h.2.2.1,fun y hy => ihq _ (h.2.2.2 y hy)⟩
  | both p q ihp ihq =>
    exact ⟨h.1.trans hST,fun y hy => (h.2.1 y hy).trans hST,ihp _ h.2.2.1,ihq _ h.2.2.2⟩
  | branch p q ihp ihq =>
    refine ⟨h.1.trans hST,fun y hy => (h.2.1 y hy).trans hST,?_⟩
    rcases x with ⟨v,x⟩
    cases v <;> simp only [Bool.false_eq_true,ite_false,ite_true] at *
    · exact ihp _ h.2.2
    · exact ihq _ h.2.2
  | fold p ih =>
    exact ⟨h.1.trans hST,fun y hy => (h.2.1 y hy).trans hST,
      foldSafe_mono _ _ _ (fun x hx => ih x hx) _ _ h.2.2⟩
  | _ => exact ⟨h.1.trans hST,fun y hy => (h.2.1 y hy).trans hST,trivial⟩

lemma safe_compose {n S : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression b c) (x : Value a)
    (hp : Safe O S p x) (hq : ∀ y,run O p x=some y → Safe O S q y) :
    Safe O S (.compose p q) x := by
  refine ⟨safe_input hp,?_,hp,hq⟩
  intro z hz
  simp only [run] at hz
  cases he : run O p x with
  | none => simp [he] at hz
  | some y =>
    simp only [he,Option.bind_some] at hz
    exact safe_output (hq y he) hz
lemma safe_both {n S : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression a c) (x : Value a)
    (hp : Safe O S p x) (hq : Safe O S q x) :
    Safe O (3*S+1) (.both p q) x := by
  have hS : S≤3*S+1 := by omega
  refine ⟨(safe_input hp).trans hS,?_,safe_mono p x hp hS,safe_mono q x hq hS⟩
  intro z hz
  simp only [run] at hz
  cases he : run O p x with
  | none => simp [he] at hz
  | some y =>
    simp only [he] at hz
    cases hf : run O q x with
    | none => simp [hf] at hz
    | some w =>
      simp only [hf,] at hz
      have hh : (y,w)=z := Option.some.inj hz
      cases hh
      have hy := safe_output hp he
      have hw := safe_output hq hf
      rw [width_pair]
      omega
namespace SizePolynomial
lemma monotone (p : SizePolynomial) : Monotone p.eval := by
  intro x y h
  induction p with
  | constant c => rfl
  | input => exact h
  | add p q ihp ihq => exact Nat.add_le_add ihp ihq
  | mul p q ihp ihq => exact Nat.mul_le_mul ihp ihq
lemma eval_subst (p q : SizePolynomial) (x : ℕ) : (p.subst q).eval x=p.eval (q.eval x) := by
  induction p <;> simp_all [subst,eval]
end SizePolynomial

lemma controlled_compose {a b c : DataType} (p : Expression a b) (q : Expression b c)
    (hp : Controlled p) (hq : Controlled q) : Controlled (.compose p q) := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨g,hg⟩ := hq
  refine ⟨.add f (g.subst f),fun O x => ?_⟩
  apply safe_compose O p q x
  · exact safe_mono p x (hf O x) (by simp only [SizePolynomial.eval]; omega)
  · intro y hy
    have h := safe_output (hf O x) hy
    apply safe_mono q y (hg O y)
    rw [SizePolynomial.eval,SizePolynomial.eval_subst]
    exact (g.monotone h).trans (Nat.le_add_left _ _)
lemma controlled_both {a b c : DataType} (p : Expression a b) (q : Expression a c)
    (hp : Controlled p) (hq : Controlled q) : Controlled (.both p q) := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨g,hg⟩ := hq
  refine ⟨.add (.mul (.constant 3) (.add f g)) (.constant 1),fun O x => ?_⟩
  apply safe_both O p q x
  · exact safe_mono p x (hf O x) (Nat.le_add_right _ _)
  · exact safe_mono q x (hg O x) (Nat.le_add_left _ _)
lemma controlled_branch {a b : DataType} (p q : Expression a b)
    (hp : Controlled p) (hq : Controlled q) : Controlled (.branch p q) := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨g,hg⟩ := hq
  refine ⟨.add .input (.add f g),fun O x => ?_⟩
  rcases x with ⟨v,x⟩
  have hw : width x≤width (a:=.prod .bool a) (v,x) := by rw [width_pair]; omega
  have hp' : Safe O (width (a:=.prod .bool a) (v,x)+
      (f.eval (width (a:=.prod .bool a) (v,x))+g.eval (width (a:=.prod .bool a) (v,x)))) p x :=
    safe_mono p x (hf O x) ((f.monotone hw).trans (by omega))
  have hq' : Safe O (width (a:=.prod .bool a) (v,x)+
      (f.eval (width (a:=.prod .bool a) (v,x))+g.eval (width (a:=.prod .bool a) (v,x)))) q x :=
    safe_mono q x (hg O x) ((g.monotone hw).trans (by omega))
  refine ⟨by simp only [SizePolynomial.eval]; omega,?_,?_⟩
  · intro y hy
    cases v
    · exact safe_output hp' hy
    · exact safe_output hq' hy
  · cases v
    · exact hp'
    · exact hq'

lemma bits_length_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h
lemma bits_length_le_value (a : ℕ) : a.bits.length≤a := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr a.lt_two_pow_self
lemma bits_length_add (a b : ℕ) : (a+b).bits.length≤a.bits.length+b.bits.length+1 := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have hpa : 1≤2^a.size := Nat.one_le_pow _ _ (by decide)
  have hpb : 1≤2^b.size := Nat.one_le_pow _ _ (by decide)
  rw [pow_succ,pow_add]
  nlinarith
lemma bits_length_mul (a b : ℕ) : (a*b).bits.length≤a.bits.length+b.bits.length := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  rw [pow_add]
  calc
    a*b≤(2^a.size)*b := Nat.mul_le_mul_right _ (Nat.lt_size_self a).le
    _ < (2^a.size)*(2^b.size) := Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (by positivity)
lemma bits_length_binaryValue (x : Word) : (binaryValue x).bits.length≤x.length := by
  rw [←normalWord_eq_bits]
  exact normal_length x
lemma width_list_bool (x : Word) : width (a:=.list .bool) x=4*x.length := by
  induction x with
  | nil => rfl
  | cons b xs ih =>
    rw [width_cons (a:=.bool),width_bool,ih,List.length_cons]
    omega
lemma width_list_append {a : DataType} (x y : List (Value a)) :
    width (a:=.list a) (x++y)=width (a:=.list a) x+width (a:=.list a) y := by
  induction x with
  | nil => simp
  | cons z x ih => simp only [List.cons_append,width_cons,ih]; omega
lemma width_list_reverse {a : DataType} (x : List (Value a)) :
    width (a:=.list a) x.reverse=width (a:=.list a) x := by
  induction x with
  | nil => rfl
  | cons z x ih => simp only [List.reverse_cons,width_list_append,width_cons,width_nil,ih]; omega
lemma width_list_member {a : DataType} (x : Value a) (xs : List (Value a)) (h : x∈xs) :
    width x≤width (a:=.list a) xs := by
  induction xs with
  | nil => cases h
  | cons z zs ih =>
    simp only [List.mem_cons] at h
    cases h with
    | inl h => subst x; rw [width_cons]; omega
    | inr h => have hi := ih h; rw [width_cons]; omega

lemma safe_atomic {n S : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Expression a b) (x : Value a) (ha : Atomic p) (hx : width x≤S)
    (hy : ∀ y,run O p x=some y → width y≤S) : Safe O S p x := by
  cases p <;> first | contradiction | exact ⟨hx,hy,trivial⟩
lemma atomic_width {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Expression a b) (x : Value a) (ha : Atomic p) (y : Value b) (hy : run O p x=some y) :
    width y≤8*(width x+constantWidth p+1) := by
  cases p with
  | compose | both | branch | fold => contradiction
  | ident => cases hy; simp only [constantWidth]; omega
  | constant z => cases hy; simp only [constantWidth]; omega
  | fst =>
    rcases x with ⟨u,v⟩
    cases hy
    simp only [width_pair,constantWidth]; omega
  | snd =>
    rcases x with ⟨u,v⟩
    cases hy
    simp only [width_pair,constantWidth]; omega
  | @cons a =>
    rcases x with ⟨u,v⟩
    cases hy
    rw [width_pair (a := a) (b := .list a)]
    simp only [width_cons,constantWidth]; omega
  | consBit =>
    rcases x with ⟨u,v⟩
    cases hy
    rw [width_pair (a := .bool) (b := .word)]
    simp only [width_word,List.length_cons,width_bool,constantWidth]; omega
  | append =>
    rcases x with ⟨u,v⟩
    cases hy
    rw [width_pair (a := .word) (b := .word)]
    simp only [width_word,List.length_append,constantWidth]; omega
  | reverse =>
    cases hy
    simp only [width_word,List.length_reverse,constantWidth]; omega
  | toList =>
    cases hy
    rw [width_list_bool]
    simp only [width_word,constantWidth]; omega
  | toBits =>
    cases hy
    simp only [width_word,width_nat,constantWidth]; omega
  | toNat =>
    cases hy
    have h := bits_length_binaryValue x
    simp only [width_word,width_nat,constantWidth]; omega
  | add =>
    rcases x with ⟨u,v⟩
    cases hy
    have h := bits_length_add u v
    rw [width_pair (a := .nat) (b := .nat)]
    simp only [width_nat,constantWidth]; omega
  | mul =>
    rcases x with ⟨u,v⟩
    cases hy
    have h := bits_length_mul u v
    rw [width_pair (a := .nat) (b := .nat)]
    simp only [width_nat,constantWidth]; omega
  | sub =>
    rcases x with ⟨u,v⟩
    simp only [run] at hy
    split_ifs at hy with hv
    · cases hy
      have h := bits_length_mono (Nat.sub_le u v)
      rw [width_pair (a := .nat) (b := .nat)]
      simp only [width_nat,constantWidth]; omega
  | less =>
    simp only [width_bool,constantWidth]; omega
  | divRem =>
    rcases x with ⟨u,v⟩
    simp only [run] at hy
    split_ifs at hy with hv
    · cases hy
      have h₁ := bits_length_mono (Nat.mod_le v u)
      have h₂ := bits_length_mono (Nat.div_le_self v u)
      simp only [width_pair (a := .nat) (b := .nat),width_nat,constantWidth]; omega
  | query b => simp only [width_bool,constantWidth]; omega
  | rank b =>
    simp only [run] at hy
    split_ifs at hy with hx
    · cases hy
      have h₁ := bits_length_binaryValue (rankBits b O x.reverse)
      have h₂ := rankBits_length O b x.reverse
      simp only [List.length_reverse] at h₂
      simp only [width_nat,width_word,constantWidth,rankWord]; omega
lemma controlled_atomic {a b : DataType} (p : Expression a b) (ha : Atomic p) : Controlled p := by
  refine ⟨.mul (.constant 8) (.add (.add .input (.constant (constantWidth p))) (.constant 1)),fun O x => ?_⟩
  apply safe_atomic O p x ha
  · dsimp [SizePolynomial.eval]; omega
  · exact fun y hy => atomic_width O p x ha y hy

lemma foldSafe_prefix {A B : Type*} (ok : A×B → Prop) (f : A×B → Option B)
    (xs : List A) (z : B)
    (h : ∀ pre x post,xs=pre++x::post → ∀ y,foldValue f pre z=some y → ok (x,y)) :
    FoldSafe ok f xs z := by
  induction xs generalizing z with
  | nil => trivial
  | cons x xs ih =>
    refine ⟨h [] x xs rfl z rfl,?_⟩
    intro y hy
    apply ih y
    intro pre a post he w hw
    apply h (x::pre) a post (by simpa using congrArg (List.cons x) he) w
    simp only [foldValue,hy,Option.bind_some]
    exact hw

lemma controlled_fold {a b : DataType} (p : Expression (.prod a b) b)
    (hp : Controlled p) (g : SizePolynomial)
    (hg : ∀ {n : ℕ} (O : IndependenceOracle n) (xs : List (Value a)) (z : Value b)
      (pre post : List (Value a)),xs=pre++post → ∀ y,foldValue (run O p) pre z=some y →
      width y≤g.eval (width (a:=.prod (.list a) b) (xs,z))) :
    Controlled (.fold p) := by
  obtain ⟨f,hf⟩ := hp
  let vP : SizePolynomial := .add (.add (.mul (.constant 2) .input) (.constant 1)) g
  let h : SizePolynomial := .add (.add .input g) (f.subst vP)
  refine ⟨h,fun O x => ?_⟩
  rcases x with ⟨xs,z⟩
  have hS : width (a:=.prod (.list a) b) (xs,z)≤h.eval (width (a:=.prod (.list a) b) (xs,z)) := by
    dsimp [h,SizePolynomial.eval]; omega
  have hgS : g.eval (width (a:=.prod (.list a) b) (xs,z))≤h.eval (width (a:=.prod (.list a) b) (xs,z)) := by
    dsimp [h,SizePolynomial.eval]; omega
  refine ⟨hS,?_,?_⟩
  · intro y hy
    exact (hg O xs z xs [] (by simp) y hy).trans hgS
  · apply foldSafe_prefix
    intro pre v post he y hy
    have hay : width y≤g.eval (width (a:=.prod (.list a) b) (xs,z)) := hg O xs z pre (v::post) he y hy
    have ha : width (a:=a) v≤width (a:=.prod (.list a) b) (xs,z) := by
      have hm : v∈xs := by rw [he]; simp
      have ha := width_list_member v xs hm
      rw [width_pair]; omega
    have hinput : width (a:=.prod a b) (v,y)≤vP.eval (width (a:=.prod (.list a) b) (xs,z)) := by
      rw [width_pair]
      dsimp [vP,SizePolynomial.eval]
      omega
    apply safe_mono p (v,y) (hf O (v,y))
    exact (f.monotone hinput).trans (by
      dsimp only [h,SizePolynomial.eval]
      rw [SizePolynomial.eval_subst]
      omega)

lemma mod_double_lt (a b : ℕ) (hb : 0<b) (hba : b≤a) : 2*(a%b)<a := by
  have hr := Nat.mod_lt a hb
  have hd := Nat.div_pos hba hb
  have hm := Nat.mul_le_mul_left b hd
  have he := Nat.mod_add_div a b
  omega
lemma mod_size_lt (a b : ℕ) (hb : 0<b) (hba : b≤a) : (a%b).size<a.size := by
  have ha : 0<a := lt_of_lt_of_le hb hba
  by_cases hz : a%b=0
  · simpa [hz] using Nat.size_pos.mpr ha
  · have h := Nat.size_le_size (Nat.le_of_lt (mod_double_lt a b hb hba))
    have hs : (2*(a%b)).size=(a%b).size+1 := by
      have he : 2*(a%b)=Nat.bit false (a%b) := by simp [Nat.bit_val]
      rw [he,Nat.size_bit (by simpa [Nat.bit_val] using hz)]
    rw [hs] at h
    omega

lemma gcdSteps_zero (k a : ℕ) : gcdSteps k (a,0)=(a,0) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [gcdSteps,gcdStep] using ih
lemma gcdSteps_done (k a b : ℕ) (hba : b≤a) (hk : a.size+b.size≤k) :
    gcdSteps k (a,b)=(Nat.gcd a b,0) := by
  induction k generalizing a b with
  | zero =>
    have ha : a=0 := Nat.size_eq_zero.mp (by omega)
    have hb : b=0 := Nat.size_eq_zero.mp (by omega)
    simp [ha,hb,gcdSteps]
  | succ k ih =>
    by_cases hb : b=0
    · subst b; simp [gcdSteps_zero]
    · have hb' := Nat.pos_of_ne_zero hb
      have hl := mod_size_lt a b hb' hba
      have hs := Nat.size_le_size hba
      have hh := ih b (a%b) (Nat.le_of_lt (Nat.mod_lt a hb')) (by omega)
      simp only [gcdSteps,gcdStep,hb,ite_false]
      rw [hh,Nat.gcd_comm b (a%b),←Nat.gcd_rec,Nat.gcd_comm b a]

namespace Expression
lemma run_sortPair {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) :
    run O sortPair (a,b)=some (if a<b then (b,a) else (a,b)) := by
  simp only [sortPair,applyIf,swap,run]
  by_cases h : a<b <;> simp [h]
lemma run_gcdStepCode {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) :
    run O gcdStepCode (a,b)=some (gcdStep (a,b)) := by
  by_cases hb : b=0 <;>
    simp [gcdStepCode,applyIf,run,swap,natEqZero,natMod,natDivRem,gcdStep,hb]
lemma fold_gcdStepCode {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) (p : ℕ × ℕ) :
    foldValue (run O (Expression.snd (a:=.bool) >>> gcdStepCode)) xs p=some (gcdSteps xs.length p) := by
  induction xs generalizing p with
  | nil => rfl
  | cons b xs ih =>
    rcases p with ⟨a,c⟩
    change ((run O gcdStepCode (a,c)).bind fun p =>
      foldValue (run O (Expression.snd (a:=.bool) >>> gcdStepCode)) xs p)=_
    rw [run_gcdStepCode,Option.bind_some,ih]
    rfl
lemma run_gcdCode {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) :
    run O gcdCode (a,b)=some (Nat.gcd a b) := by
  unfold gcdCode
  have hs := run_sortPair O a b
  simp only [run]
  rw [hs]
  simp only [Option.bind_some]
  by_cases hab : a<b
  · simp only [hab,ite_true]
    change ((foldValue (run O (Expression.snd (a:=.bool) >>> gcdStepCode)) (b.bits++a.bits) (b,a)).bind
      fun p => some p.1)=some (Nat.gcd a b)
    rw [fold_gcdStepCode]
    simp only [List.length_append,Nat.size_eq_bits_len]
    rw [gcdSteps_done _ _ _ (Nat.le_of_lt hab) (by rfl)]
    simp [Nat.gcd_comm]
  · simp only [hab,ite_false]
    change ((foldValue (run O (Expression.snd (a:=.bool) >>> gcdStepCode)) (a.bits++b.bits) (a,b)).bind
      fun p => some p.1)=some (Nat.gcd a b)
    rw [fold_gcdStepCode]
    simp only [List.length_append,Nat.size_eq_bits_len]
    rw [gcdSteps_done _ _ _ (Nat.le_of_not_gt hab) (by rfl)]
    rfl
end Expression

open Expression
lemma controlled_onLeft {a b c : DataType} (p : Expression a b) (hp : Controlled p) :
    Controlled (onLeft (c:=c) p) := by unfold onLeft; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_onRight {a b c : DataType} (p : Expression a b) (hp : Controlled p) :
    Controlled (onRight (c:=c) p) := by unfold onRight; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_swap {a b : DataType} : Controlled (Expression.swap (a:=a) (b:=b)) := by unfold Expression.swap; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_letIn {a b c : DataType} (p : Expression a b) (q : Expression (.prod a b) c)
    (hp : Controlled p) (hq : Controlled q) : Controlled (letIn p q) := by unfold letIn; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_applyIf {a b : DataType} (p : Expression a .bool) (q r : Expression a b)
    (hp : Controlled p) (hq : Controlled q) (hr : Controlled r) : Controlled (applyIf p q r) := by
  unfold applyIf; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_boolNot : Controlled boolNot := by unfold boolNot; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_boolAnd : Controlled boolAnd := by unfold boolAnd; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_natEqZero : Controlled natEqZero := by unfold natEqZero; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_natSub : Controlled natSub := by unfold natSub; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_natDivRem : Controlled natDivRem := by unfold natDivRem; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_natDiv : Controlled natDiv := by unfold natDiv; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_natMod : Controlled natMod := by unfold natMod; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_listReverse {a : DataType} : Controlled (listReverse (a:=a)) := by
  unfold listReverse
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · apply controlled_fold _ (controlled_atomic (cons (a:=a)) trivial) (.mul (.constant 2) .input)
    intro n O xs z pre post he y hy
    have hh := foldValue_eq_foldl (run O (cons (a:=a))) (fun z x => x::z) (fun _ _ => rfl) pre z
    rw [hh] at hy
    cases hy
    rw [List.foldl_flip_cons_eq_append',width_list_append,width_list_reverse]
    have hp : width (a:=.list a) pre≤width (a:=.list a) xs := by rw [he,width_list_append]; omega
    rw [width_pair (a:=.list a) (b:=.list a)]
    dsimp [SizePolynomial.eval]
    omega
lemma foldl_succ {A : Type*} (l : List A) (z : ℕ) : l.foldl (fun z _ => z+1) z=z+l.length := by
  induction l generalizing z with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons,ih,List.length_cons]; omega
lemma controlled_listLength {a : DataType} : Controlled (listLength (a:=a)) := by
  unfold listLength
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · apply controlled_fold _ (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) (.mul (.constant 2) .input)
    intro n O xs z pre post he y hy
    have hh := foldValue_eq_foldl (run O (both (snd (a:=a)) (constant 1) >>> Expression.add)) (fun z (_ : Value a) => z+1) (fun _ _ => rfl) pre z
    rw [hh] at hy
    cases hy
    have hv := foldl_succ pre z
    rw [hv,width_nat]
    have hbits := bits_length_add z pre.length
    have hlen := bits_length_le_value pre.length
    have hx := list_length_le_width xs
    have hp : pre.length≤xs.length := by rw [he,List.length_append]; omega
    rw [width_pair (a:=.list a) (b:=.nat),width_nat]
    dsimp [SizePolynomial.eval]
    omega
lemma controlled_wordLength : Controlled wordLength := by
  exact controlled_compose _ _ (controlled_atomic _ trivial) controlled_listLength
lemma gcdSteps_max (k a b : ℕ) : (gcdSteps k (a,b)).1≤ max a b ∧ (gcdSteps k (a,b)).2≤ max a b := by
  induction k generalizing a b with
  | zero => exact ⟨Nat.le_max_left _ _,Nat.le_max_right _ _⟩
  | succ k ih =>
    by_cases hb : b=0
    · simpa [hb,gcdStep,gcdSteps] using ih a 0
    · have hi := ih b (a%b)
      have hle : max b (a%b)≤ max a b := max_le (Nat.le_max_right _ _) ((Nat.mod_le _ _).trans (Nat.le_max_left _ _))
      simpa [gcdSteps,gcdStep,hb] using And.intro (hi.1.trans hle) (hi.2.trans hle)
lemma controlled_gcd : Controlled gcdCode := by
  unfold gcdCode
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · apply controlled_compose
    · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
    · apply controlled_compose
      · apply controlled_fold _ (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) (.mul (.constant 4) .input)
        intro n O xs z pre post he y hy
        rcases z with ⟨a,b⟩
        rw [fold_gcdStepCode] at hy
        cases hy
        have hh := gcdSteps_max pre.length a b
        have h₁ := bits_length_mono hh.1
        have h₂ := bits_length_mono hh.2
        have hm : (max a b).bits.length≤a.bits.length+b.bits.length := by
          rcases le_total a b with h|h
          · rw [max_eq_right h]; omega
          · rw [max_eq_left h]; omega
        rw [width_pair (a:=.nat) (b:=.nat),width_pair (a:=.list .bool) (b:=.prod .nat .nat),
          width_pair (a:=.nat) (b:=.nat)]
        simp only [width_nat,SizePolynomial.eval]
        omega
      · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)

open Expression

lemma polySafe_of_controlled {a b : DataType} (p : Expression a b) (hp : Controlled p)
    (R : ℕ → Value a → Prop) (g : SizePolynomial) (hg : ∀ S x,R S x → width x≤g.eval S) :
    PolySafe p R := by
  obtain ⟨f,hf⟩ := hp
  refine ⟨f.subst g,fun O S x hx => ?_⟩
  apply safe_mono p x (hf O x)
  rw [SizePolynomial.eval_subst]
  exact f.monotone (hg S x hx)
lemma polySafe_mono {a b : DataType} (p : Expression a b) {R Q : ℕ → Value a → Prop}
    (hp : PolySafe p Q) (h : ∀ S x,R S x → Q S x) : PolySafe p R := by
  obtain ⟨f,hf⟩ := hp
  exact ⟨f,fun O S x hx => hf O S x (h S x hx)⟩
lemma polySafe_compose {a b c : DataType} (p : Expression a b) (q : Expression b c)
    (R : ℕ → Value a → Prop) (Q : ℕ → Value b → Prop)
    (hp : PolySafe p R) (hq : PolySafe q Q)
    (h : ∀ {n : ℕ} (O : IndependenceOracle n) S x,R S x → ∀ y,run O p x=some y → Q S y) :
    PolySafe (p >>> q) R := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨g,hg⟩ := hq
  refine ⟨.add f g,fun O S x hx => ?_⟩
  apply safe_compose O p q x
  · exact safe_mono p x (hf O S x hx) (Nat.le_add_right _ _)
  · intro y hy
    exact safe_mono q y (hg O S y (h O S x hx y hy)) (Nat.le_add_left _ _)
lemma polySafe_both {a b c : DataType} (p : Expression a b) (q : Expression a c)
    (R : ℕ → Value a → Prop) (hp : PolySafe p R) (hq : PolySafe q R) :
    PolySafe (.both p q) R := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨g,hg⟩ := hq
  refine ⟨.add (.mul (.constant 3) (.add f g)) (.constant 1),fun O S x hx => ?_⟩
  apply safe_both O p q x
  · exact safe_mono p x (hf O S x hx) (Nat.le_add_right _ _)
  · exact safe_mono q x (hg O S x hx) (Nat.le_add_left _ _)
lemma polySafe_fold {a b : DataType} (p : Expression (.prod a b) b)
    (R : ℕ → Value (.prod (.list a) b) → Prop) (Q : ℕ → Value (.prod a b) → Prop)
    (hp : PolySafe p Q) (g : SizePolynomial)
    (hinput : ∀ S x,R S x → width x≤g.eval S)
    (hacc : ∀ {n : ℕ} (O : IndependenceOracle n) S xs z,R S (xs,z) →
      ∀ pre post,xs=pre++post → ∀ y,foldValue (run O p) pre z=some y → width y≤g.eval S)
    (hstep : ∀ {n : ℕ} (O : IndependenceOracle n) S xs z,R S (xs,z) →
      ∀ pre x post,xs=pre++x::post → ∀ y,foldValue (run O p) pre z=some y → Q S (x,y)) :
    PolySafe (.fold p) R := by
  obtain ⟨f,hf⟩ := hp
  refine ⟨.add f g,fun O S x hx => ?_⟩
  obtain ⟨xs,z⟩ := x
  refine ⟨(hinput S (xs,z) hx).trans (Nat.le_add_left _ _),?_,?_⟩
  · intro y hy
    exact (hacc O S xs z hx xs [] (by simp) y hy).trans (Nat.le_add_left _ _)
  · apply foldSafe_prefix
    intro pre x post he y hy
    exact safe_mono p (x,y) (hf O S (x,y) (hstep O S xs z hx pre x post he y hy))
      (Nat.le_add_right _ _)
lemma polySafe_controlled {a b : DataType} (p : Expression a b)
    (hp : PolySafe p (fun S x => width x≤S)) : Controlled p := by
  obtain ⟨f,hf⟩ := hp
  exact ⟨f,fun O x => hf O (width x) x le_rfl⟩

lemma run_mapStep_partial {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression (.prod a c) b) (x : Value a) (zs : List (Value b)) (ctx : Value c) :
    run O (mapStep p) (x,(zs,ctx))=(run O p (x,ctx)).map (fun v => (v::zs,ctx)) := by
  simp only [mapStep,run,bind_pure_comp,Option.bind_some]
  cases he : run O p (x,ctx) <;> simp [he]
lemma fold_mapStep_bound {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression (.prod a c) b) (xs : List (Value a)) (zs : List (Value b)) (ctx : Value c)
    (U : ℕ) (hu : ∀ x∈xs,∀ v,run O p (x,ctx)=some v → width v≤U)
    (y : Value (.prod (.list b) c)) (hy : foldValue (run O (mapStep p)) xs (zs,ctx)=some y) :
    width (a:=.list b) y.1≤width (a:=.list b) zs+xs.length*(2*U+2) ∧ y.2=ctx := by
  induction xs generalizing zs with
  | nil => cases hy; simp
  | cons x xs ih =>
    rw [foldValue,run_mapStep_partial] at hy
    cases he : run O p (x,ctx) with
    | none => simp [he] at hy
    | some v =>
      simp only [he,Option.map_some,Option.bind_some] at hy
      have hv := hu x (by simp) v he
      have hh := ih (v::zs) (fun x hx => hu x (by simp [hx])) hy
      rw [width_cons] at hh
      refine ⟨?_,hh.2⟩
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
lemma controlled_mapStep {a b c : DataType} (p : Expression (.prod a c) b) (hp : Controlled p) :
    Controlled (mapStep p) := by unfold mapStep; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_mapFold {a b c : DataType} (p : Expression (.prod a c) b) (hp : Controlled p) :
    Controlled (.fold (mapStep p)) := by
  obtain ⟨f,hf⟩ := hp
  let s : SizePolynomial := .add (.mul (.constant 3) .input) (.constant 1)
  let g : SizePolynomial := .mul (.add (.mul (.constant 4) .input) (.constant 3))
    (.add (.mul (.constant 2) (f.subst s)) (.constant 3))
  apply controlled_fold _ (controlled_mapStep p ⟨f,hf⟩) g
  intro n O xs z pre post he y hy
  rcases z with ⟨zs,ctx⟩
  let W := width (a:=.prod (.list a) (.prod (.list b) c)) (xs,(zs,ctx))
  have hx : width (a:=.list a) xs≤W := by dsimp [W]; rw [width_pair (a:=.list a) (b:=.prod (.list b) c)]; omega
  have hzs : width (a:=.list b) zs≤W := by dsimp [W]; rw [width_pair (a:=.list a) (b:=.prod (.list b) c),width_pair (a:=.list b) (b:=c)]; omega
  have hc : width ctx≤W := by dsimp [W]; rw [width_pair (a:=.list a) (b:=.prod (.list b) c),width_pair (a:=.list b) (b:=c)]; omega
  have hl : pre.length≤W := by
    have hh := list_length_le_width xs
    have he' := congrArg List.length he
    simp only [List.length_append] at he'
    omega
  let U := f.eval (3*W+1)
  have hh := fold_mapStep_bound O p pre zs ctx U (by
    intro x hxp v hv
    have hxx : x∈xs := by rw [he]; exact List.mem_append_left post hxp
    have hxb := (width_list_member x xs hxx).trans hx
    apply (safe_output (hf O (x,ctx)) hv).trans
    apply f.monotone
    rw [width_pair (a:=a) (b:=c)]
    omega) y hy
  have hm := Nat.mul_le_mul_right (2*U+2) hl
  have hy' : width (a:=.list b) y.1≤W+W*(2*U+2) := by omega
  change width y≤g.eval W
  have hw : width y=2*width (a:=.list b) y.1+1+width ctx := by
    obtain ⟨ys,vctx⟩ := y
    change width (a:=.prod (.list b) c) (ys,vctx)=2*width (a:=.list b) ys+1+width ctx
    rw [width_pair,show vctx=ctx from hh.2]
  rw [hw]
  simp only [g,SizePolynomial.eval,SizePolynomial.eval_subst]
  change _≤(4*W+3)*(2*U+3)
  nlinarith
lemma controlled_mapWith {a b c : DataType} (p : Expression (.prod a c) b) (hp : Controlled p) :
    Controlled (mapWith p) := by
  unfold mapWith
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · apply controlled_compose
    · exact controlled_mapFold p hp
    · apply controlled_compose
      · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
      · exact controlled_listReverse

namespace Expression
lemma run_applyIf {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Expression a .bool) (q r : Expression a b) (x : Value a) :
    run O (applyIf p q r) x=(run O p x).bind (fun t => if t then run O r x else run O q x) := by
  simp [applyIf,run,Option.bind_assoc]
lemma run_letIn {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression (.prod a b) c) (x : Value a) :
    run O (letIn p q) x=(run O p x).bind (fun y => run O q (x,y)) := by
  simp [letIn,run,Option.bind_assoc]

lemma run_normalizeRat {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) :
    run O normalizeRat (a,b)=some (normalizePair a b) := by
  rw [normalizeRat,run_applyIf]
  change ((run O natEqZero b).bind fun t => if t then some (0,1) else _)=_
  rw [run_natEqZero]
  by_cases hb : b=0
  · simp [hb,normalizePair]
  · simp only [hb,decide_false,Option.bind_some,Bool.false_eq_true,ite_false]
    rw [run_letIn,run_gcdCode]
    change (do
      let x ← run O natDiv (Nat.gcd a b,a)
      let y ← run O natDiv (Nat.gcd a b,b)
      pure (x,y))=some (normalizePair a b)
    rw [run_natDiv O _ _,run_natDiv O _ _]
    simp [normalizePair,hb]
lemma run_ratAdd_raw {n : ℕ} (O : IndependenceOracle n) (a b c d : ℕ) :
    run O ratAdd ((a,b),(c,d))=some (normalizePair (a*d+c*b) (b*d)) := by
  change run O normalizeRat (a*d+c*b,b*d)=_
  exact run_normalizeRat O _ _
lemma run_ratMul_raw {n : ℕ} (O : IndependenceOracle n) (a b c d : ℕ) :
    run O ratMul ((a,b),(c,d))=some (normalizePair (a*c) (b*d)) := by
  change run O normalizeRat (a*c,b*d)=_
  exact run_normalizeRat O _ _

lemma foldValue_iterate {n : ℕ} (O : IndependenceOracle n) {a : DataType} (p : Expression a a)
    (f : Value a → Value a) (hp : ∀ x,run O p x=some (f x)) (xs : List Bool) (z : Value a) :
    foldValue (run O (Expression.snd (a:=.bool) >>> p)) xs z=some ((f^[xs.length]) z) := by
  induction xs generalizing z with
  | nil => rfl
  | cons b xs ih =>
    change ((run O p z).bind fun y => foldValue (run O (Expression.snd (a:=.bool) >>> p)) xs y)=_
    rw [hp,Option.bind_some,ih]
    rfl
lemma run_iterateWord {n : ℕ} (O : IndependenceOracle n) {a : DataType} (p : Expression a a)
    (f : Value a → Value a) (hp : ∀ x,run O p x=some (f x)) (w : Word) (z : Value a) :
    run O (iterateWord p) (w,z)=some ((f^[w.length]) z) := by
  change foldValue (run O (Expression.snd (a:=.bool) >>> p)) w z=_
  exact foldValue_iterate O p f hp w z
lemma run_iterateNat {n : ℕ} (O : IndependenceOracle n) {a : DataType} (p : Expression a a)
    (f : Value a → Value a) (hp : ∀ x,run O p x=some (f x)) (k : ℕ) (z : Value a) :
    run O (iterateNat p) (k,z)=some ((f^[k]) z) := by
  obtain ⟨w,hw,hlen⟩ := run_unary O k
  simp only [iterateNat,onLeft,run,Option.bind_some]
  rw [hw]
  change run O (iterateWord p) (w,z)=_
  rw [run_iterateWord O p f hp,hlen]
lemma run_fromList {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) :
    run O fromList xs=some xs := by
  simp only [fromList,run]
  rw [run_listReverse]
  change foldValue (run O consBit) xs.reverse []=some xs
  have hh := foldValue_eq_foldl (run O consBit) (fun z x => x::z) (fun _ _ => rfl) xs.reverse []
  simpa using hh

lemma rangeStep_iterate (k : ℕ) : (rangeStep^[k]) (0,[])=(k,(List.range k).reverse) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; simp [rangeStep,List.range_succ]
lemma run_rangeCode {n : ℕ} (O : IndependenceOracle n) (k : ℕ) :
    run O rangeCode k=some (List.range k) := by
  have hh := run_iterateNat O rangeStepCode rangeStep (fun _ => rfl) k (0,[])
  change ((run O (iterateNat rangeStepCode) (k,(0,[]))).bind fun p => run O listReverse p.2)=_
  rw [hh,rangeStep_iterate,Option.bind_some,run_listReverse,List.reverse_reverse]

lemma run_splitStep {n : ℕ} (O : IndependenceOracle n) {a : DataType} (x : Value a)
    (k : ℕ) (u v : List (Value a)) : run O splitStep (x,(k,(u,v)))=some (splitStepValue (x,(k,(u,v)))) := by
  rw [splitStep,run_applyIf]
  change ((run O natEqZero k).bind fun t => if t then _ else _)=_
  rw [run_natEqZero]
  by_cases hk : k=0
  · subst k; rfl
  · simp only [hk,decide_false,Option.bind_some,Bool.false_eq_true,ite_false]
    change ((run O natSub (k,1)).bind fun j => some (j,(x::u,v)))=_
    rw [run_natSub]
    simp [splitStepValue,hk]
lemma fold_splitStep {n : ℕ} (O : IndependenceOracle n) {a : DataType} (xs : List (Value a))
    (k : ℕ) (u v : List (Value a)) :
    foldValue (run O splitStep) xs (k,(u,v))=
      some (k-xs.length,((xs.take k).reverse++u,(xs.drop k).reverse++v)) := by
  induction xs generalizing k u v with
  | nil => simp [foldValue]
  | cons x xs ih =>
    rw [foldValue,run_splitStep]
    cases k with
    | zero => simpa [splitStepValue,List.append_assoc] using ih 0 u (x::v)
    | succ k => simpa [splitStepValue,List.append_assoc] using ih k (x::u) v
lemma run_splitAtCode {n : ℕ} (O : IndependenceOracle n) {a : DataType} (xs : List (Value a)) (k : ℕ) :
    run O splitAtCode (xs,k)=some (xs.take k,xs.drop k) := by
  change ((foldValue (run O splitStep) xs (k,([],[]))).bind fun p => do
    let x ← run O listReverse p.2.1
    let y ← run O listReverse p.2.2
    pure (x,y))=_
  rw [fold_splitStep]
  simp only [List.append_nil,Option.bind_some]
  rw [run_listReverse,run_listReverse]
  simp
lemma run_takeCode {n : ℕ} (O : IndependenceOracle n) {a : DataType} (xs : List (Value a)) (k : ℕ) :
    run O takeCode (xs,k)=some (xs.take k) := by
  change ((run O splitAtCode (xs,k)).bind fun p => some p.1)=_
  rw [run_splitAtCode]; rfl
lemma run_dropCode {n : ℕ} (O : IndependenceOracle n) {a : DataType} (xs : List (Value a)) (k : ℕ) :
    run O dropCode (xs,k)=some (xs.drop k) := by
  change ((run O splitAtCode (xs,k)).bind fun p => some p.2)=_
  rw [run_splitAtCode]; rfl

lemma run_compose {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression b c) (x : Value a) :
    run O (p >>> q) x=(run O p x).bind (run O q) := rfl
lemma run_both {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression a c) (x : Value a) :
    run O (both p q) x=(run O p x).bind (fun y => (run O q x).map (fun z => (y,z))) := by
  simp only [run]
  congr 1
  funext y
  cases run O q x <;> rfl

lemma foldLast_append {A : Type*} (xs ys : List A) (d : A) :
    foldLast (xs++ys) d=foldLast ys (foldLast xs d) := by
  induction xs generalizing d with
  | nil => rfl
  | cons x xs ih => exact ih x
lemma foldLast_reverse {A : Type*} (xs : List A) (d : A) :
    foldLast xs.reverse d=xs.headD d := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [List.reverse_cons,foldLast_append,foldLast]
lemma run_headD {n : ℕ} (O : IndependenceOracle n) {a} (xs : List (Value a)) (d : Value a) :
    run O headD (xs,d)=some (xs.headD d) := by
  have hf : ∀ (ys : List (Value a)) (z : Value a),
      foldValue (run O (fst (b:=a))) ys z=some (foldLast ys z) := by
    intro ys
    induction ys with
    | nil => intro z; rfl
    | cons y ys ih => intro z; exact ih y
  simp only [headD,onLeft,run,run_listReverse]
  change foldValue (run O (fst (b:=a))) xs.reverse d=_
  rw [hf,foldLast_reverse]
lemma run_getDCode {n : ℕ} (O : IndependenceOracle n) {a} (xs : List (Value a)) (k : ℕ) (d : Value a) :
    run O getDCode ((xs,k),d)=some (xs.getD k d) := by
  simp [getDCode,run]
  rw [run_dropCode O xs k]
  change run O headD (xs.drop k,d)=_
  rw [run_headD]
  congr 1
  induction k generalizing xs with
  | zero => cases xs <;> rfl
  | succ k ih => cases xs with
    | nil => rfl
    | cons x xs => exact ih xs
lemma run_powCode {n : ℕ} (O : IndependenceOracle n) (a k : ℕ) :
    run O powCode (a,k)=some (a^k) := by
  let f : ℕ×ℕ → ℕ×ℕ := fun z => (z.1,z.1*z.2)
  have hi : ∀ j v,(f^[j]) (a,v)=(a,a^j*v) := by
    intro j
    induction j with
    | zero => intro v; simp [f]
    | succ j ih => intro v; rw [Function.iterate_succ_apply',ih]; simp [f,pow_succ]; ring
  have hh := run_iterateNat O powStepCode f (fun _ => rfl) k (a,1)
  simp [powCode,run,hh,hi]

end Expression

open Expression
lemma width_take {a : DataType} (xs : List (Value a)) (k : ℕ) :
    width (a:=.list a) (xs.take k)≤width (a:=.list a) xs := by
  have hh := width_list_append (xs.take k) (xs.drop k)
  rw [List.take_append_drop] at hh
  omega
lemma width_drop {a : DataType} (xs : List (Value a)) (k : ℕ) :
    width (a:=.list a) (xs.drop k)≤width (a:=.list a) xs := by
  have hh := width_list_append (xs.take k) (xs.drop k)
  rw [List.take_append_drop] at hh
  omega
lemma controlled_fromList : Controlled fromList := by
  unfold fromList
  apply controlled_compose
  · exact controlled_both _ _ controlled_listReverse (controlled_atomic _ trivial)
  · apply controlled_fold consBit (controlled_atomic _ trivial) (.mul (.constant 2) .input)
    intro n O xs z pre post he y hy
    have hh := foldValue_eq_foldl (run O consBit) (fun z x => x::z) (fun _ _ => rfl) pre z
    rw [hh] at hy
    cases hy
    rw [List.foldl_flip_cons_eq_append',width_word,List.length_append,List.length_reverse]
    have hp : pre.length≤xs.length := by rw [he,List.length_append]; omega
    rw [width_pair (a:=.list .bool) (b:=.word),width_list_bool,width_word]
    dsimp [SizePolynomial.eval]
    omega
lemma controlled_splitStep {a : DataType} : Controlled (splitStep (a:=a)) := by unfold splitStep; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_splitFold {a : DataType} : Controlled (.fold (splitStep (a:=a))) := by
  apply controlled_fold splitStep controlled_splitStep (.mul (.constant 8) .input)
  intro n O xs z pre post he y hy
  rcases z with ⟨k,u,v⟩
  rw [fold_splitStep] at hy
  cases hy
  have hpre : width (a:=.list a) pre≤width (a:=.list a) xs := by rw [he,width_list_append]; omega
  have ht := width_take (a:=a) pre k
  have hd := width_drop (a:=a) pre k
  have hk := bits_length_mono (Nat.sub_le k pre.length)
  simp only [width_pair (a:=.nat) (b:=.prod (.list a) (.list a)),
    width_pair (a:=.list a) (b:=.list a),width_nat,width_list_append,width_list_reverse,
    width_pair (a:=.list a) (b:=SplitState a),SizePolynomial.eval]
  omega
lemma controlled_splitAt {a : DataType} : Controlled (splitAtCode (a:=a)) := by
  have hf := controlled_splitFold (a:=a)
  have hr := controlled_listReverse (a:=a)
  unfold splitAtCode
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_take {a : DataType} : Controlled (takeCode (a:=a)) :=
  controlled_compose _ _ controlled_splitAt (controlled_atomic _ trivial)
lemma controlled_drop {a : DataType} : Controlled (dropCode (a:=a)) :=
  controlled_compose _ _ controlled_splitAt (controlled_atomic _ trivial)
lemma fold_fst_mem {A : Type*} (xs : List A) (z y : A)
    (hy : foldValue (fun p : A×A => some p.1) xs z=some y) : y=z ∨ y∈xs := by
  induction xs generalizing z with
  | nil => cases hy; exact Or.inl rfl
  | cons x xs ih =>
    change foldValue (fun p : A×A => some p.1) xs x=some y at hy
    rcases ih x hy with h|h
    · exact Or.inr (by simp [h])
    · exact Or.inr (by simp [h])
lemma controlled_headD {a : DataType} : Controlled (headD (a:=a)) := by
  unfold headD
  apply controlled_compose
  · exact controlled_onLeft _ controlled_listReverse
  · apply controlled_fold (Expression.fst (a:=a) (b:=a)) (controlled_atomic _ trivial) (.mul (.constant 2) .input)
    intro n O xs z pre post he y hy
    have hh := fold_fst_mem pre z y hy
    have hw : width y≤width z+width (a:=.list a) xs := by
      rcases hh with hh|hh
      · subst y; omega
      · have hm : y∈xs := by rw [he]; exact List.mem_append_left post hh
        have hb := width_list_member y xs hm
        omega
    rw [width_pair (a:=.list a) (b:=a)]
    dsimp [SizePolynomial.eval]
    omega
lemma controlled_getD {a : DataType} : Controlled (getDCode (a:=a)) := by
  have hd := controlled_drop (a:=a)
  have hh := controlled_headD (a:=a)
  unfold getDCode
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_boolOr : Controlled boolOr := by unfold boolOr; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_natEqual : Controlled natEqual := by unfold natEqual; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_listAll : Controlled listAll := by
  unfold listAll
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · apply controlled_fold boolAnd controlled_boolAnd (.add .input (.constant 1))
    intro n O xs z pre post he y hy
    simp only [width_bool,SizePolynomial.eval]
    omega

open Expression
lemma wordDouble_length_le (w : Word) (b : Bool) : w.length≤(wordDouble w b).length := by
  cases b <;> simp [wordDouble,List.length_append] ; omega
lemma wordDouble_fold_length_le (xs : List Bool) (z : Word) : z.length≤(xs.foldl wordDouble z).length := by
  induction xs generalizing z with
  | nil => rfl
  | cons b xs ih => exact (wordDouble_length_le z b).trans (ih (wordDouble z b))
lemma wordDouble_prefix_length_le (pre post : List Bool) (z : Word) :
    (pre.foldl wordDouble z).length≤((pre++post).foldl wordDouble z).length := by
  rw [List.foldl_append]
  exact wordDouble_fold_length_le post _
lemma fold_wordDouble {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) (z : Word) :
    foldValue (run O wordRepeatStep) xs z=some (xs.foldl wordDouble z) := by
  apply foldValue_eq_foldl
  intro b w
  exact run_wordRepeatStep O b w
lemma controlled_wordRepeatStep : Controlled wordRepeatStep := by unfold wordRepeatStep; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma polySafe_wordRepeatFold : PolySafe (.fold wordRepeatStep)
    (fun S x => x.1.length≤S ∧ (x.1.foldl wordDouble x.2).length≤S) := by
  apply polySafe_fold wordRepeatStep _ (fun S x => width x≤5*S+4)
    (polySafe_of_controlled wordRepeatStep controlled_wordRepeatStep _
      (.add (.mul (.constant 5) .input) (.constant 4)) (by intros; assumption))
    (.add (.mul (.constant 10) .input) (.constant 4))
  · intro S x hx
    obtain ⟨xs,z⟩ := x
    dsimp only [Prod.fst,Prod.snd] at hx
    have hh := wordDouble_fold_length_le xs z
    rw [width_pair (a:=.list .bool) (b:=.word),width_list_bool,width_word]
    dsimp [SizePolynomial.eval]
    omega
  · intro n O S xs z hx pre post he y hy
    dsimp only [Prod.fst,Prod.snd] at hx
    rw [fold_wordDouble] at hy
    cases hy
    have hh := wordDouble_prefix_length_le pre post z
    rw [←he] at hh
    rw [width_word]
    dsimp [SizePolynomial.eval]
    omega
  · intro n O S xs z hx pre b post he y hy
    dsimp only [Prod.fst,Prod.snd] at hx
    rw [fold_wordDouble] at hy
    cases hy
    have hh := wordDouble_prefix_length_le pre (b::post) z
    rw [←he] at hh
    rw [width_pair (a:=.bool) (b:=.word),width_bool,width_word]
    omega
lemma polySafe_unary : PolySafe unary (fun S x => x≤S) := by
  unfold unary
  apply polySafe_compose _ _ _ _
    (polySafe_of_controlled _ (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ .input (by
      intro S x hx
      exact (bits_length_le_value x).trans hx)) polySafe_wordRepeatFold
  intro n O S x hx y hy
  cases hy
  obtain ⟨w,hw,hlen⟩ := unary_value O x.bits []
  rw [fold_wordDouble] at hw
  have hwe : (x.bits.reverse.foldl wordDouble [])=w := Option.some.inj hw
  refine ⟨?_,?_⟩
  · simpa only [List.length_reverse] using (bits_length_le_value x).trans hx
  · rw [hwe,hlen]
    simpa only [List.length_nil,mul_zero,zero_add,binaryValue_bits] using hx

namespace Expression

lemma run_wordGet {n : ℕ} (O : IndependenceOracle n) (x : Word) (j : ℕ) :
    run O wordGet (x,j)=some (x[j]?.getD false) := by
  change run O (getDCode (a:=.bool)) ((x,j),false)=_
  exact run_getDCode O (a:=.bool) x j false
lemma run_wordNot {n : ℕ} (O : IndependenceOracle n) (x : Word) :
    run O wordNot x=some (x.map Bool.not) := by
  change ((run O (mapWith (c:=.unit) (fst >>> boolNot)) (x,())).bind (run O fromList))=_
  rw [run_mapWith O _ (fun b (_ : Unit) => !b) (by intro b z; exact run_boolNot O b)]
  change run O fromList (x.map Bool.not)=_
  exact run_fromList O _
end Expression

lemma foldValue_append {A B : Type*} (f : A×B → Option B) (xs ys : List A) (z : B) :
    foldValue f (xs++ys) z=(foldValue f xs z).bind (foldValue f ys) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,foldValue,ih,Option.bind_assoc]

namespace Expression
lemma run_wordTake {n : ℕ} (O : IndependenceOracle n) (x : Word) (k : ℕ) :
    run O wordTake (x,k)=some (x.take k) := by
  change ((run O (takeCode (a:=.bool)) (x,k)).bind (run O fromList))=_
  rw [run_takeCode]; exact run_fromList O _
lemma run_rejectStep {n : ℕ} (O : IndependenceOracle n) (x : Word) (v k : ℕ) (z : Bool×ℕ) :
    run O rejectStep (x,((v,k),z))=some ((v,k),
      if binaryValue (x.take k).reverse<v then (true,binaryValue (x.take k).reverse) else z) := by
  simp only [rejectStep,run_both,run_letIn,run_compose,run_fst,run_snd,run_constant,
    run_reverse,run_toNat,run_applyIf,Option.bind_some,Option.map_some]
  rw [run_wordTake O x k]
  by_cases h : binaryValue (x.take k).reverse<v <;> simp [run,h]
lemma fold_reject {n : ℕ} (O : IndependenceOracle n) (v k : ℕ) (xs : List Word) (z : Bool×ℕ) :
    foldValue (run O rejectStep) xs.reverse ((v,k),z)=
      some ((v,k),match rejectValue v k xs with | none => z | some y => (true,y)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons,foldValue_append,ih]
    simp only [Option.bind_some,foldValue]
    rw [run_rejectStep]
    simp only [Option.bind_some]
    change _=some ((v,k),match rejectValue v k (x::xs) with | none => z | some y => (true,y))
    simp only [rejectValue]
    split_ifs <;> rfl
lemma run_rejectCode {n : ℕ} (O : IndependenceOracle n) (xs : List Word) (v k : ℕ) :
    run O rejectCode (xs,(v,k))=some (optionData 0 (rejectValue v k xs)) := by
  simp only [rejectCode,run_compose,run_both,run_fst,run_snd,run_constant,Option.bind_some,
    run_listReverse,Option.map_some]
  change ((foldValue (run O rejectStep) xs.reverse ((v,k),(false,0))).bind fun z => some z.2)=_
  rw [fold_reject]
  cases rejectValue v k xs <;> rfl
end Expression

lemma binaryValue_ofFn_reverse (h : ℕ) (bits : BitWord h) :
    binaryValue (List.ofFn bits).reverse=(wordEquiv h bits).val := by
  induction h with
  | zero => simp [wordEquiv,binaryValue]
  | succ h ih =>
    rw [List.ofFn_succ,List.reverse_cons,binaryValue_append]
    simp only [List.length_reverse,List.length_ofFn,ih,binaryValue]
    simp [wordEquiv,Equiv.trans_apply,Fin.consEquiv,finProdFinEquiv,finTwoEquiv]
    cases bits 0 <;> simp <;> rfl

lemma bankEval_bind {A B : Type*} (t : DrawTree A) (f : A → DrawTree B) (bank : Bank) :
    bankEval (t.bind f) bank=
      match bankEval t bank with
      | (none,rest) => (none,rest)
      | (some a,rest) => bankEval (f a) rest := by
  induction t generalizing bank with
  | leaf a => rfl
  | draw v k ih =>
    cases bank with
    | nil => rfl
    | cons rows bank =>
      simp only [DrawTree.bind,bankEval]
      split <;> first | rfl | exact ih _ bank

open Expression

namespace Expression
lemma clog_two_size_pred (v : ℕ) : Nat.clog 2 v=(v-1).size := by
  apply Nat.le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by norm_num)).mpr
    have h := Nat.lt_size_self (v-1)
    omega
  · apply Nat.size_le.mpr
    have h := Nat.le_pow_clog (by norm_num : 1<2) v
    have hp : 0<2^(Nat.clog 2 v) := by positivity
    omega

lemma run_clogCode {n : ℕ} (O : IndependenceOracle n) (v : ℕ) :
    run O clogCode v=some (Nat.clog 2 v) := by
  simp only [clogCode,run_compose,run_both,run_ident,run_constant,Option.bind_some,Option.map_some]
  rw [run_natSub]
  change run O wordLength (v-1).bits=_
  rw [run_wordLength,Nat.size_eq_bits_len,clog_two_size_pred]

end Expression
open Expression
namespace Effect

lemma run_pure {n : ℕ} (O : IndependenceOracle n) {a b} (p : Expression a b)
    (x : Value a) (y : Value b) (bank : Bank) (hp : run O p x=some y) :
    run O (pure p) (x,bank)=some (optionalValue b (some y),bank) := by
  simp only [pure,run_both,run_compose,run_fst,run_snd,run_constant,
    Option.bind_some,hp,Option.map_some]
  rfl
lemma run_bind {n : ℕ} (O : IndependenceOracle n) {a b c} (p : Effect a b) (q : Effect b c)
    (x : Value a) (bank rest : Bank) (y : Option (Value b))
    (hp : run O p (x,bank)=some (optionalValue b y,rest)) :
    run O (bind p q) (x,bank)=
      match y with
      | none => some (optionalValue c none,rest)
      | some z => run O q (z,rest) := by
  cases y <;> dsimp only <;> rw [bind,run_compose,hp,Option.bind_some,run_applyIf] <;> rfl
lemma run_keep {n : ℕ} (O : IndependenceOracle n) {a b} (p : Effect a b)
    (x : Value a) (bank rest : Bank) (y : Value b)
    (hp : run O p (x,bank)=some (optionalValue b (some y),rest)) :
    run O (keep p) (x,bank)=some (optionalValue (.prod a b) (some (x,y)),rest) := by
  rw [keep,run_letIn,hp]
  rfl
lemma run_draw {n : ℕ} (O : IndependenceOracle n) (v : ℕ) (bank : Bank) :
    run O draw (v,bank)=some (optionData 0
      (Expression.rejectValue v (Nat.clog 2 v) (bank.headD [])),bank.drop 1) := by
  simp only [draw,run_both,run_compose,run_fst,run_snd,run_ident,run_constant,Option.bind_some,Option.map_some]
  rw [run_headD,run_clogCode,run_dropCode]
  simp only [Option.bind_some,Option.map_some]
  rw [run_rejectCode]
  rfl

lemma realizes_pure {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b : DataType}
    (p : Expression a b) (encode : A → Value b) (x : Value a) (y : A)
    (hp : run O p x=some (encode y)) : Realizes O (pure p) encode x (.leaf y) := by
  intro bank
  exact run_pure O p x (encode y) bank hp

lemma realizes_bind {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c : DataType}
    (p : Effect a b) (q : Effect b c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree A) (f : A → DrawTree B)
    (hp : Realizes O p ea x t) (hq : ∀ y,Realizes O q eb (ea y) (f y)) :
    Realizes O (bind p q) eb x (t.bind f) := by
  intro bank
  rw [bankEval_bind]
  cases ht : bankEval t bank with
  | mk out rest =>
    have hh := hp bank
    rw [ht] at hh
    cases out with
    | none => exact run_bind O p q x bank rest none hh
    | some y =>
      rw [run_bind O p q x bank rest (some (ea y)) hh]
      exact hq y rest

lemma realizes_keep {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b : DataType}
    (p : Effect a b) (ea : A → Value b) (x : Value a) (t : DrawTree A)
    (hp : Realizes O p ea x t) :
    Realizes O (keep p) (fun y => (x,ea y)) x t := by
  intro bank
  have hh := hp bank
  cases ht : bankEval t bank with
  | mk out rest =>
    rw [ht] at hh
    cases out with
    | none => rw [keep,run_letIn,hh]; rfl
    | some y => exact run_keep O p x bank rest (ea y) hh

lemma realizes_letIn {n : ℕ} (O : IndependenceOracle n) {A B : Type*} {a b c : DataType}
    (p : Effect a b) (q : Effect (.prod a b) c) (ea : A → Value b) (eb : B → Value c)
    (x : Value a) (t : DrawTree A) (f : A → DrawTree B)
    (hp : Realizes O p ea x t) (hq : ∀ y,Realizes O q eb (x,ea y) (f y)) :
    Realizes O (letIn p q) eb x (t.bind f) :=
  realizes_bind O (keep p) q _ eb x t f (realizes_keep O p ea x t hp) hq

lemma realizes_draw {n : ℕ} (O : IndependenceOracle n) (v : ℕ) :
    Realizes O draw Fin.val (v+1) (.draw v DrawTree.leaf) := by
  intro bank
  rw [run_draw]
  cases bank with
  | nil => rfl
  | cons rows bank =>
    simp only [bankEval]
    split
    · rename_i hi
      simp only [List.headD_cons,List.drop_succ_cons,List.drop_zero,hi,Option.map_none]
      rfl
    · rename_i i hi
      simp only [List.headD_cons,List.drop_succ_cons,List.drop_zero,hi,Option.map_some]
      rfl

lemma run_precompose {n : ℕ} (O : IndependenceOracle n) {a b c} (p : Expression a b)
    (q : Effect b c) (x : Value a) (y : Value b) (bank : Bank)
    (hp : run O p x=some y) : run O (precompose p q) (x,bank)=run O q (y,bank) := by
  simp only [precompose,onLeft,run_compose,run_both,run_fst,run_snd,Option.bind_some,hp,Option.map_some]

lemma realizes_precompose {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b c}
    (p : Expression a b) (q : Effect b c) (ea : A → Value c) (x : Value a) (y : Value b)
    (t : DrawTree A) (hp : run O p x=some y) (hq : Realizes O q ea y t) :
    Realizes O (precompose p q) ea x t := by
  intro bank
  rw [run_precompose O p q x y bank hp]
  exact hq bank

end Effect

end MachineCode

namespace MachineCode
open Expression
namespace Effect

lemma Realizes.law {n : ℕ} {O : IndependenceOracle n} {A : Type*} {a b} {p : Effect a b}
    {e : A → Value b} {x : Value a} {t : DrawTree A} (h : Realizes O p e x t) :
    RealizesLaw O p e x t := ⟨t,.refl t,h⟩
lemma law_precompose {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b c}
    (p : Expression a b) (q : Effect b c) (ea : A → Value c) (x : Value a) (y : Value b)
    (t : DrawTree A) (hp : run O p x=some y) (hq : RealizesLaw O q ea y t) :
    RealizesLaw O (precompose p q) ea x t := by
  rcases hq with ⟨u,hu,hq⟩
  exact ⟨u,hu,realizes_precompose O p q ea x y u hp hq⟩
end Effect
end MachineCode

namespace MachineCode

open Expression

lemma polySafe_reparam {a b : DataType} (p : Expression a b) (R : ℕ → Value a → Prop)
    (hp : PolySafe p R) (g : SizePolynomial) : PolySafe p (fun S x => R (g.eval S) x) := by
  obtain ⟨f,hf⟩ := hp
  exact ⟨f.subst g,fun O S x hx => by rw [SizePolynomial.eval_subst]; exact hf O _ x hx⟩
lemma polySafe_post {a b c : DataType} (p : Expression a b) (q : Expression b c)
    (R : ℕ → Value a → Prop) (hp : PolySafe p R) (hq : Controlled q) : PolySafe (p >>> q) R := by
  obtain ⟨f,hf⟩ := hp
  apply polySafe_compose p q R (fun S y => width y≤f.eval S) ⟨f,hf⟩
    (polySafe_of_controlled q hq _ f (by intros; assumption))
  intro n O S x hx y hy
  exact safe_output (hf O S x hx) hy
lemma foldValue_iterateM {n : ℕ} (O : IndependenceOracle n) {a : DataType}
    (p : Expression a a) (xs : List Bool) (z : Value a) :
    foldValue (run O (Expression.snd (a:=.bool) >>> p)) xs z=iterateM (run O p) xs.length z := by
  induction xs generalizing z with
  | nil => rfl
  | cons b xs ih => simp only [foldValue,run_compose,run_snd,Option.bind_some,List.length_cons,iterateM]; simp_rw [ih]

lemma polySafe_iterateNat {a : DataType} (p : Expression a a)
    (R : ℕ → Value (.prod .nat a) → Prop) (Q : ℕ → Value a → Prop)
    (hp : PolySafe p Q) (g : SizePolynomial)
    (hinput : ∀ S k z,R S (k,z) → k+width (a:=a) z≤g.eval S)
    (hacc : ∀ {n : ℕ} (O : IndependenceOracle n) S k z,R S (k,z) →
      ∀ j,j≤k → ∀ y,iterateM (run O p) j z=some y → width (a:=a) y≤g.eval S)
    (hbody : ∀ {n : ℕ} (O : IndependenceOracle n) S k z,R S (k,z) →
      ∀ j,j<k → ∀ y,iterateM (run O p) j z=some y → Q S y) :
    PolySafe (iterateNat p) R := by
  let T : SizePolynomial := .add (.mul (.constant 12) g) (.constant 4)
  have hnatwidth : ∀ S x,R S x → width x≤T.eval S := by
    intro S x hx
    obtain ⟨k,z⟩ := x
    have hh : k+width (a:=a) z≤g.eval S := hinput S k z hx
    have hb := bits_length_le_value k
    rw [width_pair (a:=.nat) (b:=a),width_nat]
    dsimp [T,SizePolynomial.eval]
    have h₁ := Nat.mul_le_mul_left 2 hh
    omega
  have hu : PolySafe (onLeft (c:=a) unary) R := by
    unfold onLeft
    apply polySafe_both
    · apply polySafe_compose _ _ R (fun S k => k≤g.eval S)
        (polySafe_of_controlled Expression.fst (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) R T hnatwidth)
        (polySafe_reparam unary (fun S k => k≤S) polySafe_unary g)
      intro n O S x hx y hy
      obtain ⟨k,z⟩ := x
      simp only [run_fst, Option.some.injEq] at hy
      subst y
      have hh : k+width (a:=a) z≤g.eval S := hinput S k z hx
      exact (Nat.le_add_right k (width (a:=a) z)).trans hh
    · exact polySafe_of_controlled Expression.snd (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) R T hnatwidth
  let Rw : ℕ → Value (.prod .word a) → Prop := fun S x => R S (x.1.length,x.2)
  let Rl : ℕ → Value (.prod (.list .bool) a) → Prop := fun S x => R S (x.1.length,x.2)
  have hw : ∀ S x,Rw S x → width x≤T.eval S := by
    intro S x hx
    obtain ⟨w,z⟩ := x
    have hh : w.length+width (a:=a) z≤g.eval S := hinput S w.length z hx
    rw [width_pair (a:=.word) (b:=a),width_word]
    dsimp [T,SizePolynomial.eval]
    omega
  have hfold : PolySafe (.fold (snd >>> p)) Rl := by
    refine polySafe_fold (Expression.snd (a:=.bool) >>> p) Rl
      (fun S x => width x≤T.eval S ∧ Q S x.2) ?_ T ?_ ?_ ?_
    · apply polySafe_compose _ _ _ Q
        (polySafe_of_controlled Expression.snd (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ T (by intro S x hx; exact hx.1)) hp
      intro n O S x hx y hy
      cases hy
      exact hx.2
    · intro S x hx
      obtain ⟨xs,z⟩ := x
      have hh : xs.length+width (a:=a) z≤g.eval S := hinput S xs.length z hx
      rw [width_pair (a:=.list .bool) (b:=a),width_list_bool]
      dsimp [T,SizePolynomial.eval]
      omega
    · intro n O S xs z hx pre post he y hy
      rw [foldValue_iterateM] at hy
      have hj : pre.length≤xs.length := by rw [he,List.length_append]; omega
      have hh := hacc O S xs.length z hx pre.length hj y hy
      dsimp [T,SizePolynomial.eval]
      omega
    · intro n O S xs z hx pre b post he y hy
      rw [foldValue_iterateM] at hy
      have hj : pre.length<xs.length := by rw [he,List.length_append,List.length_cons]; omega
      have hh := hacc O S xs.length z hx pre.length hj.le y hy
      refine ⟨?_,hbody O S xs.length z hx pre.length hj y hy⟩
      rw [width_pair (a:=.bool) (b:=a),width_bool]
      dsimp [T,SizePolynomial.eval]
      omega
  unfold iterateNat iterateWord
  apply polySafe_compose _ _ R Rw hu
  · apply polySafe_compose _ _ Rw Rl
      (polySafe_of_controlled _ (by unfold onLeft; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) Rw T hw) hfold
    intro n O S x hx y hy
    cases hy
    exact hx
  · intro n O S x hx y hy
    obtain ⟨k,z⟩ := x
    obtain ⟨w,hw,hk⟩ := run_unary O k
    simp only [onLeft,run_both,run_compose,run_fst,run_snd,Option.bind_some,hw,Option.map_some] at hy
    cases hy
    change R S (w.length,z)
    rwa [hk]

lemma iterateM_total {A : Type*} (p : A → Option A) (f : A → A)
    (hp : ∀ x,p x=some (f x)) (k : ℕ) (x : A) : iterateM p k x=some ((f^[k]) x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [iterateM,hp,Option.bind_some,ih,Function.iterate_succ_apply]
lemma width_list_le {a : DataType} (xs : List (Value a)) (S : ℕ)
    (hs : ∀ x∈xs,width (a:=a) x≤S) : width (a:=.list a) xs≤xs.length*(2*S+2) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hs x (by simp)
    have hh := ih (fun y hy => hs y (by simp [hy]))
    rw [width_cons (a:=a),List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
lemma width_range (k : ℕ) : width (a:=.list .nat) (List.range k)≤k*(2*k+2) := by
  simpa only [List.length_range] using width_list_le (a:=.nat) (List.range k) k (by
    intro x hx
    exact (bits_length_le_value x).trans (List.mem_range.mp hx).le)
lemma width_rangeState (k : ℕ) : width (a:=.prod .nat (.list .nat)) (k,(List.range k).reverse)≤4*(k+1)^2 := by
  rw [width_pair (a:=.nat) (b:=.list .nat),width_nat,width_list_reverse (a:=.nat)]
  have h := width_range k
  have h' := bits_length_le_value k
  nlinarith
lemma controlled_rangeStep : Controlled rangeStepCode := by unfold rangeStepCode; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma polySafe_rangeCode : PolySafe rangeCode (fun S k => k≤S) := by
  let g : SizePolynomial := .mul (.constant 10) (.mul (.add .input (.constant 1)) (.add .input (.constant 1)))
  have hg (S : ℕ) : g.eval S=10*(S+1)^2 := by simp [g,SizePolynomial.eval,pow_two]
  let R : ℕ → Value (.prod .nat (.prod .nat (.list .nat))) → Prop := fun S x => x.1≤S ∧ x.2=(0,[])
  have hi : PolySafe (iterateNat rangeStepCode) R := by
    refine polySafe_iterateNat rangeStepCode R (fun S z => width z≤g.eval S)
      (polySafe_of_controlled _ controlled_rangeStep _ g (by intros; assumption)) g ?_ ?_ ?_
    · intro S k z hx
      dsimp [R] at hx
      rcases hx with ⟨hk,rfl⟩
      rw [hg]
      change k+1≤10*(S+1)^2
      exact (Nat.add_le_add_right hk 1).trans (by nlinarith)
    · intro n O S k z hx j hj y hy
      dsimp [R] at hx
      rcases hx with ⟨hk,rfl⟩
      rw [iterateM_total (run O rangeStepCode) rangeStep (fun _ => rfl),rangeStep_iterate] at hy
      cases hy
      apply (width_rangeState j).trans
      rw [hg]
      have hjk : Nat.le j S := hj.trans hk
      exact (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.add_le_add_right hjk 1) 2)).trans
        (Nat.mul_le_mul_right _ (by decide : 4≤10))
    · intro n O S k z hx j hj y hy
      dsimp [R] at hx
      rcases hx with ⟨hk,rfl⟩
      rw [iterateM_total (run O rangeStepCode) rangeStep (fun _ => rfl),rangeStep_iterate] at hy
      cases hy
      apply (width_rangeState j).trans
      rw [hg]
      have hjk : Nat.le j S := hj.le.trans hk
      exact (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.add_le_add_right hjk 1) 2)).trans
        (Nat.mul_le_mul_right _ (by decide : 4≤10))
  unfold rangeCode
  apply polySafe_compose _ _ _ R
    (polySafe_of_controlled _ (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ .input (by
      intro S k hk
      exact (bits_length_le_value k).trans hk))
    (polySafe_post _ _ R hi (controlled_compose _ _ (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) controlled_listReverse))
  intro n O S x hx y hy
  cases hy
  exact ⟨hx,rfl⟩
lemma controlled_wordRange : Controlled (wordLength >>> rangeCode) := by
  apply polySafe_controlled
  apply polySafe_compose _ _ _ (fun S k => k≤S)
    (polySafe_of_controlled _ controlled_wordLength _ .input (by intros; assumption)) polySafe_rangeCode
  intro n O S x hx y hy
  rw [run_wordLength] at hy
  cases hy
  exact hx

lemma run_filterStep_partial {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Expression (.prod a b) .bool) (x : Value a) (ys : List (Value a)) (z : Value b) :
    run O (filterStep p) (x,(ys,z))=(run O p (x,z)).map (fun t => ((if t then x::ys else ys),z)) := by
  simp only [filterStep,run_both,run_applyIf,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some]
  cases he : run O p (x,z) with
  | none => rfl
  | some t => cases t <;> rfl
lemma fold_filterStep_bound {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Expression (.prod a b) .bool) (xs ys : List (Value a)) (z : Value b)
    (v : Value (.prod (.list a) b)) (hv : foldValue (run O (filterStep p)) xs (ys,z)=some v) :
    width (a:=.list a) v.1≤width (a:=.list a) xs+width (a:=.list a) ys ∧ v.2=z := by
  induction xs generalizing ys with
  | nil => cases hv; simp
  | cons x xs ih =>
    rw [foldValue,run_filterStep_partial] at hv
    cases he : run O p (x,z) with
    | none => simp [he] at hv
    | some t =>
      simp only [he,Option.map_some,Option.bind_some] at hv
      cases t with
      | false =>
        have hh := ih ys hv
        rw [width_cons (a:=a)]
        exact ⟨by omega,hh.2⟩
      | true =>
        have hh := ih (x::ys) hv
        rw [width_cons (a:=a)] at hh ⊢
        exact ⟨by omega,hh.2⟩
lemma controlled_filterStep {a b : DataType} (p : Expression (.prod a b) .bool) (hp : Controlled p) :
    Controlled (filterStep p) := by unfold filterStep; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_filterFold {a b : DataType} (p : Expression (.prod a b) .bool) (hp : Controlled p) :
    Controlled (.fold (filterStep p)) := by
  apply controlled_fold _ (controlled_filterStep p hp) (.mul (.constant 3) .input)
  intro n O xs z pre post he y hy
  obtain ⟨ys,ctx⟩ := z
  have hh := fold_filterStep_bound O p pre ys ctx y hy
  have hpre : width (a:=.list a) pre≤width (a:=.list a) xs := by rw [he,width_list_append]; omega
  obtain ⟨out,outctx⟩ := y
  dsimp only [Prod.fst,Prod.snd] at hh
  rw [width_pair (a:=.list a) (b:=b),width_pair (a:=.list a) (b:=.prod (.list a) b),
    width_pair (a:=.list a) (b:=b),hh.2]
  dsimp [SizePolynomial.eval]
  omega
lemma controlled_filterWith {a b : DataType} (p : Expression (.prod a b) .bool) (hp : Controlled p) :
    Controlled (filterWith p) := by
  unfold filterWith
  have hf := controlled_filterFold p hp
  have hr := controlled_listReverse (a:=a)
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)

open scoped Classical

namespace Expression

lemma run_listAppend {n : ℕ} (O : IndependenceOracle n) {a} (xs ys : List (Value a)) :
    run O listAppend (xs,ys)=some (xs++ys) := by
  have hf : ∀ (us vs : List (Value a)),foldValue (run O cons) us vs=some (us.reverse++vs) := by
    intro us
    induction us with
    | nil => intro vs; rfl
    | cons u us ih => intro vs; simpa [foldValue,run,List.reverse_cons,List.append_assoc] using ih (u::vs)
  simp only [listAppend,onLeft,run_compose,run_both,run_fst,run_snd,Option.bind_some]
  rw [run_listReverse]
  simp only [Option.bind_some,Option.map_some]
  change foldValue (run O cons) xs.reverse ys=_
  rw [hf,List.reverse_reverse]

lemma run_productStep {n : ℕ} (O : IndependenceOracle n) {a b}
    (x : Value a) (zs : List (Value a × Value b)) (ys : List (Value b)) :
    run O productStep (x,(zs,ys))=some (zs++ys.map (fun y => (x,y)),ys) := by
  simp only [productStep,run_both,run_compose,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_mapWith O swap (fun y x => (x,y)) (fun _ _ => rfl)]
  simp only [Option.map_some,Option.bind_some]
  rw [run_listAppend]
  rfl
end Expression

open Expression
lemma controlled_listAppend {a : DataType} : Controlled (listAppend (a:=a)) := by
  unfold listAppend
  apply controlled_compose
  · exact controlled_onLeft _ controlled_listReverse
  · apply controlled_fold (Expression.cons (a:=a)) (controlled_atomic _ trivial) (.mul (.constant 2) .input)
    intro n O xs z pre post he y hy
    have hh := foldValue_eq_foldl (run O (cons (a:=a))) (fun z x => x::z) (fun _ _ => rfl) pre z
    rw [hh] at hy
    cases hy
    rw [List.foldl_flip_cons_eq_append',width_list_append,width_list_reverse]
    have hp : width (a:=.list a) pre≤width (a:=.list a) xs := by rw [he,width_list_append]; omega
    rw [width_pair (a:=.list a) (b:=.list a)]
    dsimp [SizePolynomial.eval]
    omega
lemma width_list_map_pair {a b : DataType} (x : Value a) (ys : List (Value b)) :
    width (a:=.list (.prod a b)) (ys.map (fun y => (x,y)))≤
      4*(width x+1)*(width (a:=.list b) ys+1) := by
  have he : width (a:=.list (.prod a b)) (ys.map (fun y => (x,y)))=
      (4*width x+2)*ys.length+width (a:=.list b) ys := by
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.map_cons,width_cons (a:=.prod a b),width_pair (a:=a) (b:=b),ih,
        List.length_cons,width_cons (a:=b)]
      ring
  rw [he]
  have hl := list_length_le_width ys
  nlinarith
lemma width_list_product {a b : DataType} (xs : List (Value a)) (ys : List (Value b)) :
    width (a:=.list (.prod a b)) (xs ×ˢ ys)≤
      8*(width (a:=.list a) xs+1)*(width (a:=.list b) ys+1) := by
  have hh : width (a:=.list (.prod a b)) (xs ×ˢ ys)≤
      4*width (a:=.list a) xs*(width (a:=.list b) ys+1) := by
    induction xs with
    | nil => simp only [List.nil_product,width_nil (a:=.prod a b)]; omega
    | cons x xs ih =>
      rw [List.product_cons,width_list_append (a:=.prod a b)]
      have hx := width_list_map_pair x ys
      rw [width_cons (a:=a)]
      nlinarith
  nlinarith
lemma controlled_productStep {a b : DataType} : Controlled (productStep (a:=a) (b:=b)) := by
  have hm := controlled_mapWith (Expression.swap (a:=b) (b:=a)) controlled_swap
  have ha := controlled_listAppend (a:=.prod a b)
  unfold productStep
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma fold_productStep {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (xs : List (Value a)) (zs : List (Value a×Value b)) (ys : List (Value b)) :
    foldValue (run O (productStep (a:=a) (b:=b))) xs (zs,ys)=some (zs++(xs ×ˢ ys),ys) := by
  induction xs generalizing zs with
  | nil => simp [foldValue]
  | cons x xs ih =>
    rw [foldValue,run_productStep,Option.bind_some,ih]
    simp [List.product_cons,List.append_assoc]
lemma controlled_productCode {a b : DataType} : Controlled (productCode (a:=a) (b:=b)) := by
  unfold productCode
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · apply controlled_compose
    · apply controlled_fold productStep controlled_productStep
        (.mul (.constant 32) (.mul (.add .input (.constant 1)) (.add .input (.constant 1))))
      intro n O xs z pre post he y hy
      rcases z with ⟨zs,ys⟩
      rw [fold_productStep] at hy
      cases hy
      have hp : width (a:=.list a) pre≤width (a:=.list a) xs := by rw [he,width_list_append]; omega
      have hb := width_list_product pre ys
      rw [width_pair (a:=.list (.prod a b)) (b:=.list b),width_list_append,
        width_pair (a:=.list a) (b:=.prod (.list (.prod a b)) (.list b)),
        width_pair (a:=.list (.prod a b)) (b:=.list b)]
      dsimp [SizePolynomial.eval]
      nlinarith
    · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_wordGet : Controlled wordGet := by
  have hg := controlled_getD (a:=.bool)
  unfold wordGet
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_wordNot : Controlled wordNot := by
  have hm := controlled_mapWith (c:=.unit) (fst >>> boolNot) (by
    apply controlled_compose; exact controlled_atomic _ trivial; exact controlled_boolNot)
  have hf := controlled_fromList
  unfold wordNot
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_wordCountStep : Controlled wordCountStep := by unfold wordCountStep; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma fold_wordCount_bound {n : ℕ} (O : IndependenceOracle n) (xs : List Bool) (z y : ℕ)
    (hy : foldValue (run O wordCountStep) xs z=some y) : y≤z+xs.length := by
  induction xs generalizing z with
  | nil => cases hy; simp
  | cons b xs ih =>
    cases b with
    | false => have hh := ih z hy; simp only [List.length_cons]; omega
    | true => have hh := ih (z+1) hy; simp only [List.length_cons]; omega
lemma controlled_wordCount : Controlled wordCount := by
  unfold wordCount
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · apply controlled_compose
    · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
    · apply controlled_fold wordCountStep controlled_wordCountStep (.mul (.constant 2) .input)
      intro n O xs z pre post he y hy
      have hh := bits_length_mono (fold_wordCount_bound O pre z y hy)
      have ha := bits_length_add z pre.length
      have hp : pre.length≤xs.length := by rw [he,List.length_append]; omega
      have hl := bits_length_le_value pre.length
      rw [width_nat,width_pair (a:=.list .bool) (b:=.nat),width_nat,width_list_bool]
      dsimp [SizePolynomial.eval]
      omega
lemma controlled_deficiency : Controlled deficiencyCode := by
  have hl := controlled_wordLength
  have hc := controlled_wordCount
  have hn := controlled_wordNot
  have hs := controlled_natSub
  unfold deficiencyCode
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)

open Expression
lemma controlled_normalizeRat : Controlled normalizeRat := by
  have hg := controlled_gcd
  unfold normalizeRat
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_ratAdd : Controlled ratAdd := by
  have hg := controlled_normalizeRat
  unfold ratAdd
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_ratMul : Controlled ratMul := by
  have hg := controlled_normalizeRat
  unfold ratMul
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_ratDiv : Controlled ratDiv := by
  have hg := controlled_normalizeRat
  unfold ratDiv
  repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma controlled_ratLess : Controlled ratLess := by unfold ratLess; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_ratMinOne : Controlled ratMinOne := by unfold ratMinOne; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))

open Expression
open scoped Classical

open Expression

open scoped Classical

open scoped Classical

open scoped Classical

open Expression

open Expression
open scoped Classical

open scoped Classical

open Expression
namespace Effect

lemma uniformVia_size {A : Type*} [Fintype A] [Nonempty A] (m : ℕ) (e : Fin m ≃ A)
    (h : m=Fintype.card A) (hc : m-1+1=m) :
    (DrawTree.draw (m-1) (fun i => .leaf (e (Fin.cast hc i))))=
      DrawTree.uniformVia A ((finCongr h.symm).trans e) := by
  subst m
  rfl

end Effect

open scoped Classical
open Expression

section
open Expression
open scoped Classical

lemma binaryValue_injective_length (x y : Word) (hlen : x.length=y.length)
    (hv : binaryValue x=binaryValue y) : x=y := by
  induction x generalizing y with
  | nil => cases y <;> simp_all
  | cons b x ih =>
    cases y with
    | nil => simp at hlen
    | cons c y =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hlen
      have hbc : b=c := by cases b <;> cases c <;> simp_all [binaryValue] <;> omega
      subst c
      have hxy : binaryValue x=binaryValue y := by cases b <;> simp_all [binaryValue]
      rw [ih y hlen hxy]

lemma binaryValue_replicate_false (k : ℕ) : binaryValue (List.replicate k false)=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,binaryValue,ih]

lemma padded_range (w : Word) (k : ℕ) (hk : w.length≤k) :
    (List.range k).map (fun i => w[i]?.getD false)=w++List.replicate (k-w.length) false := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    by_cases h : i<w.length
    · rw [List.getElem?_eq_getElem h,List.getElem_append_left h]; rfl
    · rw [List.getElem?_eq_none (by omega),List.getElem_append_right (by omega)]
      simp
namespace Expression

lemma run_paddedBitsCode {n : ℕ} (O : IndependenceOracle n) (k v : ℕ) (hv : v<2^k) :
    run O paddedBitsCode (k,v)=some (List.ofFn ((wordEquiv k).symm ⟨v,hv⟩)) := by
  have hk : v.bits.length≤k := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr hv
  have hr : (List.range k).map (fun i => v.bits[i]?.getD false)=v.bits++List.replicate (k-v.bits.length) false := padded_range _ _ hk
  have he : ((List.range k).map (fun i => v.bits[i]?.getD false)).reverse=
      List.ofFn ((wordEquiv k).symm ⟨v,hv⟩) := by
    apply List.reverse_inj.mp
    simp only [List.reverse_reverse]
    apply binaryValue_injective_length
    · simp
    · rw [hr,binaryValue_append,binaryValue_replicate_false,binaryValue_bits,binaryValue_ofFn_reverse]
      simp
  simp only [paddedBitsCode,run_compose,run_both,run_fst,run_snd,Option.bind_some]
  rw [run_rangeCode]
  change ((run O (mapWith (c:=.word) (Expression.swap >>> wordGet)) (List.range k,v.bits)).bind fun l =>
    (run O fromList l).bind (run O reverse))=_
  rw [run_mapWith O (c:=.word) (Expression.swap >>> wordGet) (fun i w => w[i]?.getD false) (fun i w => run_wordGet O w i)]
  simp only [Option.bind_some]
  rw [run_fromList]
  exact congrArg some he

lemma plainDecodeCode_source {n : ℕ} (O : IndependenceOracle n) (v : Fin (2^n)) :
    run O plainDecodeCode (n,v.val)=some (stateEncode (wordPlainEquiv n ((wordEquiv n).symm v)).val.val) := by
  rw [plainDecodeCode,run_compose,run_paddedBitsCode O n v.val v.isLt,Option.bind_some,run_both,run_ident,Option.bind_some,run_wordNot]
  simp only [Option.map_some]
  congr 1
  change (List.ofFn _,(List.ofFn _).map Bool.not)=_
  unfold stateEncode wordPlainEquiv
  simp only []
  apply Prod.ext
  · apply List.ext_getElem <;> simp [transversal]
  · apply List.ext_getElem <;> simp [transversal]
end Expression
namespace Effect
attribute [local instance] OAI.CommonBasesFPRAS.MachineCode.Effect.instNonemptyPlainIndexSumFinPairedSlots
lemma plainCode_source {n : ℕ} (O : IndependenceOracle n) :
    RealizesLaw O plainCode (fun S : PlainIndex (pairedSlots n) => stateEncode S.val.val) n
      (DrawTree.uniformVia _ (canonicalPlainEnumeration n)) := by
  have hp : 0<2^n := by positivity
  let hc : 2^n-1+1=2^n := by omega
  let e : Fin (2^n) ≃ PlainIndex (pairedSlots n) := (wordEquiv n).symm.trans (wordPlainEquiv n)
  let t : DrawTree (PlainIndex (pairedSlots n)) := .draw (2^n-1) (fun i => .leaf (e (Fin.cast hc i)))
  have ht : t=DrawTree.uniformVia _ (canonicalPlainEnumeration n) := by
    exact uniformVia_size (2^n) e (plainIndex_card n).symm hc
  rw [←ht]
  apply Realizes.law
  change Realizes O (letIn (a:=.nat) (b:=.nat) (c:=StateData) _ _) _ n
    ((DrawTree.draw (2^n-1) DrawTree.leaf).bind (fun i => .leaf (e (Fin.cast hc i))))
  apply realizes_letIn O (a:=.nat) (b:=.nat) (c:=StateData) _ _
    (fun i : Fin (2^n-1+1) => i.val) _ n _ _
  · apply realizes_precompose O _ draw _ _ (2^n)
    · change run O powCode (2,n)=_; exact run_powCode O 2 n
    · simpa only [hc] using realizes_draw O (2^n-1)
  · intro i
    apply realizes_pure
    exact plainDecodeCode_source O (Fin.cast hc i)

end Effect

open Effect
end

open Expression
open scoped Classical
end MachineCode

namespace MachineCode

open Expression

open Expression

lemma bits_length_add_max (a b : ℕ) : (a+b).bits.length≤ max a.bits.length b.bits.length+1 := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have ha := (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.le_max_left a.size b.size))
  have hb := (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.le_max_right a.size b.size))
  rw [pow_succ]
  omega

lemma pairHeight_pos (p : ℕ × ℕ) : 1≤pairHeight p := Nat.le_max_left _ _
lemma pairHeight_fst (p : ℕ × ℕ) : p.1.bits.length≤pairHeight p := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
lemma pairHeight_snd (p : ℕ × ℕ) : p.2.bits.length≤pairHeight p := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
lemma width_le_pairHeight (p : ℕ × ℕ) : width (a:=NN) p≤4*pairHeight p := by
  obtain ⟨a,b⟩ := p
  have h₀ := pairHeight_pos (a,b)
  have h₁ := pairHeight_fst (a,b)
  have h₂ := pairHeight_snd (a,b)
  dsimp only [Prod.fst,Prod.snd] at h₁ h₂
  rw [width_pair (a:=.nat) (b:=.nat),width_nat,width_nat]
  omega
lemma pairHeight_le_width (p : ℕ × ℕ) : pairHeight p≤width (a:=NN) p := by
  obtain ⟨a,b⟩ := p
  simp only [pairHeight,width_pair (a:=.nat) (b:=.nat),width_nat]
  omega
lemma pairHeight_normalize (a b : ℕ) : pairHeight (normalizePair a b)≤pairHeight (a,b) := by
  by_cases hb : b=0
  · subst b
    simp [normalizePair,pairHeight]
  · rw [normalizePair,ite_eq_right hb]
    have h₁ := bits_length_mono (Nat.div_le_self a (Nat.gcd a b))
    have h₂ := bits_length_mono (Nat.div_le_self b (Nat.gcd a b))
    dsimp [pairHeight]
    omega
lemma pairHeight_ratAdd_raw (a b c d : ℕ) :
    pairHeight (normalizePair (a*d+c*b) (b*d))≤pairHeight (a,b)+pairHeight (c,d)+1 := by
  apply (pairHeight_normalize _ _).trans
  have h₁ := bits_length_mul a d
  have h₂ := bits_length_mul c b
  have h₃ := bits_length_mul b d
  have h₄ := bits_length_add_max (a*d) (c*b)
  have ha := pairHeight_fst (a,b)
  have hb := pairHeight_snd (a,b)
  have hc := pairHeight_fst (c,d)
  have hd := pairHeight_snd (c,d)
  dsimp only [pairHeight] at *
  omega
lemma pairHeight_ratMul_raw (a b c d : ℕ) :
    pairHeight (normalizePair (a*c) (b*d))≤pairHeight (a,b)+pairHeight (c,d) := by
  apply (pairHeight_normalize _ _).trans
  have h₁ := bits_length_mul a c
  have h₂ := bits_length_mul b d
  have ha := pairHeight_fst (a,b)
  have hb := pairHeight_snd (a,b)
  have hc := pairHeight_fst (c,d)
  have hd := pairHeight_snd (c,d)
  have hp := pairHeight_pos (a,b)
  dsimp only [pairHeight] at *
  omega
lemma run_ratAdd_height {n : ℕ} (O : IndependenceOracle n) (p q y : ℕ×ℕ)
    (hy : run O ratAdd (p,q)=some y) : pairHeight y≤ pairHeight p+pairHeight q+1 := by
  obtain ⟨a,b⟩ := p
  obtain ⟨c,d⟩ := q
  rw [run_ratAdd_raw] at hy
  cases hy
  exact pairHeight_ratAdd_raw _ _ _ _
lemma run_ratMul_height {n : ℕ} (O : IndependenceOracle n) (p q y : ℕ×ℕ)
    (hy : run O ratMul (p,q)=some y) : pairHeight y≤ pairHeight p+pairHeight q+1 := by
  obtain ⟨a,b⟩ := p
  obtain ⟨c,d⟩ := q
  rw [run_ratMul_raw] at hy
  cases hy
  have hh := pairHeight_ratMul_raw a b c d
  omega
lemma fold_pairHeight {n : ℕ} (O : IndependenceOracle n) (p : Expression (.prod NN NN) NN)
    (hp : ∀ x z y,run O p (x,z)=some y → pairHeight y≤pairHeight x+pairHeight z+1)
    (xs : List (ℕ×ℕ)) (z y : ℕ×ℕ) (hy : foldValue (run O p) xs z=some y) :
    pairHeight y≤pairHeight z+width (a:=.list NN) xs := by
  induction xs generalizing z with
  | nil => cases hy; simp
  | cons x xs ih =>
    rw [foldValue] at hy
    cases he : run O p (x,z) with
    | none => simp [he] at hy
    | some w =>
      simp only [he,Option.bind_some] at hy
      have hw := hp x z w he
      have hh := ih w hy
      have hx := pairHeight_le_width x
      rw [width_cons (a:=NN)]
      omega
lemma controlled_pairFold (p : Expression (.prod NN NN) NN) (hp : Controlled p)
    (hg : ∀ {n : ℕ} (O : IndependenceOracle n) (x z y : ℕ×ℕ),
      run O p (x,z)=some y → pairHeight y≤pairHeight x+pairHeight z+1) : Controlled (.fold p) := by
  apply controlled_fold p hp (.mul (.constant 4) .input)
  intro n O xs z pre post he y hy
  have hh := fold_pairHeight O p (hg O) pre z y hy
  have hb := width_le_pairHeight y
  have hz := pairHeight_le_width z
  have hpre : width (a:=.list NN) pre≤width (a:=.list NN) xs := by rw [he,width_list_append]; omega
  simp only [SizePolynomial.eval,width_pair (a:=.list NN) (b:=NN)]
  omega
lemma controlled_ratSum : Controlled ratSumCode := by
  unfold ratSumCode
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · exact controlled_pairFold ratAdd controlled_ratAdd run_ratAdd_height
lemma controlled_ratProduct : Controlled ratProductCode := by
  unfold ratProductCode
  apply controlled_compose
  · repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
  · exact controlled_pairFold ratMul controlled_ratMul run_ratMul_height


lemma controlled_wordTake : Controlled wordTake := by unfold wordTake; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_clog : Controlled clogCode := by unfold clogCode; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_rejectStep : Controlled rejectStep := by
  have h := controlled_wordTake
  unfold rejectStep
  repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma fold_reject_width {n : ℕ} (O : IndependenceOracle n) (xs : List Word)
    (v k : ℕ) (z : Bool×ℕ) (y : Value RejectState)
    (hy : foldValue (run O rejectStep) xs ((v,k),z)=some y) :
    y.1=(v,k) ∧ y.2.2.bits.length ≤ max z.2.bits.length v.bits.length := by
  induction xs generalizing z with
  | nil => cases hy; exact ⟨rfl,Nat.le_max_left _ _⟩
  | cons x xs ih =>
    rw [foldValue,run_rejectStep] at hy
    simp only [Option.bind_some] at hy
    split_ifs at hy with hh
    · have hi := ih _ hy
      refine ⟨hi.1,hi.2.trans ?_⟩
      have hb := bits_length_mono hh.le
      dsimp only [Prod.snd]
      exact max_le (hb.trans (Nat.le_max_right _ _)) (Nat.le_max_right _ _)
    · exact ih z hy
lemma controlled_rejectFold : Controlled (.fold rejectStep) := by
  apply controlled_fold rejectStep controlled_rejectStep (.mul (.constant 3) .input)
  intro n O xs z pre post he y hy
  obtain ⟨⟨v,k⟩,⟨b,u⟩⟩ := z
  change ℕ at v k u
  obtain ⟨⟨v',k'⟩,⟨b',u'⟩⟩ := y
  change ℕ at v' k' u'
  have hh := fold_reject_width O pre v k (b,u) ((v',k'),(b',u')) hy
  dsimp only [Prod.fst,Prod.snd] at hh
  rw [width_pair (a:=NN) (b:=Optional .nat),hh.1,width_pair (a:=.bool) (b:=.nat),width_bool,width_nat]
  simp only [SizePolynomial.eval,width_pair (a:=.list .word) (b:=RejectState),
    width_pair (a:=NN) (b:=Optional .nat),width_pair (a:=.bool) (b:=.nat),
    width_pair (a:=.nat) (b:=.nat),width_nat,width_bool] at *
  omega
lemma controlled_reject : Controlled rejectCode := by
  have h := controlled_rejectFold
  unfold rejectCode
  repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
namespace Effect
lemma controlled_pure {a b : DataType} (p : Expression a b) (hp : Controlled p) : Controlled (pure p) := by
  unfold pure; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply _root_.OAI.CommonBasesFPRAS.MachineCode.controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_bind {a b c : DataType} (p : Effect a b) (q : Effect b c)
    (hp : Controlled p) (hq : Controlled q) : Controlled (bind p q) := by unfold bind; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply _root_.OAI.CommonBasesFPRAS.MachineCode.controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_keep {a b : DataType} (p : Effect a b) (hp : Controlled p) : Controlled (keep p) := by
  unfold keep; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply _root_.OAI.CommonBasesFPRAS.MachineCode.controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma controlled_letIn {a b c : DataType} (p : Effect a b) (q : Effect (.prod a b) c)
    (hp : Controlled p) (hq : Controlled q) : Controlled (letIn p q) :=
  controlled_bind _ _ (controlled_keep _ hp) hq
lemma controlled_draw : Controlled draw := by
  have h₁ := controlled_reject
  have h₂ := controlled_clog
  unfold draw
  repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
end Effect

lemma bits_length_pow (a k : ℕ) : (a^k).bits.length≤k*a.bits.length+1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h := bits_length_mul (a^k) a
    rw [Nat.add_mul,Nat.one_mul]
    omega
lemma powStep_iterate (a k : ℕ) : ((fun z : ℕ×ℕ => (z.1,z.1*z.2))^[k]) (a,1)=(a,a^k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply',ih,pow_succ]; simp [mul_comm]
lemma controlled_powStep : Controlled powStepCode := by unfold powStepCode; (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))
lemma polySafe_powCode : PolySafe powCode (fun S x => x.1.bits.length≤S ∧ x.2≤S) := by
  let g : SizePolynomial := .mul (.constant 10) (.mul (.add .input (.constant 1)) (.add .input (.constant 1)))
  have hg (S : ℕ) : g.eval S=10*(S+1)^2 := by simp [g,SizePolynomial.eval,pow_two]
  let R : ℕ → Value (.prod .nat NN) → Prop := fun S x => x.1≤S ∧ x.2.1.bits.length≤S ∧ x.2.2=1
  have hi : PolySafe (iterateNat powStepCode) R := by
    refine polySafe_iterateNat powStepCode R (fun S z => width z≤g.eval S)
      (polySafe_of_controlled _ controlled_powStep _ g (by intros; assumption)) g ?_ ?_ ?_
    · intro S k z hx
      obtain ⟨a,v⟩ := z
      dsimp [R] at hx
      rcases hx with ⟨hk,ha,rfl⟩
      rw [hg,width_pair (a:=.nat) (b:=.nat),width_nat,width_nat]
      have h1 : (1:ℕ).bits.length=1 := rfl
      rw [h1]
      calc
        _ ≤ S+(2*S+1+1) := Nat.add_le_add hk (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 2 ha) 1) 1)
        _ ≤ _ := by nlinarith
    · intro n O S k z hx j hj y hy
      obtain ⟨a,v⟩ := z
      dsimp [R] at hx
      rcases hx with ⟨hk,ha,rfl⟩
      rw [iterateM_total (run O powStepCode) (fun z : ℕ×ℕ => (z.1,z.1*z.2)) (fun _ => rfl),powStep_iterate] at hy
      cases hy
      rw [width_pair (a:=.nat) (b:=.nat),width_nat,width_nat,hg]
      have hh := bits_length_pow a j
      have hm : j*a.bits.length≤S*S := Nat.mul_le_mul (hj.trans hk) ha
      have hb := hh.trans (Nat.add_le_add_right hm 1)
      calc
        _ ≤ 2*S+1+(S*S+1) := Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2 ha) 1) hb
        _ ≤ _ := by nlinarith
    · intro n O S k z hx j hj y hy
      obtain ⟨a,v⟩ := z
      dsimp [R] at hx
      rcases hx with ⟨hk,ha,rfl⟩
      rw [iterateM_total (run O powStepCode) (fun z : ℕ×ℕ => (z.1,z.1*z.2)) (fun _ => rfl),powStep_iterate] at hy
      cases hy
      rw [width_pair (a:=.nat) (b:=.nat),width_nat,width_nat,hg]
      have hh := bits_length_pow a j
      have hm : j*a.bits.length≤S*S := Nat.mul_le_mul (hj.le.trans hk) ha
      have hb := hh.trans (Nat.add_le_add_right hm 1)
      calc
        _ ≤ 2*S+1+(S*S+1) := Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2 ha) 1) hb
        _ ≤ _ := by nlinarith
  unfold powCode
  apply polySafe_compose _ _ _ R
    (polySafe_of_controlled _ (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ (.add (.mul (.constant 3) .input) (.constant 1)) (by
      intro S x hx
      obtain ⟨a,k⟩ := x
      dsimp only [Prod.fst,Prod.snd] at hx
      rw [width_pair (a:=.nat) (b:=.nat),width_nat,width_nat]
      have hk : k.bits.length≤S := (bits_length_le_value k).trans hx.2
      dsimp [SizePolynomial.eval]
      omega)) (polySafe_post _ _ R hi (by (repeat' (first | assumption | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))))
  intro n O S x hx y hy
  cases hy
  exact ⟨hx.2,hx.1,rfl⟩

lemma run_both_parts {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression a c) (x : Value a) (z : Value (.prod b c))
    (hz : run O (both p q) x=some z) : run O p x=some z.1 ∧ run O q x=some z.2 := by
  rw [run_both] at hz
  cases hp : run O p x with
  | none => simp [hp] at hz
  | some y =>
    simp only [hp,Option.bind_some] at hz
    cases hq : run O q x with
    | none => simp [hq] at hz
    | some w =>
      simp only [hq,Option.map_some,Option.some.injEq] at hz
      subst z
      exact ⟨rfl,rfl⟩
lemma width_fst {a b : DataType} (x : Value (.prod a b)) : width x.1≤width x := by
  obtain ⟨p,q⟩ := x; simp only [width_pair]; omega
lemma width_snd {a b : DataType} (x : Value (.prod a b)) : width x.2≤width x := by
  obtain ⟨p,q⟩ := x; simp only [width_pair]; omega

lemma bankEval_rest_suffix {A : Type*} (t : DrawTree A) (bank : Bank) :
    ∃ pre,bank=pre++(bankEval t bank).2 := by
  induction t generalizing bank with
  | leaf a => exact ⟨[],rfl⟩
  | draw v k ih =>
    cases bank with
    | nil => exact ⟨[],rfl⟩
    | cons row bank =>
      simp only [bankEval]
      split
      · exact ⟨[row],rfl⟩
      · rename_i i hi
        obtain ⟨pre,hpre⟩ := ih ⟨i,rejectValue_lt _ _ _ hi⟩ bank
        exact ⟨row::pre,congrArg (List.cons row) hpre⟩
lemma bankEval_rest_width {A : Type*} (t : DrawTree A) (bank : Bank) :
    width (a:=BankData) (bankEval t bank).2≤width (a:=BankData) bank := by
  obtain ⟨pre,hpre⟩ := bankEval_rest_suffix t bank
  calc
    width (a:=BankData) (bankEval t bank).2 ≤ width (a:=BankData) (pre ++ (bankEval t bank).2) := by
      rw [width_list_append (a:=RandomRows)]; exact Nat.le_add_left _ _
    _ = width (a:=BankData) bank := congrArg (width (a:=BankData)) hpre.symm

open Expression

open Expression
lemma oracleSafe_lift {a b : DataType} (p : Expression a b) (R : ℕ → Value a → Prop)
    (h : PolySafe p R) : OracleSafe p (fun _ _ => R) := h
lemma oracleSafe_controlled {a b : DataType} (p : Expression a b) (hp : Controlled p)
    (R : OraclePredicate a) (g : SizePolynomial)
    (hg : ∀ n O S x,R n O S x → width x≤g.eval S) : OracleSafe p R := by
  obtain ⟨f,hf⟩ := hp
  refine ⟨f.subst g,fun O S x hx => ?_⟩
  apply safe_mono p x (hf O x)
  rw [SizePolynomial.eval_subst]
  exact f.monotone (hg _ O S x hx)
lemma oracleSafe_mono {a b : DataType} (p : Expression a b) {R Q : OraclePredicate a}
    (hp : OracleSafe p Q) (h : ∀ n O S x,R n O S x → Q n O S x) : OracleSafe p R := by
  obtain ⟨f,hf⟩ := hp
  exact ⟨f,fun O S x hx => hf O S x (h _ O S x hx)⟩
lemma oracleSafe_reparam {a b : DataType} (p : Expression a b) (R : OraclePredicate a)
    (hp : OracleSafe p R) (g : SizePolynomial) : OracleSafe p (fun n O S x => R n O (g.eval S) x) := by
  obtain ⟨f,hf⟩ := hp
  exact ⟨f.subst g,fun O S x hx => by rw [SizePolynomial.eval_subst]; exact hf O _ x hx⟩
lemma oracleSafe_compose {a b c : DataType} (p : Expression a b) (q : Expression b c)
    (R : OraclePredicate a) (Q : OraclePredicate b) (hp : OracleSafe p R) (hq : OracleSafe q Q)
    (h : ∀ n O S x,R n O S x → ∀ y,run O p x=some y → Q n O S y) : OracleSafe (p >>> q) R := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨g,hg⟩ := hq
  refine ⟨.add f g,fun O S x hx => ?_⟩
  apply safe_compose O p q x
  · exact safe_mono p x (hf O S x hx) (Nat.le_add_right _ _)
  · intro y hy
    exact safe_mono q y (hg O S y (h _ O S x hx y hy)) (Nat.le_add_left _ _)
lemma oracleSafe_both {a b c : DataType} (p : Expression a b) (q : Expression a c)
    (R : OraclePredicate a) (hp : OracleSafe p R) (hq : OracleSafe q R) : OracleSafe (both p q) R := by
  obtain ⟨f,hf⟩ := hp
  obtain ⟨g,hg⟩ := hq
  refine ⟨.add (.mul (.constant 3) (.add f g)) (.constant 1),fun O S x hx => ?_⟩
  apply safe_both O p q x
  · exact safe_mono p x (hf O S x hx) (Nat.le_add_right _ _)
  · exact safe_mono q x (hg O S x hx) (Nat.le_add_left _ _)
lemma oracleSafe_post {a b c : DataType} (p : Expression a b) (q : Expression b c)
    (R : OraclePredicate a) (hp : OracleSafe p R) (hq : Controlled q) : OracleSafe (p >>> q) R := by
  obtain ⟨f,hf⟩ := hp
  apply oracleSafe_compose p q R (fun _ _ S y => width y≤f.eval S) ⟨f,hf⟩
    (oracleSafe_controlled q hq _ f (by intros; assumption))
  intro n O S x hx y hy
  exact safe_output (hf O S x hx) hy
lemma oracleSafe_pull {a b c : DataType} (p : Expression a b) (q : Expression b c)
    (R : OraclePredicate a) (Q : OraclePredicate b) (hp : Controlled p)
    (g : SizePolynomial) (hw : ∀ n O S x,R n O S x → width x≤g.eval S)
    (hq : OracleSafe q Q)
    (hh : ∀ n O S x,R n O S x → ∀ y,run O p x=some y → Q n O S y) : OracleSafe (p >>> q) R :=
  oracleSafe_compose p q R Q (oracleSafe_controlled p hp R g hw) hq hh
lemma oracleSafe_input_bound {a b : DataType} (p : Expression a b) (R : OraclePredicate a)
    (hp : OracleSafe p R) : ∃ f : SizePolynomial,∀ n O S x,R n O S x → width x≤f.eval S := by
  obtain ⟨f,hf⟩ := hp
  exact ⟨f,fun _ O S x hx => safe_input (hf O S x hx)⟩
lemma oracleSafe_applyIf {a b : DataType} (t : Expression a .bool) (p q : Expression a b)
    (R : OraclePredicate a) (ht : OracleSafe t R)
    (hp : OracleSafe p (fun n O S x => R n O S x ∧ run O t x=some false))
    (hq : OracleSafe q (fun n O S x => R n O S x ∧ run O t x=some true)) :
    OracleSafe (applyIf t p q) R := by
  have hid : OracleSafe (ident (a:=a)) R := by
    obtain ⟨f,hf⟩ := oracleSafe_input_bound t R ht
    exact oracleSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) R f hf
  have hboth := oracleSafe_both t ident R ht hid
  obtain ⟨f,hf⟩ := hboth
  obtain ⟨g,hg⟩ := hp
  obtain ⟨k,hk⟩ := hq
  unfold applyIf
  apply oracleSafe_compose (both t ident) (branch p q) R
    (fun n O S z => width z≤f.eval S ∧ R n O S z.2 ∧ run O t z.2=some z.1) ⟨f,hf⟩
  · refine ⟨.add f (.add g k),fun O S z hz => ?_⟩
    obtain ⟨v,x⟩ := z
    refine ⟨hz.1.trans (Nat.le_add_right _ _),?_,?_⟩
    · intro y hy
      cases v
      · exact (safe_output (hg O S x ⟨hz.2.1,hz.2.2⟩) hy).trans (by dsimp [SizePolynomial.eval]; omega)
      · exact (safe_output (hk O S x ⟨hz.2.1,hz.2.2⟩) hy).trans (by dsimp [SizePolynomial.eval]; omega)
    · cases v
      · exact safe_mono p x (hg O S x ⟨hz.2.1,hz.2.2⟩) (by dsimp [SizePolynomial.eval]; omega)
      · exact safe_mono q x (hk O S x ⟨hz.2.1,hz.2.2⟩) (by dsimp [SizePolynomial.eval]; omega)
  · intro n O S x hx z hz
    have hh := run_both_parts O t ident x z hz
    have he : x=z.2 := Option.some.inj hh.2
    exact ⟨safe_output (hf O S x hx) hz,he ▸ hx,he ▸ hh.1⟩

namespace Effect
lemma scope_width {a b : DataType} (p : Expression a b) (R : OraclePredicate a)
    (hp : OracleSafe p R) : ∃ f : SizePolynomial,∀ n O S x,bankScope R n O S x → width x≤f.eval S := by
  obtain ⟨f,hf⟩ := oracleSafe_input_bound p R hp
  refine ⟨.add (.mul (.constant 2) f) (.add .input (.constant 1)),?_⟩
  intro n O S x hx
  have hh := hf n O S x.1 hx.1
  have hb : width (a:=BankData) x.2≤S := hx.2
  rw [width_pair (a:=a) (b:=BankData)]
  dsimp only [SizePolynomial.eval]
  omega
lemma safe_scope_fst {a b : DataType} (p : Expression a b) (R : OraclePredicate a)
    (hp : OracleSafe p R) : OracleSafe (fst (b:=BankData) >>> p) (bankScope R) := by
  obtain ⟨f,hf⟩ := scope_width p R hp
  apply oracleSafe_pull _ _ _ R (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) f hf hp
  intro n O S x hx y hy
  cases hy
  exact hx.1
lemma safe_scope_controlled {a b c : DataType} (p : Expression a b) (q : Expression (.prod a BankData) c)
    (R : OraclePredicate a) (hp : OracleSafe p R) (hq : Controlled q) : OracleSafe q (bankScope R) := by
  obtain ⟨f,hf⟩ := scope_width p R hp
  exact oracleSafe_controlled q hq _ f hf
lemma oracleSafe_pure {a b : DataType} (p : Expression a b) (R : OraclePredicate a)
    (hp : OracleSafe p R) : OracleSafe (pure p) (bankScope R) := by
  unfold pure
  apply oracleSafe_both
  · apply oracleSafe_both
    · exact safe_scope_controlled p _ R hp (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)))
    · exact safe_scope_fst p R hp
  · exact safe_scope_controlled p _ R hp (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)))
lemma oracleSafe_precompose {a b c : DataType} (p : Expression a b) (q : Effect b c)
    (R : OraclePredicate a) (Q : OraclePredicate b) (hp : OracleSafe p R)
    (hq : OracleSafe q (bankScope Q))
    (h : ∀ n O S x,R n O S x → ∀ y,run O p x=some y → Q n O S y) :
    OracleSafe (precompose p q) (bankScope R) := by
  unfold precompose onLeft
  apply oracleSafe_compose _ _ _ (bankScope Q)
    (oracleSafe_both _ _ _ (safe_scope_fst p R hp) (safe_scope_controlled p _ R hp (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))))) hq
  intro n O S x hx y hy
  have hh := run_both_parts O (fst >>> p) snd x y hy
  have hp' : run O p x.1=some y.1 := hh.1

  have hb : x.2=y.2 := Option.some.inj hh.2
  exact ⟨h n O S x.1 hx.1 y.1 hp',hb ▸ hx.2⟩
lemma oracleSafe_keep {a b : DataType} (p : Effect a b) (R : OraclePredicate (.prod a BankData))
    (hp : OracleSafe p R) : OracleSafe (keep p) R := by
  obtain ⟨f,hf⟩ := oracleSafe_input_bound p R hp
  unfold keep Expression.letIn
  apply oracleSafe_post
  · exact oracleSafe_both _ _ _ (oracleSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) R f hf) hp
  · repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma oracleSafe_bind {a b c : DataType} (p : Effect a b) (q : Effect b c)
    (R : OraclePredicate a) (Q : OraclePredicate b)
    (hp : OracleSafe p (bankScope R)) (hq : OracleSafe q (bankScope Q))
    (h : ∀ n O S x bank,R n O S x → width (a:=BankData) bank≤S → ∀ y rest,
      run O p (x,bank)=some ((true,y),rest) → Q n O S y ∧ width (a:=BankData) rest≤S) :
    OracleSafe (bind p q) (bankScope R) := by
  obtain ⟨f,hf⟩ := hp
  let T : OraclePredicate (.prod (Optional b) BankData) := fun n O S z =>
    ∃ x bank,bankScope R n O S (x,bank) ∧ run O p (x,bank)=some z
  have hw : ∀ n O S z,T n O S z → width z≤f.eval S := by
    intro n O S z hz
    obtain ⟨x,bank,hx,he⟩ := hz
    exact safe_output (hf O S (x,bank) hx) he
  unfold bind
  apply oracleSafe_compose p _ (bankScope R) T ⟨f,hf⟩
  · apply oracleSafe_applyIf _ _ _ T
    · exact oracleSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) T f hw
    · exact oracleSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ f (by intro n O S z hz; exact hw n O S z hz.1)
    · apply oracleSafe_pull _ q _ (bankScope Q) (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) f
        (by intro n O S z hz; exact hw n O S z hz.1) hq
      intro n O S z hz y hy
      obtain ⟨⟨flag,v⟩,rest⟩ := z
      have hv : flag=true := Option.some.inj hz.2
      subst flag
      have hy' : (v,rest)=y := Option.some.inj hy
      subst y
      obtain ⟨x,bank,hx,he⟩ := hz.1
      exact h n O S x bank hx.1 hx.2 v rest he
  · intro n O S x hx z hz
    exact ⟨x.1,x.2,hx,hz⟩
end Effect
end MachineCode

namespace MachineCode

lemma bankEval_all {A : Type*} (t : DrawTree A) (P : A → Prop)
    (ht : DrawTree.All P t) (bank : Bank) (x : A)
    (hx : (bankEval t bank).1=some x) : P x := by
  induction t generalizing bank with
  | leaf a =>
    have he : a=x := Option.some.inj hx
    exact he ▸ ht
  | draw v k ih =>
    cases bank with
    | nil => cases hx
    | cons row bank =>
      simp only [bankEval] at hx
      split at hx
      · cases hx
      · exact ih _ (ht _) bank hx
open Expression
namespace Effect
lemma RealizesLaw.outputs_all {n : ℕ} {O : IndependenceOracle n}
    {A : Type*} {a b : DataType} {p : Effect a b} {e : A → Value b}
    {x : Value a} {t : DrawTree A} (h : RealizesLaw O p e x t)
    (P : A → Prop) (ht : DrawTree.All P t) (bank : Bank) :
    ∃ y : Option A,∃ rest : Bank,
      run O p (x,bank)=some (optionalValue b (y.map e),rest) ∧
      width (a:=BankData) rest≤width (a:=BankData) bank ∧
      ∀ v,y=some v → P v := by
  obtain ⟨u,hu,hp⟩ := h
  refine ⟨(bankEval u bank).1,(bankEval u bank).2,hp bank,bankEval_rest_width u bank,?_⟩
  intro v hv
  exact bankEval_all u P (hu.all P ht) bank v hv
lemma RealizesLaw.output_some_all {n : ℕ} {O : IndependenceOracle n}
    {A : Type*} {a b : DataType} {p : Effect a b} {e : A → Value b}
    {x : Value a} {t : DrawTree A} (h : RealizesLaw O p e x t)
    (P : A → Prop) (ht : DrawTree.All P t) (bank : Bank)
    (y : Value b) (rest : Bank) (hy : run O p (x,bank)=some ((true,y),rest)) :
    ∃ v,y=e v ∧ P v ∧ width (a:=BankData) rest≤width (a:=BankData) bank := by
  obtain ⟨v,r,he,hw,hv⟩ := h.outputs_all P ht bank
  rw [hy] at he
  have hh := Option.some.inj he
  cases v with
  | none => cases (congrArg (fun z => z.1.1) hh)
  | some v =>
    have hry : rest=r := congrArg Prod.snd hh
    have hyy : y=e v := congrArg (fun z => z.1.2) hh
    exact ⟨v,hyy,hv v rfl,hry ▸ hw⟩
lemma run_keep_value {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Effect a b) (x : Value a) (bank : Bank) (v : Value (.prod (Optional b) BankData))
    (hp : run O p (x,bank)=some v) :
    run O (keep p) (x,bank)=some
      ((if v.1.1 then optionalValue (.prod a b) (some (x,v.1.2)) else optionalValue (.prod a b) none),v.2) := by
  rw [keep,run_letIn,hp]
  obtain ⟨⟨flag,y⟩,rest⟩ := v
  cases flag <;> rfl
lemma run_keep_some {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Effect a b) (x : Value a) (bank : Bank) (x' : Value a) (y : Value b) (rest : Bank)
    (h : run O (keep p) (x,bank)=some ((true,(x',y)),rest)) :
    x'=x ∧ run O p (x,bank)=some ((true,y),rest) := by
  cases he : run O p (x,bank) with
  | none => simp only [keep,run_letIn,he,Option.bind_none] at h; contradiction
  | some v =>
    rw [run_keep_value O p x bank v he] at h
    obtain ⟨⟨flag,y'⟩,r⟩ := v
    cases flag
    · cases h
    · cases h
      exact ⟨rfl,rfl⟩
end Effect

open Expression
lemma attrSafe_controlled {a b : DataType} (p : Expression a b) (hp : Controlled p)
    (R : Attribute a) : AttrSafe p R :=
  polySafe_of_controlled p hp _ .input (by intro S x hx; exact hx.1)
lemma attrSafe_compose {a b c : DataType} (p : Expression a b) (q : Expression b c)
    (R : Attribute a) (Q : Attribute b) (hp : AttrSafe p R) (hq : AttrSafe q Q)
    (hm : Q.Mono)
    (h : ∀ {n : ℕ} (O : IndependenceOracle n) S x,R S x → ∀ y,run O p x=some y → Q S y) :
    AttrSafe (p >>> q) R := by
  obtain ⟨f,hf⟩ := hp
  let g : SizePolynomial := .add f .input
  apply polySafe_compose p q _ (fun S y => width y≤g.eval S ∧ Q (g.eval S) y) ⟨f,hf⟩
    (polySafe_reparam q _ hq g)
  intro n O S x hx y hy
  exact ⟨(safe_output (hf O S x hx) hy).trans (Nat.le_add_right _ _),
    hm S _ (Nat.le_add_left _ _) y (h O S x hx.2 y hy)⟩
lemma attrSafe_both {a b c : DataType} (p : Expression a b) (q : Expression a c)
    (R : Attribute a) (hp : AttrSafe p R) (hq : AttrSafe q R) : AttrSafe (both p q) R :=
  polySafe_both p q _ hp hq
lemma attrSafe_post {a b c : DataType} (p : Expression a b) (q : Expression b c)
    (R : Attribute a) (hp : AttrSafe p R) (hq : Controlled q) : AttrSafe (p >>> q) R :=
  polySafe_post p q _ hp hq
lemma attrSafe_pull {a b c : DataType} (p : Expression a b) (q : Expression b c)
    (R : Attribute a) (Q : Attribute b) (hp : Controlled p) (hq : AttrSafe q Q)
    (hm : Q.Mono)
    (h : ∀ {n : ℕ} (O : IndependenceOracle n) S x,R S x → ∀ y,run O p x=some y → Q S y) :
    AttrSafe (p >>> q) R :=
  attrSafe_compose p q R Q (attrSafe_controlled p hp R) hq hm h
namespace Effect
lemma attr_pure {a b : DataType} (p : Expression a b) (R : Attribute a) (hm : R.Mono)
    (hp : AttrSafe p R) : EffectSafe (pure p) R := by
  unfold pure
  apply attrSafe_both
  · apply attrSafe_both
    · exact attrSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _
    · apply attrSafe_pull _ p _ R (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) hp hm
      intro n O S x hx y hy
      cases hy; exact hx
  · exact attrSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _
lemma attr_precompose {a b c : DataType} (p : Expression a b) (q : Effect b c)
    (R : Attribute a) (Q : Attribute b) (hp : AttrSafe p R) (hq : EffectSafe q Q)
    (hmR : R.Mono) (hmQ : Q.Mono)
    (h : ∀ {n : ℕ} (O : IndependenceOracle n) S x,R S x → ∀ y,run O p x=some y → Q S y) :
    EffectSafe (precompose p q) R := by
  unfold precompose onLeft
  apply attrSafe_compose _ q _ _ ?_ hq
  · intro S T h z hz; exact hmQ S T h z.1 hz
  · intro n O S x hx y hy
    exact h O S x.1 hx y.1 (run_both_parts O _ _ x y hy).1
  · apply attrSafe_both
    · apply attrSafe_pull _ p _ R (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) hp hmR
      intro n O S x hx y hy
      cases hy; exact hx
    · exact attrSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _
lemma attr_keep {a b : DataType} (p : Effect a b) (R : Attribute a)
    (hp : EffectSafe p R) : EffectSafe (keep p) R := by
  unfold keep Expression.letIn
  apply attrSafe_post
  · exact attrSafe_both _ _ _ (attrSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _) hp
  · repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma attr_bind {a b c : DataType} (p : Effect a b) (q : Effect b c)
    (R : Attribute a) (Q : Attribute b) (hmQ : Q.Mono)
    (hp : EffectSafe p R) (hq : EffectSafe q Q)
    (h : ∀ {n : ℕ} (O : IndependenceOracle n) S x bank,R S x → ∀ y rest,
      run O p (x,bank)=some ((true,y),rest) → Q S y) : EffectSafe (bind p q) R := by
  let T : Attribute (.prod (Optional b) BankData) := fun S z => z.1.1=true → Q S z.1.2
  have hmT : T.Mono := by intro S U h z hz hf; exact hmQ S U h z.1.2 (hz hf)
  have hq' : AttrSafe (applyIf (fst >>> fst) (both (constant (optionalValue c none)) snd)
      (both (fst >>> snd) snd >>> q)) T := by

    apply (show OracleSafe _ (fun _ _ S x => width x≤S ∧ T S x) from ?_)
    apply oracleSafe_applyIf _ _ _ (fun _ _ S x => width x≤S ∧ T S x)
    · exact oracleSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ .input (by intro n O S x hx; exact hx.1)
    · exact oracleSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ .input (by intro n O S x hx; exact hx.1.1)
    · apply oracleSafe_pull _ q _ (fun _ _ S x => width x≤S ∧ Q S x.1) (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)))
        (.mul (.constant 2) .input)
        (by intro n O S x hx; exact hx.1.1.trans (by dsimp [SizePolynomial.eval]; omega))
      · exact oracleSafe_lift q _ hq
      · intro n O S x hx y hy
        have hv : x.1.1=true := Option.some.inj hx.2
        cases hy
        refine ⟨?_,hx.1.2 hv⟩
        have hb := width_fst (a:=Optional b) (b:=BankData) x
        have hs := width_snd (a:=.bool) (b:=b) x.1
        rw [width_pair (a:=b) (b:=BankData)]
        have hi := hx.1.1
        rw [width_pair (a:=Optional b) (b:=BankData),width_pair (a:=.bool) (b:=b),width_bool] at hi
        omega
  unfold bind
  apply attrSafe_compose p _ _ T hp hq' hmT
  intro n O S x hx z hz hv
  obtain ⟨⟨flag,y⟩,rest⟩ := z
  dsimp only [Prod.fst] at hv
  subst flag
  exact h O S x.1 x.2 hx y rest hz
lemma attr_letIn {a b c : DataType} (p : Effect a b) (q : Effect (.prod a b) c)
    (R : Attribute a) (Q : Attribute (.prod a b)) (hmQ : Q.Mono)
    (hp : EffectSafe p R) (hq : EffectSafe q Q)
    (h : ∀ S x y,R S x → Q S (x,y)) : EffectSafe (letIn p q) R := by
  apply attr_bind (keep p) q R Q hmQ (attr_keep p R hp) hq
  intro n O S x bank hx z rest hz
  obtain ⟨x',y⟩ := z
  have he := (run_keep_some O p x bank x' y rest hz).1
  subst x'
  exact h S x y hx

lemma attr_controlled {a b : DataType} (p : Effect a b) (hp : Controlled p) (R : Attribute a) :
    EffectSafe p R := attrSafe_controlled p hp _
lemma attr_preControlled {a b c : DataType} (p : Expression a b) (q : Effect b c)
    (R : Attribute a) (hm : R.Mono) (hp : AttrSafe p R) (hq : Controlled q) : EffectSafe (precompose p q) R :=
  attr_precompose p q R (fun _ _ => True) hp (attr_controlled q hq _) hm (by unfold Attribute.Mono; intros; trivial) (by intros; trivial)

lemma oracleSafe_mapControlled {a b c : DataType} (p : Effect a b) (q : Expression b c)
    (R : OraclePredicate (.prod a BankData)) (hp : OracleSafe p R) (hq : Controlled q) :
    OracleSafe (map p q) R := by
  unfold map bind
  apply oracleSafe_post _ _ R hp
  have hh := controlled_pure q hq
  repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
end Effect

lemma oracleSafe_attr {a b : DataType} (p : Expression a b) (A : Attribute a)
    (hA : A.Mono) (hp : AttrSafe p A) (R : OraclePredicate a) (g : SizePolynomial)
    (hw : ∀ n O S x,R n O S x → width x≤g.eval S)
    (ha : ∀ n O S x,R n O S x → A S x) : OracleSafe p R := by
  let W : SizePolynomial := .add g .input
  apply oracleSafe_mono p (oracleSafe_reparam p _ (oracleSafe_lift p _ hp) W)
  intro n O S x hx
  exact ⟨(hw n O S x hx).trans (Nat.le_add_right _ _),
    hA S _ (Nat.le_add_left _ _) x (ha n O S x hx)⟩
namespace Effect
lemma oracleSafe_effectAttr {a b : DataType} (p : Effect a b) (A : Attribute a)
    (hA : A.Mono) (hp : EffectSafe p A) (R : OraclePredicate a) (g : SizePolynomial)
    (hw : ∀ n O S x,R n O S x → width x≤g.eval S)
    (ha : ∀ n O S x,R n O S x → A S x) : OracleSafe p (bankScope R) := by
  apply oracleSafe_attr p (fun S x => A S x.1) (fun S T h x hx => hA S T h x.1 hx) hp _
    (.add (.mul (.constant 2) g) (.add .input (.constant 1)))
  · intro n O S x hx
    have hw' := hw n O S x.1 hx.1
    have hb := hx.2
    rw [width_pair (a:=a) (b:=BankData)]
    dsimp [SizePolynomial.eval]
    omega
  · intro n O S x hx; exact ha n O S x.1 hx.1
lemma oracleSafe_letIn {a b c : DataType} (p : Effect a b) (q : Effect (.prod a b) c)
    (R : OraclePredicate a) (Q : OraclePredicate (.prod a b))
    (hp : OracleSafe p (bankScope R)) (hq : OracleSafe q (bankScope Q))
    (h : ∀ n O S x bank,R n O S x → width (a:=BankData) bank≤S → ∀ y rest,
      run O p (x,bank)=some ((true,y),rest) → Q n O S (x,y) ∧ width (a:=BankData) rest≤S) :
    OracleSafe (letIn p q) (bankScope R) := by
  apply oracleSafe_bind (keep p) q R Q (oracleSafe_keep p _ hp) hq
  intro n O S x bank hx hb z rest hz
  obtain ⟨x',y⟩ := z
  have he := run_keep_some O p x bank x' y rest hz
  rw [he.1]
  exact h n O S x bank hx hb y rest he.2

end Effect

open scoped Classical
lemma width_stateEncode {n : ℕ} (T : Set (Fin n⊕Fin n)) : width (a:=StateData) (stateEncode T)=3*n+1 := by
  rw [width_pair (a:=.word) (b:=.word),width_word,width_word,stateEncode_left_length,stateEncode_right_length]
  omega
lemma width_sampleEncode {n : ℕ} (xs : List (Set (Fin n⊕Fin n))) :
    width (a:=SampleData) (sampleEncode xs)=xs.length*(6*n+4) := by
  induction xs with
  | nil => change width (a:=.list StateData) []=0*(6*n+4); rw [width_nil,Nat.zero_mul]
  | cons x xs ih =>
    change width (a:=.list StateData) (stateEncode x::sampleEncode xs)=_
    rw [width_cons (a:=StateData),width_stateEncode,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
lemma width_observation {n N : ℕ} (v : PhaseSample n N) :
    width (a:=SampleData) (sampleEncode (observedSets n N v))≤(N+1)*(6*n+4) := by
  rw [width_sampleEncode]
  have hl : (observedSets n N v).length=N-1+1 := by
    simp only [observedSets,List.length_map]
    exact FiniteChain.Sample.toList_length v
  rw [hl]
  exact Nat.mul_le_mul_right _ (by omega)
lemma width_history_observed {n N : ℕ} (h : List (PhaseSample n N)) :
    width (a:=HistoryData) (historyEncode (h.map (observedSets n N)))≤h.length*(2*((N+1)*(6*n+4))+2) := by
  unfold historyEncode
  apply (width_list_le _ _ ?_).trans
  · simp only [List.length_map]; rfl
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    exact width_observation u

open Expression
open Effect
open scoped Classical

namespace SamplerModel
variable {n : ℕ} {O : IndependenceOracle n}
lemma width_histValue (m : SamplerModel n O) (S : ℕ) (hm : m.Bounded S)
    (h : m.Hist) (hh : h.length≤S) : width (m.histValue h)≤20*(S+1)^3 := by
  have he := width_history_observed h
  have hb : h.length*(2*((m.samples+1)*(6*n+4))+2)≤S*(2*((S+1)*(6*S+4))+2) := by
    gcongr
    · exact hm.2.2.1
    · exact hm.1
  exact he.trans (hb.trans (by nlinarith))
lemma width_restartValue (m : SamplerModel n O) (S : ℕ) (hm : m.Bounded S)
    (h : m.Hist) (hh : h.length≤S) (j : ℕ) (hj : j≤S) (x : PlainIndex (pairedSlots n)) :
    width (m.restartValue h j x)≤200*(S+1)^3 := by
  have hr := (bits_length_le_value m.rank).trans hm.2.1
  have hb := (bits_length_le_value j).trans hj
  have hc := (bits_length_le_value m.cap).trans hm.2.2.2.2.1
  have ht := (bits_length_le_value m.tau).trans hm.2.2.2.2.2
  have hs := width_stateEncode x.val.val
  have hn := hm.1
  have hh := m.width_histValue S hm h hh
  rw [restartValue,restartContext,width_pair (a:=.prod RestartContext .nat) (b:=StateData),
    width_pair (a:=RestartContext) (b:=.nat),width_pair (a:=.prod .nat HistoryData) (b:=NN),
    width_pair (a:=.nat) (b:=HistoryData),width_pair (a:=.nat) (b:=.nat),
    width_nat,width_nat,width_nat,width_nat,hs]
  have hp : S+1≤(S+1)^3 := Nat.le_self_pow (by decide) _
  omega
lemma width_phaseValue (m : SamplerModel n O) (S : ℕ) (hm : m.Bounded S)
    (h : m.Hist) (hh : h.length≤S) : width (m.phaseValue h)≤100*(S+1)^3 := by
  have hn := (bits_length_le_value n).trans hm.1
  have hr := (bits_length_le_value m.rank).trans hm.2.1
  have hs := (bits_length_le_value m.samples).trans hm.2.2.1
  have hl := (bits_length_le_value m.phases).trans hm.2.2.2.1
  have hc := (bits_length_le_value m.cap).trans hm.2.2.2.2.1
  have ht := (bits_length_le_value m.tau).trans hm.2.2.2.2.2
  have hh := m.width_histValue S hm h hh
  rw [phaseValue,width_pair (a:=AlgorithmParams) (b:=HistoryData)]
  rw [params,width_pair (a:=NN) (b:=.prod NN NN),width_pair (a:=NN) (b:=NN),
    width_pair (a:=.nat) (b:=.nat),width_pair (a:=.nat) (b:=.nat),width_pair (a:=.nat) (b:=.nat)]
  simp only [width_nat]
  dsimp only [cap,tau] at hc ht
  have hp : S+1≤(S+1)^3 := Nat.le_self_pow (by decide) _
  omega
end SamplerModel

lemma eval_sourceWidthPoly (c S : ℕ) : (sourceWidthPoly c).eval S=c*(S+1)^3 := by
  simp only [sourceWidthPoly,SizePolynomial.eval]; ring

end MachineCode

namespace DrawTree
lemma all_of_forall {A : Type*} (t : DrawTree A) (P : A → Prop) (h : ∀ x,P x) : All P t := by
  induction t with
  | leaf x => exact h x
  | draw n k ih => exact ih
end DrawTree
namespace MachineCode

open Expression
open scoped Classical

open Expression
lemma attr_rangeCode : AttrSafe rangeCode (fun S k => k≤S) :=
  polySafe_mono rangeCode polySafe_rangeCode (by intro S k hk; exact hk.2)
lemma attr_powCode : AttrSafe powCode (fun S x => x.2≤S) := by
  apply polySafe_mono powCode polySafe_powCode
  intro S x hx
  exact ⟨(width_fst (a:=.nat) (b:=.nat) x).trans hx.1,hx.2⟩
lemma attr_paddedBits : AttrSafe paddedBitsCode (fun S x => x.1≤S) := by
  unfold paddedBitsCode
  apply attrSafe_post
  · apply attrSafe_both
    · apply attrSafe_pull fst rangeCode _ _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) attr_rangeCode
        (fun S T h k hk => hk.trans h)
      intro n O S x hx y hy
      cases hy; exact hx
    · exact attrSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _
  · repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)
lemma attr_plainDecode : AttrSafe plainDecodeCode (fun S x => x.1≤S) := by
  unfold plainDecodeCode
  exact attrSafe_post _ _ _ attr_paddedBits (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)))
namespace Effect
lemma attr_plain : EffectSafe plainCode (fun S x => x≤S) := by
  unfold plainCode
  apply attr_letIn (a:=.nat) (b:=.nat) (c:=StateData) _ _
    (fun (S : ℕ) (x : ℕ) => x≤S) (fun (S : ℕ) (x : ℕ × ℕ) => x.1≤S)
    (fun S T h x hx => hx.trans h)
  · apply attr_preControlled _ _ _ (fun S T h x hx => hx.trans h) _ controlled_draw
    apply attrSafe_pull _ powCode _ _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) attr_powCode
      (fun S T h x hx => hx.trans h)
    intro n O S x hx y hy
    cases hy
    exact hx
  · exact attr_pure plainDecodeCode _ (fun S T h x hx => hx.trans h) attr_plainDecode
  · intro S x y hx
    exact hx
lemma safe_plain : OracleSafe plainCode (bankScope (fun _ _ S x => x≤S)) := by
  apply oracleSafe_effectAttr plainCode _ (fun S T h x hx => hx.trans h) attr_plain _ .input
  · intro n O S x hx
    exact (bits_length_le_value x).trans hx
  · intros; assumption
end Effect

open Expression
open scoped Classical

open Expression
open scoped Classical
namespace SamplerModel
lemma width_restartInput {n : ℕ} {O : IndependenceOracle n} (m : SamplerModel n O)
    (S : ℕ) (hm : m.Bounded S) (h : m.Hist) (hh : h.length≤S) (k : ℕ) (hk : k≤S) :
    width (m.restartInput h k)≤(sourceWidthPoly 210).eval S := by
  let x : PlainIndex (pairedSlots n) := Classical.choice
    (plainIndex_nonempty (pairedSlots n) (pairedSlots_fresh n) (pairedSlots_cover n))
  have hw := m.width_restartValue S hm h hh 0 (Nat.zero_le S) x
  have hc : width (m.restartContext h)≤200*(S+1)^3 :=
    (width_fst (a:=RestartContext) (b:=.nat) (m.restartContext h,0)).trans
      ((width_fst (a:=.prod RestartContext .nat) (b:=StateData) (m.restartValue h 0 x)).trans hw)
  have hn := (bits_length_le_value n).trans hm.1
  have hb := (bits_length_le_value k).trans hk
  rw [eval_sourceWidthPoly,restartInput,width_pair (a:=.nat) (b:=.prod .nat RestartContext),
    width_pair (a:=.nat) (b:=RestartContext),width_nat,width_nat]
  have hp : S+1≤(S+1)^3 := Nat.le_self_pow (by decide) _
  omega
end SamplerModel
namespace Effect
lemma restartInputScope_width : ∀ n O S z,restartInputScope n O S z → width z≤(sourceWidthPoly 210).eval S := by
  intro n O S z hz
  obtain ⟨m,hm,h,hh,k,hk,rfl⟩ := hz
  exact m.width_restartInput S hm h hh k hk
lemma restartAfterPlainScope_width : ∀ n O S z,restartAfterPlainScope n O S z →
    width z≤(sourceWidthPoly 430).eval S := by
  intro n O S z hz
  obtain ⟨m,hm,h,hh,k,hk,x,rfl⟩ := hz
  have hw := m.width_restartInput S hm h hh k hk
  rw [width_pair (a:=RestartInput) (b:=StateData),width_stateEncode,eval_sourceWidthPoly]
  rw [eval_sourceWidthPoly] at hw
  have hn := hm.1
  have hp : S+1≤(S+1)^3 := Nat.le_self_pow (by decide) _
  omega
lemma safe_restart : OracleSafe restartCode (bankScope restartInputScope) := by
  unfold restartCode
  apply oracleSafe_mapControlled _ _ _ _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial)))
  apply oracleSafe_letIn _ _ restartInputScope restartAfterPlainScope
  · apply oracleSafe_precompose fst plainCode restartInputScope (fun _ _ S x => x≤S)
      (oracleSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ _ restartInputScope_width) safe_plain
    intro n O S z hz y hy
    obtain ⟨m,hm,h,hh,k,hk,rfl⟩ := hz
    cases hy
    exact hm.1
  · apply oracleSafe_precompose restartPrep _ restartAfterPlainScope restartRepeatScope
      (oracleSafe_controlled _ (by unfold restartPrep; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ _ restartAfterPlainScope_width) safe_restartRepeat
    intro n O S z hz y hy
    obtain ⟨m,hm,h,hh,k,hk,x,rfl⟩ := hz
    have he : (k,optionEncode (m.restartValue h 0) (some x))=y := Option.some.inj hy
    subst y
    exact ⟨hk,m,hm,h,hh,x,rfl⟩
  · intro n O S z bank hz hb y rest hy
    obtain ⟨m,hm,h,hh,k,hk,rfl⟩ := hz
    have hl := law_precompose O fst plainCode _ (m.restartInput h k) n _ rfl (plainCode_source O)
    obtain ⟨x,he,_,hr⟩ := hl.output_some_all (fun _ => True) (DrawTree.all_of_forall _ _ (by intros; trivial)) bank y rest hy
    exact ⟨⟨m,hm,h,hh,k,hk,x,by rw [he]⟩,hr.trans hb⟩
end Effect

namespace Effect
lemma phaseScope_width : ∀ n O S z,phaseScope n O S z → width z≤(sourceWidthPoly 100).eval S := by
  intro n O S z hz
  obtain ⟨m,hm,h,hh,rfl⟩ := hz
  rw [eval_sourceWidthPoly]
  exact m.width_phaseValue S hm h hh
lemma safe_phaseRestart : OracleSafe phaseRestartCode (bankScope phaseScope) := by
  unfold phaseRestartCode
  apply oracleSafe_precompose phaseRestartPrep restartCode phaseScope restartInputScope
    (oracleSafe_controlled _ (by unfold phaseRestartPrep; (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ _ phaseScope_width) safe_restart
  intro n O S z hz y hy
  obtain ⟨m,hm,h,hh,rfl⟩ := hz
  have he : run O phaseRestartPrep (m.phaseValue h)=some (m.restartInput h h.length) := by
    simp only [phaseRestartPrep,SamplerModel.phaseValue,params,run_both,run_compose,run_fst,run_snd,
      Option.bind_some,Option.map_some]
    rw [run_listLength]
    simp only [SamplerModel.histValue,historyEncode,List.length_map]
    rfl
  have hey := Option.some.inj (he.symm.trans hy)
  subst y
  exact ⟨m,hm,h,hh,h.length,hh,rfl⟩
end Effect

open Expression

open Expression
open scoped Classical
namespace Effect
lemma oracleSafe_chooseScoped {a b : DataType} (t : Expression a .bool) (p q : Effect a b)
    (R : OraclePredicate a) (ht : OracleSafe t R)
    (hp : OracleSafe p (bankScope R)) (hq : OracleSafe q (bankScope R)) :
    OracleSafe (choose t p q) (bankScope R) := by
  apply oracleSafe_applyIf _ _ _ (bankScope R)
  · exact safe_scope_fst t R ht
  · exact oracleSafe_mono p hp (by intro n O S x hx; exact hx.1)
  · exact oracleSafe_mono q hq (by intro n O S x hx; exact hx.1)
lemma safe_witness_oai : OracleSafe witnessCode (bankScope phaseScope) := by
  unfold witnessCode
  apply oracleSafe_chooseScoped _ _ _ phaseScope safe_positiveTest _ safe_phaseRestart
  exact oracleSafe_pure _ phaseScope (oracleSafe_controlled _ (by (repeat' (first | assumption | exact controlled_wordRange | exact controlled_boolNot | exact controlled_boolAnd | exact controlled_boolOr | exact controlled_natEqual | exact controlled_natEqZero | exact controlled_natSub | exact controlled_natDiv | exact controlled_natMod | exact controlled_natDivRem | exact controlled_swap | exact controlled_listLength | exact controlled_wordLength | exact controlled_fromList | exact controlled_listReverse | exact controlled_listAppend | exact controlled_productCode | exact controlled_wordGet | exact controlled_wordNot | exact controlled_wordCount | exact controlled_deficiency | exact controlled_listAll | exact controlled_splitAt | exact controlled_take | exact controlled_drop | exact controlled_headD | exact controlled_getD | exact controlled_normalizeRat | exact controlled_ratAdd | exact controlled_ratMul | exact controlled_ratDiv | exact controlled_ratLess | exact controlled_ratMinOne | exact controlled_ratSum | exact controlled_ratProduct | apply controlled_mapWith | apply controlled_filterWith | apply controlled_onLeft | apply controlled_onRight | apply controlled_letIn | apply controlled_applyIf | apply controlled_compose | apply controlled_both | apply controlled_branch | exact controlled_atomic _ trivial))) _ _ phaseScope_width)
end Effect

open Expression
open scoped Classical

open Expression

open Expression Effect

open Expression
open scoped Classical

open Expression

open Expression Effect

open Expression
open Expression Effect

open Expression

open Expression

open Expression Effect

open Expression

open Expression

open Expression Effect
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression

open scoped Classical

end MachineCode
end CommonBasesFPRAS

open CommonBasesFPRAS CommonBasesFPRAS.MachineCode

end OAI
end

theorem solution : type_of% @OAI.CommonBasesFPRAS.MachineCode.Effect.safe_witness_oai := @OAI.CommonBasesFPRAS.MachineCode.Effect.safe_witness_oai
