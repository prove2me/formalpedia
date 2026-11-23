-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_hermite251_initial_grid
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:02:18.706538+00:00
-- url     : https://prove2.me/submissions/bcf3e0c0-cb15-4de6-ac61-06bd1deca0a0

import Theorems.Thm_GrothendieckLB_Supplement_cq_initial_hermite251_centers
import Theorems.Thm_GrothendieckLB_Supplement_cq_initial_hermite251_widths
import Definitions.Def_GrothendieckLB_Supplement_cqInitialHermite251
import Definitions.Def_GrothendieckLB_Supplement_cqDegree251Tables
import Mathlib.Tactic.NormNum
import Definitions.Def_GrothendieckLB_Supplement_cqHermite251Checkpoints
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option maxRecDepth 150000
set_option exponentiation.threshold 50000


open GrothendieckLB.Supplement.CQHeadArithmetic GrothendieckLB.Supplement.CQDegree251
namespace CQRowEncoding
set_option maxRecDepth 10000
set_option exponentiation.threshold 50000

def packNat {α : Type} (B : ℕ) (f : α → ℕ) : List α → ℕ
  | [] => 0
  | x::xs => f x + B*packNat B f xs

private theorem pack_digit {α : Type} (B : ℕ) (hB : 0<B) (f : α → ℕ) (xs : List α)
    (hs : ∀ x ∈ xs, f x < B) (i : ℕ) (hi : i<xs.length) :
    digit B (packNat B f xs) i = f xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have hx := hs x (by simp)
    have ht (t) (hm : t∈xs) : f t<B := hs t (by simp [hm])
    cases i with
    | zero => simp [digit,packNat,Nat.add_mod,Nat.mod_eq_of_lt hx]
    | succ i =>
      have hj : i<xs.length := by simpa using hi
      have peel (w : ℕ) : digit B w (i+1) = digit B (w/B) i := by
        simp [digit,Nat.div_div_eq_div_mul,pow_succ']
      rw [peel,packNat,Nat.add_mul_div_left _ _ hB,Nat.div_eq_of_lt hx,Nat.zero_add,ih ht i hj]
      rfl

def admissible (B : ℕ) (x : Interval) :=
  x.lo.toNat<radix ∧ (-x.lo).toNat<radix ∧ x.lo≤x.hi ∧ (x.hi-x.lo).toNat<B

instance (B : ℕ) (x : Interval) : Decidable (admissible B x) :=
  inferInstanceAs (Decidable (_ ∧ _))

def valid (B : ℕ) (p : PackedRow) (xs : List Interval) : Prop :=
  (xs.all (fun x => decide (admissible B x)) = true) ∧
  packNat radix (fun x => x.lo.toNat) xs = p.pos ∧
  packNat radix (fun x => (-x.lo).toNat) xs = p.neg ∧
  packNat B (fun x => (x.hi-x.lo).toNat) xs = p.wid

instance (B : ℕ) (p : PackedRow) (xs : List Interval) : Decidable (valid B p xs) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem validRow (B : ℕ) (hB : 0<B) (p : PackedRow) (xs : List Interval) (h : valid B p xs)
    (n : ℕ) (hn : xs.length=n) : tab n (cell false B p)=xs.toArray := by
  obtain ⟨ha,hp,hn',hw⟩ := h
  have hc (x) (hx : x∈xs) : admissible B x := of_decide_eq_true (List.all_eq_true.mp ha x hx)
  apply Array.ext
  · simp [tab,hn]
  · intro i hi hx
    have hi' : i<n := by simpa [tab] using hi
    have hidx : i<xs.length := by omega
    have hr : 0<radix := by decide
    have eqp := pack_digit radix hr (fun (x : Interval) => x.lo.toNat) xs
      (fun x hm => (hc _ hm).1) i hidx
    have eqn := pack_digit radix hr (fun (x : Interval) => (-x.lo).toNat) xs
      (fun x hm => (hc _ hm).2.1) i hidx
    have eqw := pack_digit B hB (fun (x : Interval) => (x.hi-x.lo).toNat) xs
      (fun x hm => (hc _ hm).2.2.2) i hidx
    rw [hp] at eqp
    rw [hn'] at eqn
    rw [hw] at eqw
    have hord := (hc xs[i] (List.getElem_mem hidx)).2.2.1
    simp only [tab,Array.getElem_ofFn,List.getElem_toArray,cell,low,Bool.false_eq_true,if_false,
      one_mul,eqp,eqn,eqw]
    cases he : xs[i] with
    | mk lo hi =>
      rw [he] at hord
      simp at hord ⊢
      constructor <;> omega

theorem tabPush {α : Type} (n : ℕ) (f : ℕ → α) :
    (tab n f).push (f n) = tab (n+1) f := by
  apply Array.ext
  · simp [tab]
  · intro j h h'
    have hs : j<n+1 := by simpa [tab] using h'
    by_cases hj : j<n
    · rw [Array.getElem_push_lt (by simpa [tab] using hj)]
      simp [tab]
    · have he : j=n := by omega
      subst j
      simp [tab,Array.getElem_push]

theorem lookup {α : Type} (d : α) (n : ℕ) (f : ℕ → α) (i : ℕ) (hi : i<n) :
    entry d (tab n f) i = f i := by simp [entry,tab,hi]

end CQRowEncoding



open GrothendieckLB.Supplement.CQHeadArithmetic GrothendieckLB.Supplement.CQDegree251
open GrothendieckLB.Supplement.CQHermite251 CQRowEncoding

namespace CQGrid251

def twist (b : ℕ) (x : Interval) : Interval :=
  let z := (-1:ℤ)^b*x.lo
  ⟨z,z+(x.hi-x.lo)⟩

private theorem undo (b : ℕ) (x : Interval) : twist b (twist b x) = x := by
  cases x with
  | mk l h =>
    rcases neg_one_pow_eq_or ℤ b with hs|hs <;>
      simp [twist,hs]

private theorem twistCell (p : PackedRow) (b : ℕ) :
    twist b (cell false 2 p b) = cell true 2 p b := by
  simp [twist,cell,low]

theorem weightValid (n : ℕ) (p : PackedRow) (xs : List Interval) (hl : xs.length=n)
    (h : valid 2 p (xs.mapIdx twist)) : wrow p n=xs.toArray := by
  have hv := validRow 2 (by decide) p (xs.mapIdx twist) h n (by simp [hl])
  apply Array.ext
  · simp [wrow,tab,hl]
  · intro b hb hb'
    have hn : b<n := by simpa [wrow,tab] using hb
    have hk : b<(tab n (cell false 2 p)).size := by simpa [tab] using hn
    have h1 := congrArg (fun v : Array Interval => entry zeroInterval v b) hv
    rw [lookup _ _ _ _ hn] at h1
    have hxl : b<(xs.mapIdx twist).length := by simp [hl,hn]
    simp only [entry,List.getElem?_toArray,List.getElem?_eq_getElem hxl,Option.getD_some] at h1
    simp only [List.getElem_mapIdx] at h1
    simp only [wrow,tab,Array.getElem_ofFn,List.getElem_toArray]
    rw [← twistCell,h1,undo]

end CQGrid251



open GrothendieckLB.Supplement.CQHeadArithmetic GrothendieckLB.Supplement.CQDegree251
open GrothendieckLB.Supplement.CQHermite251 CQRowEncoding CQGrid251
set_option autoImplicit false
set_option maxRecDepth 150000
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 50000

namespace CQStream
open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadArithmetic
def shiftList : Nat → MomentCombination → List MomentCombination → List MomentCombination
  | n, x, y::z::zs => addCombination z (scaleCombination n x) :: shiftList (n+1) y (z::zs)
  | _, _, _ => []

def nextList (p : Nat) (prev cur : List MomentCombination) : List MomentCombination :=
  let x1 := shiftList 0 zeroCombination cur
  let x3 := shiftList 0 zeroCombination (shiftList 0 zeroCombination x1)
  List.zipWith (fun (a : MomentCombination × MomentCombination) b =>
    subCombination (multiplyByParityFactor p (subCombination (scaleCombination 3 a.1) a.2))
      (scaleCombination p b)) (x1.zip x3) prev

end CQStream
open GrothendieckLB.Supplement.CQHeadArithmetic CQStream
namespace CQRowProof

private theorem shiftLength (i : Nat) (prev : MomentCombination) (x : List MomentCombination) :
    (shiftList i prev x).length = x.length-1 := by
  induction x generalizing i prev with
  | nil => rfl
  | cons y ys ih =>
    cases ys with
    | nil => rfl
    | cons z zs =>
      simp only [shiftList,List.length_cons,ih]
      omega

private theorem shiftAt (x : List MomentCombination) (idx : Nat) (prev : MomentCombination)
    (b : Nat) (hb : b+1 < x.length) :
    (shiftList idx prev x)[b]?.getD zeroCombination =
      addCombination (x[b+1]?.getD zeroCombination)
        (scaleCombination ((idx+b : Nat) : Int) (if b=0 then prev else x[b-1]?.getD zeroCombination)) := by
  induction b generalizing x idx prev with
  | zero =>
    cases x with
    | nil => simp at hb
    | cons y ys =>
      cases ys with
      | nil => simp at hb
      | cons z zs => rfl
  | succ b ih =>
    cases x with
    | nil => simp at hb
    | cons y ys =>
      cases ys with
      | nil => simp at hb
      | cons z zs =>
        have h := ih (z::zs) (idx+1) y (by simp only [List.length_cons] at *; omega)
        simp only [shiftList,List.getElem?_cons_succ] 
        rw [h]
        cases b <;> simp [Nat.add_comm,Nat.add_left_comm]

private theorem tabList {α : Type} (d : α) (n : Nat) (f : Nat → α) (x : List α)
    (hlen : x.length=n) (hx : ∀ b, b<n → x[b]?.getD d=f b) :
    tab n f=x.toArray := by
  apply Array.ext
  · simp [tab,hlen]
  · intro b hb hx'
    have h : b < n := by simpa [tab] using hb
    have h' : b < x.length := hlen.symm ▸ h
    simpa [tab,List.getElem?_eq_getElem h'] using (hx b h).symm

theorem shift_eq (x : List MomentCombination) :
    shift x.toArray=(shiftList 0 zeroCombination x).toArray := by
  apply tabList zeroCombination
  · simp [shiftLength]
  · intro b hb
    have h : b+1 < x.length := by simp at hb; omega
    rw [shiftAt x 0 zeroCombination b h]
    simp only [entry,List.getElem?_toArray,Nat.zero_add]
    by_cases he : b=0
    · subst b; rfl
    · rw [if_neg he]

theorem next_eq (p : Nat) (prev cur : List MomentCombination)
    (hlen : cur.length-3 ≤ prev.length) :
    nextRow p prev.toArray cur.toArray = (nextList p prev cur).toArray := by
  simp only [nextRow,shift_eq]
  let x1 := shiftList 0 zeroCombination cur
  let x3 := shiftList 0 zeroCombination (shiftList 0 zeroCombination x1)
  have hl1 : x1.length=cur.length-1 := shiftLength .. 
  have hl3 : x3.length=cur.length-3 := by
    dsimp only [x3,x1]; simp only [shiftLength]; omega
  change tab x3.toArray.size _ = (List.zipWith _ (x1.zip x3) prev).toArray
  apply tabList zeroCombination
  · simp [hl1,hl3]; omega
  · intro b hb
    simp only [List.size_toArray] at hb
    have h1 : b<x1.length := by omega
    have hp : b<prev.length := by omega
    have hz : b<(List.zip x1 x3).length := by simp; omega
    have hz' : b<(List.zipWith (fun (a : MomentCombination × MomentCombination) c =>
      subCombination (multiplyByParityFactor p (subCombination (scaleCombination 3 a.1) a.2))
        (scaleCombination p c)) (x1.zip x3) prev).length := by simp; omega
    change _ = subCombination
      (multiplyByParityFactor p (subCombination (scaleCombination 3 (entry zeroCombination x1.toArray b))
        (entry zeroCombination x3.toArray b))) (scaleCombination p (entry zeroCombination prev.toArray b))
    simp only [List.getElem?_eq_getElem hz',List.getElem_zipWith,List.getElem_zip,entry,
      List.getElem?_toArray,List.getElem?_eq_getElem h1,List.getElem?_eq_getElem hb,
      List.getElem?_eq_getElem hp,Option.getD_some]

theorem weight_eq (n p : Nat) (x : List MomentCombination) (hlen : n-p ≤ x.length) :
    (tab (n-p) (fun b => toWeight (p+1) b (entry zeroCombination x.toArray b))) =
      ((x.take (n-p)).mapIdx (fun b v => toWeight (p+1) b v)).toArray := by
  apply tabList zeroInterval
  · simp [Nat.min_eq_left hlen]
  · intro b hb
    have h : b<x.length := by omega
    have h' : b<((x.take (n-p)).mapIdx (fun b v => toWeight (p+1) b v)).length := by simp; omega
    simp [List.getElem?_eq_getElem h',entry,h]
end CQRowProof

namespace CQGrid251
open CQRowProof CQStream

theorem advance {p : ℕ} {ini : Array MomentCombination} {pr cu nx : List MomentCombination} {ws : List Interval}
    (h : grid 251 ini p=⟨pr.toArray,cu.toArray,tab (p+1) weightRow⟩)
    (hlen : cu.length-3≤pr.length) (hsize : 251-p≤cu.length)
    (hn : nextList p pr cu=nx)
    (hw : (cu.take (251-p)).mapIdx (fun b x => toWeight (p+1) b x) = ws)
    (he : weightRow (p+1) = ws.toArray) :
    grid 251 ini (p+1)=⟨cu.toArray,nx.toArray,tab (p+1+1) weightRow⟩ := by
  simp only [grid,h,next_eq p pr cu hlen,hn,weight_eq 251 p cu hsize,hw,← he,tabPush]

theorem encoded {p : ℕ} {ws : List Interval} (hl : ws.length=252-p)
    (h : valid 2 (entry default wp p) (ws.mapIdx twist)) :
    weightRow p = ws.toArray := weightValid _ _ _ hl h

private def initFast (N : Nat) (raw : Array MomentCombination) : Array MomentCombination := Id.run do
  let len := 3*N+1
  let mut fact := #[1]
  let mut dbl := #[1,1]
  for i in [:len] do
    fact := fact.push ((i+1)*fact[i]!)
    dbl := dbl.push ((i+2)*dbl[i]!)
  let mut ini := #[]
  for b in [:len] do
    let mut sum := zeroCombination
    if b%2=0 then
      for t in [:b/2+1] do
        let k := 2*t
        let d := b-k
        let mag : Nat := dbl[d-1]! * (fact[b]! / (fact[k]! * fact[d]!))
        let coeff : Int := if d%4 = 0 then mag else -(mag:Int)
        sum := addCombination sum (scaleCombination coeff raw[k]!)
    ini := ini.push sum
  return ini


/-- A block of integer witnesses for adjacent moment rows and newly appended weight rows. -/
def sampleBlock (lo len : ℕ) : List (List MomentCombination) × List (List Interval) := Id.run do
  let raw := momentRows 748
  let mut cur := initFast 251 raw
  let mut prev := cur
  let mut ms := #[]
  let mut ws := #[]
  for p in [:lo+len+1] do
    if lo-1 ≤ p then ms := ms.push cur.toList
    if lo ≤ p && p < lo+len then
      ws := ws.push ((tab (251-p) (fun b => toWeight (p+1) b (entry zeroCombination cur b))).toList)
    let next := nextRow p prev cur
    prev := cur
    cur := next
  return (ms.toList,ws.toList)

end CQGrid251



open Polynomial
open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadArithmetic
open GrothendieckLB.Supplement.CQDegree251
namespace CQPackedCertificate

private theorem smallConstant (B : ℤ) (hB : 0 < B) (p : ℤ[X])
    (hr : p.eval B = 0) (hb : |p.coeff 0| < B) :
    p.coeff 0=0 ∧ p.divX.eval B=0 := by
  have hrec := congrArg (Polynomial.eval B) (X_mul_divX_add p)
  simp only [eval_add, eval_mul, eval_X, eval_C, hr] at hrec
  have hz : p.coeff 0 = 0 := Int.eq_zero_of_abs_lt_dvd
    ⟨-(p.divX.eval B), by rw [mul_neg]; omega⟩ hb
  rw [hz, add_zero] at hrec
  exact ⟨hz, (mul_eq_zero.mp hrec).resolve_left hB.ne'⟩

/-- An integer polynomial with a root at B and small low-order coefficients
has those coefficients equal to zero, one place at a time. -/
theorem coefficient_unique (B : ℤ) (hB : 0 < B) (p : ℤ[X]) (n : ℕ)
    (hr : p.eval B = 0) (hb : ∀ i, i ≤ n → |p.coeff i| < B) : p.coeff n = 0 := by
  induction n generalizing p with
  | zero => exact (smallConstant B hB p hr (hb 0 (by omega))).1
  | succ n ih =>
    rw [← coeff_divX]
    apply ih p.divX (smallConstant B hB p hr (hb 0 (by omega))).2
    intro i hi
    simpa only [coeff_divX] using hb (i+1) (by omega)

noncomputable def ofCoefficients : List ℤ → ℤ[X]
  | [] => 0
  | x :: xs => C x + X * ofCoefficients xs

def horner (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | x :: xs => x + B * horner B xs

theorem eval_ofCoefficients (B : ℤ) (xs : List ℤ) :
    (ofCoefficients xs).eval B = horner B xs := by
  induction xs with
  | nil => simp [ofCoefficients, horner]
  | cons x xs ih => simp [ofCoefficients, horner, ih]

theorem coeff_ofCoefficients (xs : List ℤ) (i : ℕ) :
    (ofCoefficients xs).coeff i = xs[i]?.getD 0 := by
  induction xs generalizing i with
  | nil => simp [ofCoefficients]
  | cons x xs ih => cases i <;> simp only [ofCoefficients,coeff_add,coeff_C_zero,coeff_X_mul_zero,
      add_zero,List.getElem?_cons_zero,Option.getD_some,coeff_C_succ,coeff_X_mul,zero_add,
      List.getElem?_cons_succ,ih]


end CQPackedCertificate



open GrothendieckLB.Supplement.CQHeadArithmetic
namespace CQInitial251
set_option maxRecDepth 10000
set_option exponentiation.threshold 50000

lemma den_pos (d : ℕ) : 0<den d := by unfold den; positivity
lemma fac_pos (i : ℕ) : 0<fac i := Nat.factorial_pos _
lemma fac_cancel {i : ℕ} (hi : i≤376) : scaleF i * fac i = Q :=
  Nat.div_mul_cancel (Nat.factorial_dvd_factorial (by omega : 2*i≤2*376))
lemma den_cancel {d : ℕ} (hd : d≤376) : scaleD d * den d = T :=
  Nat.div_mul_cancel (Nat.mul_dvd_mul (pow_dvd_pow 2 hd) (Nat.factorial_dvd_factorial hd))

def magnitude (i j : ℕ) := (2*(i-j)-1).doubleFactorial *
  (fac i / (fac j*(2*(i-j)).factorial))

lemma mag_cancel {i j : ℕ} (hj : j≤i) : magnitude i j * (fac j * den (i-j)) = fac i := by
  have hmul : 2*i-2*j=2*(i-j) := by omega
  have hdiv := Nat.factorial_mul_factorial_dvd_factorial (by omega : 2*j≤2*i)
  rw [hmul] at hdiv
  have hfact := Nat.div_mul_cancel hdiv
  have hd (k : ℕ) : (2*k-1).doubleFactorial * den k = (2*k).factorial := by
    cases k with
    | zero => decide
    | succ k =>
      have h := Nat.factorial_eq_mul_doubleFactorial (2*(k+1)-1)
      rw [show 2*(k+1)-1+1=2*(k+1) by omega, Nat.doubleFactorial_two_mul] at h
      simpa only [den,mul_comm] using h.symm
  calc
    _ = (fac i / (fac j*(2*(i-j)).factorial)) * (fac j*((2*(i-j)-1).doubleFactorial * den (i-j))) := by
      unfold magnitude; ring
    _ = _ := by rw [hd]; exact hfact

lemma original_coeff {i j : ℕ} (hj : j≤i) :
    hermiteCoeff (2*i) (2*j) = (-1:ℤ)^(i-j)*(magnitude i j:ℤ) := by
  have h : 2*i-2*j=2*(i-j) := by omega
  simp [hermiteCoeff,magnitude,fac,h,show (2*i+2*j)%2=0 by omega, mul_assoc]

lemma scaled_mag {i j : ℕ} (hi : i≤376) (hj : j≤i) :
    scaleF i*magnitude i j*T=scaleF j*scaleD (i-j) := by
  have hC : 0<fac j*den (i-j) := Nat.mul_pos (fac_pos _) (den_pos _)
  apply Nat.eq_of_mul_eq_mul_right hC
  calc
    _ = (scaleF i*(magnitude i j*(fac j*den (i-j)))) * T := by ring
    _ = Q*T := by rw [mag_cancel hj,fac_cancel hi]
    _ = (scaleF j*fac j)*(scaleD (i-j)*den (i-j)) := by
      rw [fac_cancel (by omega),den_cancel (by omega)]
    _ = _ := by ring

lemma projection_zero (a : Axis) (w : Bool) : projection a w zeroCombination=0 := by
  cases a <;> cases w <;> rfl

lemma projection_add (a : Axis) (w : Bool) (x y : MomentCombination) :
    projection a w (addCombination x y)=projection a w x+projection a w y := by
  cases a <;> cases w <;> simp [projection,component,addCombination,addInterval] <;> ring

lemma projection_scale (a : Axis) (w : Bool) (k : ℤ) (x : MomentCombination) :
    projection a w (scaleCombination k x)=multiplier w k * projection a w x := by
  by_cases h : k=0
  · subst k; cases a <;> cases w <;> simp [projection,component,scaleCombination,scaleInterval,zeroInterval,multiplier]
  · by_cases hs : 0≤k
    · cases a <;> cases w <;> simp [projection,component,scaleCombination,scaleInterval,
        h,hs,multiplier,abs_of_nonneg hs] <;> ring
    · have hn : k≤0 := by omega
      cases a <;> cases w <;> simp [projection,component,scaleCombination,scaleInterval,
        h,hs,multiplier,abs_of_nonpos hn] <;> ring

lemma projection_sum (a : Axis) (w : Bool) (f : ℕ → MomentCombination) (n : ℕ) :
    projection a w (sumCombinations f n)=∑ k∈Finset.range n, projection a w (f k) := by
  induction n with
  | zero => simp [sumCombinations,projection_zero]
  | succ n ih => rw [sumCombinations,projection_add,ih,Finset.sum_range_succ]

lemma evenSum (f : ℕ → ℤ) (m : ℕ) (h : ∀ j, f (2*j+1)=0) :
    (∑ k∈Finset.range (2*m+1),f k) = ∑ j∈Finset.range (m+1),f (2*j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1)+1=(2*m+1)+1+1 by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ _ (2*m+1), ih, h, add_zero, Finset.sum_range_succ _ (m+1)]
    rfl

lemma mult_coeff (w : Bool) {i j : ℕ} (hj : j≤i) :
    multiplier w (hermiteCoeff (2*i) (2*j)) = sign w (i-j) * magnitude i j := by
  rw [original_coeff hj]
  cases w <;> simp [sign,multiplier,abs_mul,abs_pow]

theorem transform (a : Axis) (w : Bool) (raw : Array MomentCombination)
    (i : ℕ) (hi : i≤376) :
    (scaleF i:ℤ)*T*projection a w (hStart raw (2*i)) =
      ∑ j∈Finset.range (i+1),
        ((scaleF j:ℤ)*projection a w (entry zeroCombination raw (2*j))) *
        (sign w (i-j) * scaleD (i-j)) := by
  let g (k : ℕ) := multiplier w (hermiteCoeff (2*i) k) * projection a w (entry zeroCombination raw k)
  have odd (j : ℕ) : g (2*j+1)=0 := by
    simp [g,hermiteCoeff,show (2*i+(2*j+1))%2≠0 by omega,multiplier]
  rw [hStart,if_pos (by omega),projection_sum]
  simp only [projection_scale]
  change _ * (∑ k∈Finset.range (2*i+1),g k) = _
  rw [evenSum g i odd,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j≤i := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
  have hz : (scaleF i:ℤ)*magnitude i j*T=(scaleF j:ℤ)*scaleD (i-j) := by exact_mod_cast scaled_mag hi hj'
  dsimp only [g]
  rw [mult_coeff w hj']
  linear_combination (sign w (i-j) * projection a w (entry zeroCombination raw (2*j))) * hz

end CQInitial251



open GrothendieckLB.Supplement.CQHeadArithmetic
open CQRowEncoding
namespace CQInitial251
set_option maxRecDepth 150000
set_option exponentiation.threshold 50000
set_option maxHeartbeats 200000000
set_option Elab.async false

def update (n : ℕ) (x y z : MomentCombination) :=
  divideCombination (3*slopeNumerator)
    (addCombination (subCombination (scaleCombination (((n:ℤ)+1)*slopeDenominator) x)
      (scaleCombination (slopeDenominator+9*slopeNumerator) y)) (scaleCombination (12*slopeNumerator) z))

theorem rawBase : momentRows 0=tab 6 rawAt := by decide +kernel
theorem rawTransitions : ∀ n : Fin 748,
    (if n.val%2=0 then update n.val (rawAt n.val) (rawAt (n.val+2)) (rawAt (n.val+4))
      else zeroCombination) = rawAt (n.val+6) := by decide +kernel

theorem raw_correct (n : ℕ) (hn : n≤748) : momentRows n=tab (n+6) rawAt := by
  induction n with
  | zero => exact rawBase
  | succ n ih =>
    have hi : n<748 := by omega
    simp only [momentRows, ih (by omega)]
    rw [lookup zeroCombination (n+6) rawAt n (by omega),lookup zeroCombination (n+6) rawAt (n+2) (by omega),
      lookup zeroCombination (n+6) rawAt (n+4) (by omega)]
    change (tab (n+6) rawAt).push (if n%2=0 then update n (rawAt n) (rawAt (n+2)) (rawAt (n+4))
      else zeroCombination) = tab (n+1+6) rawAt
    rw [rawTransitions ⟨n,hi⟩,tabPush]

end CQInitial251



open GrothendieckLB.Supplement.CQHeadArithmetic GrothendieckLB.Supplement.CQHermite251
open CQPackedCertificate Polynomial
namespace CQInitial251
set_option maxRecDepth 150000
set_option exponentiation.threshold 50000
set_option maxHeartbeats 300000000
set_option Elab.async false

theorem factorsF : ∀ i : Fin 377, sf i = scaleF i := by decide +kernel
theorem factorsD : ∀ i : Fin 377, sd i = scaleD i := by decide +kernel

theorem shift_horner (xs : List ℤ) : shiftHorner xs=horner B xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [shiftHorner,horner,ih,Int.shiftLeft_eq,mul_comm]; rfl


end CQInitial251


open Polynomial CQPackedCertificate CQRowEncoding
open GrothendieckLB.Supplement.CQHeadArithmetic GrothendieckLB.Supplement.CQHermite251
namespace CQInitial251
set_option maxRecDepth 120000
set_option exponentiation.threshold 50000
set_option maxHeartbeats 200000000

private theorem unique_mod (b : ℤ) (hb : 0<b) (p : ℤ[X]) (k n : ℕ) (hn : n<k)
    (hd : b^k ∣ p.eval b) (hsmall : ∀ j, j≤n → |p.coeff j|<b) : p.coeff n=0 := by
  obtain ⟨v,hv⟩ := hd
  let q : ℤ[X] := p-C v*X^k
  have hz (j : ℕ) (hj : j<k) : q.coeff j=p.coeff j := by
    simp [q,coeff_C_mul_X_pow,hj.ne]
  rw [← hz n hn]
  apply coefficient_unique b hb
  · simp [q,hv,mul_comm]
  · intro j hj; rw [hz _ (by omega)]; exact hsmall _ hj

private theorem sampleAt (f : ℕ → ℤ) (n : ℕ) (hn : n<377) :
    (sample f)[n]?.getD 0=f n := by simp [sample, List.getElem?_eq_getElem,hn]

private theorem coeffAt (f : ℕ → ℤ) (n : ℕ) (hn : n<377) :
    (ofCoefficients (sample f)).coeff n=f n := by rw [coeff_ofCoefficients,sampleAt _ _ hn]

private theorem productAt (f g : ℕ → ℤ) (n : ℕ) (hn : n<377) :
    (ofCoefficients (sample f)*ofCoefficients (sample g)).coeff n=
      ∑ i∈Finset.range (n+1),f i*g (n-i) := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  have hh := Finset.mem_range.mp hi
  rw [coeffAt _ _ (by omega),coeffAt _ _ (by omega)]

private def smallInterval (v : Interval) : Prop := |v.lo|≤2^5999 ∧ |v.hi|≤2^5999
private instance (v : Interval) : Decidable (smallInterval v) := inferInstanceAs (Decidable (_ ∧ _))
private def smallMC (x : MomentCombination) : Prop := smallInterval x.e0 ∧ smallInterval x.e2 ∧ smallInterval x.e4
private instance (x : MomentCombination) : Decidable (smallMC x) := inferInstanceAs (Decidable (_ ∧ _))

private theorem smallRaw : rawValues.all (fun x => decide (smallMC x))=true := by decide +kernel
private theorem smallInit : (pair 0).2.all (fun x => decide (smallMC x))=true := by decide +kernel
private theorem rawLength : rawValues.length=754 := by decide +kernel
theorem initLength : (pair 0).2.length=754 := by decide +kernel

private theorem boundProjection {x : MomentCombination} (h : smallMC x) (a : Axis) (w : Bool) :
    |projection a w x|≤2^6000 := by
  have hc : smallInterval (component a x) := by
    cases a with
    | e0 => exact h.1
    | e2 => exact h.2.1
    | e4 => exact h.2.2
  obtain ⟨hl,hh⟩ := hc
  have hl' := abs_le.mp hl
  have hh' := abs_le.mp hh
  have he : (2:ℤ)^6000=2*2^5999 := by rw [show 6000=5999+1 by decide,pow_succ,mul_comm]
  cases w <;> simp only [projection,Bool.false_eq_true,if_false,if_true,he,abs_le] <;> omega

private theorem boundAt (xs : List MomentCombination) (hs : xs.all (fun x => decide (smallMC x))=true)
    (a : Axis) (w : Bool) (i : ℕ) (hi : i<xs.length) :
    |projection a w (xs[i]?.getD zeroCombination)| ≤ 2^6000 := by
  rw [List.getElem?_eq_getElem hi,Option.getD_some]
  exact boundProjection (of_decide_eq_true (List.all_eq_true.mp hs _ (List.getElem_mem hi))) a w

private theorem boundQ : (Q:ℤ) ≤ 2^6200 := by decide +kernel
private theorem boundT : (T:ℤ) ≤ 2^3200 := by decide +kernel
private theorem sf_le (j : ℕ) (hj : j<377) : (sf j : ℤ) ≤ 2^6200 := by
  have he : sf j=scaleF j := factorsF ⟨j,hj⟩
  rw [he]
  exact (Int.ofNat_le.mpr (Nat.div_le_self Q _)).trans boundQ
private theorem sd_le (j : ℕ) (hj : j<377) : (sd j : ℤ) ≤ 2^3200 := by
  have he : sd j=scaleD j := factorsD ⟨j,hj⟩
  rw [he]
  exact (Int.ofNat_le.mpr (Nat.div_le_self T _)).trans boundT

private theorem boundA (a : Axis) (w : Bool) {j : ℕ} (hj : j<377) :
    |A a w j| ≤ 2^12200 := by
  rw [A,abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
  have h := boundAt rawValues smallRaw a w (2*j) (by rw [rawLength]; omega)
  calc
    _ ≤ (2:ℤ)^6200*2^6000 := mul_le_mul (sf_le j hj) h (abs_nonneg _) (by positivity)
    _ = _ := (pow_add ..).symm

private theorem boundK (w : Bool) {j : ℕ} (hj : j<377) : |K w j| ≤ 2^3200 := by
  cases w <;> simpa [K,sign,abs_mul,abs_pow] using sd_le j hj

private theorem boundZ (a : Axis) (w : Bool) {j : ℕ} (hj : j<377) :
    |Z a w j| ≤ 2^15400 := by
  rw [Z,abs_mul,abs_mul,abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _)]
  have h := boundAt (pair 0).2 smallInit a w (2*j) (by rw [initLength]; omega)
  calc
    _ ≤ ((2:ℤ)^6200*2^3200)*2^6000 :=
      mul_le_mul (mul_le_mul (sf_le j hj) boundT (Int.natCast_nonneg _) (by positivity)) h
        (abs_nonneg _) (by positivity)
    _ = _ := by rw [← pow_add,← pow_add]

private theorem prodSmall (a : Axis) (w : Bool) {m : ℕ} (hm : m<377) :
    |∑ j∈Finset.range (m+1), A a w j * K w (m-j)| ≤ 377*(2:ℤ)^15400 := by
  calc
    _ ≤ ∑ j∈Finset.range (m+1), |A a w j * K w (m-j)| := Finset.abs_sum_le_sum_abs .. 
    _ ≤ ∑ _j∈Finset.range (m+1), (2:ℤ)^15400 := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [abs_mul, show (2:ℤ)^15400=2^12200*2^3200 from pow_add (2:ℤ) 12200 3200]
      exact mul_le_mul (boundA a w (by omega)) (boundK w (by omega)) (abs_nonneg _) (by positivity)
    _ ≤ _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; gcongr; omega

theorem decodedProduct (a : Axis) (w : Bool) (h : correctProduct a w) (i : ℕ) (hi : i<377) :
    (∑ j∈Finset.range (i+1), A a w j * K w (i-j))= Z a w i := by
  let p := ofCoefficients (sample (A a w))*ofCoefficients (sample (K w)) - ofCoefficients (sample (Z a w))
  have hp (j : ℕ) (hj : j<377) : p.coeff j = (∑ b∈Finset.range (j+1), A a w b*K w (j-b))-Z a w j := by
    dsimp only [p]
    rw [coeff_sub,productAt _ _ _ hj,coeffAt _ _ hj]
  apply sub_eq_zero.mp
  rw [← hp i hi]
  apply unique_mod B (by unfold B; positivity) p 377 i hi
  · unfold correctProduct at h
    simp only [shift_horner] at h
    simp only [p,eval_sub,eval_mul,eval_ofCoefficients]
    exact Int.dvd_of_emod_eq_zero h
  · intro j hj
    have hj' : j<377 := by omega
    rw [hp _ hj',sub_eq_add_neg]
    calc
      _ ≤ |∑ b∈Finset.range (j+1), A a w b*K w (j-b)| + |Z a w j| := by
        simpa only [abs_neg] using abs_add_le (∑ b∈Finset.range (j+1), A a w b*K w (j-b)) (-Z a w j)
      _ ≤ 377*(2:ℤ)^15400 + 2^15400 := add_le_add (prodSmall a w hj') (boundZ a w hj')
      _ < _ := by decide +kernel

theorem projected (a : Axis) (w : Bool) (h : correctProduct a w) (i : ℕ) (hi : i<377) :
    projection a w (hStart (tab 754 rawAt) (2*i)) = projection a w (initialAt (2*i)) := by
  have ht := transform a w (tab 754 rawAt) i (by omega)
  have hs : sf i=scaleF i := factorsF ⟨i,hi⟩
  have hz := decodedProduct a w h i hi
  have hh : ((scaleF i:ℤ)*T)*projection a w (hStart (tab 754 rawAt) (2*i)) =
      ((scaleF i:ℤ)*T)*projection a w (initialAt (2*i)) := by
    rw [ht,← hs]
    change _ = Z a w i
    rw [← hz]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hf : sf j=scaleF j := factorsF ⟨j,by omega⟩
    have hd : sd (i-j)=scaleD (i-j) := factorsD ⟨i-j,by omega⟩
    rw [A,K,hf,hd,lookup _ 754 rawAt (2*j) (by omega)]
  apply mul_left_cancel₀ _ hh
  have h0 : scaleF i ≠ 0 := by
    intro h
    have h' := fac_cancel (by omega : i≤376)
    rw [h,zero_mul] at h'
    exact (fac_pos 376).ne' h'.symm
  have ht0 := (den_pos 376).ne'
  exact mul_ne_zero (Int.natCast_ne_zero.mpr h0) (Int.natCast_ne_zero.mpr ht0)

theorem initialEquality (hc : ∀ a w, correctProduct a w) :
    startAt 251=(pair 0).2.toArray := by
  have hodd : ∀ i : Fin 377, initialAt (2*i.val+1)=zeroCombination := by decide +kernel
  change tab 754 (hStart (momentRows 748))=_
  rw [raw_correct 748 (by omega)]
  apply Array.ext
  · simp [tab,initLength]
  · intro n hn hn'
    have hN : n<754 := by simpa [tab] using hn
    have hn0 : n<(pair 0).2.length := by rw [initLength]; exact hN
    have lookupIni : initialAt n=(pair 0).2[n] := by simp [initialAt,hn0]
    simp only [tab,Array.getElem_ofFn,List.getElem_toArray]
    rw [← lookupIni]
    change hStart (tab 754 rawAt) n=initialAt n
    let i := n/2
    have hi : i<377 := by dsimp [i]; omega
    by_cases he : n%2=0
    · have e : n=2*i := by dsimp [i]; omega
      rw [e]
      have hp (a w) := projected a w (hc a w) i hi
      generalize hStart (tab 754 rawAt) (2*i)=x at hp ⊢
      generalize initialAt (2*i)=y at hp ⊢
      cases x with | mk x0 x2 x4 =>
       cases y with | mk y0 y2 y4 =>
        have heq (x y : Interval) (hc : x.lo+x.hi=y.lo+y.hi) (hw : x.hi-x.lo=y.hi-y.lo) : x=y := by
          cases x; cases y; simp_all; omega
        rw [heq x0 y0 (hp .e0 false) (hp .e0 true),heq x2 y2 (hp .e2 false) (hp .e2 true),
          heq x4 y4 (hp .e4 false) (hp .e4 true)]
    · have e : n=2*i+1 := by dsimp [i]; omega
      have hh := hodd ⟨i,hi⟩
      change initialAt (2*i+1)=zeroCombination at hh
      rw [hStart,if_neg he,e,hh]

end CQInitial251


open GrothendieckLB.Supplement.CQHeadArithmetic GrothendieckLB.Supplement.CQDegree251
open GrothendieckLB.Supplement.CQHermite251 CQRowEncoding CQStream CQRowProof CQGrid251 CQInitial251

namespace CQInitial251
set_option maxRecDepth 150000
set_option maxHeartbeats 250000000
set_option exponentiation.threshold 50000
set_option Elab.async false

private def zeroList (N : ℕ) (x : List MomentCombination) : List Interval :=
  let s2 := shiftList 0 zeroCombination (shiftList 0 zeroCombination x)
  zeroInterval :: ((s2.zip x).take N).mapIdx (fun b pair =>
    scaledSq (9*slopeNumerator) (slopeDenominator*(b+1).factorial) (subCombination pair.1 pair.2))

private theorem shiftLen (i : ℕ) (prev : MomentCombination) (x : List MomentCombination) :
    (shiftList i prev x).length=x.length-1 := by
  induction x generalizing i prev with
  | nil => rfl
  | cons y ys ih =>
    cases ys with
    | nil => rfl
    | cons z zs => simp only [shiftList,List.length_cons,ih]; omega

private theorem zeroCorrect (N : ℕ) (x : List MomentCombination) (hx : N+2≤x.length) :
    zeroWeights N x.toArray=(zeroList N x).toArray := by
  let s2 := shiftList 0 zeroCombination (shiftList 0 zeroCombination x)
  have hs : s2.length=x.length-2 := by dsimp only [s2]; rw [shiftLen,shiftLen]; omega
  have hp : N≤(s2.zip x).length := by simp [hs]; omega
  have hl : (zeroList N x).length=N+1 := by
    simp only [zeroList,List.length_cons,List.length_mapIdx,List.length_take]
    exact congrArg (·+1) (Nat.min_eq_left hp)
  unfold zeroWeights
  rw [shift_eq,shift_eq]
  apply Array.ext
  · simp [tab,hl]
  · intro i h _
    have hi : i<N+1 := by simpa [tab] using h
    simp only [tab,Array.getElem_ofFn,List.getElem_toArray]
    cases i with
    | zero => rfl
    | succ j =>
      have hj : j<N := by omega
      have hj1 : j<s2.length := by omega
      have hj2 : j<x.length := by omega
      change (if j+1=0 then zeroInterval else
        scaledSq (9*slopeNumerator) (slopeDenominator*(j+1).factorial)
          (subCombination (entry zeroCombination s2.toArray (j+1-1))
            (entry zeroCombination x.toArray (j+1-1)))) =
          (zeroList N x)[j+1]
      simp only [Nat.succ_ne_zero,if_false,Nat.add_sub_cancel,zeroList,List.getElem_cons_succ,
        List.getElem_mapIdx,List.getElem_take,List.getElem_zip,entry,List.getElem?_toArray,
        List.getElem?_eq_getElem hj1,List.getElem?_eq_getElem hj2,Option.getD_some]
      rfl

private noncomputable def wzero : List Interval := eval% ((zeroWeights 251 (((sampleBlock 0 0).1.head!).toArray)).toList)
private theorem verifiedZero : zeroList 251 (pair 0).2=wzero := by decide +kernel
private theorem zeroPacked : weightRow 0=wzero.toArray := encoded (by decide +kernel) (by decide +kernel)

theorem gridSeed (checks : ∀ a w, correctProduct a w) : grid 251 (startAt 251) 0=state 0 := by
  have hp : (pair 0).1=(pair 0).2 := by decide +kernel
  have ht : tab (cut 0+1) weightRow = #[weightRow 0] := by
    change tab 1 weightRow=_
    apply Array.ext
    · simp [tab]
    · intro i hi _
      have : i=0 := by simp [tab] at hi; omega
      subst i; simp [tab]
  rw [state, hp, ht, grid, initialEquality checks, zeroCorrect _ _ (by rw [initLength]; omega),
    verifiedZero,zeroPacked]

end CQInitial251

open GrothendieckLB.Supplement in
theorem solution : CQHeadArithmetic.grid 251 (CQHeadArithmetic.startAt 251) 0 = CQHermite251.state 0 := by
  apply CQInitial251.gridSeed
  intro a w
  cases w with
  | false => exact cq_initial_hermite251_centers a
  | true => exact cq_initial_hermite251_widths a
