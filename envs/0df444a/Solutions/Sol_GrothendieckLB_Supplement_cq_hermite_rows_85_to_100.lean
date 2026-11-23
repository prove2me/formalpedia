-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_hermite_rows_85_to_100
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:26:23.936799+00:00
-- url     : https://prove2.me/submissions/d408e802-3f34-4574-9d9d-fefc31e86316

import Definitions.Def_GrothendieckLB_Supplement_cqDegree251Tables
import Mathlib.Tactic.NormNum
import Definitions.Def_GrothendieckLB_Supplement_cqHermite251Checkpoints
import Mathlib.Tactic.Ring


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

open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadArithmetic GrothendieckLB.Supplement.CQDegree251
open GrothendieckLB.Supplement.CQHermite251 CQRowEncoding CQGrid251 CQStream
namespace HermiteBlock
set_option maxRecDepth 150000
set_option maxHeartbeats 300000000
set_option exponentiation.threshold 50000
set_option Elab.async false
private noncomputable def data := eval% (sampleBlock 85 15)
private noncomputable def m84 := data.1[0]!
private noncomputable def m85 := data.1[1]!
private noncomputable def m86 := data.1[2]!
private noncomputable def m87 := data.1[3]!
private noncomputable def m88 := data.1[4]!
private noncomputable def m89 := data.1[5]!
private noncomputable def m90 := data.1[6]!
private noncomputable def m91 := data.1[7]!
private noncomputable def m92 := data.1[8]!
private noncomputable def m93 := data.1[9]!
private noncomputable def m94 := data.1[10]!
private noncomputable def m95 := data.1[11]!
private noncomputable def m96 := data.1[12]!
private noncomputable def m97 := data.1[13]!
private noncomputable def m98 := data.1[14]!
private noncomputable def m99 := data.1[15]!
private noncomputable def m100 := data.1[16]!
private noncomputable def w86 := data.2[0]!
private theorem next85 : nextList 85 m84 m85=m86 := by decide +kernel
private theorem weight85 : (m85.take (251-85)).mapIdx (fun b x => toWeight (85+1) b x)=w86 := by decide +kernel
private theorem encoded85 : weightRow (85+1)=w86.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w87 := data.2[1]!
private theorem next86 : nextList 86 m85 m86=m87 := by decide +kernel
private theorem weight86 : (m86.take (251-86)).mapIdx (fun b x => toWeight (86+1) b x)=w87 := by decide +kernel
private theorem encoded86 : weightRow (86+1)=w87.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w88 := data.2[2]!
private theorem next87 : nextList 87 m86 m87=m88 := by decide +kernel
private theorem weight87 : (m87.take (251-87)).mapIdx (fun b x => toWeight (87+1) b x)=w88 := by decide +kernel
private theorem encoded87 : weightRow (87+1)=w88.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w89 := data.2[3]!
private theorem next88 : nextList 88 m87 m88=m89 := by decide +kernel
private theorem weight88 : (m88.take (251-88)).mapIdx (fun b x => toWeight (88+1) b x)=w89 := by decide +kernel
private theorem encoded88 : weightRow (88+1)=w89.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w90 := data.2[4]!
private theorem next89 : nextList 89 m88 m89=m90 := by decide +kernel
private theorem weight89 : (m89.take (251-89)).mapIdx (fun b x => toWeight (89+1) b x)=w90 := by decide +kernel
private theorem encoded89 : weightRow (89+1)=w90.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w91 := data.2[5]!
private theorem next90 : nextList 90 m89 m90=m91 := by decide +kernel
private theorem weight90 : (m90.take (251-90)).mapIdx (fun b x => toWeight (90+1) b x)=w91 := by decide +kernel
private theorem encoded90 : weightRow (90+1)=w91.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w92 := data.2[6]!
private theorem next91 : nextList 91 m90 m91=m92 := by decide +kernel
private theorem weight91 : (m91.take (251-91)).mapIdx (fun b x => toWeight (91+1) b x)=w92 := by decide +kernel
private theorem encoded91 : weightRow (91+1)=w92.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w93 := data.2[7]!
private theorem next92 : nextList 92 m91 m92=m93 := by decide +kernel
private theorem weight92 : (m92.take (251-92)).mapIdx (fun b x => toWeight (92+1) b x)=w93 := by decide +kernel
private theorem encoded92 : weightRow (92+1)=w93.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w94 := data.2[8]!
private theorem next93 : nextList 93 m92 m93=m94 := by decide +kernel
private theorem weight93 : (m93.take (251-93)).mapIdx (fun b x => toWeight (93+1) b x)=w94 := by decide +kernel
private theorem encoded93 : weightRow (93+1)=w94.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w95 := data.2[9]!
private theorem next94 : nextList 94 m93 m94=m95 := by decide +kernel
private theorem weight94 : (m94.take (251-94)).mapIdx (fun b x => toWeight (94+1) b x)=w95 := by decide +kernel
private theorem encoded94 : weightRow (94+1)=w95.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w96 := data.2[10]!
private theorem next95 : nextList 95 m94 m95=m96 := by decide +kernel
private theorem weight95 : (m95.take (251-95)).mapIdx (fun b x => toWeight (95+1) b x)=w96 := by decide +kernel
private theorem encoded95 : weightRow (95+1)=w96.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w97 := data.2[11]!
private theorem next96 : nextList 96 m95 m96=m97 := by decide +kernel
private theorem weight96 : (m96.take (251-96)).mapIdx (fun b x => toWeight (96+1) b x)=w97 := by decide +kernel
private theorem encoded96 : weightRow (96+1)=w97.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w98 := data.2[12]!
private theorem next97 : nextList 97 m96 m97=m98 := by decide +kernel
private theorem weight97 : (m97.take (251-97)).mapIdx (fun b x => toWeight (97+1) b x)=w98 := by decide +kernel
private theorem encoded97 : weightRow (97+1)=w98.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w99 := data.2[13]!
private theorem next98 : nextList 98 m97 m98=m99 := by decide +kernel
private theorem weight98 : (m98.take (251-98)).mapIdx (fun b x => toWeight (98+1) b x)=w99 := by decide +kernel
private theorem encoded98 : weightRow (98+1)=w99.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w100 := data.2[14]!
private theorem next99 : nextList 99 m98 m99=m100 := by decide +kernel
private theorem weight99 : (m99.take (251-99)).mapIdx (fun b x => toWeight (99+1) b x)=w100 := by decide +kernel
private theorem encoded99 : weightRow (99+1)=w100.toArray := encoded (by decide +kernel) (by decide +kernel)
end HermiteBlock

open HermiteBlock
theorem solution : ∀ ini : Array MomentCombination,
      grid 251 ini 85 = state 8 →
      grid 251 ini 100 = state 9 := by
  intro ini h
  have prev8 : (pair 8).1=m84 := by decide +kernel
  have cur8 : (pair 8).2=m85 := by decide +kernel
  have prev9 : (pair 9).1=m99 := by decide +kernel
  have cur9 : (pair 9).2=m100 := by decide +kernel
  rw [state,prev8,cur8] at h
  change grid 251 ini 85=⟨m84.toArray,m85.toArray,tab (85+1) weightRow⟩ at h
  have s86 := advance h (by decide +kernel) (by decide +kernel) next85 weight85 encoded85
  have s87 := advance s86 (by decide +kernel) (by decide +kernel) next86 weight86 encoded86
  have s88 := advance s87 (by decide +kernel) (by decide +kernel) next87 weight87 encoded87
  have s89 := advance s88 (by decide +kernel) (by decide +kernel) next88 weight88 encoded88
  have s90 := advance s89 (by decide +kernel) (by decide +kernel) next89 weight89 encoded89
  have s91 := advance s90 (by decide +kernel) (by decide +kernel) next90 weight90 encoded90
  have s92 := advance s91 (by decide +kernel) (by decide +kernel) next91 weight91 encoded91
  have s93 := advance s92 (by decide +kernel) (by decide +kernel) next92 weight92 encoded92
  have s94 := advance s93 (by decide +kernel) (by decide +kernel) next93 weight93 encoded93
  have s95 := advance s94 (by decide +kernel) (by decide +kernel) next94 weight94 encoded94
  have s96 := advance s95 (by decide +kernel) (by decide +kernel) next95 weight95 encoded95
  have s97 := advance s96 (by decide +kernel) (by decide +kernel) next96 weight96 encoded96
  have s98 := advance s97 (by decide +kernel) (by decide +kernel) next97 weight97 encoded97
  have s99 := advance s98 (by decide +kernel) (by decide +kernel) next98 weight98 encoded98
  have s100 := advance s99 (by decide +kernel) (by decide +kernel) next99 weight99 encoded99
  rw [state,prev9,cur9]
  exact s100
