-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_hermite_rows_100_to_116
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:24:57.036198+00:00
-- url     : https://prove2.me/submissions/2d85992f-de4c-477c-95ec-de293b213597

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
private noncomputable def data := eval% (sampleBlock 100 16)
private noncomputable def m99 := data.1[0]!
private noncomputable def m100 := data.1[1]!
private noncomputable def m101 := data.1[2]!
private noncomputable def m102 := data.1[3]!
private noncomputable def m103 := data.1[4]!
private noncomputable def m104 := data.1[5]!
private noncomputable def m105 := data.1[6]!
private noncomputable def m106 := data.1[7]!
private noncomputable def m107 := data.1[8]!
private noncomputable def m108 := data.1[9]!
private noncomputable def m109 := data.1[10]!
private noncomputable def m110 := data.1[11]!
private noncomputable def m111 := data.1[12]!
private noncomputable def m112 := data.1[13]!
private noncomputable def m113 := data.1[14]!
private noncomputable def m114 := data.1[15]!
private noncomputable def m115 := data.1[16]!
private noncomputable def m116 := data.1[17]!
private noncomputable def w101 := data.2[0]!
private theorem next100 : nextList 100 m99 m100=m101 := by decide +kernel
private theorem weight100 : (m100.take (251-100)).mapIdx (fun b x => toWeight (100+1) b x)=w101 := by decide +kernel
private theorem encoded100 : weightRow (100+1)=w101.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w102 := data.2[1]!
private theorem next101 : nextList 101 m100 m101=m102 := by decide +kernel
private theorem weight101 : (m101.take (251-101)).mapIdx (fun b x => toWeight (101+1) b x)=w102 := by decide +kernel
private theorem encoded101 : weightRow (101+1)=w102.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w103 := data.2[2]!
private theorem next102 : nextList 102 m101 m102=m103 := by decide +kernel
private theorem weight102 : (m102.take (251-102)).mapIdx (fun b x => toWeight (102+1) b x)=w103 := by decide +kernel
private theorem encoded102 : weightRow (102+1)=w103.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w104 := data.2[3]!
private theorem next103 : nextList 103 m102 m103=m104 := by decide +kernel
private theorem weight103 : (m103.take (251-103)).mapIdx (fun b x => toWeight (103+1) b x)=w104 := by decide +kernel
private theorem encoded103 : weightRow (103+1)=w104.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w105 := data.2[4]!
private theorem next104 : nextList 104 m103 m104=m105 := by decide +kernel
private theorem weight104 : (m104.take (251-104)).mapIdx (fun b x => toWeight (104+1) b x)=w105 := by decide +kernel
private theorem encoded104 : weightRow (104+1)=w105.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w106 := data.2[5]!
private theorem next105 : nextList 105 m104 m105=m106 := by decide +kernel
private theorem weight105 : (m105.take (251-105)).mapIdx (fun b x => toWeight (105+1) b x)=w106 := by decide +kernel
private theorem encoded105 : weightRow (105+1)=w106.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w107 := data.2[6]!
private theorem next106 : nextList 106 m105 m106=m107 := by decide +kernel
private theorem weight106 : (m106.take (251-106)).mapIdx (fun b x => toWeight (106+1) b x)=w107 := by decide +kernel
private theorem encoded106 : weightRow (106+1)=w107.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w108 := data.2[7]!
private theorem next107 : nextList 107 m106 m107=m108 := by decide +kernel
private theorem weight107 : (m107.take (251-107)).mapIdx (fun b x => toWeight (107+1) b x)=w108 := by decide +kernel
private theorem encoded107 : weightRow (107+1)=w108.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w109 := data.2[8]!
private theorem next108 : nextList 108 m107 m108=m109 := by decide +kernel
private theorem weight108 : (m108.take (251-108)).mapIdx (fun b x => toWeight (108+1) b x)=w109 := by decide +kernel
private theorem encoded108 : weightRow (108+1)=w109.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w110 := data.2[9]!
private theorem next109 : nextList 109 m108 m109=m110 := by decide +kernel
private theorem weight109 : (m109.take (251-109)).mapIdx (fun b x => toWeight (109+1) b x)=w110 := by decide +kernel
private theorem encoded109 : weightRow (109+1)=w110.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w111 := data.2[10]!
private theorem next110 : nextList 110 m109 m110=m111 := by decide +kernel
private theorem weight110 : (m110.take (251-110)).mapIdx (fun b x => toWeight (110+1) b x)=w111 := by decide +kernel
private theorem encoded110 : weightRow (110+1)=w111.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w112 := data.2[11]!
private theorem next111 : nextList 111 m110 m111=m112 := by decide +kernel
private theorem weight111 : (m111.take (251-111)).mapIdx (fun b x => toWeight (111+1) b x)=w112 := by decide +kernel
private theorem encoded111 : weightRow (111+1)=w112.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w113 := data.2[12]!
private theorem next112 : nextList 112 m111 m112=m113 := by decide +kernel
private theorem weight112 : (m112.take (251-112)).mapIdx (fun b x => toWeight (112+1) b x)=w113 := by decide +kernel
private theorem encoded112 : weightRow (112+1)=w113.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w114 := data.2[13]!
private theorem next113 : nextList 113 m112 m113=m114 := by decide +kernel
private theorem weight113 : (m113.take (251-113)).mapIdx (fun b x => toWeight (113+1) b x)=w114 := by decide +kernel
private theorem encoded113 : weightRow (113+1)=w114.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w115 := data.2[14]!
private theorem next114 : nextList 114 m113 m114=m115 := by decide +kernel
private theorem weight114 : (m114.take (251-114)).mapIdx (fun b x => toWeight (114+1) b x)=w115 := by decide +kernel
private theorem encoded114 : weightRow (114+1)=w115.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w116 := data.2[15]!
private theorem next115 : nextList 115 m114 m115=m116 := by decide +kernel
private theorem weight115 : (m115.take (251-115)).mapIdx (fun b x => toWeight (115+1) b x)=w116 := by decide +kernel
private theorem encoded115 : weightRow (115+1)=w116.toArray := encoded (by decide +kernel) (by decide +kernel)
end HermiteBlock

open HermiteBlock
theorem solution : ∀ ini : Array MomentCombination,
      grid 251 ini 100 = state 9 →
      grid 251 ini 116 = state 10 := by
  intro ini h
  have prev9 : (pair 9).1=m99 := by decide +kernel
  have cur9 : (pair 9).2=m100 := by decide +kernel
  have prev10 : (pair 10).1=m115 := by decide +kernel
  have cur10 : (pair 10).2=m116 := by decide +kernel
  rw [state,prev9,cur9] at h
  change grid 251 ini 100=⟨m99.toArray,m100.toArray,tab (100+1) weightRow⟩ at h
  have s101 := advance h (by decide +kernel) (by decide +kernel) next100 weight100 encoded100
  have s102 := advance s101 (by decide +kernel) (by decide +kernel) next101 weight101 encoded101
  have s103 := advance s102 (by decide +kernel) (by decide +kernel) next102 weight102 encoded102
  have s104 := advance s103 (by decide +kernel) (by decide +kernel) next103 weight103 encoded103
  have s105 := advance s104 (by decide +kernel) (by decide +kernel) next104 weight104 encoded104
  have s106 := advance s105 (by decide +kernel) (by decide +kernel) next105 weight105 encoded105
  have s107 := advance s106 (by decide +kernel) (by decide +kernel) next106 weight106 encoded106
  have s108 := advance s107 (by decide +kernel) (by decide +kernel) next107 weight107 encoded107
  have s109 := advance s108 (by decide +kernel) (by decide +kernel) next108 weight108 encoded108
  have s110 := advance s109 (by decide +kernel) (by decide +kernel) next109 weight109 encoded109
  have s111 := advance s110 (by decide +kernel) (by decide +kernel) next110 weight110 encoded110
  have s112 := advance s111 (by decide +kernel) (by decide +kernel) next111 weight111 encoded111
  have s113 := advance s112 (by decide +kernel) (by decide +kernel) next112 weight112 encoded112
  have s114 := advance s113 (by decide +kernel) (by decide +kernel) next113 weight113 encoded113
  have s115 := advance s114 (by decide +kernel) (by decide +kernel) next114 weight114 encoded114
  have s116 := advance s115 (by decide +kernel) (by decide +kernel) next115 weight115 encoded115
  rw [state,prev10,cur10]
  exact s116
