-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_hermite_rows_46_to_58
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:12:15.519826+00:00
-- url     : https://prove2.me/submissions/25193ebd-c20f-4b4b-b415-4c7202ac85c7

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
private noncomputable def data := eval% (sampleBlock 46 12)
private noncomputable def m45 := data.1[0]!
private noncomputable def m46 := data.1[1]!
private noncomputable def m47 := data.1[2]!
private noncomputable def m48 := data.1[3]!
private noncomputable def m49 := data.1[4]!
private noncomputable def m50 := data.1[5]!
private noncomputable def m51 := data.1[6]!
private noncomputable def m52 := data.1[7]!
private noncomputable def m53 := data.1[8]!
private noncomputable def m54 := data.1[9]!
private noncomputable def m55 := data.1[10]!
private noncomputable def m56 := data.1[11]!
private noncomputable def m57 := data.1[12]!
private noncomputable def m58 := data.1[13]!
private noncomputable def w47 := data.2[0]!
private theorem next46 : nextList 46 m45 m46=m47 := by decide +kernel
private theorem weight46 : (m46.take (251-46)).mapIdx (fun b x => toWeight (46+1) b x)=w47 := by decide +kernel
private theorem encoded46 : weightRow (46+1)=w47.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w48 := data.2[1]!
private theorem next47 : nextList 47 m46 m47=m48 := by decide +kernel
private theorem weight47 : (m47.take (251-47)).mapIdx (fun b x => toWeight (47+1) b x)=w48 := by decide +kernel
private theorem encoded47 : weightRow (47+1)=w48.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w49 := data.2[2]!
private theorem next48 : nextList 48 m47 m48=m49 := by decide +kernel
private theorem weight48 : (m48.take (251-48)).mapIdx (fun b x => toWeight (48+1) b x)=w49 := by decide +kernel
private theorem encoded48 : weightRow (48+1)=w49.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w50 := data.2[3]!
private theorem next49 : nextList 49 m48 m49=m50 := by decide +kernel
private theorem weight49 : (m49.take (251-49)).mapIdx (fun b x => toWeight (49+1) b x)=w50 := by decide +kernel
private theorem encoded49 : weightRow (49+1)=w50.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w51 := data.2[4]!
private theorem next50 : nextList 50 m49 m50=m51 := by decide +kernel
private theorem weight50 : (m50.take (251-50)).mapIdx (fun b x => toWeight (50+1) b x)=w51 := by decide +kernel
private theorem encoded50 : weightRow (50+1)=w51.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w52 := data.2[5]!
private theorem next51 : nextList 51 m50 m51=m52 := by decide +kernel
private theorem weight51 : (m51.take (251-51)).mapIdx (fun b x => toWeight (51+1) b x)=w52 := by decide +kernel
private theorem encoded51 : weightRow (51+1)=w52.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w53 := data.2[6]!
private theorem next52 : nextList 52 m51 m52=m53 := by decide +kernel
private theorem weight52 : (m52.take (251-52)).mapIdx (fun b x => toWeight (52+1) b x)=w53 := by decide +kernel
private theorem encoded52 : weightRow (52+1)=w53.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w54 := data.2[7]!
private theorem next53 : nextList 53 m52 m53=m54 := by decide +kernel
private theorem weight53 : (m53.take (251-53)).mapIdx (fun b x => toWeight (53+1) b x)=w54 := by decide +kernel
private theorem encoded53 : weightRow (53+1)=w54.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w55 := data.2[8]!
private theorem next54 : nextList 54 m53 m54=m55 := by decide +kernel
private theorem weight54 : (m54.take (251-54)).mapIdx (fun b x => toWeight (54+1) b x)=w55 := by decide +kernel
private theorem encoded54 : weightRow (54+1)=w55.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w56 := data.2[9]!
private theorem next55 : nextList 55 m54 m55=m56 := by decide +kernel
private theorem weight55 : (m55.take (251-55)).mapIdx (fun b x => toWeight (55+1) b x)=w56 := by decide +kernel
private theorem encoded55 : weightRow (55+1)=w56.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w57 := data.2[10]!
private theorem next56 : nextList 56 m55 m56=m57 := by decide +kernel
private theorem weight56 : (m56.take (251-56)).mapIdx (fun b x => toWeight (56+1) b x)=w57 := by decide +kernel
private theorem encoded56 : weightRow (56+1)=w57.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w58 := data.2[11]!
private theorem next57 : nextList 57 m56 m57=m58 := by decide +kernel
private theorem weight57 : (m57.take (251-57)).mapIdx (fun b x => toWeight (57+1) b x)=w58 := by decide +kernel
private theorem encoded57 : weightRow (57+1)=w58.toArray := encoded (by decide +kernel) (by decide +kernel)
end HermiteBlock

open HermiteBlock
theorem solution : ∀ ini : Array MomentCombination,
      grid 251 ini 46 = state 5 →
      grid 251 ini 58 = state 6 := by
  intro ini h
  have prev5 : (pair 5).1=m45 := by decide +kernel
  have cur5 : (pair 5).2=m46 := by decide +kernel
  have prev6 : (pair 6).1=m57 := by decide +kernel
  have cur6 : (pair 6).2=m58 := by decide +kernel
  rw [state,prev5,cur5] at h
  change grid 251 ini 46=⟨m45.toArray,m46.toArray,tab (46+1) weightRow⟩ at h
  have s47 := advance h (by decide +kernel) (by decide +kernel) next46 weight46 encoded46
  have s48 := advance s47 (by decide +kernel) (by decide +kernel) next47 weight47 encoded47
  have s49 := advance s48 (by decide +kernel) (by decide +kernel) next48 weight48 encoded48
  have s50 := advance s49 (by decide +kernel) (by decide +kernel) next49 weight49 encoded49
  have s51 := advance s50 (by decide +kernel) (by decide +kernel) next50 weight50 encoded50
  have s52 := advance s51 (by decide +kernel) (by decide +kernel) next51 weight51 encoded51
  have s53 := advance s52 (by decide +kernel) (by decide +kernel) next52 weight52 encoded52
  have s54 := advance s53 (by decide +kernel) (by decide +kernel) next53 weight53 encoded53
  have s55 := advance s54 (by decide +kernel) (by decide +kernel) next54 weight54 encoded54
  have s56 := advance s55 (by decide +kernel) (by decide +kernel) next55 weight55 encoded55
  have s57 := advance s56 (by decide +kernel) (by decide +kernel) next56 weight56 encoded56
  have s58 := advance s57 (by decide +kernel) (by decide +kernel) next57 weight57 encoded57
  rw [state,prev6,cur6]
  exact s58
