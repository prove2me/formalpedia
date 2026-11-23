-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_hermite_rows_116_to_134
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:10:59.000123+00:00
-- url     : https://prove2.me/submissions/eb5f1848-b653-412d-9cb7-155ed050052e

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
private noncomputable def data := eval% (sampleBlock 116 18)
private noncomputable def m115 := data.1[0]!
private noncomputable def m116 := data.1[1]!
private noncomputable def m117 := data.1[2]!
private noncomputable def m118 := data.1[3]!
private noncomputable def m119 := data.1[4]!
private noncomputable def m120 := data.1[5]!
private noncomputable def m121 := data.1[6]!
private noncomputable def m122 := data.1[7]!
private noncomputable def m123 := data.1[8]!
private noncomputable def m124 := data.1[9]!
private noncomputable def m125 := data.1[10]!
private noncomputable def m126 := data.1[11]!
private noncomputable def m127 := data.1[12]!
private noncomputable def m128 := data.1[13]!
private noncomputable def m129 := data.1[14]!
private noncomputable def m130 := data.1[15]!
private noncomputable def m131 := data.1[16]!
private noncomputable def m132 := data.1[17]!
private noncomputable def m133 := data.1[18]!
private noncomputable def m134 := data.1[19]!
private noncomputable def w117 := data.2[0]!
private theorem next116 : nextList 116 m115 m116=m117 := by decide +kernel
private theorem weight116 : (m116.take (251-116)).mapIdx (fun b x => toWeight (116+1) b x)=w117 := by decide +kernel
private theorem encoded116 : weightRow (116+1)=w117.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w118 := data.2[1]!
private theorem next117 : nextList 117 m116 m117=m118 := by decide +kernel
private theorem weight117 : (m117.take (251-117)).mapIdx (fun b x => toWeight (117+1) b x)=w118 := by decide +kernel
private theorem encoded117 : weightRow (117+1)=w118.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w119 := data.2[2]!
private theorem next118 : nextList 118 m117 m118=m119 := by decide +kernel
private theorem weight118 : (m118.take (251-118)).mapIdx (fun b x => toWeight (118+1) b x)=w119 := by decide +kernel
private theorem encoded118 : weightRow (118+1)=w119.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w120 := data.2[3]!
private theorem next119 : nextList 119 m118 m119=m120 := by decide +kernel
private theorem weight119 : (m119.take (251-119)).mapIdx (fun b x => toWeight (119+1) b x)=w120 := by decide +kernel
private theorem encoded119 : weightRow (119+1)=w120.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w121 := data.2[4]!
private theorem next120 : nextList 120 m119 m120=m121 := by decide +kernel
private theorem weight120 : (m120.take (251-120)).mapIdx (fun b x => toWeight (120+1) b x)=w121 := by decide +kernel
private theorem encoded120 : weightRow (120+1)=w121.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w122 := data.2[5]!
private theorem next121 : nextList 121 m120 m121=m122 := by decide +kernel
private theorem weight121 : (m121.take (251-121)).mapIdx (fun b x => toWeight (121+1) b x)=w122 := by decide +kernel
private theorem encoded121 : weightRow (121+1)=w122.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w123 := data.2[6]!
private theorem next122 : nextList 122 m121 m122=m123 := by decide +kernel
private theorem weight122 : (m122.take (251-122)).mapIdx (fun b x => toWeight (122+1) b x)=w123 := by decide +kernel
private theorem encoded122 : weightRow (122+1)=w123.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w124 := data.2[7]!
private theorem next123 : nextList 123 m122 m123=m124 := by decide +kernel
private theorem weight123 : (m123.take (251-123)).mapIdx (fun b x => toWeight (123+1) b x)=w124 := by decide +kernel
private theorem encoded123 : weightRow (123+1)=w124.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w125 := data.2[8]!
private theorem next124 : nextList 124 m123 m124=m125 := by decide +kernel
private theorem weight124 : (m124.take (251-124)).mapIdx (fun b x => toWeight (124+1) b x)=w125 := by decide +kernel
private theorem encoded124 : weightRow (124+1)=w125.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w126 := data.2[9]!
private theorem next125 : nextList 125 m124 m125=m126 := by decide +kernel
private theorem weight125 : (m125.take (251-125)).mapIdx (fun b x => toWeight (125+1) b x)=w126 := by decide +kernel
private theorem encoded125 : weightRow (125+1)=w126.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w127 := data.2[10]!
private theorem next126 : nextList 126 m125 m126=m127 := by decide +kernel
private theorem weight126 : (m126.take (251-126)).mapIdx (fun b x => toWeight (126+1) b x)=w127 := by decide +kernel
private theorem encoded126 : weightRow (126+1)=w127.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w128 := data.2[11]!
private theorem next127 : nextList 127 m126 m127=m128 := by decide +kernel
private theorem weight127 : (m127.take (251-127)).mapIdx (fun b x => toWeight (127+1) b x)=w128 := by decide +kernel
private theorem encoded127 : weightRow (127+1)=w128.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w129 := data.2[12]!
private theorem next128 : nextList 128 m127 m128=m129 := by decide +kernel
private theorem weight128 : (m128.take (251-128)).mapIdx (fun b x => toWeight (128+1) b x)=w129 := by decide +kernel
private theorem encoded128 : weightRow (128+1)=w129.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w130 := data.2[13]!
private theorem next129 : nextList 129 m128 m129=m130 := by decide +kernel
private theorem weight129 : (m129.take (251-129)).mapIdx (fun b x => toWeight (129+1) b x)=w130 := by decide +kernel
private theorem encoded129 : weightRow (129+1)=w130.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w131 := data.2[14]!
private theorem next130 : nextList 130 m129 m130=m131 := by decide +kernel
private theorem weight130 : (m130.take (251-130)).mapIdx (fun b x => toWeight (130+1) b x)=w131 := by decide +kernel
private theorem encoded130 : weightRow (130+1)=w131.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w132 := data.2[15]!
private theorem next131 : nextList 131 m130 m131=m132 := by decide +kernel
private theorem weight131 : (m131.take (251-131)).mapIdx (fun b x => toWeight (131+1) b x)=w132 := by decide +kernel
private theorem encoded131 : weightRow (131+1)=w132.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w133 := data.2[16]!
private theorem next132 : nextList 132 m131 m132=m133 := by decide +kernel
private theorem weight132 : (m132.take (251-132)).mapIdx (fun b x => toWeight (132+1) b x)=w133 := by decide +kernel
private theorem encoded132 : weightRow (132+1)=w133.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w134 := data.2[17]!
private theorem next133 : nextList 133 m132 m133=m134 := by decide +kernel
private theorem weight133 : (m133.take (251-133)).mapIdx (fun b x => toWeight (133+1) b x)=w134 := by decide +kernel
private theorem encoded133 : weightRow (133+1)=w134.toArray := encoded (by decide +kernel) (by decide +kernel)
end HermiteBlock

open HermiteBlock
theorem solution : ∀ ini : Array MomentCombination,
      grid 251 ini 116 = state 10 →
      grid 251 ini 134 = state 11 := by
  intro ini h
  have prev10 : (pair 10).1=m115 := by decide +kernel
  have cur10 : (pair 10).2=m116 := by decide +kernel
  have prev11 : (pair 11).1=m133 := by decide +kernel
  have cur11 : (pair 11).2=m134 := by decide +kernel
  rw [state,prev10,cur10] at h
  change grid 251 ini 116=⟨m115.toArray,m116.toArray,tab (116+1) weightRow⟩ at h
  have s117 := advance h (by decide +kernel) (by decide +kernel) next116 weight116 encoded116
  have s118 := advance s117 (by decide +kernel) (by decide +kernel) next117 weight117 encoded117
  have s119 := advance s118 (by decide +kernel) (by decide +kernel) next118 weight118 encoded118
  have s120 := advance s119 (by decide +kernel) (by decide +kernel) next119 weight119 encoded119
  have s121 := advance s120 (by decide +kernel) (by decide +kernel) next120 weight120 encoded120
  have s122 := advance s121 (by decide +kernel) (by decide +kernel) next121 weight121 encoded121
  have s123 := advance s122 (by decide +kernel) (by decide +kernel) next122 weight122 encoded122
  have s124 := advance s123 (by decide +kernel) (by decide +kernel) next123 weight123 encoded123
  have s125 := advance s124 (by decide +kernel) (by decide +kernel) next124 weight124 encoded124
  have s126 := advance s125 (by decide +kernel) (by decide +kernel) next125 weight125 encoded125
  have s127 := advance s126 (by decide +kernel) (by decide +kernel) next126 weight126 encoded126
  have s128 := advance s127 (by decide +kernel) (by decide +kernel) next127 weight127 encoded127
  have s129 := advance s128 (by decide +kernel) (by decide +kernel) next128 weight128 encoded128
  have s130 := advance s129 (by decide +kernel) (by decide +kernel) next129 weight129 encoded129
  have s131 := advance s130 (by decide +kernel) (by decide +kernel) next130 weight130 encoded130
  have s132 := advance s131 (by decide +kernel) (by decide +kernel) next131 weight131 encoded131
  have s133 := advance s132 (by decide +kernel) (by decide +kernel) next132 weight132 encoded132
  have s134 := advance s133 (by decide +kernel) (by decide +kernel) next133 weight133 encoded133
  rw [state,prev11,cur11]
  exact s134
