-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_hermite_rows_154_to_176
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:18:17.599081+00:00
-- url     : https://prove2.me/submissions/70033a5e-7353-4f75-bce1-61112cca126c

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
private noncomputable def data := eval% (sampleBlock 154 22)
private noncomputable def m153 := data.1[0]!
private noncomputable def m154 := data.1[1]!
private noncomputable def m155 := data.1[2]!
private noncomputable def m156 := data.1[3]!
private noncomputable def m157 := data.1[4]!
private noncomputable def m158 := data.1[5]!
private noncomputable def m159 := data.1[6]!
private noncomputable def m160 := data.1[7]!
private noncomputable def m161 := data.1[8]!
private noncomputable def m162 := data.1[9]!
private noncomputable def m163 := data.1[10]!
private noncomputable def m164 := data.1[11]!
private noncomputable def m165 := data.1[12]!
private noncomputable def m166 := data.1[13]!
private noncomputable def m167 := data.1[14]!
private noncomputable def m168 := data.1[15]!
private noncomputable def m169 := data.1[16]!
private noncomputable def m170 := data.1[17]!
private noncomputable def m171 := data.1[18]!
private noncomputable def m172 := data.1[19]!
private noncomputable def m173 := data.1[20]!
private noncomputable def m174 := data.1[21]!
private noncomputable def m175 := data.1[22]!
private noncomputable def m176 := data.1[23]!
private noncomputable def w155 := data.2[0]!
private theorem next154 : nextList 154 m153 m154=m155 := by decide +kernel
private theorem weight154 : (m154.take (251-154)).mapIdx (fun b x => toWeight (154+1) b x)=w155 := by decide +kernel
private theorem encoded154 : weightRow (154+1)=w155.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w156 := data.2[1]!
private theorem next155 : nextList 155 m154 m155=m156 := by decide +kernel
private theorem weight155 : (m155.take (251-155)).mapIdx (fun b x => toWeight (155+1) b x)=w156 := by decide +kernel
private theorem encoded155 : weightRow (155+1)=w156.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w157 := data.2[2]!
private theorem next156 : nextList 156 m155 m156=m157 := by decide +kernel
private theorem weight156 : (m156.take (251-156)).mapIdx (fun b x => toWeight (156+1) b x)=w157 := by decide +kernel
private theorem encoded156 : weightRow (156+1)=w157.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w158 := data.2[3]!
private theorem next157 : nextList 157 m156 m157=m158 := by decide +kernel
private theorem weight157 : (m157.take (251-157)).mapIdx (fun b x => toWeight (157+1) b x)=w158 := by decide +kernel
private theorem encoded157 : weightRow (157+1)=w158.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w159 := data.2[4]!
private theorem next158 : nextList 158 m157 m158=m159 := by decide +kernel
private theorem weight158 : (m158.take (251-158)).mapIdx (fun b x => toWeight (158+1) b x)=w159 := by decide +kernel
private theorem encoded158 : weightRow (158+1)=w159.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w160 := data.2[5]!
private theorem next159 : nextList 159 m158 m159=m160 := by decide +kernel
private theorem weight159 : (m159.take (251-159)).mapIdx (fun b x => toWeight (159+1) b x)=w160 := by decide +kernel
private theorem encoded159 : weightRow (159+1)=w160.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w161 := data.2[6]!
private theorem next160 : nextList 160 m159 m160=m161 := by decide +kernel
private theorem weight160 : (m160.take (251-160)).mapIdx (fun b x => toWeight (160+1) b x)=w161 := by decide +kernel
private theorem encoded160 : weightRow (160+1)=w161.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w162 := data.2[7]!
private theorem next161 : nextList 161 m160 m161=m162 := by decide +kernel
private theorem weight161 : (m161.take (251-161)).mapIdx (fun b x => toWeight (161+1) b x)=w162 := by decide +kernel
private theorem encoded161 : weightRow (161+1)=w162.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w163 := data.2[8]!
private theorem next162 : nextList 162 m161 m162=m163 := by decide +kernel
private theorem weight162 : (m162.take (251-162)).mapIdx (fun b x => toWeight (162+1) b x)=w163 := by decide +kernel
private theorem encoded162 : weightRow (162+1)=w163.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w164 := data.2[9]!
private theorem next163 : nextList 163 m162 m163=m164 := by decide +kernel
private theorem weight163 : (m163.take (251-163)).mapIdx (fun b x => toWeight (163+1) b x)=w164 := by decide +kernel
private theorem encoded163 : weightRow (163+1)=w164.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w165 := data.2[10]!
private theorem next164 : nextList 164 m163 m164=m165 := by decide +kernel
private theorem weight164 : (m164.take (251-164)).mapIdx (fun b x => toWeight (164+1) b x)=w165 := by decide +kernel
private theorem encoded164 : weightRow (164+1)=w165.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w166 := data.2[11]!
private theorem next165 : nextList 165 m164 m165=m166 := by decide +kernel
private theorem weight165 : (m165.take (251-165)).mapIdx (fun b x => toWeight (165+1) b x)=w166 := by decide +kernel
private theorem encoded165 : weightRow (165+1)=w166.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w167 := data.2[12]!
private theorem next166 : nextList 166 m165 m166=m167 := by decide +kernel
private theorem weight166 : (m166.take (251-166)).mapIdx (fun b x => toWeight (166+1) b x)=w167 := by decide +kernel
private theorem encoded166 : weightRow (166+1)=w167.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w168 := data.2[13]!
private theorem next167 : nextList 167 m166 m167=m168 := by decide +kernel
private theorem weight167 : (m167.take (251-167)).mapIdx (fun b x => toWeight (167+1) b x)=w168 := by decide +kernel
private theorem encoded167 : weightRow (167+1)=w168.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w169 := data.2[14]!
private theorem next168 : nextList 168 m167 m168=m169 := by decide +kernel
private theorem weight168 : (m168.take (251-168)).mapIdx (fun b x => toWeight (168+1) b x)=w169 := by decide +kernel
private theorem encoded168 : weightRow (168+1)=w169.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w170 := data.2[15]!
private theorem next169 : nextList 169 m168 m169=m170 := by decide +kernel
private theorem weight169 : (m169.take (251-169)).mapIdx (fun b x => toWeight (169+1) b x)=w170 := by decide +kernel
private theorem encoded169 : weightRow (169+1)=w170.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w171 := data.2[16]!
private theorem next170 : nextList 170 m169 m170=m171 := by decide +kernel
private theorem weight170 : (m170.take (251-170)).mapIdx (fun b x => toWeight (170+1) b x)=w171 := by decide +kernel
private theorem encoded170 : weightRow (170+1)=w171.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w172 := data.2[17]!
private theorem next171 : nextList 171 m170 m171=m172 := by decide +kernel
private theorem weight171 : (m171.take (251-171)).mapIdx (fun b x => toWeight (171+1) b x)=w172 := by decide +kernel
private theorem encoded171 : weightRow (171+1)=w172.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w173 := data.2[18]!
private theorem next172 : nextList 172 m171 m172=m173 := by decide +kernel
private theorem weight172 : (m172.take (251-172)).mapIdx (fun b x => toWeight (172+1) b x)=w173 := by decide +kernel
private theorem encoded172 : weightRow (172+1)=w173.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w174 := data.2[19]!
private theorem next173 : nextList 173 m172 m173=m174 := by decide +kernel
private theorem weight173 : (m173.take (251-173)).mapIdx (fun b x => toWeight (173+1) b x)=w174 := by decide +kernel
private theorem encoded173 : weightRow (173+1)=w174.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w175 := data.2[20]!
private theorem next174 : nextList 174 m173 m174=m175 := by decide +kernel
private theorem weight174 : (m174.take (251-174)).mapIdx (fun b x => toWeight (174+1) b x)=w175 := by decide +kernel
private theorem encoded174 : weightRow (174+1)=w175.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w176 := data.2[21]!
private theorem next175 : nextList 175 m174 m175=m176 := by decide +kernel
private theorem weight175 : (m175.take (251-175)).mapIdx (fun b x => toWeight (175+1) b x)=w176 := by decide +kernel
private theorem encoded175 : weightRow (175+1)=w176.toArray := encoded (by decide +kernel) (by decide +kernel)
end HermiteBlock

open HermiteBlock
theorem solution : ∀ ini : Array MomentCombination,
      grid 251 ini 154 = state 12 →
      grid 251 ini 176 = state 13 := by
  intro ini h
  have prev12 : (pair 12).1=m153 := by decide +kernel
  have cur12 : (pair 12).2=m154 := by decide +kernel
  have prev13 : (pair 13).1=m175 := by decide +kernel
  have cur13 : (pair 13).2=m176 := by decide +kernel
  rw [state,prev12,cur12] at h
  change grid 251 ini 154=⟨m153.toArray,m154.toArray,tab (154+1) weightRow⟩ at h
  have s155 := advance h (by decide +kernel) (by decide +kernel) next154 weight154 encoded154
  have s156 := advance s155 (by decide +kernel) (by decide +kernel) next155 weight155 encoded155
  have s157 := advance s156 (by decide +kernel) (by decide +kernel) next156 weight156 encoded156
  have s158 := advance s157 (by decide +kernel) (by decide +kernel) next157 weight157 encoded157
  have s159 := advance s158 (by decide +kernel) (by decide +kernel) next158 weight158 encoded158
  have s160 := advance s159 (by decide +kernel) (by decide +kernel) next159 weight159 encoded159
  have s161 := advance s160 (by decide +kernel) (by decide +kernel) next160 weight160 encoded160
  have s162 := advance s161 (by decide +kernel) (by decide +kernel) next161 weight161 encoded161
  have s163 := advance s162 (by decide +kernel) (by decide +kernel) next162 weight162 encoded162
  have s164 := advance s163 (by decide +kernel) (by decide +kernel) next163 weight163 encoded163
  have s165 := advance s164 (by decide +kernel) (by decide +kernel) next164 weight164 encoded164
  have s166 := advance s165 (by decide +kernel) (by decide +kernel) next165 weight165 encoded165
  have s167 := advance s166 (by decide +kernel) (by decide +kernel) next166 weight166 encoded166
  have s168 := advance s167 (by decide +kernel) (by decide +kernel) next167 weight167 encoded167
  have s169 := advance s168 (by decide +kernel) (by decide +kernel) next168 weight168 encoded168
  have s170 := advance s169 (by decide +kernel) (by decide +kernel) next169 weight169 encoded169
  have s171 := advance s170 (by decide +kernel) (by decide +kernel) next170 weight170 encoded170
  have s172 := advance s171 (by decide +kernel) (by decide +kernel) next171 weight171 encoded171
  have s173 := advance s172 (by decide +kernel) (by decide +kernel) next172 weight172 encoded172
  have s174 := advance s173 (by decide +kernel) (by decide +kernel) next173 weight173 encoded173
  have s175 := advance s174 (by decide +kernel) (by decide +kernel) next174 weight174 encoded174
  have s176 := advance s175 (by decide +kernel) (by decide +kernel) next175 weight175 encoded175
  rw [state,prev13,cur13]
  exact s176
