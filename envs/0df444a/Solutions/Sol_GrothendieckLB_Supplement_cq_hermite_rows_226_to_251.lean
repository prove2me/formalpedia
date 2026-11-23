-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_hermite_rows_226_to_251
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:09:03.166548+00:00
-- url     : https://prove2.me/submissions/ffac781a-5208-44f7-9e87-3aff3e4602ea

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
private noncomputable def data := eval% (sampleBlock 226 25)
private noncomputable def m225 := data.1[0]!
private noncomputable def m226 := data.1[1]!
private noncomputable def m227 := data.1[2]!
private noncomputable def m228 := data.1[3]!
private noncomputable def m229 := data.1[4]!
private noncomputable def m230 := data.1[5]!
private noncomputable def m231 := data.1[6]!
private noncomputable def m232 := data.1[7]!
private noncomputable def m233 := data.1[8]!
private noncomputable def m234 := data.1[9]!
private noncomputable def m235 := data.1[10]!
private noncomputable def m236 := data.1[11]!
private noncomputable def m237 := data.1[12]!
private noncomputable def m238 := data.1[13]!
private noncomputable def m239 := data.1[14]!
private noncomputable def m240 := data.1[15]!
private noncomputable def m241 := data.1[16]!
private noncomputable def m242 := data.1[17]!
private noncomputable def m243 := data.1[18]!
private noncomputable def m244 := data.1[19]!
private noncomputable def m245 := data.1[20]!
private noncomputable def m246 := data.1[21]!
private noncomputable def m247 := data.1[22]!
private noncomputable def m248 := data.1[23]!
private noncomputable def m249 := data.1[24]!
private noncomputable def m250 := data.1[25]!
private noncomputable def m251 := data.1[26]!
private noncomputable def w227 := data.2[0]!
private theorem next226 : nextList 226 m225 m226=m227 := by decide +kernel
private theorem weight226 : (m226.take (251-226)).mapIdx (fun b x => toWeight (226+1) b x)=w227 := by decide +kernel
private theorem encoded226 : weightRow (226+1)=w227.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w228 := data.2[1]!
private theorem next227 : nextList 227 m226 m227=m228 := by decide +kernel
private theorem weight227 : (m227.take (251-227)).mapIdx (fun b x => toWeight (227+1) b x)=w228 := by decide +kernel
private theorem encoded227 : weightRow (227+1)=w228.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w229 := data.2[2]!
private theorem next228 : nextList 228 m227 m228=m229 := by decide +kernel
private theorem weight228 : (m228.take (251-228)).mapIdx (fun b x => toWeight (228+1) b x)=w229 := by decide +kernel
private theorem encoded228 : weightRow (228+1)=w229.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w230 := data.2[3]!
private theorem next229 : nextList 229 m228 m229=m230 := by decide +kernel
private theorem weight229 : (m229.take (251-229)).mapIdx (fun b x => toWeight (229+1) b x)=w230 := by decide +kernel
private theorem encoded229 : weightRow (229+1)=w230.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w231 := data.2[4]!
private theorem next230 : nextList 230 m229 m230=m231 := by decide +kernel
private theorem weight230 : (m230.take (251-230)).mapIdx (fun b x => toWeight (230+1) b x)=w231 := by decide +kernel
private theorem encoded230 : weightRow (230+1)=w231.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w232 := data.2[5]!
private theorem next231 : nextList 231 m230 m231=m232 := by decide +kernel
private theorem weight231 : (m231.take (251-231)).mapIdx (fun b x => toWeight (231+1) b x)=w232 := by decide +kernel
private theorem encoded231 : weightRow (231+1)=w232.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w233 := data.2[6]!
private theorem next232 : nextList 232 m231 m232=m233 := by decide +kernel
private theorem weight232 : (m232.take (251-232)).mapIdx (fun b x => toWeight (232+1) b x)=w233 := by decide +kernel
private theorem encoded232 : weightRow (232+1)=w233.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w234 := data.2[7]!
private theorem next233 : nextList 233 m232 m233=m234 := by decide +kernel
private theorem weight233 : (m233.take (251-233)).mapIdx (fun b x => toWeight (233+1) b x)=w234 := by decide +kernel
private theorem encoded233 : weightRow (233+1)=w234.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w235 := data.2[8]!
private theorem next234 : nextList 234 m233 m234=m235 := by decide +kernel
private theorem weight234 : (m234.take (251-234)).mapIdx (fun b x => toWeight (234+1) b x)=w235 := by decide +kernel
private theorem encoded234 : weightRow (234+1)=w235.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w236 := data.2[9]!
private theorem next235 : nextList 235 m234 m235=m236 := by decide +kernel
private theorem weight235 : (m235.take (251-235)).mapIdx (fun b x => toWeight (235+1) b x)=w236 := by decide +kernel
private theorem encoded235 : weightRow (235+1)=w236.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w237 := data.2[10]!
private theorem next236 : nextList 236 m235 m236=m237 := by decide +kernel
private theorem weight236 : (m236.take (251-236)).mapIdx (fun b x => toWeight (236+1) b x)=w237 := by decide +kernel
private theorem encoded236 : weightRow (236+1)=w237.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w238 := data.2[11]!
private theorem next237 : nextList 237 m236 m237=m238 := by decide +kernel
private theorem weight237 : (m237.take (251-237)).mapIdx (fun b x => toWeight (237+1) b x)=w238 := by decide +kernel
private theorem encoded237 : weightRow (237+1)=w238.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w239 := data.2[12]!
private theorem next238 : nextList 238 m237 m238=m239 := by decide +kernel
private theorem weight238 : (m238.take (251-238)).mapIdx (fun b x => toWeight (238+1) b x)=w239 := by decide +kernel
private theorem encoded238 : weightRow (238+1)=w239.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w240 := data.2[13]!
private theorem next239 : nextList 239 m238 m239=m240 := by decide +kernel
private theorem weight239 : (m239.take (251-239)).mapIdx (fun b x => toWeight (239+1) b x)=w240 := by decide +kernel
private theorem encoded239 : weightRow (239+1)=w240.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w241 := data.2[14]!
private theorem next240 : nextList 240 m239 m240=m241 := by decide +kernel
private theorem weight240 : (m240.take (251-240)).mapIdx (fun b x => toWeight (240+1) b x)=w241 := by decide +kernel
private theorem encoded240 : weightRow (240+1)=w241.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w242 := data.2[15]!
private theorem next241 : nextList 241 m240 m241=m242 := by decide +kernel
private theorem weight241 : (m241.take (251-241)).mapIdx (fun b x => toWeight (241+1) b x)=w242 := by decide +kernel
private theorem encoded241 : weightRow (241+1)=w242.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w243 := data.2[16]!
private theorem next242 : nextList 242 m241 m242=m243 := by decide +kernel
private theorem weight242 : (m242.take (251-242)).mapIdx (fun b x => toWeight (242+1) b x)=w243 := by decide +kernel
private theorem encoded242 : weightRow (242+1)=w243.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w244 := data.2[17]!
private theorem next243 : nextList 243 m242 m243=m244 := by decide +kernel
private theorem weight243 : (m243.take (251-243)).mapIdx (fun b x => toWeight (243+1) b x)=w244 := by decide +kernel
private theorem encoded243 : weightRow (243+1)=w244.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w245 := data.2[18]!
private theorem next244 : nextList 244 m243 m244=m245 := by decide +kernel
private theorem weight244 : (m244.take (251-244)).mapIdx (fun b x => toWeight (244+1) b x)=w245 := by decide +kernel
private theorem encoded244 : weightRow (244+1)=w245.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w246 := data.2[19]!
private theorem next245 : nextList 245 m244 m245=m246 := by decide +kernel
private theorem weight245 : (m245.take (251-245)).mapIdx (fun b x => toWeight (245+1) b x)=w246 := by decide +kernel
private theorem encoded245 : weightRow (245+1)=w246.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w247 := data.2[20]!
private theorem next246 : nextList 246 m245 m246=m247 := by decide +kernel
private theorem weight246 : (m246.take (251-246)).mapIdx (fun b x => toWeight (246+1) b x)=w247 := by decide +kernel
private theorem encoded246 : weightRow (246+1)=w247.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w248 := data.2[21]!
private theorem next247 : nextList 247 m246 m247=m248 := by decide +kernel
private theorem weight247 : (m247.take (251-247)).mapIdx (fun b x => toWeight (247+1) b x)=w248 := by decide +kernel
private theorem encoded247 : weightRow (247+1)=w248.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w249 := data.2[22]!
private theorem next248 : nextList 248 m247 m248=m249 := by decide +kernel
private theorem weight248 : (m248.take (251-248)).mapIdx (fun b x => toWeight (248+1) b x)=w249 := by decide +kernel
private theorem encoded248 : weightRow (248+1)=w249.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w250 := data.2[23]!
private theorem next249 : nextList 249 m248 m249=m250 := by decide +kernel
private theorem weight249 : (m249.take (251-249)).mapIdx (fun b x => toWeight (249+1) b x)=w250 := by decide +kernel
private theorem encoded249 : weightRow (249+1)=w250.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w251 := data.2[24]!
private theorem next250 : nextList 250 m249 m250=m251 := by decide +kernel
private theorem weight250 : (m250.take (251-250)).mapIdx (fun b x => toWeight (250+1) b x)=w251 := by decide +kernel
private theorem encoded250 : weightRow (250+1)=w251.toArray := encoded (by decide +kernel) (by decide +kernel)
end HermiteBlock

open HermiteBlock
theorem solution : ∀ ini : Array MomentCombination,
      grid 251 ini 226 = state 15 →
      grid 251 ini 251 = state 16 := by
  intro ini h
  have prev15 : (pair 15).1=m225 := by decide +kernel
  have cur15 : (pair 15).2=m226 := by decide +kernel
  have prev16 : (pair 16).1=m250 := by decide +kernel
  have cur16 : (pair 16).2=m251 := by decide +kernel
  rw [state,prev15,cur15] at h
  change grid 251 ini 226=⟨m225.toArray,m226.toArray,tab (226+1) weightRow⟩ at h
  have s227 := advance h (by decide +kernel) (by decide +kernel) next226 weight226 encoded226
  have s228 := advance s227 (by decide +kernel) (by decide +kernel) next227 weight227 encoded227
  have s229 := advance s228 (by decide +kernel) (by decide +kernel) next228 weight228 encoded228
  have s230 := advance s229 (by decide +kernel) (by decide +kernel) next229 weight229 encoded229
  have s231 := advance s230 (by decide +kernel) (by decide +kernel) next230 weight230 encoded230
  have s232 := advance s231 (by decide +kernel) (by decide +kernel) next231 weight231 encoded231
  have s233 := advance s232 (by decide +kernel) (by decide +kernel) next232 weight232 encoded232
  have s234 := advance s233 (by decide +kernel) (by decide +kernel) next233 weight233 encoded233
  have s235 := advance s234 (by decide +kernel) (by decide +kernel) next234 weight234 encoded234
  have s236 := advance s235 (by decide +kernel) (by decide +kernel) next235 weight235 encoded235
  have s237 := advance s236 (by decide +kernel) (by decide +kernel) next236 weight236 encoded236
  have s238 := advance s237 (by decide +kernel) (by decide +kernel) next237 weight237 encoded237
  have s239 := advance s238 (by decide +kernel) (by decide +kernel) next238 weight238 encoded238
  have s240 := advance s239 (by decide +kernel) (by decide +kernel) next239 weight239 encoded239
  have s241 := advance s240 (by decide +kernel) (by decide +kernel) next240 weight240 encoded240
  have s242 := advance s241 (by decide +kernel) (by decide +kernel) next241 weight241 encoded241
  have s243 := advance s242 (by decide +kernel) (by decide +kernel) next242 weight242 encoded242
  have s244 := advance s243 (by decide +kernel) (by decide +kernel) next243 weight243 encoded243
  have s245 := advance s244 (by decide +kernel) (by decide +kernel) next244 weight244 encoded244
  have s246 := advance s245 (by decide +kernel) (by decide +kernel) next245 weight245 encoded245
  have s247 := advance s246 (by decide +kernel) (by decide +kernel) next246 weight246 encoded246
  have s248 := advance s247 (by decide +kernel) (by decide +kernel) next247 weight247 encoded247
  have s249 := advance s248 (by decide +kernel) (by decide +kernel) next248 weight248 encoded248
  have s250 := advance s249 (by decide +kernel) (by decide +kernel) next249 weight249 encoded249
  have s251 := advance s250 (by decide +kernel) (by decide +kernel) next250 weight250 encoded250
  rw [state,prev16,cur16]
  exact s251
