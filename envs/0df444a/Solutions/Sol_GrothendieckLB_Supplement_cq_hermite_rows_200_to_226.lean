-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_hermite_rows_200_to_226
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:11:52.385086+00:00
-- url     : https://prove2.me/submissions/b0e73de8-5b9c-4eeb-bd1e-913ab42d64fb

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
private noncomputable def data := eval% (sampleBlock 200 26)
private noncomputable def m199 := data.1[0]!
private noncomputable def m200 := data.1[1]!
private noncomputable def m201 := data.1[2]!
private noncomputable def m202 := data.1[3]!
private noncomputable def m203 := data.1[4]!
private noncomputable def m204 := data.1[5]!
private noncomputable def m205 := data.1[6]!
private noncomputable def m206 := data.1[7]!
private noncomputable def m207 := data.1[8]!
private noncomputable def m208 := data.1[9]!
private noncomputable def m209 := data.1[10]!
private noncomputable def m210 := data.1[11]!
private noncomputable def m211 := data.1[12]!
private noncomputable def m212 := data.1[13]!
private noncomputable def m213 := data.1[14]!
private noncomputable def m214 := data.1[15]!
private noncomputable def m215 := data.1[16]!
private noncomputable def m216 := data.1[17]!
private noncomputable def m217 := data.1[18]!
private noncomputable def m218 := data.1[19]!
private noncomputable def m219 := data.1[20]!
private noncomputable def m220 := data.1[21]!
private noncomputable def m221 := data.1[22]!
private noncomputable def m222 := data.1[23]!
private noncomputable def m223 := data.1[24]!
private noncomputable def m224 := data.1[25]!
private noncomputable def m225 := data.1[26]!
private noncomputable def m226 := data.1[27]!
private noncomputable def w201 := data.2[0]!
private theorem next200 : nextList 200 m199 m200=m201 := by decide +kernel
private theorem weight200 : (m200.take (251-200)).mapIdx (fun b x => toWeight (200+1) b x)=w201 := by decide +kernel
private theorem encoded200 : weightRow (200+1)=w201.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w202 := data.2[1]!
private theorem next201 : nextList 201 m200 m201=m202 := by decide +kernel
private theorem weight201 : (m201.take (251-201)).mapIdx (fun b x => toWeight (201+1) b x)=w202 := by decide +kernel
private theorem encoded201 : weightRow (201+1)=w202.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w203 := data.2[2]!
private theorem next202 : nextList 202 m201 m202=m203 := by decide +kernel
private theorem weight202 : (m202.take (251-202)).mapIdx (fun b x => toWeight (202+1) b x)=w203 := by decide +kernel
private theorem encoded202 : weightRow (202+1)=w203.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w204 := data.2[3]!
private theorem next203 : nextList 203 m202 m203=m204 := by decide +kernel
private theorem weight203 : (m203.take (251-203)).mapIdx (fun b x => toWeight (203+1) b x)=w204 := by decide +kernel
private theorem encoded203 : weightRow (203+1)=w204.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w205 := data.2[4]!
private theorem next204 : nextList 204 m203 m204=m205 := by decide +kernel
private theorem weight204 : (m204.take (251-204)).mapIdx (fun b x => toWeight (204+1) b x)=w205 := by decide +kernel
private theorem encoded204 : weightRow (204+1)=w205.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w206 := data.2[5]!
private theorem next205 : nextList 205 m204 m205=m206 := by decide +kernel
private theorem weight205 : (m205.take (251-205)).mapIdx (fun b x => toWeight (205+1) b x)=w206 := by decide +kernel
private theorem encoded205 : weightRow (205+1)=w206.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w207 := data.2[6]!
private theorem next206 : nextList 206 m205 m206=m207 := by decide +kernel
private theorem weight206 : (m206.take (251-206)).mapIdx (fun b x => toWeight (206+1) b x)=w207 := by decide +kernel
private theorem encoded206 : weightRow (206+1)=w207.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w208 := data.2[7]!
private theorem next207 : nextList 207 m206 m207=m208 := by decide +kernel
private theorem weight207 : (m207.take (251-207)).mapIdx (fun b x => toWeight (207+1) b x)=w208 := by decide +kernel
private theorem encoded207 : weightRow (207+1)=w208.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w209 := data.2[8]!
private theorem next208 : nextList 208 m207 m208=m209 := by decide +kernel
private theorem weight208 : (m208.take (251-208)).mapIdx (fun b x => toWeight (208+1) b x)=w209 := by decide +kernel
private theorem encoded208 : weightRow (208+1)=w209.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w210 := data.2[9]!
private theorem next209 : nextList 209 m208 m209=m210 := by decide +kernel
private theorem weight209 : (m209.take (251-209)).mapIdx (fun b x => toWeight (209+1) b x)=w210 := by decide +kernel
private theorem encoded209 : weightRow (209+1)=w210.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w211 := data.2[10]!
private theorem next210 : nextList 210 m209 m210=m211 := by decide +kernel
private theorem weight210 : (m210.take (251-210)).mapIdx (fun b x => toWeight (210+1) b x)=w211 := by decide +kernel
private theorem encoded210 : weightRow (210+1)=w211.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w212 := data.2[11]!
private theorem next211 : nextList 211 m210 m211=m212 := by decide +kernel
private theorem weight211 : (m211.take (251-211)).mapIdx (fun b x => toWeight (211+1) b x)=w212 := by decide +kernel
private theorem encoded211 : weightRow (211+1)=w212.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w213 := data.2[12]!
private theorem next212 : nextList 212 m211 m212=m213 := by decide +kernel
private theorem weight212 : (m212.take (251-212)).mapIdx (fun b x => toWeight (212+1) b x)=w213 := by decide +kernel
private theorem encoded212 : weightRow (212+1)=w213.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w214 := data.2[13]!
private theorem next213 : nextList 213 m212 m213=m214 := by decide +kernel
private theorem weight213 : (m213.take (251-213)).mapIdx (fun b x => toWeight (213+1) b x)=w214 := by decide +kernel
private theorem encoded213 : weightRow (213+1)=w214.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w215 := data.2[14]!
private theorem next214 : nextList 214 m213 m214=m215 := by decide +kernel
private theorem weight214 : (m214.take (251-214)).mapIdx (fun b x => toWeight (214+1) b x)=w215 := by decide +kernel
private theorem encoded214 : weightRow (214+1)=w215.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w216 := data.2[15]!
private theorem next215 : nextList 215 m214 m215=m216 := by decide +kernel
private theorem weight215 : (m215.take (251-215)).mapIdx (fun b x => toWeight (215+1) b x)=w216 := by decide +kernel
private theorem encoded215 : weightRow (215+1)=w216.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w217 := data.2[16]!
private theorem next216 : nextList 216 m215 m216=m217 := by decide +kernel
private theorem weight216 : (m216.take (251-216)).mapIdx (fun b x => toWeight (216+1) b x)=w217 := by decide +kernel
private theorem encoded216 : weightRow (216+1)=w217.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w218 := data.2[17]!
private theorem next217 : nextList 217 m216 m217=m218 := by decide +kernel
private theorem weight217 : (m217.take (251-217)).mapIdx (fun b x => toWeight (217+1) b x)=w218 := by decide +kernel
private theorem encoded217 : weightRow (217+1)=w218.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w219 := data.2[18]!
private theorem next218 : nextList 218 m217 m218=m219 := by decide +kernel
private theorem weight218 : (m218.take (251-218)).mapIdx (fun b x => toWeight (218+1) b x)=w219 := by decide +kernel
private theorem encoded218 : weightRow (218+1)=w219.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w220 := data.2[19]!
private theorem next219 : nextList 219 m218 m219=m220 := by decide +kernel
private theorem weight219 : (m219.take (251-219)).mapIdx (fun b x => toWeight (219+1) b x)=w220 := by decide +kernel
private theorem encoded219 : weightRow (219+1)=w220.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w221 := data.2[20]!
private theorem next220 : nextList 220 m219 m220=m221 := by decide +kernel
private theorem weight220 : (m220.take (251-220)).mapIdx (fun b x => toWeight (220+1) b x)=w221 := by decide +kernel
private theorem encoded220 : weightRow (220+1)=w221.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w222 := data.2[21]!
private theorem next221 : nextList 221 m220 m221=m222 := by decide +kernel
private theorem weight221 : (m221.take (251-221)).mapIdx (fun b x => toWeight (221+1) b x)=w222 := by decide +kernel
private theorem encoded221 : weightRow (221+1)=w222.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w223 := data.2[22]!
private theorem next222 : nextList 222 m221 m222=m223 := by decide +kernel
private theorem weight222 : (m222.take (251-222)).mapIdx (fun b x => toWeight (222+1) b x)=w223 := by decide +kernel
private theorem encoded222 : weightRow (222+1)=w223.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w224 := data.2[23]!
private theorem next223 : nextList 223 m222 m223=m224 := by decide +kernel
private theorem weight223 : (m223.take (251-223)).mapIdx (fun b x => toWeight (223+1) b x)=w224 := by decide +kernel
private theorem encoded223 : weightRow (223+1)=w224.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w225 := data.2[24]!
private theorem next224 : nextList 224 m223 m224=m225 := by decide +kernel
private theorem weight224 : (m224.take (251-224)).mapIdx (fun b x => toWeight (224+1) b x)=w225 := by decide +kernel
private theorem encoded224 : weightRow (224+1)=w225.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w226 := data.2[25]!
private theorem next225 : nextList 225 m224 m225=m226 := by decide +kernel
private theorem weight225 : (m225.take (251-225)).mapIdx (fun b x => toWeight (225+1) b x)=w226 := by decide +kernel
private theorem encoded225 : weightRow (225+1)=w226.toArray := encoded (by decide +kernel) (by decide +kernel)
end HermiteBlock

open HermiteBlock
theorem solution : ∀ ini : Array MomentCombination,
      grid 251 ini 200 = state 14 →
      grid 251 ini 226 = state 15 := by
  intro ini h
  have prev14 : (pair 14).1=m199 := by decide +kernel
  have cur14 : (pair 14).2=m200 := by decide +kernel
  have prev15 : (pair 15).1=m225 := by decide +kernel
  have cur15 : (pair 15).2=m226 := by decide +kernel
  rw [state,prev14,cur14] at h
  change grid 251 ini 200=⟨m199.toArray,m200.toArray,tab (200+1) weightRow⟩ at h
  have s201 := advance h (by decide +kernel) (by decide +kernel) next200 weight200 encoded200
  have s202 := advance s201 (by decide +kernel) (by decide +kernel) next201 weight201 encoded201
  have s203 := advance s202 (by decide +kernel) (by decide +kernel) next202 weight202 encoded202
  have s204 := advance s203 (by decide +kernel) (by decide +kernel) next203 weight203 encoded203
  have s205 := advance s204 (by decide +kernel) (by decide +kernel) next204 weight204 encoded204
  have s206 := advance s205 (by decide +kernel) (by decide +kernel) next205 weight205 encoded205
  have s207 := advance s206 (by decide +kernel) (by decide +kernel) next206 weight206 encoded206
  have s208 := advance s207 (by decide +kernel) (by decide +kernel) next207 weight207 encoded207
  have s209 := advance s208 (by decide +kernel) (by decide +kernel) next208 weight208 encoded208
  have s210 := advance s209 (by decide +kernel) (by decide +kernel) next209 weight209 encoded209
  have s211 := advance s210 (by decide +kernel) (by decide +kernel) next210 weight210 encoded210
  have s212 := advance s211 (by decide +kernel) (by decide +kernel) next211 weight211 encoded211
  have s213 := advance s212 (by decide +kernel) (by decide +kernel) next212 weight212 encoded212
  have s214 := advance s213 (by decide +kernel) (by decide +kernel) next213 weight213 encoded213
  have s215 := advance s214 (by decide +kernel) (by decide +kernel) next214 weight214 encoded214
  have s216 := advance s215 (by decide +kernel) (by decide +kernel) next215 weight215 encoded215
  have s217 := advance s216 (by decide +kernel) (by decide +kernel) next216 weight216 encoded216
  have s218 := advance s217 (by decide +kernel) (by decide +kernel) next217 weight217 encoded217
  have s219 := advance s218 (by decide +kernel) (by decide +kernel) next218 weight218 encoded218
  have s220 := advance s219 (by decide +kernel) (by decide +kernel) next219 weight219 encoded219
  have s221 := advance s220 (by decide +kernel) (by decide +kernel) next220 weight220 encoded220
  have s222 := advance s221 (by decide +kernel) (by decide +kernel) next221 weight221 encoded221
  have s223 := advance s222 (by decide +kernel) (by decide +kernel) next222 weight222 encoded222
  have s224 := advance s223 (by decide +kernel) (by decide +kernel) next223 weight223 encoded223
  have s225 := advance s224 (by decide +kernel) (by decide +kernel) next224 weight224 encoded224
  have s226 := advance s225 (by decide +kernel) (by decide +kernel) next225 weight225 encoded225
  rw [state,prev15,cur15]
  exact s226
