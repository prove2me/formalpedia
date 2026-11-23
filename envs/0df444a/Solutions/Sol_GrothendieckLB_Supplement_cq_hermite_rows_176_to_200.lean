-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_hermite_rows_176_to_200
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:14:54.506307+00:00
-- url     : https://prove2.me/submissions/d6fccc81-df01-4aa2-b993-907ee6db76ba

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
private noncomputable def data := eval% (sampleBlock 176 24)
private noncomputable def m175 := data.1[0]!
private noncomputable def m176 := data.1[1]!
private noncomputable def m177 := data.1[2]!
private noncomputable def m178 := data.1[3]!
private noncomputable def m179 := data.1[4]!
private noncomputable def m180 := data.1[5]!
private noncomputable def m181 := data.1[6]!
private noncomputable def m182 := data.1[7]!
private noncomputable def m183 := data.1[8]!
private noncomputable def m184 := data.1[9]!
private noncomputable def m185 := data.1[10]!
private noncomputable def m186 := data.1[11]!
private noncomputable def m187 := data.1[12]!
private noncomputable def m188 := data.1[13]!
private noncomputable def m189 := data.1[14]!
private noncomputable def m190 := data.1[15]!
private noncomputable def m191 := data.1[16]!
private noncomputable def m192 := data.1[17]!
private noncomputable def m193 := data.1[18]!
private noncomputable def m194 := data.1[19]!
private noncomputable def m195 := data.1[20]!
private noncomputable def m196 := data.1[21]!
private noncomputable def m197 := data.1[22]!
private noncomputable def m198 := data.1[23]!
private noncomputable def m199 := data.1[24]!
private noncomputable def m200 := data.1[25]!
private noncomputable def w177 := data.2[0]!
private theorem next176 : nextList 176 m175 m176=m177 := by decide +kernel
private theorem weight176 : (m176.take (251-176)).mapIdx (fun b x => toWeight (176+1) b x)=w177 := by decide +kernel
private theorem encoded176 : weightRow (176+1)=w177.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w178 := data.2[1]!
private theorem next177 : nextList 177 m176 m177=m178 := by decide +kernel
private theorem weight177 : (m177.take (251-177)).mapIdx (fun b x => toWeight (177+1) b x)=w178 := by decide +kernel
private theorem encoded177 : weightRow (177+1)=w178.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w179 := data.2[2]!
private theorem next178 : nextList 178 m177 m178=m179 := by decide +kernel
private theorem weight178 : (m178.take (251-178)).mapIdx (fun b x => toWeight (178+1) b x)=w179 := by decide +kernel
private theorem encoded178 : weightRow (178+1)=w179.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w180 := data.2[3]!
private theorem next179 : nextList 179 m178 m179=m180 := by decide +kernel
private theorem weight179 : (m179.take (251-179)).mapIdx (fun b x => toWeight (179+1) b x)=w180 := by decide +kernel
private theorem encoded179 : weightRow (179+1)=w180.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w181 := data.2[4]!
private theorem next180 : nextList 180 m179 m180=m181 := by decide +kernel
private theorem weight180 : (m180.take (251-180)).mapIdx (fun b x => toWeight (180+1) b x)=w181 := by decide +kernel
private theorem encoded180 : weightRow (180+1)=w181.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w182 := data.2[5]!
private theorem next181 : nextList 181 m180 m181=m182 := by decide +kernel
private theorem weight181 : (m181.take (251-181)).mapIdx (fun b x => toWeight (181+1) b x)=w182 := by decide +kernel
private theorem encoded181 : weightRow (181+1)=w182.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w183 := data.2[6]!
private theorem next182 : nextList 182 m181 m182=m183 := by decide +kernel
private theorem weight182 : (m182.take (251-182)).mapIdx (fun b x => toWeight (182+1) b x)=w183 := by decide +kernel
private theorem encoded182 : weightRow (182+1)=w183.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w184 := data.2[7]!
private theorem next183 : nextList 183 m182 m183=m184 := by decide +kernel
private theorem weight183 : (m183.take (251-183)).mapIdx (fun b x => toWeight (183+1) b x)=w184 := by decide +kernel
private theorem encoded183 : weightRow (183+1)=w184.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w185 := data.2[8]!
private theorem next184 : nextList 184 m183 m184=m185 := by decide +kernel
private theorem weight184 : (m184.take (251-184)).mapIdx (fun b x => toWeight (184+1) b x)=w185 := by decide +kernel
private theorem encoded184 : weightRow (184+1)=w185.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w186 := data.2[9]!
private theorem next185 : nextList 185 m184 m185=m186 := by decide +kernel
private theorem weight185 : (m185.take (251-185)).mapIdx (fun b x => toWeight (185+1) b x)=w186 := by decide +kernel
private theorem encoded185 : weightRow (185+1)=w186.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w187 := data.2[10]!
private theorem next186 : nextList 186 m185 m186=m187 := by decide +kernel
private theorem weight186 : (m186.take (251-186)).mapIdx (fun b x => toWeight (186+1) b x)=w187 := by decide +kernel
private theorem encoded186 : weightRow (186+1)=w187.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w188 := data.2[11]!
private theorem next187 : nextList 187 m186 m187=m188 := by decide +kernel
private theorem weight187 : (m187.take (251-187)).mapIdx (fun b x => toWeight (187+1) b x)=w188 := by decide +kernel
private theorem encoded187 : weightRow (187+1)=w188.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w189 := data.2[12]!
private theorem next188 : nextList 188 m187 m188=m189 := by decide +kernel
private theorem weight188 : (m188.take (251-188)).mapIdx (fun b x => toWeight (188+1) b x)=w189 := by decide +kernel
private theorem encoded188 : weightRow (188+1)=w189.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w190 := data.2[13]!
private theorem next189 : nextList 189 m188 m189=m190 := by decide +kernel
private theorem weight189 : (m189.take (251-189)).mapIdx (fun b x => toWeight (189+1) b x)=w190 := by decide +kernel
private theorem encoded189 : weightRow (189+1)=w190.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w191 := data.2[14]!
private theorem next190 : nextList 190 m189 m190=m191 := by decide +kernel
private theorem weight190 : (m190.take (251-190)).mapIdx (fun b x => toWeight (190+1) b x)=w191 := by decide +kernel
private theorem encoded190 : weightRow (190+1)=w191.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w192 := data.2[15]!
private theorem next191 : nextList 191 m190 m191=m192 := by decide +kernel
private theorem weight191 : (m191.take (251-191)).mapIdx (fun b x => toWeight (191+1) b x)=w192 := by decide +kernel
private theorem encoded191 : weightRow (191+1)=w192.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w193 := data.2[16]!
private theorem next192 : nextList 192 m191 m192=m193 := by decide +kernel
private theorem weight192 : (m192.take (251-192)).mapIdx (fun b x => toWeight (192+1) b x)=w193 := by decide +kernel
private theorem encoded192 : weightRow (192+1)=w193.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w194 := data.2[17]!
private theorem next193 : nextList 193 m192 m193=m194 := by decide +kernel
private theorem weight193 : (m193.take (251-193)).mapIdx (fun b x => toWeight (193+1) b x)=w194 := by decide +kernel
private theorem encoded193 : weightRow (193+1)=w194.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w195 := data.2[18]!
private theorem next194 : nextList 194 m193 m194=m195 := by decide +kernel
private theorem weight194 : (m194.take (251-194)).mapIdx (fun b x => toWeight (194+1) b x)=w195 := by decide +kernel
private theorem encoded194 : weightRow (194+1)=w195.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w196 := data.2[19]!
private theorem next195 : nextList 195 m194 m195=m196 := by decide +kernel
private theorem weight195 : (m195.take (251-195)).mapIdx (fun b x => toWeight (195+1) b x)=w196 := by decide +kernel
private theorem encoded195 : weightRow (195+1)=w196.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w197 := data.2[20]!
private theorem next196 : nextList 196 m195 m196=m197 := by decide +kernel
private theorem weight196 : (m196.take (251-196)).mapIdx (fun b x => toWeight (196+1) b x)=w197 := by decide +kernel
private theorem encoded196 : weightRow (196+1)=w197.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w198 := data.2[21]!
private theorem next197 : nextList 197 m196 m197=m198 := by decide +kernel
private theorem weight197 : (m197.take (251-197)).mapIdx (fun b x => toWeight (197+1) b x)=w198 := by decide +kernel
private theorem encoded197 : weightRow (197+1)=w198.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w199 := data.2[22]!
private theorem next198 : nextList 198 m197 m198=m199 := by decide +kernel
private theorem weight198 : (m198.take (251-198)).mapIdx (fun b x => toWeight (198+1) b x)=w199 := by decide +kernel
private theorem encoded198 : weightRow (198+1)=w199.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w200 := data.2[23]!
private theorem next199 : nextList 199 m198 m199=m200 := by decide +kernel
private theorem weight199 : (m199.take (251-199)).mapIdx (fun b x => toWeight (199+1) b x)=w200 := by decide +kernel
private theorem encoded199 : weightRow (199+1)=w200.toArray := encoded (by decide +kernel) (by decide +kernel)
end HermiteBlock

open HermiteBlock
theorem solution : ∀ ini : Array MomentCombination,
      grid 251 ini 176 = state 13 →
      grid 251 ini 200 = state 14 := by
  intro ini h
  have prev13 : (pair 13).1=m175 := by decide +kernel
  have cur13 : (pair 13).2=m176 := by decide +kernel
  have prev14 : (pair 14).1=m199 := by decide +kernel
  have cur14 : (pair 14).2=m200 := by decide +kernel
  rw [state,prev13,cur13] at h
  change grid 251 ini 176=⟨m175.toArray,m176.toArray,tab (176+1) weightRow⟩ at h
  have s177 := advance h (by decide +kernel) (by decide +kernel) next176 weight176 encoded176
  have s178 := advance s177 (by decide +kernel) (by decide +kernel) next177 weight177 encoded177
  have s179 := advance s178 (by decide +kernel) (by decide +kernel) next178 weight178 encoded178
  have s180 := advance s179 (by decide +kernel) (by decide +kernel) next179 weight179 encoded179
  have s181 := advance s180 (by decide +kernel) (by decide +kernel) next180 weight180 encoded180
  have s182 := advance s181 (by decide +kernel) (by decide +kernel) next181 weight181 encoded181
  have s183 := advance s182 (by decide +kernel) (by decide +kernel) next182 weight182 encoded182
  have s184 := advance s183 (by decide +kernel) (by decide +kernel) next183 weight183 encoded183
  have s185 := advance s184 (by decide +kernel) (by decide +kernel) next184 weight184 encoded184
  have s186 := advance s185 (by decide +kernel) (by decide +kernel) next185 weight185 encoded185
  have s187 := advance s186 (by decide +kernel) (by decide +kernel) next186 weight186 encoded186
  have s188 := advance s187 (by decide +kernel) (by decide +kernel) next187 weight187 encoded187
  have s189 := advance s188 (by decide +kernel) (by decide +kernel) next188 weight188 encoded188
  have s190 := advance s189 (by decide +kernel) (by decide +kernel) next189 weight189 encoded189
  have s191 := advance s190 (by decide +kernel) (by decide +kernel) next190 weight190 encoded190
  have s192 := advance s191 (by decide +kernel) (by decide +kernel) next191 weight191 encoded191
  have s193 := advance s192 (by decide +kernel) (by decide +kernel) next192 weight192 encoded192
  have s194 := advance s193 (by decide +kernel) (by decide +kernel) next193 weight193 encoded193
  have s195 := advance s194 (by decide +kernel) (by decide +kernel) next194 weight194 encoded194
  have s196 := advance s195 (by decide +kernel) (by decide +kernel) next195 weight195 encoded195
  have s197 := advance s196 (by decide +kernel) (by decide +kernel) next196 weight196 encoded196
  have s198 := advance s197 (by decide +kernel) (by decide +kernel) next197 weight197 encoded197
  have s199 := advance s198 (by decide +kernel) (by decide +kernel) next198 weight198 encoded198
  have s200 := advance s199 (by decide +kernel) (by decide +kernel) next199 weight199 encoded199
  rw [state,prev14,cur14]
  exact s200
