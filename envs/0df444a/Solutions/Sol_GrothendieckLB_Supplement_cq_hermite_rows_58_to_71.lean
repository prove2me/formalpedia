-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_hermite_rows_58_to_71
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:25:01.119583+00:00
-- url     : https://prove2.me/submissions/5db20430-b20b-47e3-ac01-48b3d638a1ad

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
private noncomputable def data := eval% (sampleBlock 58 13)
private noncomputable def m57 := data.1[0]!
private noncomputable def m58 := data.1[1]!
private noncomputable def m59 := data.1[2]!
private noncomputable def m60 := data.1[3]!
private noncomputable def m61 := data.1[4]!
private noncomputable def m62 := data.1[5]!
private noncomputable def m63 := data.1[6]!
private noncomputable def m64 := data.1[7]!
private noncomputable def m65 := data.1[8]!
private noncomputable def m66 := data.1[9]!
private noncomputable def m67 := data.1[10]!
private noncomputable def m68 := data.1[11]!
private noncomputable def m69 := data.1[12]!
private noncomputable def m70 := data.1[13]!
private noncomputable def m71 := data.1[14]!
private noncomputable def w59 := data.2[0]!
private theorem next58 : nextList 58 m57 m58=m59 := by decide +kernel
private theorem weight58 : (m58.take (251-58)).mapIdx (fun b x => toWeight (58+1) b x)=w59 := by decide +kernel
private theorem encoded58 : weightRow (58+1)=w59.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w60 := data.2[1]!
private theorem next59 : nextList 59 m58 m59=m60 := by decide +kernel
private theorem weight59 : (m59.take (251-59)).mapIdx (fun b x => toWeight (59+1) b x)=w60 := by decide +kernel
private theorem encoded59 : weightRow (59+1)=w60.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w61 := data.2[2]!
private theorem next60 : nextList 60 m59 m60=m61 := by decide +kernel
private theorem weight60 : (m60.take (251-60)).mapIdx (fun b x => toWeight (60+1) b x)=w61 := by decide +kernel
private theorem encoded60 : weightRow (60+1)=w61.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w62 := data.2[3]!
private theorem next61 : nextList 61 m60 m61=m62 := by decide +kernel
private theorem weight61 : (m61.take (251-61)).mapIdx (fun b x => toWeight (61+1) b x)=w62 := by decide +kernel
private theorem encoded61 : weightRow (61+1)=w62.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w63 := data.2[4]!
private theorem next62 : nextList 62 m61 m62=m63 := by decide +kernel
private theorem weight62 : (m62.take (251-62)).mapIdx (fun b x => toWeight (62+1) b x)=w63 := by decide +kernel
private theorem encoded62 : weightRow (62+1)=w63.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w64 := data.2[5]!
private theorem next63 : nextList 63 m62 m63=m64 := by decide +kernel
private theorem weight63 : (m63.take (251-63)).mapIdx (fun b x => toWeight (63+1) b x)=w64 := by decide +kernel
private theorem encoded63 : weightRow (63+1)=w64.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w65 := data.2[6]!
private theorem next64 : nextList 64 m63 m64=m65 := by decide +kernel
private theorem weight64 : (m64.take (251-64)).mapIdx (fun b x => toWeight (64+1) b x)=w65 := by decide +kernel
private theorem encoded64 : weightRow (64+1)=w65.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w66 := data.2[7]!
private theorem next65 : nextList 65 m64 m65=m66 := by decide +kernel
private theorem weight65 : (m65.take (251-65)).mapIdx (fun b x => toWeight (65+1) b x)=w66 := by decide +kernel
private theorem encoded65 : weightRow (65+1)=w66.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w67 := data.2[8]!
private theorem next66 : nextList 66 m65 m66=m67 := by decide +kernel
private theorem weight66 : (m66.take (251-66)).mapIdx (fun b x => toWeight (66+1) b x)=w67 := by decide +kernel
private theorem encoded66 : weightRow (66+1)=w67.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w68 := data.2[9]!
private theorem next67 : nextList 67 m66 m67=m68 := by decide +kernel
private theorem weight67 : (m67.take (251-67)).mapIdx (fun b x => toWeight (67+1) b x)=w68 := by decide +kernel
private theorem encoded67 : weightRow (67+1)=w68.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w69 := data.2[10]!
private theorem next68 : nextList 68 m67 m68=m69 := by decide +kernel
private theorem weight68 : (m68.take (251-68)).mapIdx (fun b x => toWeight (68+1) b x)=w69 := by decide +kernel
private theorem encoded68 : weightRow (68+1)=w69.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w70 := data.2[11]!
private theorem next69 : nextList 69 m68 m69=m70 := by decide +kernel
private theorem weight69 : (m69.take (251-69)).mapIdx (fun b x => toWeight (69+1) b x)=w70 := by decide +kernel
private theorem encoded69 : weightRow (69+1)=w70.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w71 := data.2[12]!
private theorem next70 : nextList 70 m69 m70=m71 := by decide +kernel
private theorem weight70 : (m70.take (251-70)).mapIdx (fun b x => toWeight (70+1) b x)=w71 := by decide +kernel
private theorem encoded70 : weightRow (70+1)=w71.toArray := encoded (by decide +kernel) (by decide +kernel)
end HermiteBlock

open HermiteBlock
theorem solution : ∀ ini : Array MomentCombination,
      grid 251 ini 58 = state 6 →
      grid 251 ini 71 = state 7 := by
  intro ini h
  have prev6 : (pair 6).1=m57 := by decide +kernel
  have cur6 : (pair 6).2=m58 := by decide +kernel
  have prev7 : (pair 7).1=m70 := by decide +kernel
  have cur7 : (pair 7).2=m71 := by decide +kernel
  rw [state,prev6,cur6] at h
  change grid 251 ini 58=⟨m57.toArray,m58.toArray,tab (58+1) weightRow⟩ at h
  have s59 := advance h (by decide +kernel) (by decide +kernel) next58 weight58 encoded58
  have s60 := advance s59 (by decide +kernel) (by decide +kernel) next59 weight59 encoded59
  have s61 := advance s60 (by decide +kernel) (by decide +kernel) next60 weight60 encoded60
  have s62 := advance s61 (by decide +kernel) (by decide +kernel) next61 weight61 encoded61
  have s63 := advance s62 (by decide +kernel) (by decide +kernel) next62 weight62 encoded62
  have s64 := advance s63 (by decide +kernel) (by decide +kernel) next63 weight63 encoded63
  have s65 := advance s64 (by decide +kernel) (by decide +kernel) next64 weight64 encoded64
  have s66 := advance s65 (by decide +kernel) (by decide +kernel) next65 weight65 encoded65
  have s67 := advance s66 (by decide +kernel) (by decide +kernel) next66 weight66 encoded66
  have s68 := advance s67 (by decide +kernel) (by decide +kernel) next67 weight67 encoded67
  have s69 := advance s68 (by decide +kernel) (by decide +kernel) next68 weight68 encoded68
  have s70 := advance s69 (by decide +kernel) (by decide +kernel) next69 weight69 encoded69
  have s71 := advance s70 (by decide +kernel) (by decide +kernel) next70 weight70 encoded70
  rw [state,prev7,cur7]
  exact s71
