-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_hermite_rows_71_to_85
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:25:02.907466+00:00
-- url     : https://prove2.me/submissions/50366ecf-d4c1-4a13-8916-ddd96a14831f

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
private noncomputable def data := eval% (sampleBlock 71 14)
private noncomputable def m70 := data.1[0]!
private noncomputable def m71 := data.1[1]!
private noncomputable def m72 := data.1[2]!
private noncomputable def m73 := data.1[3]!
private noncomputable def m74 := data.1[4]!
private noncomputable def m75 := data.1[5]!
private noncomputable def m76 := data.1[6]!
private noncomputable def m77 := data.1[7]!
private noncomputable def m78 := data.1[8]!
private noncomputable def m79 := data.1[9]!
private noncomputable def m80 := data.1[10]!
private noncomputable def m81 := data.1[11]!
private noncomputable def m82 := data.1[12]!
private noncomputable def m83 := data.1[13]!
private noncomputable def m84 := data.1[14]!
private noncomputable def m85 := data.1[15]!
private noncomputable def w72 := data.2[0]!
private theorem next71 : nextList 71 m70 m71=m72 := by decide +kernel
private theorem weight71 : (m71.take (251-71)).mapIdx (fun b x => toWeight (71+1) b x)=w72 := by decide +kernel
private theorem encoded71 : weightRow (71+1)=w72.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w73 := data.2[1]!
private theorem next72 : nextList 72 m71 m72=m73 := by decide +kernel
private theorem weight72 : (m72.take (251-72)).mapIdx (fun b x => toWeight (72+1) b x)=w73 := by decide +kernel
private theorem encoded72 : weightRow (72+1)=w73.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w74 := data.2[2]!
private theorem next73 : nextList 73 m72 m73=m74 := by decide +kernel
private theorem weight73 : (m73.take (251-73)).mapIdx (fun b x => toWeight (73+1) b x)=w74 := by decide +kernel
private theorem encoded73 : weightRow (73+1)=w74.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w75 := data.2[3]!
private theorem next74 : nextList 74 m73 m74=m75 := by decide +kernel
private theorem weight74 : (m74.take (251-74)).mapIdx (fun b x => toWeight (74+1) b x)=w75 := by decide +kernel
private theorem encoded74 : weightRow (74+1)=w75.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w76 := data.2[4]!
private theorem next75 : nextList 75 m74 m75=m76 := by decide +kernel
private theorem weight75 : (m75.take (251-75)).mapIdx (fun b x => toWeight (75+1) b x)=w76 := by decide +kernel
private theorem encoded75 : weightRow (75+1)=w76.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w77 := data.2[5]!
private theorem next76 : nextList 76 m75 m76=m77 := by decide +kernel
private theorem weight76 : (m76.take (251-76)).mapIdx (fun b x => toWeight (76+1) b x)=w77 := by decide +kernel
private theorem encoded76 : weightRow (76+1)=w77.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w78 := data.2[6]!
private theorem next77 : nextList 77 m76 m77=m78 := by decide +kernel
private theorem weight77 : (m77.take (251-77)).mapIdx (fun b x => toWeight (77+1) b x)=w78 := by decide +kernel
private theorem encoded77 : weightRow (77+1)=w78.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w79 := data.2[7]!
private theorem next78 : nextList 78 m77 m78=m79 := by decide +kernel
private theorem weight78 : (m78.take (251-78)).mapIdx (fun b x => toWeight (78+1) b x)=w79 := by decide +kernel
private theorem encoded78 : weightRow (78+1)=w79.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w80 := data.2[8]!
private theorem next79 : nextList 79 m78 m79=m80 := by decide +kernel
private theorem weight79 : (m79.take (251-79)).mapIdx (fun b x => toWeight (79+1) b x)=w80 := by decide +kernel
private theorem encoded79 : weightRow (79+1)=w80.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w81 := data.2[9]!
private theorem next80 : nextList 80 m79 m80=m81 := by decide +kernel
private theorem weight80 : (m80.take (251-80)).mapIdx (fun b x => toWeight (80+1) b x)=w81 := by decide +kernel
private theorem encoded80 : weightRow (80+1)=w81.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w82 := data.2[10]!
private theorem next81 : nextList 81 m80 m81=m82 := by decide +kernel
private theorem weight81 : (m81.take (251-81)).mapIdx (fun b x => toWeight (81+1) b x)=w82 := by decide +kernel
private theorem encoded81 : weightRow (81+1)=w82.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w83 := data.2[11]!
private theorem next82 : nextList 82 m81 m82=m83 := by decide +kernel
private theorem weight82 : (m82.take (251-82)).mapIdx (fun b x => toWeight (82+1) b x)=w83 := by decide +kernel
private theorem encoded82 : weightRow (82+1)=w83.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w84 := data.2[12]!
private theorem next83 : nextList 83 m82 m83=m84 := by decide +kernel
private theorem weight83 : (m83.take (251-83)).mapIdx (fun b x => toWeight (83+1) b x)=w84 := by decide +kernel
private theorem encoded83 : weightRow (83+1)=w84.toArray := encoded (by decide +kernel) (by decide +kernel)
private noncomputable def w85 := data.2[13]!
private theorem next84 : nextList 84 m83 m84=m85 := by decide +kernel
private theorem weight84 : (m84.take (251-84)).mapIdx (fun b x => toWeight (84+1) b x)=w85 := by decide +kernel
private theorem encoded84 : weightRow (84+1)=w85.toArray := encoded (by decide +kernel) (by decide +kernel)
end HermiteBlock

open HermiteBlock
theorem solution : ∀ ini : Array MomentCombination,
      grid 251 ini 71 = state 7 →
      grid 251 ini 85 = state 8 := by
  intro ini h
  have prev7 : (pair 7).1=m70 := by decide +kernel
  have cur7 : (pair 7).2=m71 := by decide +kernel
  have prev8 : (pair 8).1=m84 := by decide +kernel
  have cur8 : (pair 8).2=m85 := by decide +kernel
  rw [state,prev7,cur7] at h
  change grid 251 ini 71=⟨m70.toArray,m71.toArray,tab (71+1) weightRow⟩ at h
  have s72 := advance h (by decide +kernel) (by decide +kernel) next71 weight71 encoded71
  have s73 := advance s72 (by decide +kernel) (by decide +kernel) next72 weight72 encoded72
  have s74 := advance s73 (by decide +kernel) (by decide +kernel) next73 weight73 encoded73
  have s75 := advance s74 (by decide +kernel) (by decide +kernel) next74 weight74 encoded74
  have s76 := advance s75 (by decide +kernel) (by decide +kernel) next75 weight75 encoded75
  have s77 := advance s76 (by decide +kernel) (by decide +kernel) next76 weight76 encoded76
  have s78 := advance s77 (by decide +kernel) (by decide +kernel) next77 weight77 encoded77
  have s79 := advance s78 (by decide +kernel) (by decide +kernel) next78 weight78 encoded78
  have s80 := advance s79 (by decide +kernel) (by decide +kernel) next79 weight79 encoded79
  have s81 := advance s80 (by decide +kernel) (by decide +kernel) next80 weight80 encoded80
  have s82 := advance s81 (by decide +kernel) (by decide +kernel) next81 weight81 encoded81
  have s83 := advance s82 (by decide +kernel) (by decide +kernel) next82 weight82 encoded82
  have s84 := advance s83 (by decide +kernel) (by decide +kernel) next83 weight83 encoded83
  have s85 := advance s84 (by decide +kernel) (by decide +kernel) next84 weight84 encoded84
  rw [state,prev8,cur8]
  exact s85
