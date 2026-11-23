-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_degree51_hermite_weights
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:03:54.996736+00:00
-- url     : https://prove2.me/submissions/bdb788fb-1afa-442b-aa58-5ddc890febf5

import Definitions.Def_GrothendieckLB_Supplement_cqDegree51Tables
import Mathlib.Tactic.Eval
import Lean

open GrothendieckLB.Supplement.CQHeadArithmetic
set_option autoImplicit false
set_option maxRecDepth 250000
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 50000
set_option Elab.async false

/- The candidate tables contain only integer data. Each use of a candidate in the
   proof is justified separately by reduction of a closed equality in the kernel. -/
namespace CubicQuinticIntegerData
open Lean
deriving instance ToExpr for Interval
deriving instance ToExpr for MomentCombination
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

private def candidateRows (N lo len : Nat) : List (List MomentCombination) := Id.run do
  let raw := momentRows (3*N-5)
  let mut prev := initFast N raw
  let mut cur := prev
  let mut rows := #[]
  for p in [:lo+len] do
    if lo ≤ p then rows := rows.push cur.toList
    let next := nextRow p prev cur
    prev := cur
    cur := next
  return rows.toList

end CubicQuinticIntegerData
open CubicQuinticIntegerData
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
open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadArithmetic CQStream CQRowProof
set_option maxRecDepth 250000
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 50000
set_option Elab.async false
private theorem gridSeed {n : Nat} {x w} {ini : Array MomentCombination}
    (h : ini=x) (hw : zeroWeights n x=w) : grid n ini 0 = ⟨x,x,#[w]⟩ := by
  subst ini; simp [grid,hw]
private theorem gridStep {n p : Nat} {ini prev cur next ws w}
    (h : grid n ini p=⟨prev,cur,ws⟩)
    (hn : nextRow p prev cur=next)
    (hw : tab (n-p) (fun b => toWeight (p+1) b (entry zeroCombination cur b))=w) :
    grid n ini (p+1)=⟨cur,next,ws.push w⟩ := by
  simp only [grid,h,hn,hw]
private noncomputable def data0 : List (List MomentCombination) :=
  eval% (candidateRows 51 0 8)
private noncomputable def v0 : List MomentCombination := data0[0]!
private noncomputable def ws0 := #[GrothendieckLB.Supplement.CQDegree51.w0.toArray]
private noncomputable def v1 : List MomentCombination := data0[1]!
private noncomputable def ws1 := ws0.push GrothendieckLB.Supplement.CQDegree51.w1.toArray
private noncomputable def v2 : List MomentCombination := data0[2]!
private noncomputable def ws2 := ws1.push GrothendieckLB.Supplement.CQDegree51.w2.toArray
private noncomputable def v3 : List MomentCombination := data0[3]!
private noncomputable def ws3 := ws2.push GrothendieckLB.Supplement.CQDegree51.w3.toArray
private noncomputable def v4 : List MomentCombination := data0[4]!
private noncomputable def ws4 := ws3.push GrothendieckLB.Supplement.CQDegree51.w4.toArray
private noncomputable def v5 : List MomentCombination := data0[5]!
private noncomputable def ws5 := ws4.push GrothendieckLB.Supplement.CQDegree51.w5.toArray
private noncomputable def v6 : List MomentCombination := data0[6]!
private noncomputable def ws6 := ws5.push GrothendieckLB.Supplement.CQDegree51.w6.toArray
private noncomputable def v7 : List MomentCombination := data0[7]!
private noncomputable def ws7 := ws6.push GrothendieckLB.Supplement.CQDegree51.w7.toArray
private noncomputable def data8 : List (List MomentCombination) :=
  eval% (candidateRows 51 8 8)
private noncomputable def v8 : List MomentCombination := data8[0]!
private noncomputable def ws8 := ws7.push GrothendieckLB.Supplement.CQDegree51.w8.toArray
private noncomputable def v9 : List MomentCombination := data8[1]!
private noncomputable def ws9 := ws8.push GrothendieckLB.Supplement.CQDegree51.w9.toArray
private noncomputable def v10 : List MomentCombination := data8[2]!
private noncomputable def ws10 := ws9.push GrothendieckLB.Supplement.CQDegree51.w10.toArray
private noncomputable def v11 : List MomentCombination := data8[3]!
private noncomputable def ws11 := ws10.push GrothendieckLB.Supplement.CQDegree51.w11.toArray
private noncomputable def v12 : List MomentCombination := data8[4]!
private noncomputable def ws12 := ws11.push GrothendieckLB.Supplement.CQDegree51.w12.toArray
private noncomputable def v13 : List MomentCombination := data8[5]!
private noncomputable def ws13 := ws12.push GrothendieckLB.Supplement.CQDegree51.w13.toArray
private noncomputable def v14 : List MomentCombination := data8[6]!
private noncomputable def ws14 := ws13.push GrothendieckLB.Supplement.CQDegree51.w14.toArray
private noncomputable def v15 : List MomentCombination := data8[7]!
private noncomputable def ws15 := ws14.push GrothendieckLB.Supplement.CQDegree51.w15.toArray
private noncomputable def data16 : List (List MomentCombination) :=
  eval% (candidateRows 51 16 8)
private noncomputable def v16 : List MomentCombination := data16[0]!
private noncomputable def ws16 := ws15.push GrothendieckLB.Supplement.CQDegree51.w16.toArray
private noncomputable def v17 : List MomentCombination := data16[1]!
private noncomputable def ws17 := ws16.push GrothendieckLB.Supplement.CQDegree51.w17.toArray
private noncomputable def v18 : List MomentCombination := data16[2]!
private noncomputable def ws18 := ws17.push GrothendieckLB.Supplement.CQDegree51.w18.toArray
private noncomputable def v19 : List MomentCombination := data16[3]!
private noncomputable def ws19 := ws18.push GrothendieckLB.Supplement.CQDegree51.w19.toArray
private noncomputable def v20 : List MomentCombination := data16[4]!
private noncomputable def ws20 := ws19.push GrothendieckLB.Supplement.CQDegree51.w20.toArray
private noncomputable def v21 : List MomentCombination := data16[5]!
private noncomputable def ws21 := ws20.push GrothendieckLB.Supplement.CQDegree51.w21.toArray
private noncomputable def v22 : List MomentCombination := data16[6]!
private noncomputable def ws22 := ws21.push GrothendieckLB.Supplement.CQDegree51.w22.toArray
private noncomputable def v23 : List MomentCombination := data16[7]!
private noncomputable def ws23 := ws22.push GrothendieckLB.Supplement.CQDegree51.w23.toArray
private noncomputable def data24 : List (List MomentCombination) :=
  eval% (candidateRows 51 24 8)
private noncomputable def v24 : List MomentCombination := data24[0]!
private noncomputable def ws24 := ws23.push GrothendieckLB.Supplement.CQDegree51.w24.toArray
private noncomputable def v25 : List MomentCombination := data24[1]!
private noncomputable def ws25 := ws24.push GrothendieckLB.Supplement.CQDegree51.w25.toArray
private noncomputable def v26 : List MomentCombination := data24[2]!
private noncomputable def ws26 := ws25.push GrothendieckLB.Supplement.CQDegree51.w26.toArray
private noncomputable def v27 : List MomentCombination := data24[3]!
private noncomputable def ws27 := ws26.push GrothendieckLB.Supplement.CQDegree51.w27.toArray
private noncomputable def v28 : List MomentCombination := data24[4]!
private noncomputable def ws28 := ws27.push GrothendieckLB.Supplement.CQDegree51.w28.toArray
private noncomputable def v29 : List MomentCombination := data24[5]!
private noncomputable def ws29 := ws28.push GrothendieckLB.Supplement.CQDegree51.w29.toArray
private noncomputable def v30 : List MomentCombination := data24[6]!
private noncomputable def ws30 := ws29.push GrothendieckLB.Supplement.CQDegree51.w30.toArray
private noncomputable def v31 : List MomentCombination := data24[7]!
private noncomputable def ws31 := ws30.push GrothendieckLB.Supplement.CQDegree51.w31.toArray
private noncomputable def data32 : List (List MomentCombination) :=
  eval% (candidateRows 51 32 8)
private noncomputable def v32 : List MomentCombination := data32[0]!
private noncomputable def ws32 := ws31.push GrothendieckLB.Supplement.CQDegree51.w32.toArray
private noncomputable def v33 : List MomentCombination := data32[1]!
private noncomputable def ws33 := ws32.push GrothendieckLB.Supplement.CQDegree51.w33.toArray
private noncomputable def v34 : List MomentCombination := data32[2]!
private noncomputable def ws34 := ws33.push GrothendieckLB.Supplement.CQDegree51.w34.toArray
private noncomputable def v35 : List MomentCombination := data32[3]!
private noncomputable def ws35 := ws34.push GrothendieckLB.Supplement.CQDegree51.w35.toArray
private noncomputable def v36 : List MomentCombination := data32[4]!
private noncomputable def ws36 := ws35.push GrothendieckLB.Supplement.CQDegree51.w36.toArray
private noncomputable def v37 : List MomentCombination := data32[5]!
private noncomputable def ws37 := ws36.push GrothendieckLB.Supplement.CQDegree51.w37.toArray
private noncomputable def v38 : List MomentCombination := data32[6]!
private noncomputable def ws38 := ws37.push GrothendieckLB.Supplement.CQDegree51.w38.toArray
private noncomputable def v39 : List MomentCombination := data32[7]!
private noncomputable def ws39 := ws38.push GrothendieckLB.Supplement.CQDegree51.w39.toArray
private noncomputable def data40 : List (List MomentCombination) :=
  eval% (candidateRows 51 40 8)
private noncomputable def v40 : List MomentCombination := data40[0]!
private noncomputable def ws40 := ws39.push GrothendieckLB.Supplement.CQDegree51.w40.toArray
private noncomputable def v41 : List MomentCombination := data40[1]!
private noncomputable def ws41 := ws40.push GrothendieckLB.Supplement.CQDegree51.w41.toArray
private noncomputable def v42 : List MomentCombination := data40[2]!
private noncomputable def ws42 := ws41.push GrothendieckLB.Supplement.CQDegree51.w42.toArray
private noncomputable def v43 : List MomentCombination := data40[3]!
private noncomputable def ws43 := ws42.push GrothendieckLB.Supplement.CQDegree51.w43.toArray
private noncomputable def v44 : List MomentCombination := data40[4]!
private noncomputable def ws44 := ws43.push GrothendieckLB.Supplement.CQDegree51.w44.toArray
private noncomputable def v45 : List MomentCombination := data40[5]!
private noncomputable def ws45 := ws44.push GrothendieckLB.Supplement.CQDegree51.w45.toArray
private noncomputable def v46 : List MomentCombination := data40[6]!
private noncomputable def ws46 := ws45.push GrothendieckLB.Supplement.CQDegree51.w46.toArray
private noncomputable def v47 : List MomentCombination := data40[7]!
private noncomputable def ws47 := ws46.push GrothendieckLB.Supplement.CQDegree51.w47.toArray
private noncomputable def data48 : List (List MomentCombination) :=
  eval% (candidateRows 51 48 4)
private noncomputable def v48 : List MomentCombination := data48[0]!
private noncomputable def ws48 := ws47.push GrothendieckLB.Supplement.CQDegree51.w48.toArray
private noncomputable def v49 : List MomentCombination := data48[1]!
private noncomputable def ws49 := ws48.push GrothendieckLB.Supplement.CQDegree51.w49.toArray
private noncomputable def v50 : List MomentCombination := data48[2]!
private noncomputable def ws50 := ws49.push GrothendieckLB.Supplement.CQDegree51.w50.toArray
private noncomputable def v51 : List MomentCombination := data48[3]!
private noncomputable def ws51 := ws50.push GrothendieckLB.Supplement.CQDegree51.w51.toArray
private noncomputable def raw : List MomentCombination := eval% ((momentRows (3*51-5)).toList)
private theorem rawOK : momentRows (3*51-5) = raw.toArray := by decide +kernel
private theorem iniOK : startAt 51 = v0.toArray := by
  unfold startAt
  rw [rawOK]
  decide +kernel
private theorem zwOK : zeroWeights 51 v0.toArray = GrothendieckLB.Supplement.CQDegree51.w0.toArray := by decide +kernel
private theorem g0 : grid 51 (startAt 51) 0 = ⟨v0.toArray,v0.toArray,ws0⟩ := gridSeed iniOK zwOK
private theorem n1 : nextRow 0 v0.toArray v0.toArray=v1.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t1 : tab (51-0) (fun b => toWeight (0+1) b (entry zeroCombination v0.toArray b))=GrothendieckLB.Supplement.CQDegree51.w1.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g1 : grid 51 (startAt 51) 1=⟨v0.toArray,v1.toArray,ws1⟩ := gridStep g0 n1 t1
private theorem n2 : nextRow 1 v0.toArray v1.toArray=v2.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t2 : tab (51-1) (fun b => toWeight (1+1) b (entry zeroCombination v1.toArray b))=GrothendieckLB.Supplement.CQDegree51.w2.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g2 : grid 51 (startAt 51) 2=⟨v1.toArray,v2.toArray,ws2⟩ := gridStep g1 n2 t2
private theorem n3 : nextRow 2 v1.toArray v2.toArray=v3.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t3 : tab (51-2) (fun b => toWeight (2+1) b (entry zeroCombination v2.toArray b))=GrothendieckLB.Supplement.CQDegree51.w3.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g3 : grid 51 (startAt 51) 3=⟨v2.toArray,v3.toArray,ws3⟩ := gridStep g2 n3 t3
private theorem n4 : nextRow 3 v2.toArray v3.toArray=v4.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t4 : tab (51-3) (fun b => toWeight (3+1) b (entry zeroCombination v3.toArray b))=GrothendieckLB.Supplement.CQDegree51.w4.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g4 : grid 51 (startAt 51) 4=⟨v3.toArray,v4.toArray,ws4⟩ := gridStep g3 n4 t4
private theorem n5 : nextRow 4 v3.toArray v4.toArray=v5.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t5 : tab (51-4) (fun b => toWeight (4+1) b (entry zeroCombination v4.toArray b))=GrothendieckLB.Supplement.CQDegree51.w5.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g5 : grid 51 (startAt 51) 5=⟨v4.toArray,v5.toArray,ws5⟩ := gridStep g4 n5 t5
private theorem n6 : nextRow 5 v4.toArray v5.toArray=v6.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t6 : tab (51-5) (fun b => toWeight (5+1) b (entry zeroCombination v5.toArray b))=GrothendieckLB.Supplement.CQDegree51.w6.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g6 : grid 51 (startAt 51) 6=⟨v5.toArray,v6.toArray,ws6⟩ := gridStep g5 n6 t6
private theorem n7 : nextRow 6 v5.toArray v6.toArray=v7.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t7 : tab (51-6) (fun b => toWeight (6+1) b (entry zeroCombination v6.toArray b))=GrothendieckLB.Supplement.CQDegree51.w7.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g7 : grid 51 (startAt 51) 7=⟨v6.toArray,v7.toArray,ws7⟩ := gridStep g6 n7 t7
private theorem n8 : nextRow 7 v6.toArray v7.toArray=v8.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t8 : tab (51-7) (fun b => toWeight (7+1) b (entry zeroCombination v7.toArray b))=GrothendieckLB.Supplement.CQDegree51.w8.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g8 : grid 51 (startAt 51) 8=⟨v7.toArray,v8.toArray,ws8⟩ := gridStep g7 n8 t8
private theorem n9 : nextRow 8 v7.toArray v8.toArray=v9.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t9 : tab (51-8) (fun b => toWeight (8+1) b (entry zeroCombination v8.toArray b))=GrothendieckLB.Supplement.CQDegree51.w9.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g9 : grid 51 (startAt 51) 9=⟨v8.toArray,v9.toArray,ws9⟩ := gridStep g8 n9 t9
private theorem n10 : nextRow 9 v8.toArray v9.toArray=v10.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t10 : tab (51-9) (fun b => toWeight (9+1) b (entry zeroCombination v9.toArray b))=GrothendieckLB.Supplement.CQDegree51.w10.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g10 : grid 51 (startAt 51) 10=⟨v9.toArray,v10.toArray,ws10⟩ := gridStep g9 n10 t10
private theorem n11 : nextRow 10 v9.toArray v10.toArray=v11.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t11 : tab (51-10) (fun b => toWeight (10+1) b (entry zeroCombination v10.toArray b))=GrothendieckLB.Supplement.CQDegree51.w11.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g11 : grid 51 (startAt 51) 11=⟨v10.toArray,v11.toArray,ws11⟩ := gridStep g10 n11 t11
private theorem n12 : nextRow 11 v10.toArray v11.toArray=v12.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t12 : tab (51-11) (fun b => toWeight (11+1) b (entry zeroCombination v11.toArray b))=GrothendieckLB.Supplement.CQDegree51.w12.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g12 : grid 51 (startAt 51) 12=⟨v11.toArray,v12.toArray,ws12⟩ := gridStep g11 n12 t12
private theorem n13 : nextRow 12 v11.toArray v12.toArray=v13.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t13 : tab (51-12) (fun b => toWeight (12+1) b (entry zeroCombination v12.toArray b))=GrothendieckLB.Supplement.CQDegree51.w13.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g13 : grid 51 (startAt 51) 13=⟨v12.toArray,v13.toArray,ws13⟩ := gridStep g12 n13 t13
private theorem n14 : nextRow 13 v12.toArray v13.toArray=v14.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t14 : tab (51-13) (fun b => toWeight (13+1) b (entry zeroCombination v13.toArray b))=GrothendieckLB.Supplement.CQDegree51.w14.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g14 : grid 51 (startAt 51) 14=⟨v13.toArray,v14.toArray,ws14⟩ := gridStep g13 n14 t14
private theorem n15 : nextRow 14 v13.toArray v14.toArray=v15.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t15 : tab (51-14) (fun b => toWeight (14+1) b (entry zeroCombination v14.toArray b))=GrothendieckLB.Supplement.CQDegree51.w15.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g15 : grid 51 (startAt 51) 15=⟨v14.toArray,v15.toArray,ws15⟩ := gridStep g14 n15 t15
private theorem n16 : nextRow 15 v14.toArray v15.toArray=v16.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t16 : tab (51-15) (fun b => toWeight (15+1) b (entry zeroCombination v15.toArray b))=GrothendieckLB.Supplement.CQDegree51.w16.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g16 : grid 51 (startAt 51) 16=⟨v15.toArray,v16.toArray,ws16⟩ := gridStep g15 n16 t16
private theorem n17 : nextRow 16 v15.toArray v16.toArray=v17.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t17 : tab (51-16) (fun b => toWeight (16+1) b (entry zeroCombination v16.toArray b))=GrothendieckLB.Supplement.CQDegree51.w17.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g17 : grid 51 (startAt 51) 17=⟨v16.toArray,v17.toArray,ws17⟩ := gridStep g16 n17 t17
private theorem n18 : nextRow 17 v16.toArray v17.toArray=v18.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t18 : tab (51-17) (fun b => toWeight (17+1) b (entry zeroCombination v17.toArray b))=GrothendieckLB.Supplement.CQDegree51.w18.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g18 : grid 51 (startAt 51) 18=⟨v17.toArray,v18.toArray,ws18⟩ := gridStep g17 n18 t18
private theorem n19 : nextRow 18 v17.toArray v18.toArray=v19.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t19 : tab (51-18) (fun b => toWeight (18+1) b (entry zeroCombination v18.toArray b))=GrothendieckLB.Supplement.CQDegree51.w19.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g19 : grid 51 (startAt 51) 19=⟨v18.toArray,v19.toArray,ws19⟩ := gridStep g18 n19 t19
private theorem n20 : nextRow 19 v18.toArray v19.toArray=v20.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t20 : tab (51-19) (fun b => toWeight (19+1) b (entry zeroCombination v19.toArray b))=GrothendieckLB.Supplement.CQDegree51.w20.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g20 : grid 51 (startAt 51) 20=⟨v19.toArray,v20.toArray,ws20⟩ := gridStep g19 n20 t20
private theorem n21 : nextRow 20 v19.toArray v20.toArray=v21.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t21 : tab (51-20) (fun b => toWeight (20+1) b (entry zeroCombination v20.toArray b))=GrothendieckLB.Supplement.CQDegree51.w21.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g21 : grid 51 (startAt 51) 21=⟨v20.toArray,v21.toArray,ws21⟩ := gridStep g20 n21 t21
private theorem n22 : nextRow 21 v20.toArray v21.toArray=v22.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t22 : tab (51-21) (fun b => toWeight (21+1) b (entry zeroCombination v21.toArray b))=GrothendieckLB.Supplement.CQDegree51.w22.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g22 : grid 51 (startAt 51) 22=⟨v21.toArray,v22.toArray,ws22⟩ := gridStep g21 n22 t22
private theorem n23 : nextRow 22 v21.toArray v22.toArray=v23.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t23 : tab (51-22) (fun b => toWeight (22+1) b (entry zeroCombination v22.toArray b))=GrothendieckLB.Supplement.CQDegree51.w23.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g23 : grid 51 (startAt 51) 23=⟨v22.toArray,v23.toArray,ws23⟩ := gridStep g22 n23 t23
private theorem n24 : nextRow 23 v22.toArray v23.toArray=v24.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t24 : tab (51-23) (fun b => toWeight (23+1) b (entry zeroCombination v23.toArray b))=GrothendieckLB.Supplement.CQDegree51.w24.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g24 : grid 51 (startAt 51) 24=⟨v23.toArray,v24.toArray,ws24⟩ := gridStep g23 n24 t24
private theorem n25 : nextRow 24 v23.toArray v24.toArray=v25.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t25 : tab (51-24) (fun b => toWeight (24+1) b (entry zeroCombination v24.toArray b))=GrothendieckLB.Supplement.CQDegree51.w25.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g25 : grid 51 (startAt 51) 25=⟨v24.toArray,v25.toArray,ws25⟩ := gridStep g24 n25 t25
private theorem n26 : nextRow 25 v24.toArray v25.toArray=v26.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t26 : tab (51-25) (fun b => toWeight (25+1) b (entry zeroCombination v25.toArray b))=GrothendieckLB.Supplement.CQDegree51.w26.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g26 : grid 51 (startAt 51) 26=⟨v25.toArray,v26.toArray,ws26⟩ := gridStep g25 n26 t26
private theorem n27 : nextRow 26 v25.toArray v26.toArray=v27.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t27 : tab (51-26) (fun b => toWeight (26+1) b (entry zeroCombination v26.toArray b))=GrothendieckLB.Supplement.CQDegree51.w27.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g27 : grid 51 (startAt 51) 27=⟨v26.toArray,v27.toArray,ws27⟩ := gridStep g26 n27 t27
private theorem n28 : nextRow 27 v26.toArray v27.toArray=v28.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t28 : tab (51-27) (fun b => toWeight (27+1) b (entry zeroCombination v27.toArray b))=GrothendieckLB.Supplement.CQDegree51.w28.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g28 : grid 51 (startAt 51) 28=⟨v27.toArray,v28.toArray,ws28⟩ := gridStep g27 n28 t28
private theorem n29 : nextRow 28 v27.toArray v28.toArray=v29.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t29 : tab (51-28) (fun b => toWeight (28+1) b (entry zeroCombination v28.toArray b))=GrothendieckLB.Supplement.CQDegree51.w29.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g29 : grid 51 (startAt 51) 29=⟨v28.toArray,v29.toArray,ws29⟩ := gridStep g28 n29 t29
private theorem n30 : nextRow 29 v28.toArray v29.toArray=v30.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t30 : tab (51-29) (fun b => toWeight (29+1) b (entry zeroCombination v29.toArray b))=GrothendieckLB.Supplement.CQDegree51.w30.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g30 : grid 51 (startAt 51) 30=⟨v29.toArray,v30.toArray,ws30⟩ := gridStep g29 n30 t30
private theorem n31 : nextRow 30 v29.toArray v30.toArray=v31.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t31 : tab (51-30) (fun b => toWeight (30+1) b (entry zeroCombination v30.toArray b))=GrothendieckLB.Supplement.CQDegree51.w31.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g31 : grid 51 (startAt 51) 31=⟨v30.toArray,v31.toArray,ws31⟩ := gridStep g30 n31 t31
private theorem n32 : nextRow 31 v30.toArray v31.toArray=v32.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t32 : tab (51-31) (fun b => toWeight (31+1) b (entry zeroCombination v31.toArray b))=GrothendieckLB.Supplement.CQDegree51.w32.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g32 : grid 51 (startAt 51) 32=⟨v31.toArray,v32.toArray,ws32⟩ := gridStep g31 n32 t32
private theorem n33 : nextRow 32 v31.toArray v32.toArray=v33.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t33 : tab (51-32) (fun b => toWeight (32+1) b (entry zeroCombination v32.toArray b))=GrothendieckLB.Supplement.CQDegree51.w33.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g33 : grid 51 (startAt 51) 33=⟨v32.toArray,v33.toArray,ws33⟩ := gridStep g32 n33 t33
private theorem n34 : nextRow 33 v32.toArray v33.toArray=v34.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t34 : tab (51-33) (fun b => toWeight (33+1) b (entry zeroCombination v33.toArray b))=GrothendieckLB.Supplement.CQDegree51.w34.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g34 : grid 51 (startAt 51) 34=⟨v33.toArray,v34.toArray,ws34⟩ := gridStep g33 n34 t34
private theorem n35 : nextRow 34 v33.toArray v34.toArray=v35.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t35 : tab (51-34) (fun b => toWeight (34+1) b (entry zeroCombination v34.toArray b))=GrothendieckLB.Supplement.CQDegree51.w35.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g35 : grid 51 (startAt 51) 35=⟨v34.toArray,v35.toArray,ws35⟩ := gridStep g34 n35 t35
private theorem n36 : nextRow 35 v34.toArray v35.toArray=v36.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t36 : tab (51-35) (fun b => toWeight (35+1) b (entry zeroCombination v35.toArray b))=GrothendieckLB.Supplement.CQDegree51.w36.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g36 : grid 51 (startAt 51) 36=⟨v35.toArray,v36.toArray,ws36⟩ := gridStep g35 n36 t36
private theorem n37 : nextRow 36 v35.toArray v36.toArray=v37.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t37 : tab (51-36) (fun b => toWeight (36+1) b (entry zeroCombination v36.toArray b))=GrothendieckLB.Supplement.CQDegree51.w37.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g37 : grid 51 (startAt 51) 37=⟨v36.toArray,v37.toArray,ws37⟩ := gridStep g36 n37 t37
private theorem n38 : nextRow 37 v36.toArray v37.toArray=v38.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t38 : tab (51-37) (fun b => toWeight (37+1) b (entry zeroCombination v37.toArray b))=GrothendieckLB.Supplement.CQDegree51.w38.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g38 : grid 51 (startAt 51) 38=⟨v37.toArray,v38.toArray,ws38⟩ := gridStep g37 n38 t38
private theorem n39 : nextRow 38 v37.toArray v38.toArray=v39.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t39 : tab (51-38) (fun b => toWeight (38+1) b (entry zeroCombination v38.toArray b))=GrothendieckLB.Supplement.CQDegree51.w39.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g39 : grid 51 (startAt 51) 39=⟨v38.toArray,v39.toArray,ws39⟩ := gridStep g38 n39 t39
private theorem n40 : nextRow 39 v38.toArray v39.toArray=v40.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t40 : tab (51-39) (fun b => toWeight (39+1) b (entry zeroCombination v39.toArray b))=GrothendieckLB.Supplement.CQDegree51.w40.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g40 : grid 51 (startAt 51) 40=⟨v39.toArray,v40.toArray,ws40⟩ := gridStep g39 n40 t40
private theorem n41 : nextRow 40 v39.toArray v40.toArray=v41.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t41 : tab (51-40) (fun b => toWeight (40+1) b (entry zeroCombination v40.toArray b))=GrothendieckLB.Supplement.CQDegree51.w41.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g41 : grid 51 (startAt 51) 41=⟨v40.toArray,v41.toArray,ws41⟩ := gridStep g40 n41 t41
private theorem n42 : nextRow 41 v40.toArray v41.toArray=v42.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t42 : tab (51-41) (fun b => toWeight (41+1) b (entry zeroCombination v41.toArray b))=GrothendieckLB.Supplement.CQDegree51.w42.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g42 : grid 51 (startAt 51) 42=⟨v41.toArray,v42.toArray,ws42⟩ := gridStep g41 n42 t42
private theorem n43 : nextRow 42 v41.toArray v42.toArray=v43.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t43 : tab (51-42) (fun b => toWeight (42+1) b (entry zeroCombination v42.toArray b))=GrothendieckLB.Supplement.CQDegree51.w43.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g43 : grid 51 (startAt 51) 43=⟨v42.toArray,v43.toArray,ws43⟩ := gridStep g42 n43 t43
private theorem n44 : nextRow 43 v42.toArray v43.toArray=v44.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t44 : tab (51-43) (fun b => toWeight (43+1) b (entry zeroCombination v43.toArray b))=GrothendieckLB.Supplement.CQDegree51.w44.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g44 : grid 51 (startAt 51) 44=⟨v43.toArray,v44.toArray,ws44⟩ := gridStep g43 n44 t44
private theorem n45 : nextRow 44 v43.toArray v44.toArray=v45.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t45 : tab (51-44) (fun b => toWeight (44+1) b (entry zeroCombination v44.toArray b))=GrothendieckLB.Supplement.CQDegree51.w45.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g45 : grid 51 (startAt 51) 45=⟨v44.toArray,v45.toArray,ws45⟩ := gridStep g44 n45 t45
private theorem n46 : nextRow 45 v44.toArray v45.toArray=v46.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t46 : tab (51-45) (fun b => toWeight (45+1) b (entry zeroCombination v45.toArray b))=GrothendieckLB.Supplement.CQDegree51.w46.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g46 : grid 51 (startAt 51) 46=⟨v45.toArray,v46.toArray,ws46⟩ := gridStep g45 n46 t46
private theorem n47 : nextRow 46 v45.toArray v46.toArray=v47.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t47 : tab (51-46) (fun b => toWeight (46+1) b (entry zeroCombination v46.toArray b))=GrothendieckLB.Supplement.CQDegree51.w47.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g47 : grid 51 (startAt 51) 47=⟨v46.toArray,v47.toArray,ws47⟩ := gridStep g46 n47 t47
private theorem n48 : nextRow 47 v46.toArray v47.toArray=v48.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t48 : tab (51-47) (fun b => toWeight (47+1) b (entry zeroCombination v47.toArray b))=GrothendieckLB.Supplement.CQDegree51.w48.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g48 : grid 51 (startAt 51) 48=⟨v47.toArray,v48.toArray,ws48⟩ := gridStep g47 n48 t48
private theorem n49 : nextRow 48 v47.toArray v48.toArray=v49.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t49 : tab (51-48) (fun b => toWeight (48+1) b (entry zeroCombination v48.toArray b))=GrothendieckLB.Supplement.CQDegree51.w49.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g49 : grid 51 (startAt 51) 49=⟨v48.toArray,v49.toArray,ws49⟩ := gridStep g48 n49 t49
private theorem n50 : nextRow 49 v48.toArray v49.toArray=v50.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t50 : tab (51-49) (fun b => toWeight (49+1) b (entry zeroCombination v49.toArray b))=GrothendieckLB.Supplement.CQDegree51.w50.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g50 : grid 51 (startAt 51) 50=⟨v49.toArray,v50.toArray,ws50⟩ := gridStep g49 n50 t50
private theorem n51 : nextRow 50 v49.toArray v50.toArray=v51.toArray := by
  rw [next_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem t51 : tab (51-50) (fun b => toWeight (50+1) b (entry zeroCombination v50.toArray b))=GrothendieckLB.Supplement.CQDegree51.w51.toArray := by
  rw [weight_eq (hlen:=by decide +kernel)]
  apply congrArg List.toArray
  decide +kernel
private theorem g51 : grid 51 (startAt 51) 51=⟨v50.toArray,v51.toArray,ws51⟩ := gridStep g50 n51 t51
open GrothendieckLB.Supplement in
theorem solution : (grid 51 (startAt 51) 51).weights = CQDegree51.weights := by
  rw [g51]
  rfl
