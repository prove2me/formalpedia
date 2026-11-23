-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_head_integer_comparisons_51
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:12:18.361247+00:00
-- url     : https://prove2.me/submissions/f8f3fc83-bd80-4b88-8a5b-c64de3ae3a8c

import Theorems.Thm_GrothendieckLB_Supplement_cq_degree51_hermite_weights
import Theorems.Thm_GrothendieckLB_Supplement_cq_degree51_covariance_powers
import Definitions.Def_GrothendieckLB_Supplement_cqDegree51Tables

open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadArithmetic
namespace CQSum

private theorem assocI (x y z : Interval) : addInterval (addInterval x y) z = addInterval x (addInterval y z) := by
  cases x; cases y; cases z; simp [addInterval,Int.add_assoc]
private theorem addZero (x : Interval) : addInterval x zeroInterval=x := by cases x; simp [addInterval,zeroInterval]
private theorem zeroAdd (x : Interval) : addInterval zeroInterval x=x := by cases x; simp [addInterval,zeroInterval]

private theorem sumCons (f : ℕ → Interval) (n : ℕ) :
    sumIntervals f (n+1) = addInterval (f 0) (sumIntervals (fun k => f (k+1)) n) := by
  induction n with
  | zero => simp only [sumIntervals,addZero,zeroAdd]
  | succ n ih =>
    change addInterval (sumIntervals f (n+1)) (f (n+1)) = _
    rw [ih,assocI]
    rfl

private theorem sumExt {f g : ℕ → Interval} (n : ℕ) (h : ∀ k, k<n → f k=g k) :
    sumIntervals f n = sumIntervals g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumIntervals,ih (fun k hk => h k (by omega)),h n (by omega)]

private def scan : ℕ → ℕ → List Interval → List Interval → Interval
  | k+1, b, x::xs, y::ys => addInterval (scaleInterval ((-1:ℤ)^b) (mulInterval coefficientScale x y))
      (scan k (b+1) xs ys)
  | _,_,_,_ => zeroInterval

private theorem scan_get (l b : ℕ) (w r : List Interval) (hw : l≤w.length) (hr : l≤r.length) :
    scan l b w r = sumIntervals (fun j => scaleInterval ((-1:ℤ)^(b+j))
      (mulInterval coefficientScale (w[j]?.getD zeroInterval) (r[j]?.getD zeroInterval))) l := by
  induction l generalizing b w r with
  | zero => rfl
  | succ l ih =>
    cases w with
    | nil => simp at hw
    | cons x xs =>
      cases r with
      | nil => simp at hr
      | cons y ys =>
        rw [scan,sumCons,ih (b+1) xs ys (by simpa using hw) (by simpa using hr)]
        simp only [Nat.add_zero,List.getElem?_cons_zero,Option.getD_some,List.getElem?_cons_succ]
        apply congrArg (addInterval _)
        apply sumExt
        intro j _
        rw [show b+1+j = b+(j+1) by omega]

private def fastSum (w r : Array (Array Interval)) (m : ℕ) :=
  sumIntervals (fun a => scan (m+1-a) 0 (entry #[] w a).toList
       (((entry #[] r a).toList.take (m+1)).reverse)) (m+1)

private theorem fast_eq (w r : Array (Array Interval)) (m : ℕ)
    (hs : ∀ a, a ≤ m → m+1-a ≤ (entry #[] w a).size ∧ m+1 ≤ (entry #[] r a).size) :
    fullSum w r m = fastSum w r m := by
  unfold fullSum fastSum
  apply sumExt
  intro a ha
  obtain ⟨hw,hr⟩ := hs a (by omega)
  have hlen : ((entry #[] r a).toList.take (m+1)).length=m+1 := by simp [Nat.min_eq_left hr]
  rw [scan_get _ _ _ _ (by simpa using hw) (by rw [List.length_reverse,hlen]; omega)]
  apply sumExt
  intro b hb
  have hrev := List.getElem?_reverse' (l:=(entry #[] r a).toList.take (m+1))
    (i:=b) (j:=m-b) (by rw [hlen]; omega)
  rw [hrev,List.getElem?_take_of_lt (by omega)]
  simp only [Nat.zero_add,entry,Array.getElem?_toList]

private def test (j : ℕ) :=
  let v := fastSum CQDegree51.weights CQDegree51.powers (2*j+3)
  decide (max (-v.lo) v.hi * 10^40 ≤ coefficientScale*2*314159265358979323846*(cqHeadUnits[j]?.getD 0))

set_option maxRecDepth 100000
set_option exponentiation.threshold 50000
set_option maxHeartbeats 300000000

private theorem shapes : ∀ a : Fin 52, (entry #[] CQDegree51.weights a).size=52-a ∧
    (entry #[] CQDegree51.powers a).size=52 := by decide +kernel

private theorem official_to_test (j : ℕ) (hj : j < 25) :
    (let v := fullSum CQDegree51.weights CQDegree51.powers (2*j+3)
     decide (max (-v.lo) v.hi * 10^40 ≤ coefficientScale*2*314159265358979323846*(cqHeadUnits[j]?.getD 0))) =
      test j := by
  unfold test
  rw [fast_eq]
  intro a ha
  have h := shapes ⟨a,by omega⟩
  change (entry #[] CQDegree51.weights a).size=52-a ∧ (entry #[] CQDegree51.powers a).size=52 at h
  omega

set_option Elab.async false
private theorem checks51 : (List.range 25).all test = true := by decide +kernel
end CQSum

open CQSum
theorem solution : verifyList 51 (List.range 25) = true := by
  unfold verifyList
  rw [cq_degree51_hermite_weights,cq_degree51_covariance_powers]
  apply List.all_eq_true.mpr
  intro j hj
  exact (official_to_test j (List.mem_range.mp hj)).trans (List.all_eq_true.mp checks51 j hj)
