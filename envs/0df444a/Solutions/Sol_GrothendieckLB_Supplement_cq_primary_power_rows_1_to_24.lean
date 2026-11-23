-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_primary_power_rows_1_to_24
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:40:59.72061+00:00
-- url     : https://prove2.me/submissions/5305d95f-d602-4f98-aa13-339689300371

import Definitions.Def_GrothendieckLB_Supplement_cqReplayPowers
open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadCertificate GrothendieckLB.Supplement.CQHeadArithmetic
set_option maxRecDepth 100000
set_option maxHeartbeats 120000000
set_option Elab.async false
namespace SparsePower

private theorem parity_zero (a i : ℕ) (h : i%2 ≠ a%2) : power a i = zeroInterval := by
  simp only [power,getB,if_neg h]
private theorem mismatch (p j : ℕ) (h : j%2 ≠ (p+1)%2) : power (p+1) j = powerAt p j := by
  have hs (k : ℕ) (hk : k%2=1) : (if k≤j then power p (j-k) else zeroInterval)=zeroInterval := by
    split <;> rename_i he
    · apply parity_zero; omega
    · rfl
  rw [parity_zero _ _ h]
  simp only [powerAt,hs 1 (by decide),hs 3 (by decide),hs 5 (by decide)]
  decide +kernel

private def encodedCell (p k : ℕ) : Bool :=
  let j := 2*k+(p+1)%2
  decide (power (p+1) j=powerAt p j)
private theorem restore (p : ℕ) (hp : (List.range 126).all (encodedCell p)=true) :
    (List.range 252).all (fun j => decide (power (p+1) j = powerAt p j))=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have hj' := List.mem_range.mp hj
  by_cases h : j%2 = (p+1)%2
  · have e := List.all_eq_true.mp hp (j/2) (List.mem_range.mpr (by omega))
    simpa only [encodedCell,show 2*(j/2)+(p+1)%2=j by omega] using e
  · exact decide_eq_true (mismatch p j h)
private def inSupport (p j : ℕ) := p ≤ j ∧ j ≤ 5*p
private instance (p j : ℕ) : Decidable (inSupport p j) := inferInstanceAs (Decidable (_ ∧ _))
private def zeros (p k : ℕ) : Bool :=
  let j := 2*k+p%2
  if inSupport p j then true else decide (power p j = zeroInterval)
private def inside (p k : ℕ) : Bool :=
  if inSupport (p+1) (2*k+(p+1)%2) then encodedCell p k else true
private def good (p : ℕ) := (List.range 126).all (zeros p)
private theorem leaveZero (p j : ℕ) (hj : j < 252) (hs : ¬inSupport p j) (hg : good p = true) :
    power p j = zeroInterval := by
  by_cases he : j%2=p%2
  · have h := List.all_eq_true.mp hg (j/2) (List.mem_range.mpr (by omega))
    simpa only [zeros,show 2*(j/2)+p%2=j by omega,if_neg hs,decide_eq_true_eq] using h
  · exact parity_zero p j he
private theorem supportRestore (p : ℕ) (hl : good p=true) (hr : good (p+1)=true)
    (hin : (List.range 126).all (inside p)=true) :
    (List.range 252).all (fun j => decide (power (p+1) j = powerAt p j))=true := by
  apply restore
  apply List.all_eq_true.mpr
  intro k hk
  have hk' := List.mem_range.mp hk
  let j := 2*k+(p+1)%2
  have hj : j < 252 := by dsimp [j]; omega
  by_cases hs : inSupport (p+1) j
  · have hh := List.all_eq_true.mp hin k hk
    simpa only [inside,show inSupport (p+1) (2*k+(p+1)%2) from hs,if_pos] using hh
  · have e (i : ℕ) (h1 : 1 ≤ i) (h5 : i ≤ 5) : (if i≤j then power p (j-i) else zeroInterval)=zeroInterval := by
      split
      · apply leaveZero _ _ (by omega) _ hl
        unfold inSupport at hs ⊢
        omega
      · rfl
    change decide (power (p+1) j=powerAt p j)=true
    rw [leaveZero _ _ hj hs hr]
    unfold powerAt
    simp only [e 1 (by decide) (by decide),e 3 (by decide) (by decide),e 5 (by decide) (by decide)]
    decide +kernel


private def seg (f : ℕ → Bool) (l n : ℕ) := (List.range n).all fun i => f (l+i)
private theorem join {f : ℕ → Bool} {l n m : ℕ}
    (hn : seg f l n=true) (hm : seg f (l+n) m=true) : seg f l (n+m)=true := by
  apply List.all_eq_true.mpr
  intro x hx
  have hx' := List.mem_range.mp hx
  by_cases h : x < n
  · exact List.all_eq_true.mp hn x (List.mem_range.mpr h)
  · have hh := List.all_eq_true.mp hm (x-n) (List.mem_range.mpr (by omega))
    change f (l+n+(x-n))=true at hh
    rwa [show l+n+(x-n)=l+x by omega] at hh
private theorem full {f : ℕ → Bool} {n : ℕ} (h : seg f 0 n=true) : (List.range n).all f=true := by
  simpa only [seg,Nat.zero_add] using h

private theorem z0 : good 0=true := by decide +kernel

private theorem z1 : good 1=true := by decide +kernel

private theorem z2 : good 2=true := by decide +kernel

private theorem z3 : good 3=true := by decide +kernel

private theorem z4 : good 4=true := by decide +kernel

private theorem z5 : good 5=true := by decide +kernel

private theorem z6 : good 6=true := by decide +kernel

private theorem z7 : good 7=true := by decide +kernel

private theorem z8 : good 8=true := by decide +kernel

private theorem z9 : good 9=true := by decide +kernel

private theorem z10 : good 10=true := by decide +kernel

private theorem z11 : good 11=true := by decide +kernel

private theorem z12 : good 12=true := by decide +kernel

private theorem z13 : good 13=true := by decide +kernel

private theorem z14 : good 14=true := by decide +kernel

private theorem z15 : good 15=true := by decide +kernel

private theorem z16 : good 16=true := by decide +kernel

private theorem z17 : good 17=true := by decide +kernel

private theorem z18 : good 18=true := by decide +kernel

private theorem z19 : good 19=true := by decide +kernel

private theorem z20 : good 20=true := by decide +kernel

private theorem z21 : good 21=true := by decide +kernel

private theorem z22 : good 22=true := by decide +kernel

private theorem z23 : good 23=true := by decide +kernel

private theorem z24 : good 24=true := by decide +kernel

private theorem c0 : (List.range 126).all (inside 0)=true := by decide +kernel
private theorem row0 : (List.range 252).all (fun j => decide (power (0+1) j=powerAt 0 j))=true := supportRestore 0 z0 z1 c0

private theorem c1 : (List.range 126).all (inside 1)=true := by decide +kernel
private theorem row1 : (List.range 252).all (fun j => decide (power (1+1) j=powerAt 1 j))=true := supportRestore 1 z1 z2 c1

private theorem c2 : (List.range 126).all (inside 2)=true := by decide +kernel
private theorem row2 : (List.range 252).all (fun j => decide (power (2+1) j=powerAt 2 j))=true := supportRestore 2 z2 z3 c2

private theorem c3 : (List.range 126).all (inside 3)=true := by decide +kernel
private theorem row3 : (List.range 252).all (fun j => decide (power (3+1) j=powerAt 3 j))=true := supportRestore 3 z3 z4 c3

private theorem c4 : (List.range 126).all (inside 4)=true := by decide +kernel
private theorem row4 : (List.range 252).all (fun j => decide (power (4+1) j=powerAt 4 j))=true := supportRestore 4 z4 z5 c4

private theorem c5 : (List.range 126).all (inside 5)=true := by decide +kernel
private theorem row5 : (List.range 252).all (fun j => decide (power (5+1) j=powerAt 5 j))=true := supportRestore 5 z5 z6 c5

private theorem c6 : (List.range 126).all (inside 6)=true := by decide +kernel
private theorem row6 : (List.range 252).all (fun j => decide (power (6+1) j=powerAt 6 j))=true := supportRestore 6 z6 z7 c6

private theorem c7 : (List.range 126).all (inside 7)=true := by decide +kernel
private theorem row7 : (List.range 252).all (fun j => decide (power (7+1) j=powerAt 7 j))=true := supportRestore 7 z7 z8 c7

private theorem c8 : (List.range 126).all (inside 8)=true := by decide +kernel
private theorem row8 : (List.range 252).all (fun j => decide (power (8+1) j=powerAt 8 j))=true := supportRestore 8 z8 z9 c8

private theorem c9 : (List.range 126).all (inside 9)=true := by decide +kernel
private theorem row9 : (List.range 252).all (fun j => decide (power (9+1) j=powerAt 9 j))=true := supportRestore 9 z9 z10 c9

private theorem c10 : (List.range 126).all (inside 10)=true := by decide +kernel
private theorem row10 : (List.range 252).all (fun j => decide (power (10+1) j=powerAt 10 j))=true := supportRestore 10 z10 z11 c10

private theorem c11 : (List.range 126).all (inside 11)=true := by decide +kernel
private theorem row11 : (List.range 252).all (fun j => decide (power (11+1) j=powerAt 11 j))=true := supportRestore 11 z11 z12 c11

private theorem c12 : (List.range 126).all (inside 12)=true := by decide +kernel
private theorem row12 : (List.range 252).all (fun j => decide (power (12+1) j=powerAt 12 j))=true := supportRestore 12 z12 z13 c12

private theorem c13 : (List.range 126).all (inside 13)=true := by decide +kernel
private theorem row13 : (List.range 252).all (fun j => decide (power (13+1) j=powerAt 13 j))=true := supportRestore 13 z13 z14 c13

private theorem c14 : (List.range 126).all (inside 14)=true := by decide +kernel
private theorem row14 : (List.range 252).all (fun j => decide (power (14+1) j=powerAt 14 j))=true := supportRestore 14 z14 z15 c14

private theorem c15 : (List.range 126).all (inside 15)=true := by decide +kernel
private theorem row15 : (List.range 252).all (fun j => decide (power (15+1) j=powerAt 15 j))=true := supportRestore 15 z15 z16 c15

private theorem c16 : (List.range 126).all (inside 16)=true := by decide +kernel
private theorem row16 : (List.range 252).all (fun j => decide (power (16+1) j=powerAt 16 j))=true := supportRestore 16 z16 z17 c16

private theorem c17 : (List.range 126).all (inside 17)=true := by decide +kernel
private theorem row17 : (List.range 252).all (fun j => decide (power (17+1) j=powerAt 17 j))=true := supportRestore 17 z17 z18 c17

private theorem c18 : (List.range 126).all (inside 18)=true := by decide +kernel
private theorem row18 : (List.range 252).all (fun j => decide (power (18+1) j=powerAt 18 j))=true := supportRestore 18 z18 z19 c18

private theorem c19 : (List.range 126).all (inside 19)=true := by decide +kernel
private theorem row19 : (List.range 252).all (fun j => decide (power (19+1) j=powerAt 19 j))=true := supportRestore 19 z19 z20 c19

private theorem c20 : (List.range 126).all (inside 20)=true := by decide +kernel
private theorem row20 : (List.range 252).all (fun j => decide (power (20+1) j=powerAt 20 j))=true := supportRestore 20 z20 z21 c20

private theorem c21 : (List.range 126).all (inside 21)=true := by decide +kernel
private theorem row21 : (List.range 252).all (fun j => decide (power (21+1) j=powerAt 21 j))=true := supportRestore 21 z21 z22 c21

private theorem c22 : (List.range 126).all (inside 22)=true := by decide +kernel
private theorem row22 : (List.range 252).all (fun j => decide (power (22+1) j=powerAt 22 j))=true := supportRestore 22 z22 z23 c22

private theorem c23 : (List.range 126).all (inside 23)=true := by decide +kernel
private theorem row23 : (List.range 252).all (fun j => decide (power (23+1) j=powerAt 23 j))=true := supportRestore 23 z23 z24 c23

private def row (p : ℕ) := (List.range 252).all (fun j => decide (power (p+1) j=powerAt p j))
private theorem single {i : ℕ} (h : row i=true) : seg row i 1=true := by simpa only [seg,List.range_one,List.all_cons,List.all_nil,Nat.add_zero,Bool.and_true] using h

private theorem allHere : seg row 0 24=true := (join (join (join (join (single row0) (join (single row1) (single row2))) (join (single row3) (join (single row4) (single row5)))) (join (join (single row6) (join (single row7) (single row8))) (join (single row9) (join (single row10) (single row11))))) (join (join (join (single row12) (join (single row13) (single row14))) (join (single row15) (join (single row16) (single row17)))) (join (join (single row18) (join (single row19) (single row20))) (join (single row21) (join (single row22) (single row23))))))

end SparsePower
open SparsePower in
theorem solution (p : ℕ) (hl : 0 ≤ p) (hu : p < 24) :
    (List.range 252).all (fun j => decide (power (p+1) j=powerAt p j))=true := by
  have hh := List.all_eq_true.mp allHere (p-0) (List.mem_range.mpr (by omega))
  change row (0+(p-0)) = true at hh
  rwa [show 0+(p-0)=p by omega] at hh
