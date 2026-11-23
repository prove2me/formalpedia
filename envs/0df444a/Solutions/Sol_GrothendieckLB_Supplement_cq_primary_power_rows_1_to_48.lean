-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_primary_power_rows_1_to_48
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:40:59.7727+00:00
-- url     : https://prove2.me/submissions/d9613489-6174-47a9-bd8e-b6baf80bcde4

import Theorems.Thm_GrothendieckLB_Supplement_cq_primary_power_rows_1_to_24
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

private theorem z24 : good 24=true := by decide +kernel

private theorem z25 : good 25=true := by decide +kernel

private theorem z26 : good 26=true := by decide +kernel

private theorem z27 : good 27=true := by decide +kernel

private theorem z28 : good 28=true := by decide +kernel

private theorem z29 : good 29=true := by decide +kernel

private theorem z30 : good 30=true := by decide +kernel

private theorem z31 : good 31=true := by decide +kernel

private theorem z32 : good 32=true := by decide +kernel

private theorem z33 : good 33=true := by decide +kernel

private theorem z34 : good 34=true := by decide +kernel

private theorem z35 : good 35=true := by decide +kernel

private theorem z36 : good 36=true := by decide +kernel

private theorem z37 : good 37=true := by decide +kernel

private theorem z38 : good 38=true := by decide +kernel

private theorem z39 : good 39=true := by decide +kernel

private theorem z40 : good 40=true := by decide +kernel

private theorem z41 : good 41=true := by decide +kernel

private theorem z42 : good 42=true := by decide +kernel

private theorem z43 : good 43=true := by decide +kernel

private theorem z44 : good 44=true := by decide +kernel

private theorem z45 : good 45=true := by decide +kernel

private theorem z46 : good 46=true := by decide +kernel

private theorem z47 : good 47=true := by decide +kernel

private theorem z48 : good 48=true := by decide +kernel

private theorem c24 : (List.range 126).all (inside 24)=true := by decide +kernel
private theorem row24 : (List.range 252).all (fun j => decide (power (24+1) j=powerAt 24 j))=true := supportRestore 24 z24 z25 c24

private theorem c25 : (List.range 126).all (inside 25)=true := by decide +kernel
private theorem row25 : (List.range 252).all (fun j => decide (power (25+1) j=powerAt 25 j))=true := supportRestore 25 z25 z26 c25

private theorem c26 : (List.range 126).all (inside 26)=true := by decide +kernel
private theorem row26 : (List.range 252).all (fun j => decide (power (26+1) j=powerAt 26 j))=true := supportRestore 26 z26 z27 c26

private theorem c27 : (List.range 126).all (inside 27)=true := by decide +kernel
private theorem row27 : (List.range 252).all (fun j => decide (power (27+1) j=powerAt 27 j))=true := supportRestore 27 z27 z28 c27

private theorem c28 : (List.range 126).all (inside 28)=true := by decide +kernel
private theorem row28 : (List.range 252).all (fun j => decide (power (28+1) j=powerAt 28 j))=true := supportRestore 28 z28 z29 c28

private theorem c29 : (List.range 126).all (inside 29)=true := by decide +kernel
private theorem row29 : (List.range 252).all (fun j => decide (power (29+1) j=powerAt 29 j))=true := supportRestore 29 z29 z30 c29

private theorem c30 : (List.range 126).all (inside 30)=true := by decide +kernel
private theorem row30 : (List.range 252).all (fun j => decide (power (30+1) j=powerAt 30 j))=true := supportRestore 30 z30 z31 c30

private theorem c31 : (List.range 126).all (inside 31)=true := by decide +kernel
private theorem row31 : (List.range 252).all (fun j => decide (power (31+1) j=powerAt 31 j))=true := supportRestore 31 z31 z32 c31

private theorem c32 : (List.range 126).all (inside 32)=true := by decide +kernel
private theorem row32 : (List.range 252).all (fun j => decide (power (32+1) j=powerAt 32 j))=true := supportRestore 32 z32 z33 c32

private theorem c33 : (List.range 126).all (inside 33)=true := by decide +kernel
private theorem row33 : (List.range 252).all (fun j => decide (power (33+1) j=powerAt 33 j))=true := supportRestore 33 z33 z34 c33

private theorem c34 : (List.range 126).all (inside 34)=true := by decide +kernel
private theorem row34 : (List.range 252).all (fun j => decide (power (34+1) j=powerAt 34 j))=true := supportRestore 34 z34 z35 c34

private theorem c35 : (List.range 126).all (inside 35)=true := by decide +kernel
private theorem row35 : (List.range 252).all (fun j => decide (power (35+1) j=powerAt 35 j))=true := supportRestore 35 z35 z36 c35

private theorem c36 : (List.range 126).all (inside 36)=true := by decide +kernel
private theorem row36 : (List.range 252).all (fun j => decide (power (36+1) j=powerAt 36 j))=true := supportRestore 36 z36 z37 c36

private theorem c37 : (List.range 126).all (inside 37)=true := by decide +kernel
private theorem row37 : (List.range 252).all (fun j => decide (power (37+1) j=powerAt 37 j))=true := supportRestore 37 z37 z38 c37

private theorem c38 : (List.range 126).all (inside 38)=true := by decide +kernel
private theorem row38 : (List.range 252).all (fun j => decide (power (38+1) j=powerAt 38 j))=true := supportRestore 38 z38 z39 c38

private theorem c39 : (List.range 126).all (inside 39)=true := by decide +kernel
private theorem row39 : (List.range 252).all (fun j => decide (power (39+1) j=powerAt 39 j))=true := supportRestore 39 z39 z40 c39

private theorem c40 : (List.range 126).all (inside 40)=true := by decide +kernel
private theorem row40 : (List.range 252).all (fun j => decide (power (40+1) j=powerAt 40 j))=true := supportRestore 40 z40 z41 c40

private theorem c41 : (List.range 126).all (inside 41)=true := by decide +kernel
private theorem row41 : (List.range 252).all (fun j => decide (power (41+1) j=powerAt 41 j))=true := supportRestore 41 z41 z42 c41

private theorem c42 : (List.range 126).all (inside 42)=true := by decide +kernel
private theorem row42 : (List.range 252).all (fun j => decide (power (42+1) j=powerAt 42 j))=true := supportRestore 42 z42 z43 c42

private theorem c43 : (List.range 126).all (inside 43)=true := by decide +kernel
private theorem row43 : (List.range 252).all (fun j => decide (power (43+1) j=powerAt 43 j))=true := supportRestore 43 z43 z44 c43

private theorem c44 : (List.range 126).all (inside 44)=true := by decide +kernel
private theorem row44 : (List.range 252).all (fun j => decide (power (44+1) j=powerAt 44 j))=true := supportRestore 44 z44 z45 c44

private theorem c45 : (List.range 126).all (inside 45)=true := by decide +kernel
private theorem row45 : (List.range 252).all (fun j => decide (power (45+1) j=powerAt 45 j))=true := supportRestore 45 z45 z46 c45

private theorem c46 : (List.range 126).all (inside 46)=true := by decide +kernel
private theorem row46 : (List.range 252).all (fun j => decide (power (46+1) j=powerAt 46 j))=true := supportRestore 46 z46 z47 c46

private theorem c47 : (List.range 126).all (inside 47)=true := by decide +kernel
private theorem row47 : (List.range 252).all (fun j => decide (power (47+1) j=powerAt 47 j))=true := supportRestore 47 z47 z48 c47

private def row (p : ℕ) := (List.range 252).all (fun j => decide (power (p+1) j=powerAt p j))
private theorem single {i : ℕ} (h : row i=true) : seg row i 1=true := by simpa only [seg,List.range_one,List.all_cons,List.all_nil,Nat.add_zero,Bool.and_true] using h

private theorem allHere : seg row 24 24=true := (join (join (join (join (single row24) (join (single row25) (single row26))) (join (single row27) (join (single row28) (single row29)))) (join (join (single row30) (join (single row31) (single row32))) (join (single row33) (join (single row34) (single row35))))) (join (join (join (single row36) (join (single row37) (single row38))) (join (single row39) (join (single row40) (single row41)))) (join (join (single row42) (join (single row43) (single row44))) (join (single row45) (join (single row46) (single row47))))))

end SparsePower
open SparsePower in
private theorem upper (p : ℕ) (hl : 24 ≤ p) (hu : p < 48) :
    (List.range 252).all (fun j => decide (power (p+1) j=powerAt p j))=true := by
  have hh := List.all_eq_true.mp allHere (p-24) (List.mem_range.mpr (by omega))
  change row (24+(p-24)) = true at hh
  rwa [show 24+(p-24)=p by omega] at hh

theorem solution (p : ℕ) (hl : 0 ≤ p) (hu : p < 48) :
    (List.range 252).all (fun j => decide (power (p+1) j=powerAt p j))=true := by
  by_cases hm : p < 24
  · exact GrothendieckLB.Supplement.cq_primary_power_rows_1_to_24 p hl hm
  · exact upper p (by omega) hu
