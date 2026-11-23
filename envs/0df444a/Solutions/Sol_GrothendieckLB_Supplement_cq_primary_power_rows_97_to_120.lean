-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_primary_power_rows_97_to_120
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:40:59.673252+00:00
-- url     : https://prove2.me/submissions/5e799b62-dff1-40fb-b265-cc056d8941bd

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

private theorem z96 : good 96=true := by decide +kernel

private theorem z97 : good 97=true := by decide +kernel

private theorem z98 : good 98=true := by decide +kernel

private theorem z99 : good 99=true := by decide +kernel

private theorem z100 : good 100=true := by decide +kernel

private theorem z101 : good 101=true := by decide +kernel

private theorem z102 : good 102=true := by decide +kernel

private theorem z103 : good 103=true := by decide +kernel

private theorem z104 : good 104=true := by decide +kernel

private theorem z105 : good 105=true := by decide +kernel

private theorem z106 : good 106=true := by decide +kernel

private theorem z107 : good 107=true := by decide +kernel

private theorem z108 : good 108=true := by decide +kernel

private theorem z109 : good 109=true := by decide +kernel

private theorem z110 : good 110=true := by decide +kernel

private theorem z111 : good 111=true := by decide +kernel

private theorem z112 : good 112=true := by decide +kernel

private theorem z113 : good 113=true := by decide +kernel

private theorem z114 : good 114=true := by decide +kernel

private theorem z115 : good 115=true := by decide +kernel

private theorem z116 : good 116=true := by decide +kernel

private theorem z117 : good 117=true := by decide +kernel

private theorem z118 : good 118=true := by decide +kernel

private theorem z119 : good 119=true := by decide +kernel

private theorem z120 : good 120=true := by decide +kernel

private theorem c96 : (List.range 126).all (inside 96)=true := by decide +kernel
private theorem row96 : (List.range 252).all (fun j => decide (power (96+1) j=powerAt 96 j))=true := supportRestore 96 z96 z97 c96

private theorem c97 : (List.range 126).all (inside 97)=true := by decide +kernel
private theorem row97 : (List.range 252).all (fun j => decide (power (97+1) j=powerAt 97 j))=true := supportRestore 97 z97 z98 c97

private theorem c98 : (List.range 126).all (inside 98)=true := by decide +kernel
private theorem row98 : (List.range 252).all (fun j => decide (power (98+1) j=powerAt 98 j))=true := supportRestore 98 z98 z99 c98

private theorem c99 : (List.range 126).all (inside 99)=true := by decide +kernel
private theorem row99 : (List.range 252).all (fun j => decide (power (99+1) j=powerAt 99 j))=true := supportRestore 99 z99 z100 c99

private theorem c100 : (List.range 126).all (inside 100)=true := by decide +kernel
private theorem row100 : (List.range 252).all (fun j => decide (power (100+1) j=powerAt 100 j))=true := supportRestore 100 z100 z101 c100

private theorem c101 : (List.range 126).all (inside 101)=true := by decide +kernel
private theorem row101 : (List.range 252).all (fun j => decide (power (101+1) j=powerAt 101 j))=true := supportRestore 101 z101 z102 c101

private theorem c102 : (List.range 126).all (inside 102)=true := by decide +kernel
private theorem row102 : (List.range 252).all (fun j => decide (power (102+1) j=powerAt 102 j))=true := supportRestore 102 z102 z103 c102

private theorem c103 : (List.range 126).all (inside 103)=true := by decide +kernel
private theorem row103 : (List.range 252).all (fun j => decide (power (103+1) j=powerAt 103 j))=true := supportRestore 103 z103 z104 c103

private theorem c104 : (List.range 126).all (inside 104)=true := by decide +kernel
private theorem row104 : (List.range 252).all (fun j => decide (power (104+1) j=powerAt 104 j))=true := supportRestore 104 z104 z105 c104

private theorem c105 : (List.range 126).all (inside 105)=true := by decide +kernel
private theorem row105 : (List.range 252).all (fun j => decide (power (105+1) j=powerAt 105 j))=true := supportRestore 105 z105 z106 c105

private theorem c106 : (List.range 126).all (inside 106)=true := by decide +kernel
private theorem row106 : (List.range 252).all (fun j => decide (power (106+1) j=powerAt 106 j))=true := supportRestore 106 z106 z107 c106

private theorem c107 : (List.range 126).all (inside 107)=true := by decide +kernel
private theorem row107 : (List.range 252).all (fun j => decide (power (107+1) j=powerAt 107 j))=true := supportRestore 107 z107 z108 c107

private theorem c108 : (List.range 126).all (inside 108)=true := by decide +kernel
private theorem row108 : (List.range 252).all (fun j => decide (power (108+1) j=powerAt 108 j))=true := supportRestore 108 z108 z109 c108

private theorem c109 : (List.range 126).all (inside 109)=true := by decide +kernel
private theorem row109 : (List.range 252).all (fun j => decide (power (109+1) j=powerAt 109 j))=true := supportRestore 109 z109 z110 c109

private theorem c110 : (List.range 126).all (inside 110)=true := by decide +kernel
private theorem row110 : (List.range 252).all (fun j => decide (power (110+1) j=powerAt 110 j))=true := supportRestore 110 z110 z111 c110

private theorem c111 : (List.range 126).all (inside 111)=true := by decide +kernel
private theorem row111 : (List.range 252).all (fun j => decide (power (111+1) j=powerAt 111 j))=true := supportRestore 111 z111 z112 c111

private theorem c112 : (List.range 126).all (inside 112)=true := by decide +kernel
private theorem row112 : (List.range 252).all (fun j => decide (power (112+1) j=powerAt 112 j))=true := supportRestore 112 z112 z113 c112

private theorem c113 : (List.range 126).all (inside 113)=true := by decide +kernel
private theorem row113 : (List.range 252).all (fun j => decide (power (113+1) j=powerAt 113 j))=true := supportRestore 113 z113 z114 c113

private theorem c114 : (List.range 126).all (inside 114)=true := by decide +kernel
private theorem row114 : (List.range 252).all (fun j => decide (power (114+1) j=powerAt 114 j))=true := supportRestore 114 z114 z115 c114

private theorem c115 : (List.range 126).all (inside 115)=true := by decide +kernel
private theorem row115 : (List.range 252).all (fun j => decide (power (115+1) j=powerAt 115 j))=true := supportRestore 115 z115 z116 c115

private theorem c116 : (List.range 126).all (inside 116)=true := by decide +kernel
private theorem row116 : (List.range 252).all (fun j => decide (power (116+1) j=powerAt 116 j))=true := supportRestore 116 z116 z117 c116

private theorem c117 : (List.range 126).all (inside 117)=true := by decide +kernel
private theorem row117 : (List.range 252).all (fun j => decide (power (117+1) j=powerAt 117 j))=true := supportRestore 117 z117 z118 c117

private theorem c118 : (List.range 126).all (inside 118)=true := by decide +kernel
private theorem row118 : (List.range 252).all (fun j => decide (power (118+1) j=powerAt 118 j))=true := supportRestore 118 z118 z119 c118

private theorem c119 : (List.range 126).all (inside 119)=true := by decide +kernel
private theorem row119 : (List.range 252).all (fun j => decide (power (119+1) j=powerAt 119 j))=true := supportRestore 119 z119 z120 c119

private def row (p : ℕ) := (List.range 252).all (fun j => decide (power (p+1) j=powerAt p j))
private theorem single {i : ℕ} (h : row i=true) : seg row i 1=true := by simpa only [seg,List.range_one,List.all_cons,List.all_nil,Nat.add_zero,Bool.and_true] using h

private theorem allHere : seg row 96 24=true := (join (join (join (join (single row96) (join (single row97) (single row98))) (join (single row99) (join (single row100) (single row101)))) (join (join (single row102) (join (single row103) (single row104))) (join (single row105) (join (single row106) (single row107))))) (join (join (join (single row108) (join (single row109) (single row110))) (join (single row111) (join (single row112) (single row113)))) (join (join (single row114) (join (single row115) (single row116))) (join (single row117) (join (single row118) (single row119))))))

end SparsePower
open SparsePower in
theorem solution (p : ℕ) (hl : 96 ≤ p) (hu : p < 120) :
    (List.range 252).all (fun j => decide (power (p+1) j=powerAt p j))=true := by
  have hh := List.all_eq_true.mp allHere (p-96) (List.mem_range.mpr (by omega))
  change row (96+(p-96)) = true at hh
  rwa [show 96+(p-96)=p by omega] at hh
