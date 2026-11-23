-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_center_product_terminal_checks
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:19:08.680374+00:00
-- url     : https://prove2.me/submissions/b6451a47-7674-4e4c-bc47-7bd7247bc566

import Mathlib
import Definitions.Def_GrothendieckLB_Supplement_cqHeadSumProducts
open GrothendieckLB.Supplement CQHeadArithmetic CQHeadCertificate CQHeadSum
set_option maxHeartbeats 150000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace ProductEvidence

private def seq (f : ℕ → ℤ) (n s : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | m+1 => f s+base*seq f m (s+1)

private theorem seq_eq (f : ℕ → ℤ) (n s : ℕ) :
    seq f n s=pack base (fun k => f (s+k)) n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [seq,pack,ih]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]


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

private def evalSum (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n+1 => evalSum f n+f n
private theorem evalSum_eq (f : ℕ → ℤ) (n : ℕ) : evalSum f n=∑ i ∈ Finset.range n,f i := by
  induction n with
  | zero => simp [evalSum]
  | succ n ih => rw [evalSum,ih,Finset.sum_range_succ]
private def boundV (m : ℕ) := decide (|value m| ≤ 2^320)
private def lastV (j : ℕ) := decide ((|value (2*j+3)|+2^176)*10^40 ≤
      4*coefficientScale^2*2*314159265358979323846*(cqHeadUnits[j]?.getD 0))
private theorem boundV0to15 : seg boundV 0 15=true := by decide +kernel
private theorem boundV15to31 : seg boundV 15 16=true := by decide +kernel
private theorem boundV0to31 : seg boundV 0 31=true := join (l:=0) (n:=15) (m:=16) boundV0to15 boundV15to31
private theorem boundV31to47 : seg boundV 31 16=true := by decide +kernel
private theorem boundV47to63 : seg boundV 47 16=true := by decide +kernel
private theorem boundV31to63 : seg boundV 31 32=true := join (l:=31) (n:=16) (m:=16) boundV31to47 boundV47to63
private theorem boundV0to63 : seg boundV 0 63=true := join (l:=0) (n:=31) (m:=32) boundV0to31 boundV31to63
private theorem boundV63to78 : seg boundV 63 15=true := by decide +kernel
private theorem boundV78to94 : seg boundV 78 16=true := by decide +kernel
private theorem boundV63to94 : seg boundV 63 31=true := join (l:=63) (n:=15) (m:=16) boundV63to78 boundV78to94
private theorem boundV94to110 : seg boundV 94 16=true := by decide +kernel
private theorem boundV110to126 : seg boundV 110 16=true := by decide +kernel
private theorem boundV94to126 : seg boundV 94 32=true := join (l:=94) (n:=16) (m:=16) boundV94to110 boundV110to126
private theorem boundV63to126 : seg boundV 63 63=true := join (l:=63) (n:=31) (m:=32) boundV63to94 boundV94to126
private theorem boundV0to126 : seg boundV 0 126=true := join (l:=0) (n:=63) (m:=63) boundV0to63 boundV63to126
private theorem boundV126to141 : seg boundV 126 15=true := by decide +kernel
private theorem boundV141to157 : seg boundV 141 16=true := by decide +kernel
private theorem boundV126to157 : seg boundV 126 31=true := join (l:=126) (n:=15) (m:=16) boundV126to141 boundV141to157
private theorem boundV157to173 : seg boundV 157 16=true := by decide +kernel
private theorem boundV173to189 : seg boundV 173 16=true := by decide +kernel
private theorem boundV157to189 : seg boundV 157 32=true := join (l:=157) (n:=16) (m:=16) boundV157to173 boundV173to189
private theorem boundV126to189 : seg boundV 126 63=true := join (l:=126) (n:=31) (m:=32) boundV126to157 boundV157to189
private theorem boundV189to204 : seg boundV 189 15=true := by decide +kernel
private theorem boundV204to220 : seg boundV 204 16=true := by decide +kernel
private theorem boundV189to220 : seg boundV 189 31=true := join (l:=189) (n:=15) (m:=16) boundV189to204 boundV204to220
private theorem boundV220to236 : seg boundV 220 16=true := by decide +kernel
private theorem boundV236to252 : seg boundV 236 16=true := by decide +kernel
private theorem boundV220to252 : seg boundV 220 32=true := join (l:=220) (n:=16) (m:=16) boundV220to236 boundV236to252
private theorem boundV189to252 : seg boundV 189 63=true := join (l:=189) (n:=31) (m:=32) boundV189to220 boundV220to252
private theorem boundV126to252 : seg boundV 126 126=true := join (l:=126) (n:=63) (m:=63) boundV126to189 boundV189to252
private theorem boundV0to252 : seg boundV 0 252=true := join (l:=0) (n:=126) (m:=126) boundV0to126 boundV126to252
private theorem allboundV : (List.range 252).all boundV=true := full boundV0to252
private theorem lastV0to15 : seg lastV 0 15=true := by decide +kernel
private theorem lastV15to31 : seg lastV 15 16=true := by decide +kernel
private theorem lastV0to31 : seg lastV 0 31=true := join (l:=0) (n:=15) (m:=16) lastV0to15 lastV15to31
private theorem lastV31to46 : seg lastV 31 15=true := by decide +kernel
private theorem lastV46to62 : seg lastV 46 16=true := by decide +kernel
private theorem lastV31to62 : seg lastV 31 31=true := join (l:=31) (n:=15) (m:=16) lastV31to46 lastV46to62
private theorem lastV0to62 : seg lastV 0 62=true := join (l:=0) (n:=31) (m:=31) lastV0to31 lastV31to62
private theorem lastV62to77 : seg lastV 62 15=true := by decide +kernel
private theorem lastV77to93 : seg lastV 77 16=true := by decide +kernel
private theorem lastV62to93 : seg lastV 62 31=true := join (l:=62) (n:=15) (m:=16) lastV62to77 lastV77to93
private theorem lastV93to109 : seg lastV 93 16=true := by decide +kernel
private theorem lastV109to125 : seg lastV 109 16=true := by decide +kernel
private theorem lastV93to125 : seg lastV 93 32=true := join (l:=93) (n:=16) (m:=16) lastV93to109 lastV109to125
private theorem lastV62to125 : seg lastV 62 63=true := join (l:=62) (n:=31) (m:=32) lastV62to93 lastV93to125
private theorem lastV0to125 : seg lastV 0 125=true := join (l:=0) (n:=62) (m:=63) lastV0to62 lastV62to125
private theorem alllastV : (List.range 125).all lastV=true := full lastV0to125

private def recordedSum : ℤ := eval% evalSum row 252
private def recordedDigits : ℤ := eval% seq value 252 0
private theorem hsum : evalSum row 252=recordedSum := by decide +kernel
private theorem hdig : seq value 252 0=recordedDigits := by decide +kernel
end ProductEvidence
open ProductEvidence in
theorem solution :
    base^252 ∣ pack base value 252-(∑ a ∈ Finset.range 252,row a) ∧
    (∀ m < 252, |value m| ≤ 2^320) ∧
    ∀ j < 125, (|value (2*j+3)|+2^176)*10^40 ≤
      4*coefficientScale^2*2*314159265358979323846*(cqHeadUnits[j]?.getD 0) := by
  refine ⟨?_,fun m hm => of_decide_eq_true (List.all_eq_true.mp allboundV m (List.mem_range.mpr hm)),
    fun j hj => of_decide_eq_true (List.all_eq_true.mp alllastV j (List.mem_range.mpr hj))⟩
  have he := seq_eq value 252 0
  simp only [Nat.zero_add] at he
  rw [←he,hdig,←evalSum_eq,hsum]
  decide +kernel
