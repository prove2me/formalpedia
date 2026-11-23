-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_primary_power_rows_97_to_144
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:40:59.624622+00:00
-- url     : https://prove2.me/submissions/a4b98d88-7b14-4ac5-aabc-486aac10f07e

import Theorems.Thm_GrothendieckLB_Supplement_cq_primary_power_rows_97_to_120
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

private theorem z120 : good 120=true := by decide +kernel

private theorem z121 : good 121=true := by decide +kernel

private theorem z122 : good 122=true := by decide +kernel

private theorem z123 : good 123=true := by decide +kernel

private theorem z124 : good 124=true := by decide +kernel

private theorem z125 : good 125=true := by decide +kernel

private theorem z126 : good 126=true := by decide +kernel

private theorem z127 : good 127=true := by decide +kernel

private theorem z128 : good 128=true := by decide +kernel

private theorem z129 : good 129=true := by decide +kernel

private theorem z130 : good 130=true := by decide +kernel

private theorem z131 : good 131=true := by decide +kernel

private theorem z132 : good 132=true := by decide +kernel

private theorem z133 : good 133=true := by decide +kernel

private theorem z134 : good 134=true := by decide +kernel

private theorem z135 : good 135=true := by decide +kernel

private theorem z136 : good 136=true := by decide +kernel

private theorem z137 : good 137=true := by decide +kernel

private theorem z138 : good 138=true := by decide +kernel

private theorem z139 : good 139=true := by decide +kernel

private theorem z140 : good 140=true := by decide +kernel

private theorem z141 : good 141=true := by decide +kernel

private theorem z142 : good 142=true := by decide +kernel

private theorem z143 : good 143=true := by decide +kernel

private theorem z144 : good 144=true := by decide +kernel

private theorem c120 : (List.range 126).all (inside 120)=true := by decide +kernel
private theorem row120 : (List.range 252).all (fun j => decide (power (120+1) j=powerAt 120 j))=true := supportRestore 120 z120 z121 c120

private theorem c121 : (List.range 126).all (inside 121)=true := by decide +kernel
private theorem row121 : (List.range 252).all (fun j => decide (power (121+1) j=powerAt 121 j))=true := supportRestore 121 z121 z122 c121

private theorem c122 : (List.range 126).all (inside 122)=true := by decide +kernel
private theorem row122 : (List.range 252).all (fun j => decide (power (122+1) j=powerAt 122 j))=true := supportRestore 122 z122 z123 c122

private theorem c123 : (List.range 126).all (inside 123)=true := by decide +kernel
private theorem row123 : (List.range 252).all (fun j => decide (power (123+1) j=powerAt 123 j))=true := supportRestore 123 z123 z124 c123

private theorem c124 : (List.range 126).all (inside 124)=true := by decide +kernel
private theorem row124 : (List.range 252).all (fun j => decide (power (124+1) j=powerAt 124 j))=true := supportRestore 124 z124 z125 c124

private theorem c125 : (List.range 126).all (inside 125)=true := by decide +kernel
private theorem row125 : (List.range 252).all (fun j => decide (power (125+1) j=powerAt 125 j))=true := supportRestore 125 z125 z126 c125

private theorem c126 : (List.range 126).all (inside 126)=true := by decide +kernel
private theorem row126 : (List.range 252).all (fun j => decide (power (126+1) j=powerAt 126 j))=true := supportRestore 126 z126 z127 c126

private theorem c127 : (List.range 126).all (inside 127)=true := by decide +kernel
private theorem row127 : (List.range 252).all (fun j => decide (power (127+1) j=powerAt 127 j))=true := supportRestore 127 z127 z128 c127

private theorem c128 : (List.range 126).all (inside 128)=true := by decide +kernel
private theorem row128 : (List.range 252).all (fun j => decide (power (128+1) j=powerAt 128 j))=true := supportRestore 128 z128 z129 c128

private theorem c129 : (List.range 126).all (inside 129)=true := by decide +kernel
private theorem row129 : (List.range 252).all (fun j => decide (power (129+1) j=powerAt 129 j))=true := supportRestore 129 z129 z130 c129

private theorem c130 : (List.range 126).all (inside 130)=true := by decide +kernel
private theorem row130 : (List.range 252).all (fun j => decide (power (130+1) j=powerAt 130 j))=true := supportRestore 130 z130 z131 c130

private theorem c131 : (List.range 126).all (inside 131)=true := by decide +kernel
private theorem row131 : (List.range 252).all (fun j => decide (power (131+1) j=powerAt 131 j))=true := supportRestore 131 z131 z132 c131

private theorem c132 : (List.range 126).all (inside 132)=true := by decide +kernel
private theorem row132 : (List.range 252).all (fun j => decide (power (132+1) j=powerAt 132 j))=true := supportRestore 132 z132 z133 c132

private theorem c133 : (List.range 126).all (inside 133)=true := by decide +kernel
private theorem row133 : (List.range 252).all (fun j => decide (power (133+1) j=powerAt 133 j))=true := supportRestore 133 z133 z134 c133

private theorem c134 : (List.range 126).all (inside 134)=true := by decide +kernel
private theorem row134 : (List.range 252).all (fun j => decide (power (134+1) j=powerAt 134 j))=true := supportRestore 134 z134 z135 c134

private theorem c135 : (List.range 126).all (inside 135)=true := by decide +kernel
private theorem row135 : (List.range 252).all (fun j => decide (power (135+1) j=powerAt 135 j))=true := supportRestore 135 z135 z136 c135

private theorem c136 : (List.range 126).all (inside 136)=true := by decide +kernel
private theorem row136 : (List.range 252).all (fun j => decide (power (136+1) j=powerAt 136 j))=true := supportRestore 136 z136 z137 c136

private theorem c137 : (List.range 126).all (inside 137)=true := by decide +kernel
private theorem row137 : (List.range 252).all (fun j => decide (power (137+1) j=powerAt 137 j))=true := supportRestore 137 z137 z138 c137

private theorem c138 : (List.range 126).all (inside 138)=true := by decide +kernel
private theorem row138 : (List.range 252).all (fun j => decide (power (138+1) j=powerAt 138 j))=true := supportRestore 138 z138 z139 c138

private theorem c139 : (List.range 126).all (inside 139)=true := by decide +kernel
private theorem row139 : (List.range 252).all (fun j => decide (power (139+1) j=powerAt 139 j))=true := supportRestore 139 z139 z140 c139

private theorem c140 : (List.range 126).all (inside 140)=true := by decide +kernel
private theorem row140 : (List.range 252).all (fun j => decide (power (140+1) j=powerAt 140 j))=true := supportRestore 140 z140 z141 c140

private theorem c141 : (List.range 126).all (inside 141)=true := by decide +kernel
private theorem row141 : (List.range 252).all (fun j => decide (power (141+1) j=powerAt 141 j))=true := supportRestore 141 z141 z142 c141

private theorem c142 : (List.range 126).all (inside 142)=true := by decide +kernel
private theorem row142 : (List.range 252).all (fun j => decide (power (142+1) j=powerAt 142 j))=true := supportRestore 142 z142 z143 c142

private theorem c143 : (List.range 126).all (inside 143)=true := by decide +kernel
private theorem row143 : (List.range 252).all (fun j => decide (power (143+1) j=powerAt 143 j))=true := supportRestore 143 z143 z144 c143

private def row (p : ℕ) := (List.range 252).all (fun j => decide (power (p+1) j=powerAt p j))
private theorem single {i : ℕ} (h : row i=true) : seg row i 1=true := by simpa only [seg,List.range_one,List.all_cons,List.all_nil,Nat.add_zero,Bool.and_true] using h

private theorem allHere : seg row 120 24=true := (join (join (join (join (single row120) (join (single row121) (single row122))) (join (single row123) (join (single row124) (single row125)))) (join (join (single row126) (join (single row127) (single row128))) (join (single row129) (join (single row130) (single row131))))) (join (join (join (single row132) (join (single row133) (single row134))) (join (single row135) (join (single row136) (single row137)))) (join (join (single row138) (join (single row139) (single row140))) (join (single row141) (join (single row142) (single row143))))))

end SparsePower
open SparsePower in
private theorem upper (p : ℕ) (hl : 120 ≤ p) (hu : p < 144) :
    (List.range 252).all (fun j => decide (power (p+1) j=powerAt p j))=true := by
  have hh := List.all_eq_true.mp allHere (p-120) (List.mem_range.mpr (by omega))
  change row (120+(p-120)) = true at hh
  rwa [show 120+(p-120)=p by omega] at hh

theorem solution (p : ℕ) (hl : 96 ≤ p) (hu : p < 144) :
    (List.range 252).all (fun j => decide (power (p+1) j=powerAt p j))=true := by
  by_cases hm : p < 120
  · exact GrothendieckLB.Supplement.cq_primary_power_rows_97_to_120 p hl hm
  · exact upper p (by omega) hu
