-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_primary_power_rows_145_to_192
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:13:30.427603+00:00
-- url     : https://prove2.me/submissions/43b3946d-ff2e-4211-9c99-b0e1ea114fd1

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

private def rowsF : ℕ → Bool := fun k => (List.range 126).all (encodedCell (144+k))

private theorem rows_0 : seg rowsF 0 1=true := by decide +kernel

private theorem rows_1 : seg rowsF 1 1=true := by decide +kernel

private theorem rows_2 : seg rowsF 2 1=true := by decide +kernel

private theorem rows_3 : seg rowsF 3 1=true := by decide +kernel

private theorem rows_4 : seg rowsF 4 1=true := by decide +kernel

private theorem rows_5 : seg rowsF 5 1=true := by decide +kernel

private theorem rows_6 : seg rowsF 6 1=true := by decide +kernel

private theorem rows_7 : seg rowsF 7 1=true := by decide +kernel

private theorem rows_8 : seg rowsF 8 1=true := by decide +kernel

private theorem rows_9 : seg rowsF 9 1=true := by decide +kernel

private theorem rows_10 : seg rowsF 10 1=true := by decide +kernel

private theorem rows_11 : seg rowsF 11 1=true := by decide +kernel

private theorem rows_12 : seg rowsF 12 1=true := by decide +kernel

private theorem rows_13 : seg rowsF 13 1=true := by decide +kernel

private theorem rows_14 : seg rowsF 14 1=true := by decide +kernel

private theorem rows_15 : seg rowsF 15 1=true := by decide +kernel

private theorem rows_16 : seg rowsF 16 1=true := by decide +kernel

private theorem rows_17 : seg rowsF 17 1=true := by decide +kernel

private theorem rows_18 : seg rowsF 18 1=true := by decide +kernel

private theorem rows_19 : seg rowsF 19 1=true := by decide +kernel

private theorem rows_20 : seg rowsF 20 1=true := by decide +kernel

private theorem rows_21 : seg rowsF 21 1=true := by decide +kernel

private theorem rows_22 : seg rowsF 22 1=true := by decide +kernel

private theorem rows_23 : seg rowsF 23 1=true := by decide +kernel

private theorem rows_24 : seg rowsF 24 1=true := by decide +kernel

private theorem rows_25 : seg rowsF 25 1=true := by decide +kernel

private theorem rows_26 : seg rowsF 26 1=true := by decide +kernel

private theorem rows_27 : seg rowsF 27 1=true := by decide +kernel

private theorem rows_28 : seg rowsF 28 1=true := by decide +kernel

private theorem rows_29 : seg rowsF 29 1=true := by decide +kernel

private theorem rows_30 : seg rowsF 30 1=true := by decide +kernel

private theorem rows_31 : seg rowsF 31 1=true := by decide +kernel

private theorem rows_32 : seg rowsF 32 1=true := by decide +kernel

private theorem rows_33 : seg rowsF 33 1=true := by decide +kernel

private theorem rows_34 : seg rowsF 34 1=true := by decide +kernel

private theorem rows_35 : seg rowsF 35 1=true := by decide +kernel

private theorem rows_36 : seg rowsF 36 1=true := by decide +kernel

private theorem rows_37 : seg rowsF 37 1=true := by decide +kernel

private theorem rows_38 : seg rowsF 38 1=true := by decide +kernel

private theorem rows_39 : seg rowsF 39 1=true := by decide +kernel

private theorem rows_40 : seg rowsF 40 1=true := by decide +kernel

private theorem rows_41 : seg rowsF 41 1=true := by decide +kernel

private theorem rows_42 : seg rowsF 42 1=true := by decide +kernel

private theorem rows_43 : seg rowsF 43 1=true := by decide +kernel

private theorem rows_44 : seg rowsF 44 1=true := by decide +kernel

private theorem rows_45 : seg rowsF 45 1=true := by decide +kernel

private theorem rows_46 : seg rowsF 46 1=true := by decide +kernel

private theorem rows_47 : seg rowsF 47 1=true := by decide +kernel

private theorem rows : (List.range 48).all rowsF = true := full (join (join (join (join (join rows_0 (join rows_1 rows_2)) (join rows_3 (join rows_4 rows_5))) (join (join rows_6 (join rows_7 rows_8)) (join rows_9 (join rows_10 rows_11)))) (join (join (join rows_12 (join rows_13 rows_14)) (join rows_15 (join rows_16 rows_17))) (join (join rows_18 (join rows_19 rows_20)) (join rows_21 (join rows_22 rows_23))))) (join (join (join (join rows_24 (join rows_25 rows_26)) (join rows_27 (join rows_28 rows_29))) (join (join rows_30 (join rows_31 rows_32)) (join rows_33 (join rows_34 rows_35)))) (join (join (join rows_36 (join rows_37 rows_38)) (join rows_39 (join rows_40 rows_41))) (join (join rows_42 (join rows_43 rows_44)) (join rows_45 (join rows_46 rows_47))))))

end SparsePower
open SparsePower in
theorem solution (p : ℕ) (hl : 144 ≤ p) (hu : p < 192) :
    (List.range 252).all (fun j => decide (power (p+1) j=powerAt p j))=true := by
  apply restore
  have h := List.all_eq_true.mp rows (p-144) (List.mem_range.mpr (by omega))
  change (List.range 126).all (encodedCell (144+(p-144)))=true at h
  rwa [show 144+(p-144)=p by omega] at h
