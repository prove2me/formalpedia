-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_primary_power_rows_225_to_251
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T19:43:07.954796+00:00
-- url     : https://prove2.me/submissions/22fbf2dc-5443-4b88-baca-5e6a6a80674c

import Definitions.Def_GrothendieckLB_Supplement_cqReplayPowers
open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadCertificate GrothendieckLB.Supplement.CQHeadArithmetic
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 120000000
namespace RowChecks

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
private def rowsF : ℕ → Bool := fun k => let p := 224+k; (List.range 252).all (fun j => decide (power (p+1) j=powerAt p j))

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

private theorem rows : (List.range 27).all rowsF = true := full (join (join (join (join rows_0 (join rows_1 rows_2)) (join rows_3 (join rows_4 rows_5))) (join (join rows_6 (join rows_7 rows_8)) (join (join rows_9 rows_10) (join rows_11 rows_12)))) (join (join (join rows_13 (join rows_14 rows_15)) (join (join rows_16 rows_17) (join rows_18 rows_19))) (join (join rows_20 (join rows_21 rows_22)) (join (join rows_23 rows_24) (join rows_25 rows_26)))))

end RowChecks
open RowChecks in
theorem solution (p : ℕ) (hl : 224≤p) (hu : p < 251) :
    (List.range 252).all (fun j => decide (power (p+1) j=powerAt p j))=true := by
  have h := List.all_eq_true.mp rows (p-224) (List.mem_range.mpr (by omega))
  change (List.range 252).all (fun j => decide (power (224+(p-224)+1) j=powerAt (224+(p-224)) j))=true at h
  rwa [show 224+(p-224)=p by omega] at h
