-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_certified_zeroth_hermite_and_primary_rows
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:06:58.31258+00:00
-- url     : https://prove2.me/submissions/4b4c827a-5319-4d17-8f54-3bbee41c855b

import Definitions.Def_GrothendieckLB_Supplement_cqReplayInitial
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
private def initialAllF : ℕ → Bool := fun b => decide (weight 0 b=zeroWeightAt b ∧ power 0 b=(if b=0 then fixed coefficientScale else zeroInterval))

private theorem initialAll_0 : seg initialAllF 0 16=true := by decide +kernel

private theorem initialAll_16 : seg initialAllF 16 16=true := by decide +kernel

private theorem initialAll_32 : seg initialAllF 32 16=true := by decide +kernel

private theorem initialAll_48 : seg initialAllF 48 16=true := by decide +kernel

private theorem initialAll_64 : seg initialAllF 64 16=true := by decide +kernel

private theorem initialAll_80 : seg initialAllF 80 16=true := by decide +kernel

private theorem initialAll_96 : seg initialAllF 96 16=true := by decide +kernel

private theorem initialAll_112 : seg initialAllF 112 16=true := by decide +kernel

private theorem initialAll_128 : seg initialAllF 128 16=true := by decide +kernel

private theorem initialAll_144 : seg initialAllF 144 16=true := by decide +kernel

private theorem initialAll_160 : seg initialAllF 160 16=true := by decide +kernel

private theorem initialAll_176 : seg initialAllF 176 16=true := by decide +kernel

private theorem initialAll_192 : seg initialAllF 192 16=true := by decide +kernel

private theorem initialAll_208 : seg initialAllF 208 16=true := by decide +kernel

private theorem initialAll_224 : seg initialAllF 224 16=true := by decide +kernel

private theorem initialAll_240 : seg initialAllF 240 12=true := by decide +kernel

private theorem initialAll : (List.range 252).all initialAllF = true := full (join (join (join (join initialAll_0 initialAll_16) (join initialAll_32 initialAll_48)) (join (join initialAll_64 initialAll_80) (join initialAll_96 initialAll_112))) (join (join (join initialAll_128 initialAll_144) (join initialAll_160 initialAll_176)) (join (join initialAll_192 initialAll_208) (join initialAll_224 initialAll_240))))


end RowChecks
open RowChecks in
theorem solution : initialChecks=true := by
  apply Bool.and_eq_true_iff.mpr
  exact ⟨Bool.and_eq_true_iff.mpr ⟨by decide +kernel,by decide +kernel⟩,initialAll⟩
