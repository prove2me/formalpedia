-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_certified_125_terminal_comparisons
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:05:49.393524+00:00
-- url     : https://prove2.me/submissions/d30e44cb-c449-4a08-9fdd-d0b757236a88

import Definitions.Def_GrothendieckLB_Supplement_cqReplaySums
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
private def totalsAllF : ℕ → Bool := fun j => let v := sumIntervals (savedPart j) (2*j+4); max (-v.lo) v.hi * 10^40 ≤ coefficientScale*2*314159265358979323846*(cqHeadUnits[j]?.getD 0)

private theorem totalsAll_0 : seg totalsAllF 0 4=true := by decide +kernel

private theorem totalsAll_4 : seg totalsAllF 4 4=true := by decide +kernel

private theorem totalsAll_8 : seg totalsAllF 8 4=true := by decide +kernel

private theorem totalsAll_12 : seg totalsAllF 12 4=true := by decide +kernel

private theorem totalsAll_16 : seg totalsAllF 16 4=true := by decide +kernel

private theorem totalsAll_20 : seg totalsAllF 20 4=true := by decide +kernel

private theorem totalsAll_24 : seg totalsAllF 24 4=true := by decide +kernel

private theorem totalsAll_28 : seg totalsAllF 28 4=true := by decide +kernel

private theorem totalsAll_32 : seg totalsAllF 32 4=true := by decide +kernel

private theorem totalsAll_36 : seg totalsAllF 36 4=true := by decide +kernel

private theorem totalsAll_40 : seg totalsAllF 40 4=true := by decide +kernel

private theorem totalsAll_44 : seg totalsAllF 44 4=true := by decide +kernel

private theorem totalsAll_48 : seg totalsAllF 48 4=true := by decide +kernel

private theorem totalsAll_52 : seg totalsAllF 52 4=true := by decide +kernel

private theorem totalsAll_56 : seg totalsAllF 56 4=true := by decide +kernel

private theorem totalsAll_60 : seg totalsAllF 60 4=true := by decide +kernel

private theorem totalsAll_64 : seg totalsAllF 64 4=true := by decide +kernel

private theorem totalsAll_68 : seg totalsAllF 68 4=true := by decide +kernel

private theorem totalsAll_72 : seg totalsAllF 72 4=true := by decide +kernel

private theorem totalsAll_76 : seg totalsAllF 76 4=true := by decide +kernel

private theorem totalsAll_80 : seg totalsAllF 80 4=true := by decide +kernel

private theorem totalsAll_84 : seg totalsAllF 84 4=true := by decide +kernel

private theorem totalsAll_88 : seg totalsAllF 88 4=true := by decide +kernel

private theorem totalsAll_92 : seg totalsAllF 92 4=true := by decide +kernel

private theorem totalsAll_96 : seg totalsAllF 96 4=true := by decide +kernel

private theorem totalsAll_100 : seg totalsAllF 100 4=true := by decide +kernel

private theorem totalsAll_104 : seg totalsAllF 104 4=true := by decide +kernel

private theorem totalsAll_108 : seg totalsAllF 108 4=true := by decide +kernel

private theorem totalsAll_112 : seg totalsAllF 112 4=true := by decide +kernel

private theorem totalsAll_116 : seg totalsAllF 116 4=true := by decide +kernel

private theorem totalsAll_120 : seg totalsAllF 120 4=true := by decide +kernel

private theorem totalsAll_124 : seg totalsAllF 124 1=true := by decide +kernel

private theorem totalsAll : (List.range 125).all totalsAllF = true := full (join (join (join (join (join totalsAll_0 totalsAll_4) (join totalsAll_8 totalsAll_12)) (join (join totalsAll_16 totalsAll_20) (join totalsAll_24 totalsAll_28))) (join (join (join totalsAll_32 totalsAll_36) (join totalsAll_40 totalsAll_44)) (join (join totalsAll_48 totalsAll_52) (join totalsAll_56 totalsAll_60)))) (join (join (join (join totalsAll_64 totalsAll_68) (join totalsAll_72 totalsAll_76)) (join (join totalsAll_80 totalsAll_84) (join totalsAll_88 totalsAll_92))) (join (join (join totalsAll_96 totalsAll_100) (join totalsAll_104 totalsAll_108)) (join (join totalsAll_112 totalsAll_116) (join totalsAll_120 totalsAll_124)))))


end RowChecks
open RowChecks in
theorem solution : totalChecks=true := totalsAll
