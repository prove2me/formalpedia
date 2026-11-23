-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_certified_raw_moment_and_factorial_tables
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:06:08.08464+00:00
-- url     : https://prove2.me/submissions/0570f71f-ad5a-4fa5-9d74-e7269ba98c46

import Definitions.Def_GrothendieckLB_Supplement_cqReplayMoments
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
private def rawAllF : ℕ → Bool := rawOK

private theorem rawAll_0 : seg rawAllF 0 64=true := by decide +kernel

private theorem rawAll_64 : seg rawAllF 64 64=true := by decide +kernel

private theorem rawAll_128 : seg rawAllF 128 64=true := by decide +kernel

private theorem rawAll_192 : seg rawAllF 192 64=true := by decide +kernel

private theorem rawAll_256 : seg rawAllF 256 64=true := by decide +kernel

private theorem rawAll_320 : seg rawAllF 320 64=true := by decide +kernel

private theorem rawAll_384 : seg rawAllF 384 64=true := by decide +kernel

private theorem rawAll_448 : seg rawAllF 448 64=true := by decide +kernel

private theorem rawAll_512 : seg rawAllF 512 64=true := by decide +kernel

private theorem rawAll_576 : seg rawAllF 576 64=true := by decide +kernel

private theorem rawAll_640 : seg rawAllF 640 64=true := by decide +kernel

private theorem rawAll_704 : seg rawAllF 704 44=true := by decide +kernel

private theorem rawAll : (List.range 748).all rawAllF = true := full (join (join (join rawAll_0 (join rawAll_64 rawAll_128)) (join rawAll_192 (join rawAll_256 rawAll_320))) (join (join rawAll_384 (join rawAll_448 rawAll_512)) (join rawAll_576 (join rawAll_640 rawAll_704))))

private def factAllF : ℕ → Bool := factOK

private theorem factAll_0 : seg factAllF 0 64=true := by decide +kernel

private theorem factAll_64 : seg factAllF 64 64=true := by decide +kernel

private theorem factAll_128 : seg factAllF 128 64=true := by decide +kernel

private theorem factAll_192 : seg factAllF 192 64=true := by decide +kernel

private theorem factAll_256 : seg factAllF 256 64=true := by decide +kernel

private theorem factAll_320 : seg factAllF 320 64=true := by decide +kernel

private theorem factAll_384 : seg factAllF 384 64=true := by decide +kernel

private theorem factAll_448 : seg factAllF 448 64=true := by decide +kernel

private theorem factAll_512 : seg factAllF 512 64=true := by decide +kernel

private theorem factAll_576 : seg factAllF 576 64=true := by decide +kernel

private theorem factAll_640 : seg factAllF 640 64=true := by decide +kernel

private theorem factAll_704 : seg factAllF 704 49=true := by decide +kernel

private theorem factAll : (List.range 753).all factAllF = true := full (join (join (join factAll_0 (join factAll_64 factAll_128)) (join factAll_192 (join factAll_256 factAll_320))) (join (join factAll_384 (join factAll_448 factAll_512)) (join factAll_576 (join factAll_640 factAll_704))))


end RowChecks
open RowChecks in
theorem solution : rawChecks=true ∧ factChecks=true := by
  refine ⟨rawAll,Bool.and_eq_true_iff.mpr ⟨by decide +kernel,factAll⟩⟩
