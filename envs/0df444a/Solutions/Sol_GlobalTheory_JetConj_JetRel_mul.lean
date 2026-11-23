-- Prove2me | solution 1 for GlobalTheory.JetConj.JetRel.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:37.296072+00:00
-- url     : https://prove2.me/submissions/3e961a21-c7bb-45cc-941a-06543a6d7bac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Theorems.Thm_GlobalTheory_JetConj_pair_natCast
import Theorems.Thm_GlobalTheory_JetConj_pair_mul
import Theorems.Thm_GlobalTheory_JetConj_pair_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter Topology
namespace GlobalTheory.JetConj
variable {S : Subring (ℂ × ℂ)} {f f' g g' h h' : ℂ → ℂ}
private lemma iteratedDeriv_mul_mem_of_iteratedDeriv_mem (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0) (hg : AnalyticAt ℂ g 0)
    (hg' : AnalyticAt ℂ g' 0) (n : ℕ) (H : ∀ i ≤ n, (iteratedDeriv i f 0, iteratedDeriv i f' 0) ∈ S)
    (K : ∀ i ≤ n, (iteratedDeriv i g 0, iteratedDeriv i g' 0) ∈ S) :
    (iteratedDeriv n (fun z => f z * g z) 0, iteratedDeriv n (fun z => f' z * g' z) 0) ∈ S := by
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, iteratedDeriv_fun_mul hf'.contDiffAt hg'.contDiffAt]
  exact pair_sum _ fun i hi => pair_mul (pair_mul (pair_natCast S _)
    (H i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))) (K (n - i) (Nat.sub_le n i))
end GlobalTheory.JetConj
end

set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.JetConj
variable {S : Subring (ℂ × ℂ)} {f f' g g' h h' : ℂ → ℂ}
namespace GlobalTheory.JetConj
namespace JetRel
theorem _root_.solution (H : JetRel S f f') (K : JetRel S g g') :
    JetRel S (fun z => f z * g z) (fun z => f' z * g' z) := by
  obtain ⟨hf, hf', hdf⟩ := H
  obtain ⟨hg, hg', hdg⟩ := K
  exact ⟨by fun_prop, by fun_prop, fun n => iteratedDeriv_mul_mem_of_iteratedDeriv_mem hf hf' hg hg' n (fun i _ => hdf i) (fun i _ => hdg i)⟩
end JetRel
end GlobalTheory.JetConj
