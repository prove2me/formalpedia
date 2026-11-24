-- Prove2me | solution 1 for GlobalTheory.JetConj.JetRel.of_deriv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:23:22.88968+00:00
-- url     : https://prove2.me/submissions/cc9d91c6-5384-46f9-b02d-84d7b572a9b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Theorems.Thm_GlobalTheory_JetConj_pair_natCast
import Theorems.Thm_GlobalTheory_JetConj_pair_mul
import Theorems.Thm_GlobalTheory_JetConj_pair_sum
import Theorems.Thm_GlobalTheory_JetConj_JetRel_zero
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
theorem _root_.solution (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0) (G : JetRel S g g')
    (e : _root_.deriv f =ᶠ[𝓝 0] fun z => f z * g z) (e' : _root_.deriv f' =ᶠ[𝓝 0] fun z => f' z * g' z)
    (h0 : (f 0, f' 0) ∈ S) : JetRel S f f' := by
  obtain ⟨hg, hg', hdg⟩ := G
  refine ⟨hf, hf', fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simpa using h0
    | succ n =>
      rw [iteratedDeriv_succ', iteratedDeriv_succ', e.iteratedDeriv_eq n, e'.iteratedDeriv_eq n]
      exact iteratedDeriv_mul_mem_of_iteratedDeriv_mem hf hf' hg hg' n (fun i hi => ih i (Nat.lt_succ_of_le hi)) (fun i _ => hdg i)
end JetRel
end GlobalTheory.JetConj
