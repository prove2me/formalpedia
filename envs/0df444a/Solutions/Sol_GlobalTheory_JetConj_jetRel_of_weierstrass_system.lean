-- Prove2me | solution 1 for GlobalTheory.JetConj.jetRel_of_weierstrass_system
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:28:23.609209+00:00
-- url     : https://prove2.me/submissions/7a227535-d7af-4c6d-a7b6-3f39464bb70f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Theorems.Thm_GlobalTheory_JetConj_pair_natCast
import Theorems.Thm_GlobalTheory_JetConj_pair_mul
import Theorems.Thm_GlobalTheory_JetConj_pair_sub
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
theorem _root_.solution {p q p' q' : ℂ → ℂ} {c c' : ℂ} (hc : (c, c') ∈ S)
    (hp : AnalyticAt ℂ p 0) (hp' : AnalyticAt ℂ p' 0) (hq : AnalyticAt ℂ q 0) (hq' : AnalyticAt ℂ q' 0)
    (e1 : deriv p =ᶠ[𝓝 0] q) (e1' : deriv p' =ᶠ[𝓝 0] q')
    (e2 : deriv q =ᶠ[𝓝 0] fun z => (6 * p z) * p z - c)
    (e2' : deriv q' =ᶠ[𝓝 0] fun z => (6 * p' z) * p' z - c')
    (h0 : (p 0, p' 0) ∈ S) (h1 : (q 0, q' 0) ∈ S) : JetRel S q q' := by
  have hA : AnalyticAt ℂ (fun z => 6 * p z * p z) 0 := by fun_prop
  have hA' : AnalyticAt ℂ (fun z => 6 * p' z * p' z) 0 := by fun_prop
  have hp6 : AnalyticAt ℂ (fun z => 6 * p z) 0 := by fun_prop
  have hp6' : AnalyticAt ℂ (fun z => 6 * p' z) 0 := by fun_prop
  have h6 : ((6 : ℂ), (6 : ℂ)) ∈ S := by simpa using pair_natCast S 6
  have key : ∀ n, (iteratedDeriv n p 0, iteratedDeriv n p' 0) ∈ S ∧
      (iteratedDeriv n q 0, iteratedDeriv n q' 0) ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      cases n with
      | zero => exact ⟨by simpa using h0, by simpa using h1⟩
      | succ n =>
        refine ⟨?_, ?_⟩
        · rw [iteratedDeriv_succ', iteratedDeriv_succ', e1.iteratedDeriv_eq n, e1'.iteratedDeriv_eq n]
          exact (ih n (Nat.lt_succ_self n)).2
        · rw [iteratedDeriv_succ', iteratedDeriv_succ', e2.iteratedDeriv_eq n, e2'.iteratedDeriv_eq n,
            iteratedDeriv_fun_sub hA.contDiffAt contDiffAt_const,
            iteratedDeriv_fun_sub hA'.contDiffAt contDiffAt_const, iteratedDeriv_const, iteratedDeriv_const]
          refine pair_sub (iteratedDeriv_mul_mem_of_iteratedDeriv_mem hp6 hp6' hp hp' n (fun i hi => ?_)
            (fun i hi => (ih i (Nat.lt_succ_of_le hi)).1)) ?_
          · rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
            exact pair_mul h6 (ih i (Nat.lt_succ_of_le hi)).1
          · split_ifs
            · exact hc
            · exact S.zero_mem
  exact ⟨hq, hq', fun n => (key n).2⟩
end GlobalTheory.JetConj
