-- Prove2me | solution 1 for GlobalTheory.JetConj.JetRel.of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:38:57.350218+00:00
-- url     : https://prove2.me/submissions/675ce7b1-6574-4882-b191-62b3adb27a97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Theorems.Thm_GlobalTheory_JetConj_pair_natCast
import Theorems.Thm_GlobalTheory_JetConj_pair_mul
import Theorems.Thm_GlobalTheory_JetConj_pair_sub
import Theorems.Thm_GlobalTheory_JetConj_pair_sum
import Theorems.Thm_GlobalTheory_JetConj_exists_iteratedDeriv_ne_zero
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
private lemma eq_div_of_binomial_convolution (a b c : ℕ → ℂ) (m n : ℕ) (hb : ∀ j < m, b j = 0) (hbm : b m ≠ 0)
    (hc : c (n + m) = ∑ j ∈ Finset.range (n + m + 1), ((n + m).choose j : ℂ) * a j * b (n + m - j)) :
    a n = (c (n + m) - ∑ j ∈ Finset.range n, ((n + m).choose j : ℂ) * a j * b (n + m - j)) *
      (((n + m).choose n : ℂ) * b m)⁻¹ := by
  have hC : ((n + m).choose n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right n m)).ne'
  have htail : ∑ j ∈ Finset.Ico (n + 1) (n + m + 1), ((n + m).choose j : ℂ) * a j * b (n + m - j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    rw [hb (n + m - j) (by omega), mul_zero]
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : n + 1 ≤ n + m + 1), htail, add_zero,
    Finset.sum_range_succ, Nat.add_sub_cancel_left] at hc
  rw [hc, add_sub_cancel_left]
  field_simp
end GlobalTheory.JetConj
end

set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.JetConj
variable {S : Subring (ℂ × ℂ)} {f f' g g' h h' : ℂ → ℂ}
namespace GlobalTheory.JetConj
namespace JetRel
theorem _root_.solution (hS : IsFieldGraph S) (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0)
    (G : JetRel S g g') (h0 : ¬ g =ᶠ[𝓝 0] 0)
    (H : JetRel S (fun z => f z * g z) (fun z => f' z * g' z)) : JetRel S f f' := by
  obtain ⟨hg, hg', hdg⟩ := G
  obtain ⟨-, -, hdH⟩ := H
  classical
  have hex : ∃ k, iteratedDeriv k g 0 ≠ 0 := exists_iteratedDeriv_ne_zero hg h0
  set m := Nat.find hex with hmdef
  have hm : iteratedDeriv m g 0 ≠ 0 := Nat.find_spec hex
  have hlt : ∀ j < m, iteratedDeriv j g 0 = 0 := fun j hj => not_not.1 (Nat.find_min hex hj)
  have hm' : iteratedDeriv m g' 0 ≠ 0 := fun h => hm ((hS.1 _ _ (hdg m)).2 h)
  have hlt' : ∀ j < m, iteratedDeriv j g' 0 = 0 := fun j hj => (hS.1 _ _ (hdg j)).1 (hlt j hj)
  refine ⟨hf, hf', fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc : iteratedDeriv (n + m) (fun z => f z * g z) 0 = _ := iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt
    have hc' : iteratedDeriv (n + m) (fun z => f' z * g' z) 0 = _ :=
      iteratedDeriv_fun_mul hf'.contDiffAt hg'.contDiffAt
    have e1 := eq_div_of_binomial_convolution (fun j => iteratedDeriv j f 0) (fun j => iteratedDeriv j g 0)
      (fun j => iteratedDeriv j (fun z => f z * g z) 0) m n hlt hm hc
    have e2 := eq_div_of_binomial_convolution (fun j => iteratedDeriv j f' 0) (fun j => iteratedDeriv j g' 0)
      (fun j => iteratedDeriv j (fun z => f' z * g' z) 0) m n hlt' hm' hc'
    beta_reduce at e1 e2
    rw [e1, e2]
    refine pair_mul (pair_sub (hdH (n + m)) (pair_sum _ fun j hj =>
      pair_mul (pair_mul (pair_natCast S _) (ih j (Finset.mem_range.1 hj))) (hdg _)))
      (hS.2 _ _ (pair_mul (pair_natCast S _) (hdg m)))
end JetRel
end GlobalTheory.JetConj
