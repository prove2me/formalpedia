-- Prove2me | solution 1 for GlobalTheory.JetConj.JetRel.of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:34.155797+00:00
-- url     : https://prove2.me/submissions/729625c0-08fc-47b8-8339-2d5b70d0268e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Theorems.Thm_GlobalTheory_JetConj_pair_natCast
import Theorems.Thm_GlobalTheory_JetConj_JetRel_congr
import Theorems.Thm_GlobalTheory_JetConj_JetRel_const
import Theorems.Thm_GlobalTheory_JetConj_JetRel_mul
import Theorems.Thm_GlobalTheory_JetConj_JetRel_of_mul
import Theorems.Thm_GlobalTheory_JetConj_JetRel_of_deriv_eq
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
private lemma deriv_eventuallyEq_logDeriv_pow_succ {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hne : f 0 ≠ 0) (j : ℕ) :
    AnalyticAt ℂ (fun z => _root_.deriv (fun w => f w ^ (j + 1)) z / (((j + 1 : ℕ) : ℂ) * f z ^ (j + 1))) 0 ∧
    (_root_.deriv (fun w => f w ^ (j + 1)) =ᶠ[𝓝 0] fun z =>
      _root_.deriv (fun w => f w ^ (j + 1)) z / (((j + 1 : ℕ) : ℂ) * f z ^ (j + 1)) *
        (((j + 1 : ℕ) : ℂ) * f z ^ (j + 1))) ∧
    (_root_.deriv f =ᶠ[𝓝 0] fun z =>
      f z * (_root_.deriv (fun w => f w ^ (j + 1)) z / (((j + 1 : ℕ) : ℂ) * f z ^ (j + 1)))) := by
  have hk : ((j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero j)
  have hu : AnalyticAt ℂ (fun w => f w ^ (j + 1)) 0 := by fun_prop
  have hne' : ∀ᶠ z in 𝓝 (0 : ℂ), f z ≠ 0 := hf.continuousAt.eventually_ne hne
  refine ⟨hu.deriv.fun_div (by fun_prop) (mul_ne_zero hk (pow_ne_zero _ hne)), ?_, ?_⟩
  · filter_upwards [hne'] with z hz
    rw [div_mul_cancel₀ _ (mul_ne_zero hk (pow_ne_zero _ hz))]
  · filter_upwards [hne', hf.eventually_analyticAt] with z hz hza
    have hz' : f z ^ j ≠ 0 := pow_ne_zero j hz
    rw [deriv_fun_pow hza.differentiableAt, Nat.add_sub_cancel]
    field_simp
    ring
end GlobalTheory.JetConj
end

set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.JetConj
variable {S : Subring (ℂ × ℂ)} {f f' g g' h h' : ℂ → ℂ}
namespace GlobalTheory.JetConj
namespace JetRel
theorem _root_.solution (hS : IsFieldGraph S) (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0) {k : ℕ}
    (hk : k ≠ 0) (H : JetRel S (fun z => f z ^ k) (fun z => f' z ^ k)) (h0 : (f 0, f' 0) ∈ S)
    (hne : f 0 ≠ 0) : JetRel S f f' := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hne' : f' 0 ≠ 0 := fun h => hne ((hS.1 _ _ h0).2 h)
  obtain ⟨hv, e1, e2⟩ := deriv_eventuallyEq_logDeriv_pow_succ hf hne j
  obtain ⟨hv', e1', e2'⟩ := deriv_eventuallyEq_logDeriv_pow_succ hf' hne' j
  have G : JetRel S (fun z => ((j + 1 : ℕ) : ℂ) * f z ^ (j + 1)) (fun z => ((j + 1 : ℕ) : ℂ) * f' z ^ (j + 1)) :=
    (JetRel.const (pair_natCast S (j + 1))).mul H
  have hnz : ¬ (fun z => ((j + 1 : ℕ) : ℂ) * f z ^ (j + 1)) =ᶠ[𝓝 0] 0 := fun hev =>
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero j)) (pow_ne_zero _ hne) hev.eq_of_nhds
  have V := JetRel.of_mul hS hv hv' G hnz (H.deriv.congr e1 e1')
  exact JetRel.of_deriv_eq hf hf' V e2 e2' h0
end JetRel
end GlobalTheory.JetConj
