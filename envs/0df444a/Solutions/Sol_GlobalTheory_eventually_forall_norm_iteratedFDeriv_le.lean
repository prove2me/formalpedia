-- Prove2me | solution 1 for GlobalTheory.eventually_forall_norm_iteratedFDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:34:47.408121+00:00
-- url     : https://prove2.me/submissions/7f9d7ecd-d865-4723-b260-5d9ea7ff2768

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded
import Theorems.Thm_GlobalTheory_norm_fderiv_le_of_small_of_lipschitz
import Theorems.Thm_GlobalTheory_norm_iteratedFDeriv_sub_le_of_bound
import Theorems.Thm_GlobalTheory_eventually_forall_norm_le_of_lipschitz_of_decay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X V : Type*} {l : Filter X}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {h : X → SchwartzMap V ℂ}
    (hp : ∀ v, Tendsto (fun x => h x v) l (𝓝 0))
    (hb : ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (h x) v‖ ≤ C)
    (n : ℕ) : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ∀ v, ‖iteratedFDeriv ℝ n (h x) v‖ ≤ ε := by
  induction n with
  | zero =>
    intro ε hε
    obtain ⟨C, hC0, hCb⟩ := hb 0 1
    obtain ⟨D, -, hDb⟩ := hb 1 0
    refine eventually_forall_norm_le_of_lipschitz_of_decay
      (h := fun x v => iteratedFDeriv ℝ 0 (h x) v) (C := C) (D := D) (fun v => ?_) hC0 ?_ ?_ hε
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_iteratedFDeriv_zero]
      exact tendsto_zero_iff_norm_tendsto_zero.1 (hp v)
    · filter_upwards [hCb] with x hx a b
      exact norm_iteratedFDeriv_sub_le_of_bound ((h x).smooth ⊤) 0 (fun w => by simpa using hx w) a b
    · filter_upwards [hDb] with x hx w
      simpa using hx w
  | succ n ih =>
    intro ε hε
    obtain ⟨C, hC0, hCb⟩ := hb 0 (n + 2)
    have ht : 0 < ε / (2 * (C + 1)) := div_pos hε (by linarith)
    have hCt : C * (ε / (2 * (C + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by linarith) two_pos]
      nlinarith
    have hδ : 0 < ε * (ε / (2 * (C + 1))) / 4 := by
      have := mul_pos hε ht
      linarith
    filter_upwards [ih _ hδ, hCb] with x hx hxC v
    have hsm := (h x).smooth ⊤
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (h x)) :=
      hsm.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
    have hLip : ∀ a b, ‖fderiv ℝ (iteratedFDeriv ℝ n (h x)) a - fderiv ℝ (iteratedFDeriv ℝ n (h x)) b‖ ≤
        C * ‖a - b‖ := by
      intro a b
      rw [fderiv_iteratedFDeriv, Function.comp_apply, Function.comp_apply,
        ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
      exact norm_iteratedFDeriv_sub_le_of_bound hsm (n + 1) (fun w => by simpa using hxC w) a b
    have hv := norm_fderiv_le_of_small_of_lipschitz hdiff hC0 ht hLip hx v
    rw [norm_fderiv_iteratedFDeriv] at hv
    have e : 2 * (ε * (ε / (2 * (C + 1))) / 4) / (ε / (2 * (C + 1))) = ε / 2 := by
      field_simp
      ring
    rw [e] at hv
    linarith
end GlobalTheory
