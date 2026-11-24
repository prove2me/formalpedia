-- Prove2me | solution 1 for GlobalTheory.LagrangeInterpolationExistence.exists_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:50:10.223529+00:00
-- url     : https://prove2.me/submissions/775b5abe-67d7-4149-9dd5-8f8fae8a3ba8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInterpolation
import Theorems.Thm_GlobalTheory_LagrangeInterpolationExistence_exists_sum_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LagrangeInterpolationExistence
namespace GlobalTheory.LagrangeInterpolationExistence
theorem _root_.solution {X : Type} (V : Submodule ℂ (X → ℂ)) (F : Finset V) :
    ∃ (S : Finset X) (u : X → V), ∀ f ∈ F, f = ∑ x ∈ S, (f : X → ℂ) x • u x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨∅, 0, by simp⟩
  | insert g F _ ih =>
    obtain ⟨S, u, hu⟩ := ih
    set h : V := g - ∑ x ∈ S, (g : X → ℂ) x • u x with hh
    by_cases h0 : h = 0
    · refine ⟨S, u, fun f hf => ?_⟩
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact sub_eq_zero.mp h0
      · exact hu f hf
    · obtain ⟨y, hy⟩ : ∃ y, (h : X → ℂ) y ≠ 0 := by
        by_contra hc
        apply h0
        ext y
        by_contra hy
        exact hc ⟨y, by simpa using hy⟩
      obtain ⟨T, w, hw⟩ := exists_sum_add S
        (fun x => u x - ((u x : X → ℂ) y / (h : X → ℂ) y) • h) y (((h : X → ℂ) y)⁻¹ • h)
      have key : ∀ f : V, ∑ x ∈ T, (f : X → ℂ) x • w x =
          ∑ x ∈ S, (f : X → ℂ) x • u x +
            (((f - ∑ x ∈ S, (f : X → ℂ) x • u x : V) : X → ℂ) y / (h : X → ℂ) y) • h := by
        intro f
        rw [hw]
        simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul,
          Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_div, sub_smul, Finset.sum_div,
          mul_div_assoc, div_eq_mul_inv, Finset.sum_mul, mul_assoc, sub_mul]
        abel
      refine ⟨T, w, fun f hf => ?_⟩
      rw [key]
      rcases Finset.mem_insert.mp hf with rfl | hf
      · rw [← hh, div_self hy, one_smul, hh]; abel
      · rw [← hu f hf]; simp
end GlobalTheory.LagrangeInterpolationExistence
