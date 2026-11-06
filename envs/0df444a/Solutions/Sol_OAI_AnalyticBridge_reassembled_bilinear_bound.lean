-- Prove2me | solution 1 for OAI.AnalyticBridge.reassembled_bilinear_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:15.483468+00:00
-- url     : https://prove2.me/submissions/24003d38-c4a0-4c7f-ae7e-23e4c323a67a

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Theorems.Thm_OAI_AnalyticBridge_weighted_cauchy_sq
import Theorems.Thm_OAI_AnalyticBridge_fiber_mass_bound

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open OAI.AnalyticBridge
variable {Ω : Type*}
namespace OAI.AnalyticBridge
theorem _root_.solution
    {Λ₁ Λ₂ : Type*} [DecidableEq Λ₁] [DecidableEq Λ₂]
    (S : Finset Ω) (T₁ : Finset Λ₁) (T₂ : Finset Λ₂)
    (label₁ : Ω → Λ₁) (label₂ : Ω → Λ₂)
    (w : Ω → ℂ) (A : Λ₁ → ℂ) (B : Λ₂ → ℂ)
    (M₁ M₂ : ℝ)
    (hM₁ : 0 ≤ M₁)
    (hmap₁ : ∀ ω ∈ S, label₁ ω ∈ T₁)
    (hmap₂ : ∀ ω ∈ S, label₂ ω ∈ T₂)
    (hfiber₁ : ∀ a ∈ T₁,
      (∑ ω ∈ S with label₁ ω = a, ‖w ω‖) ≤ M₁)
    (hfiber₂ : ∀ a ∈ T₂,
      (∑ ω ∈ S with label₂ ω = a, ‖w ω‖) ≤ M₂) :
    ‖∑ ω ∈ S, w ω * A (label₁ ω) * star (B (label₂ ω))‖ ^ 2 ≤
      (M₁ * ∑ a ∈ T₁, ‖A a‖ ^ 2) *
        (M₂ * ∑ a ∈ T₂, ‖B a‖ ^ 2) := by
  have hcs := weighted_cauchy_sq S w (fun ω => A (label₁ ω))
    (fun ω => B (label₂ ω))
  have hside₁ := fiber_mass_bound S T₁ label₁
    (fun ω => ‖w ω‖) A M₁ hmap₁ hfiber₁
  have hside₂ := fiber_mass_bound S T₂ label₂
    (fun ω => ‖w ω‖) B M₂ hmap₂ hfiber₂
  calc
    ‖∑ ω ∈ S, w ω * A (label₁ ω) * star (B (label₂ ω))‖ ^ 2 ≤
      (∑ ω ∈ S, ‖w ω‖ * ‖A (label₁ ω)‖ ^ 2) *
        (∑ ω ∈ S, ‖w ω‖ * ‖B (label₂ ω)‖ ^ 2) := hcs
    _ ≤ (M₁ * ∑ a ∈ T₁, ‖A a‖ ^ 2) *
        (M₂ * ∑ a ∈ T₂, ‖B a‖ ^ 2) := by
      have hlow₂ :
          0 ≤ ∑ ω ∈ S, ‖w ω‖ * ‖B (label₂ ω)‖ ^ 2 :=
        Finset.sum_nonneg (by intro ω hω; positivity)
      have hupp₁ : 0 ≤ M₁ * ∑ a ∈ T₁, ‖A a‖ ^ 2 := by positivity
      exact mul_le_mul hside₁ hside₂ hlow₂ hupp₁
end OAI.AnalyticBridge
