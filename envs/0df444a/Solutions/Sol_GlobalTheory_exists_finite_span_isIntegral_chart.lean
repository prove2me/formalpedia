-- Prove2me | solution 1 for GlobalTheory.exists_finite_span_isIntegral_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:34.503864+00:00
-- url     : https://prove2.me/submissions/510731f2-a7f3-4ae9-b21e-af1a62f6a67f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsIntegralMulPowOfSubalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {J : Type*}
namespace GlobalTheory
theorem _root_.solution [IsDedekindDomain o] [CharZero Ω] [Finite J]
    (t : J → Ω) {i : J} (hi : t i ≠ 0)
    (hfin : Module.Finite
      (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω) :
    ∃ G : Set Ω, G.Finite ∧
      (∀ x ∈ G, IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x) ∧
      ∀ x, IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x →
        x ∈ Submodule.span (Algebra.adjoin o (Set.range fun j => t j / t i)) G := by
  set A := Algebra.adjoin o (Set.range fun j => t j / t i) with hA
  haveI : Algebra.FiniteType o A := .adjoin_of_finite (Set.finite_range _)
  have hK : Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) ≤
      Subfield.closure (A : Set Ω) := by
    refine Subfield.closure_le.mpr ?_
    rintro x (⟨a, rfl⟩ | ⟨k, j, rfl⟩)
    · exact Subfield.subset_closure (A.algebraMap_mem a)
    · have : t j / t k = (t j / t i) / (t k / t i) := by
        rw [div_div_div_cancel_right₀ hi]
      rw [this]
      exact div_mem (Subfield.subset_closure (Algebra.subset_adjoin ⟨j, rfl⟩))
        (Subfield.subset_closure (Algebra.subset_adjoin ⟨k, rfl⟩))
  haveI : Algebra.EssFiniteType A Ω := by
    obtain ⟨σ, hσ⟩ := hfin
    refine (Algebra.essFiniteType_iff _ _).mpr ⟨σ, fun s => ?_⟩
    have hs : s ∈ Submodule.span _ (σ : Set Ω) := hσ ▸ Submodule.mem_top
    induction hs using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_mem _, isUnit_one, by simpa using Algebra.subset_adjoin hx⟩
    | zero => exact ⟨1, one_mem _, isUnit_one, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha', hx⟩ := hx
      obtain ⟨b, hb, hb', hy⟩ := hy
      refine ⟨a * b, mul_mem ha hb, ha'.mul hb', ?_⟩
      have : (x + y) * (a * b) = x * a * b + y * b * a := by ring
      rw [this]
      exact add_mem (mul_mem hx hb) (mul_mem hy ha)
    | smul c x _ hx =>
      obtain ⟨a, ha, ha', hx⟩ := hx
      obtain ⟨y, hy, w, hw, hc⟩ := Subfield.mem_closure_iff.mp (hK c.2)
      have hAA : Subring.closure (A : Set Ω) = A.toSubring := Subring.closure_eq A.toSubring
      rw [hAA] at hy hw
      have hy' : y ∈ Algebra.adjoin A (σ : Set Ω) := Subalgebra.algebraMap_mem _ (⟨y, hy⟩ : A)
      have hw' : w ∈ Algebra.adjoin A (σ : Set Ω) := Subalgebra.algebraMap_mem _ (⟨w, hw⟩ : A)
      by_cases hw0 : w = 0
      · refine ⟨1, one_mem _, isUnit_one, ?_⟩
        have : (c : Ω) = 0 := by rw [← hc, hw0, div_zero]
        rw [Subfield.smul_def, this]
        simp
      · refine ⟨a * w, mul_mem ha hw', ha'.mul (IsUnit.mk0 _ hw0), ?_⟩
        have : c • x * (a * w) = y * (x * a) := by
          rw [Subfield.smul_def, ← hc, smul_eq_mul]
          field_simp
        rw [this]
        exact mul_mem hy' hx
  haveI := finite_integralClosure_of_essFiniteType_field o A Ω
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite A (integralClosure A Ω))
  refine ⟨(integralClosure A Ω).val.toLinearMap '' s, s.finite_toSet.image _, ?_, fun x hx => ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Submodule.span_image, hs]
    exact ⟨⟨x, hx⟩, trivial, rfl⟩
end GlobalTheory
