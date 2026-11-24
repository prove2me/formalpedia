-- Prove2me | solution 1 for GlobalTheory.krullAkizuki_of_birational
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:18:59.904271+00:00
-- url     : https://prove2.me/submissions/10c4895c-6a2b-4fbc-b26e-3dd1b92e8a42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_finite_quotient_span_of_birational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
variable [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
namespace GlobalTheory
theorem _root_.solution
    (hB : ∀ x : B, ∃ c : A, c ≠ 0 ∧ ∃ b : A, algebraMap A B c * x = algebraMap A B b) :
    IsNoetherianRing B ∧ Ring.DimensionLEOne B := by
  have key : ∀ I : Ideal B, I ≠ ⊥ → ∃ a : A, a ≠ 0 ∧ algebraMap A B a ∈ I := by
    intro I hI
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨c, hc, b, hb⟩ := hB x
    refine ⟨b, ?_, hb ▸ I.mul_mem_left _ hx⟩
    rintro rfl
    simp [hc, hx0] at hb
  constructor
  · rw [isNoetherianRing_iff_ideal_fg]
    intro I
    rcases eq_or_ne I ⊥ with rfl | hI
    · exact Submodule.fg_bot
    obtain ⟨a, ha, haI⟩ := key I hI
    have h1 := finite_quotient_span_of_birational hB ha
    have h2 : IsNoetherian A (B ⧸ Ideal.span {algebraMap A B a}) := inferInstance
    have h3 : IsNoetherian B (B ⧸ Ideal.span {algebraMap A B a}) := isNoetherian_of_tower A h2
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Ideal.span {algebraMap A B a}))
      (IsNoetherian.noetherian _) ?_
    rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haI)]
    exact Submodule.fg_span_singleton _
  · refine ⟨fun {p} hp hp' => ?_⟩
    obtain ⟨a, ha, hap⟩ := key p hp
    have h1 := finite_quotient_span_of_birational hB ha
    have h2 : Module.Finite A (B ⧸ p) :=
      Module.Finite.of_surjective (Ideal.Quotient.factorₐ A
        ((Ideal.span_singleton_le_iff_mem _).mpr hap)).toLinearMap
        (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem _).mpr hap))
    have h3 : ((⊥ : Ideal (B ⧸ p)).comap (algebraMap A (B ⧸ p))).IsMaximal := by
      refine Ring.DimensionLEOne.maximalOfPrime ?_ inferInstance
      intro h
      have : a ∈ (⊥ : Ideal (B ⧸ p)).comap (algebraMap A (B ⧸ p)) := by
        rw [Ideal.mem_comap, Ideal.mem_bot]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hap
      rw [h] at this
      exact ha this
    have h4 := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) (⊥ : Ideal (B ⧸ p)) h3
    exact Ideal.Quotient.maximal_of_isField _ (Ring.isField_iff_maximal_bot.mpr h4)
end GlobalTheory
