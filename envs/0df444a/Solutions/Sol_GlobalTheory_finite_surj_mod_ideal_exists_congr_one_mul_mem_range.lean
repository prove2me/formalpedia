-- Prove2me | solution 1 for GlobalTheory.finite_surj_mod_ideal_exists_congr_one_mul_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:50:01.757133+00:00
-- url     : https://prove2.me/submissions/7b5c5f79-870d-4664-ace2-a1eed77b15b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteSurjModIdealExistsCongrOneMulMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C), f.Finite → ∀ J : Ideal B,
      Function.Surjective ((Ideal.Quotient.mk (J.map f)).comp f) →
      ∃ r : B, r - 1 ∈ J ∧ ∀ c : C, ∃ b : B, f r * c = f b := by
  intro B C _ _ f hf J hs
  letI := f.toAlgebra
  haveI : Module.Finite B C := hf
  set P : Submodule B C := LinearMap.range (Algebra.linearMap B C) with hP
  have hle : (⊤ : Submodule B (C ⧸ P)) ≤ J • ⊤ := by
    rintro m -
    obtain ⟨c, rfl⟩ := P.mkQ_surjective m
    obtain ⟨b, hb⟩ := hs (Ideal.Quotient.mk _ c)
    have hy : c - f b ∈ J • (⊤ : Submodule B C) := by
      rw [Ideal.smul_top_eq_map]
      exact Ideal.Quotient.eq.mp hb.symm
    have hfb : P.mkQ (f b) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, rfl⟩
    have hc : P.mkQ c = P.mkQ (c - f b) := by rw [map_sub, hfb, sub_zero]
    rw [hc]
    have h1 : P.mkQ (c - f b) ∈ (J • (⊤ : Submodule B C)).map P.mkQ := Submodule.mem_map_of_mem hy
    rw [Submodule.map_smul''] at h1
    exact Submodule.smul_mono le_rfl le_top h1
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J ⊤
    Module.Finite.fg_top hle
  refine ⟨r, hr1, fun c => ?_⟩
  have h := hr (P.mkQ c) trivial
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨b, hb⟩ := h
  refine ⟨b, ?_⟩
  rw [Algebra.smul_def] at hb
  exact hb.symm
end GlobalTheory
