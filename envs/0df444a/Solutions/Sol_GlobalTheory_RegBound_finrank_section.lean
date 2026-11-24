-- Prove2me | solution 1 for GlobalTheory.RegBound.finrank_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:55:16.632893+00:00
-- url     : https://prove2.me/submissions/49d5f5cb-276c-4878-b9c5-2b5615788a04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
import Theorems.Thm_GlobalTheory_RegBound_comp_succ_mul
import Theorems.Thm_GlobalTheory_RegBound_mem_sup_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution [Finite σ] {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) {h : MvPolynomial σ K}
    (hh : h.IsHomogeneous 1) (hreg : ∀ F, h * F ∈ I → F ∈ I) (hne : I ≠ ⊤) (e : ℕ) :
    finrank K (piece (I ⊔ Ideal.span {h}) (e + 1)) + finrank K (piece I e) =
      finrank K (piece I (e + 1)) + finrank K (homogeneousSubmodule σ K e) := by
  have h0 : h ≠ 0 := by
    rintro rfl
    exact hne ((Ideal.eq_top_iff_one _).2 (hreg 1 (by simp)))
  let μ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K := LinearMap.mulLeft K h
  have hμ : Function.Injective μ := fun a b hab => mul_left_cancel₀ h0 hab
  have e1 : piece (I ⊔ Ideal.span {h}) (e + 1) =
      piece I (e + 1) ⊔ (homogeneousSubmodule σ K e).map μ := by
    apply le_antisymm
    · rintro F ⟨hF1, hF2⟩
      obtain ⟨A, hA, B, hAB⟩ := mem_sup_span.1 hF2
      have : F = homogeneousComponent (e + 1) A + h * homogeneousComponent e B := by
        rw [← comp_succ_mul hh, ← map_add, ← hAB, homogeneousComponent_eq_self hF1]
      rw [this]
      exact Submodule.add_mem_sup ⟨homogeneousComponent_isHomogeneous _ _, hI A hA _⟩
        ⟨_, homogeneousComponent_isHomogeneous _ _, rfl⟩
    · refine sup_le (fun F hF => ⟨hF.1, mem_sup_span.2 ⟨F, hF.2, 0, by simp⟩⟩) ?_
      rintro _ ⟨B, hB, rfl⟩
      refine ⟨?_, mem_sup_span.2 ⟨0, I.zero_mem, B, by simp [μ]⟩⟩
      have := hh.mul hB
      rwa [add_comm] at this
  have e2 : piece I (e + 1) ⊓ (homogeneousSubmodule σ K e).map μ = (piece I e).map μ := by
    apply le_antisymm
    · rintro _ ⟨hF, B, hB, rfl⟩
      exact ⟨B, ⟨hB, hreg B hF.2⟩, rfl⟩
    · rintro _ ⟨B, hB, rfl⟩
      refine ⟨⟨?_, I.mul_mem_left h hB.2⟩, B, hB.1, rfl⟩
      have := hh.mul hB.1
      rwa [add_comm] at this
  have := Submodule.finrank_sup_add_finrank_inf_eq (piece I (e + 1))
    ((homogeneousSubmodule σ K e).map μ)
  rw [← e1, e2, ← (Submodule.equivMapOfInjective μ hμ _).finrank_eq,
    ← (Submodule.equivMapOfInjective μ hμ _).finrank_eq] at this
  exact this
end GlobalTheory.RegBound
