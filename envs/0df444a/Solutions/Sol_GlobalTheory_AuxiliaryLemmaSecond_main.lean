-- Prove2me | solution 1 for GlobalTheory.AuxiliaryLemmaSecond.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:26:03.56883+00:00
-- url     : https://prove2.me/submissions/aad8965d-098b-4697-88de-9e89848a48a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsMoreTail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AuxiliaryLemmaSecond
open IsLocalRing
namespace GlobalTheory.AuxiliaryLemmaSecond
theorem _root_.solution : ∀ {κ : Type} [inst : Field κ] (R : Subring κ) [IsNoetherianRing ↥R] [IsIntegrallyClosed ↥R]
    [IsFractionRing (↥R) κ] (Q : Ideal ↥R) [Ideal.IsPrime Q], Q ≠ ⊥ →
    (∀ (p : Ideal ↥R), Ideal.IsPrime p → p ≠ ⊥ → p ≤ Q → p = Q) →
    ∃ (W : ValuationSubring κ), IsDiscreteValuationRing ↥W ∧ (∀ (r : ↥R), (↑r : κ) ∈ W) ∧
      (∀ r ∉ Q, (↑r : κ)⁻¹ ∈ W) ∧ (∀ r ∈ Q, r ≠ (0 : ↥R) → (↑r : κ)⁻¹ ∉ W) ∧
      ∀ w ∈ W, ∃ (b : ↥R), ∃ s ∉ Q, w = (↑b : κ) / (↑s : κ) := by
  intro κ _ R _ _ _ Q _ hQ0 hmin
  have hS : Q.primeCompl ≤ nonZeroDivisors R := Q.primeCompl_le_nonZeroDivisors
  set A : Subalgebra R κ := Localization.subalgebra.ofField κ Q.primeCompl hS with hAdef
  have memA : ∀ x : κ, x ∈ A ↔ ∃ (a s : R) (_ : s ∈ Q.primeCompl),
      x = algebraMap R κ a * (algebraMap R κ s)⁻¹ := fun x => Iff.rfl
  haveI : IsLocalization.AtPrime A Q := Localization.subalgebra.isLocalization_ofField κ _ hS
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A Q
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing Q.primeCompl A inferInstance
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A Q.primeCompl hS
  have hcm : (maximalIdeal A).comap (algebraMap R A) = Q :=
    IsLocalization.AtPrime.comap_maximalIdeal A Q
  have hmap : ∀ r : R, algebraMap R κ r = (r : κ) := fun r => rfl
  simp only [hmap] at memA
  have hinj : Function.Injective (algebraMap R A) := IsLocalization.injective A hS
  have hm0 : maximalIdeal A ≠ ⊥ := by
    intro h
    apply hQ0
    rw [← hcm, h]
    exact Ideal.comap_bot_of_injective _ hinj
  have hnf : ¬ IsField A := isField_iff_maximalIdeal_eq.not.mpr hm0
  have hDVR : IsDiscreteValuationRing A := by
    have h03 := (IsDiscreteValuationRing.TFAE A hnf).out 0 3
    refine h03.mpr ⟨inferInstance, ExistsUnique.intro (maximalIdeal A) ⟨hm0, inferInstance⟩ ?_⟩
    rintro P ⟨hP0, hPp⟩
    have eP : Ideal.map (algebraMap R A) (P.comap (algebraMap R A)) = P :=
      IsLocalization.map_comap Q.primeCompl A P
    have eM : Ideal.map (algebraMap R A) ((maximalIdeal A).comap (algebraMap R A)) = maximalIdeal A :=
      IsLocalization.map_comap Q.primeCompl A (maximalIdeal A)
    have hc : P.comap (algebraMap R A) = Q := by
      apply hmin
      · exact Ideal.comap_isPrime _ _
      · intro h
        apply hP0
        rw [← eP, h, Ideal.map_bot]
      · rw [← hcm]
        exact Ideal.comap_mono (le_maximalIdeal hPp.ne_top)
    rw [← eP, ← eM, hc, hcm]
  let W : ValuationSubring κ := .ofSubring A.toSubring fun x => by
    simpa [IsLocalization.IsInteger] using ValuationRing.isInteger_or_isInteger A x
  refine ⟨W, hDVR, ?_, ?_, ?_, ?_⟩
  · intro r
    show (r : κ) ∈ A
    exact (memA _).mpr ⟨r, 1, Q.primeCompl.one_mem, by simp⟩
  · intro r hr
    show (r : κ)⁻¹ ∈ A
    exact (memA _).mpr ⟨1, r, hr, by simp⟩
  · intro r hrQ hr0 hmem
    change (r : κ)⁻¹ ∈ A at hmem
    obtain ⟨a, s, hs, hx⟩ := (memA _).mp hmem
    have hs0 : (s : κ) ≠ 0 := by
      intro h
      apply hs
      have : s = 0 := Subtype.ext h
      rw [this]; exact Q.zero_mem
    have hr0' : (r : κ) ≠ 0 := fun h => hr0 (Subtype.ext h)
    have key : (s : κ) = (r : κ) * (a : κ) := by
      have hx' : (r : κ)⁻¹ = (a : κ) * (s : κ)⁻¹ := by simpa using hx
      field_simp at hx'
      linear_combination hx'
    have : s = r * a := Subtype.ext (by simpa using key)
    exact hs (this ▸ Q.mul_mem_right a hrQ)
  · intro w hw
    change w ∈ A at hw
    obtain ⟨a, s, hs, rfl⟩ := (memA _).mp hw
    exact ⟨a, s, hs, by simp [div_eq_mul_inv]⟩
end GlobalTheory.AuxiliaryLemmaSecond
