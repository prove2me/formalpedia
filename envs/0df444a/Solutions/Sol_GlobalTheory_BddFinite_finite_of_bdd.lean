-- Prove2me | solution 1 for GlobalTheory.BddFinite.finite_of_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:29:58.745803+00:00
-- url     : https://prove2.me/submissions/08b5dbf6-6437-4e5a-bf47-462701500670

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfBoundedEmbeddingsAndValuations
import Theorems.Thm_GlobalTheory_BddFinite_exists_clearing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
open GlobalTheory GlobalTheory.BddFinite
namespace GlobalTheory.BddFinite
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (A : Set K) (R : ℝ), (∀ x ∈ A, ∀ τ : K →+* ℂ, ‖τ x‖ ≤ R) → (∀ w : HeightOneSpectrum (𝓞 K), ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ A, w.valuation K x ≤ B) → (∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite, ∀ x ∈ A, w.valuation K x ≤ 1) → A.Finite := by
  classical
  intro K _ _ A R hR hB hcof
  choose B hB using hB
  choose a ha0 ha using fun w => exists_clearing A w (B w) (hB w)
  have hF : {w : HeightOneSpectrum (𝓞 K) | ¬ ∀ x ∈ A, w.valuation K x ≤ 1}.Finite :=
    Filter.eventually_cofinite.mp hcof
  set F := hF.toFinset with hFdef
  set d : 𝓞 K := ∏ w ∈ F, a w with hd
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun w _ => ha0 w)
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0

  have hval : ∀ x ∈ A, ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ((d : K) * x) ≤ 1 := by
    intro x hx v
    by_cases hv : v ∈ F
    · have hsplit : (d : K) = ((∏ w ∈ F.erase v, a w : 𝓞 K) : K) * (a v : K) := by
        rw [hd, ← Finset.prod_erase_mul F a hv]; push_cast; ring
      rw [hsplit, mul_assoc, map_mul]
      exact mul_le_one' (v.valuation_le_one _) (ha v x hx)
    · have hv' : ∀ y ∈ A, v.valuation K y ≤ 1 := by
        have : v ∉ {w : HeightOneSpectrum (𝓞 K) | ¬ ∀ x ∈ A, w.valuation K x ≤ 1} := by
          simpa [F] using hv
        simpa using this
      rw [map_mul]
      exact mul_le_one' (v.valuation_le_one _) (hv' x hx)
  set M : ℝ := ∑ τ : K →+* ℂ, ‖τ (d : K)‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun τ _ => norm_nonneg _)
  have hfin := NumberField.Embeddings.finite_of_norm_le K ℂ (M * R)
  refine (hfin.image (fun y => (d : K)⁻¹ * y)).subset ?_
  intro x hx
  refine ⟨(d : K) * x, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K _ (hval x hx)
    rw [← hy]
    exact (NumberField.RingOfIntegers.isIntegral_coe y)
  · intro τ
    rw [map_mul, norm_mul]
    have h1 : ‖τ (d : K)‖ ≤ M :=
      Finset.single_le_sum (f := fun τ : K →+* ℂ => ‖τ (d : K)‖) (fun τ _ => norm_nonneg _) (Finset.mem_univ τ)
    exact mul_le_mul h1 (hR x hx τ) (norm_nonneg _) hM0
  · simp only
    rw [← mul_assoc, inv_mul_cancel₀ hdK, one_mul]
end GlobalTheory.BddFinite
