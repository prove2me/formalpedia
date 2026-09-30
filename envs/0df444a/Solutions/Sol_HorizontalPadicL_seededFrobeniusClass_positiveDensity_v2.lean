-- Prove2me | solution 1 for HorizontalPadicL.seededFrobeniusClass_positiveDensity_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T15:07:49.519785+00:00
-- url     : https://prove2.me/submissions/b9265b5d-2718-4daa-a574-62a007bbb4c9

import Definitions.Def_KN_SeededPrimeGaloisDataV2
import Theorems.Thm_FrobeniusDensity_chebotarev_natural_density

set_option autoImplicit false

open NumberField Ideal Filter Topology

open HorizontalPadicL

theorem solution
    {N k p m B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {f : MTT.Eigenform N k ι} {η : DirichletCharacterWithLevel}
    {V : SeededEigenformPadicPlaceData (p := p) f η}
    (D : SeededOrderlyFrobeniusClassData f η m B V) :
    ∃ δ : ℝ, 0 < δ ∧ HasPrimeNaturalDensity D.primes δ := by
  classical
  rcases D.chebotarevClass with ⟨L, σ, S, hrealizes⟩
  let δ : ℝ :=
    (Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) /
      (Nat.card (L ≃ₐ[ℚ] L) : ℝ)
  refine ⟨δ, ?_, ?_⟩
  · apply div_pos
    · exact Nat.cast_pos.mpr (Finite.card_pos_iff.mpr ⟨⟨σ, IsConj.refl σ⟩⟩)
    · exact Nat.cast_pos.mpr (Finite.card_pos_iff.mpr ⟨σ⟩)
  · have h_indicator_prime : ∀ {ℓ : ℕ},
        LanglandsTunnell.classIndicator σ ℓ = 1 → ℓ.Prime := by
      intro ℓ hℓ
      unfold LanglandsTunnell.classIndicator at hℓ
      split at hℓ
      · exact ‹∃ _ : ℓ.Prime, _›.choose
      · simp at hℓ
    have hfilter : ∀ X : ℕ,
        (Finset.range X).filter (fun ℓ => ℓ.Prime ∧ ℓ ∈ D.primes) =
          (Finset.range X).filter (fun ℓ =>
            ℓ ∉ S ∧ LanglandsTunnell.classIndicator σ ℓ = 1) := by
      intro X
      ext ℓ
      simp only [Finset.mem_filter, Finset.mem_range, hrealizes, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hX, -, hS, hclass⟩
        exact ⟨hX, hS, hclass⟩
      · rintro ⟨hX, hS, hclass⟩
        exact ⟨hX, h_indicator_prime hclass, hS, hclass⟩
    unfold HasPrimeNaturalDensity
    simpa only [δ, hfilter] using
      (FrobeniusDensity.chebotarev_natural_density L σ S)
