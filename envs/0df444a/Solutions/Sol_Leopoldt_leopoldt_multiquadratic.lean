-- Prove2me | solution 1 for Leopoldt.leopoldt_multiquadratic
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T20:19:56.681555+00:00
-- url     : https://prove2.me/submissions/9ea737ca-f637-430a-92ca-f6d72bc14182

import Theorems.Thm_Leopoldt_leopoldt_totallyReal_multiquadratic
import Theorems.Thm_Leopoldt_leopoldtConjecture_iff_maximalRealSubfield

open NumberField

namespace LeopoldtMultiquadraticCor

theorem comm_of_sq {G : Type*} [Group G] (hG : ∀ σ : G, σ * σ = 1) (g h : G) :
    g * h = h * g := by
  have e1 := hG (g * h)
  have : (g * h)⁻¹ = g * h := inv_eq_of_mul_eq_one_right e1
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hG g), inv_eq_of_mul_eq_one_right (hG h)] at this
  exact this.symm

theorem isTotallyReal_or_isTotallyComplex (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] :
    IsTotallyReal K ∨ IsTotallyComplex K := by
  by_cases h : ∃ w : InfinitePlace K, w.IsComplex
  · right
    obtain ⟨w0, hw0⟩ := h
    refine ⟨fun w => ?_⟩
    obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq (k := ℚ) (w := w0) (w' := w)
      (Subsingleton.elim _ _)
    rw [← hσ]
    exact InfinitePlace.isComplex_smul_iff.2 hw0
  · left
    push Not at h
    exact ⟨fun w => InfinitePlace.not_isComplex_iff_isReal.1 (h w)⟩

theorem main (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (hG : ∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1) : Leopoldt.LeopoldtConjecture p K := by
  rcases isTotallyReal_or_isTotallyComplex K with h | h
  · exact Leopoldt.leopoldt_totallyReal_multiquadratic p K hG
  · have : IsAbelianGalois ℚ K := { is_comm := ⟨comm_of_sq hG⟩ }
    rw [Leopoldt.leopoldtConjecture_iff_maximalRealSubfield]
    let Kp := maximalRealSubfield K
    have hab : IsAbelianGalois ℚ Kp :=
      IsAbelianGalois.of_algHom (Kp.subtype : Kp →+* K).toRatAlgHom
    have hG' : ∀ τ : Kp ≃ₐ[ℚ] Kp, τ * τ = 1 := by
      intro τ
      let σ : K ≃ₐ[ℚ] K := τ.liftNormal K
      ext x
      have e : ∀ y : Kp, σ (algebraMap Kp K y) = algebraMap Kp K (τ y) :=
        AlgEquiv.liftNormal_commutes τ K
      show algebraMap Kp K ((τ * τ) x) = algebraMap Kp K ((1 : Kp ≃ₐ[ℚ] Kp) x)
      rw [AlgEquiv.mul_apply, ← e, ← e, ← AlgEquiv.mul_apply, hG σ, AlgEquiv.one_apply,
        AlgEquiv.one_apply]
    exact Leopoldt.leopoldt_totallyReal_multiquadratic p Kp hG'

end LeopoldtMultiquadraticCor

theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (hG : ∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1) :
    Leopoldt.LeopoldtConjecture p K :=
  LeopoldtMultiquadraticCor.main p K hG
