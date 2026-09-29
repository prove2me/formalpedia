-- Prove2me | solution 1 for HorizontalPadicL.newEigenform_residualRepresentation_exists_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T15:07:51.63705+00:00
-- url     : https://prove2.me/submissions/bc3453ac-1ff6-4e6a-bb42-4c732625eca9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HorizontalPadicL_eigenform_residualGaloisRepresentation_exists_v2
import Definitions.Def_KN_SeededPrimeGaloisDataV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

open NumberField Ideal FrobeniusDensity

theorem _root_.solution
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (_hnew : IsNewEigenform f) (η : DirichletCharacterWithLevel)
    (V : SeededEigenformPadicPlaceData (p := p) f η) :
    Nonempty (ResidualEigenformRepresentationData f η V) := by
  obtain ⟨D⟩ := eigenform_residualGaloisRepresentation_exists_v2
    hN hk ι f V.embedding
  let L := D.kernelField
  let 𝕜 := EigenformResidueField f V.embedding
  letI : Field L := D.kernelField_field
  letI : NumberField L := D.kernelField_numberField
  letI : IsGalois ℚ L := D.kernelField_galois
  letI : Field 𝕜 := f.coefficientResidueFieldField hN hk V.embedding
  letI : Fintype 𝕜 := f.coefficientResidueFieldFintype hN hk V.embedding
  let S : Finset ℕ := (N * p).primeFactors
  let A : Set ℕ := {ℓ : ℕ |
    ℓ ∉ S ∧ LanglandsTunnell.classIndicator (1 : L ≃ₐ[ℚ] L) ℓ = 1}
  have hcheb : IsChebotarevPrimeClass A :=
    IsChebotarevPrimeClass.ofFiniteGalois L (1 : L ≃ₐ[ℚ] L) S rfl
  have hprime : ∀ ⦃ℓ : ℕ⦄, ℓ ∈ A → ℓ.Prime := by
    intro ℓ hℓ
    have hind := hℓ.2
    unfold LanglandsTunnell.classIndicator at hind
    split at hind
    · rename_i hex
      exact hex.choose
    · simp at hind
  have hNp : N * p ≠ 0 :=
    Nat.mul_ne_zero (Nat.ne_of_gt hN) (Fact.out : p.Prime).ne_zero
  have hcoprime : ∀ ⦃ℓ : ℕ⦄, ℓ ∈ A → Nat.Coprime ℓ (N * p) := by
    intro ℓ hℓ
    have hℓp := hprime hℓ
    apply hℓp.coprime_iff_not_dvd.mpr
    intro hdvd
    exact hℓ.1 (Nat.mem_primeFactors.mpr ⟨hℓp, hdvd, hNp⟩)
  have hnear : ∀ ⦃ℓ : ℕ⦄, ℓ ∈ A →
      ‖V.embedding (f.coeff ℓ - 2)‖ < 1 := by
    intro ℓ hℓ
    have hind := hℓ.2
    unfold LanglandsTunnell.classIndicator at hind
    split at hind
    · rename_i hex
      obtain ⟨hℓp, Q, hQp, hQover, hQunr, hconj⟩ := hex
      have hcop := hcoprime hℓ
      letI : Q.IsPrime := hQp
      letI : Q.LiesOver (ratPrimeIdeal ℓ) := hQover
      letI : Finite ((𝓞 L) ⧸ Q) :=
        finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓp)
      have hFrob : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q = 1 :=
        isConj_one_right.mp hconj
      have htr := D.trace_frobenius hℓp hcop Q hQp hQover
      rw [hFrob, map_one] at htr
      have hmk : Ideal.Quotient.mk (f.coefficientPrime V.embedding)
          (f.integralCoeff hN hk ℓ - 2) = 0 := by
        rw [map_sub, map_ofNat, ← htr]
        simp
      have hmem : f.integralCoeff hN hk ℓ - 2 ∈
          f.coefficientPrime V.embedding :=
        Ideal.Quotient.eq_zero_iff_mem.mp hmk
      have hnorm := (f.mem_coefficientPrime_iff V.embedding
        (f.integralCoeff hN hk ℓ - 2)).mp hmem
      have hcoe :
          (((f.integralCoeff hN hk ℓ - 2 : 𝓞 f.coefficientField) :
              f.coefficientField) : MTT.Qbar) = f.coeff ℓ - 2 := by
        rfl
      rw [hcoe] at hnorm
      simpa [map_sub, map_ofNat] using hnorm
    · simp at hind
  exact ⟨ResidualEigenformRepresentationData.ofRepresentation
    L 𝕜 D.representation A hcheb hprime hnear hcoprime⟩

end HorizontalPadicL
