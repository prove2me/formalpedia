-- Prove2me | solution 1 for HorizontalPadicL.residualKernel_discr_prime_dvd_level_mul_p
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-20T15:02:45.151513+00:00
-- url     : https://prove2.me/submissions/0cbcfc71-f2fd-4087-9ebd-55d7ace13654

import Definitions.Def_KN_EigenformResidualGaloisRepresentationV2
import Mathlib.NumberTheory.NumberField.Discriminant.Different

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

open NumberField Ideal FrobeniusDensity

theorem _root_.solution
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ}
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p])
    (D : EigenformResidualGaloisRepresentationData hN hk f ιp) :
    letI : Field D.kernelField := D.kernelField_field
    letI : NumberField D.kernelField := D.kernelField_numberField
    ∀ {l : ℕ}, l.Prime →
      (l : ℤ) ∣ NumberField.discr D.kernelField → l ∣ N * p := by
  let K := D.kernelField
  letI : Field K := D.kernelField_field
  letI : NumberField K := D.kernelField_numberField
  letI : IsGalois ℚ K := D.kernelField_galois
  intro l hl hldisc
  by_contra hldvd
  have hlcop : Nat.Coprime l (N * p) :=
    hl.coprime_iff_not_dvd.mpr hldvd
  have hnotdisc : ¬ (l : ℤ) ∣ NumberField.discr K := by
    rw [NumberField.not_dvd_discr_iff_forall_liesOver K (𝓞 K)
      (Nat.prime_iff_prime_int.mp hl)]
    intro Q hQmax hQover
    letI : Fact l.Prime := ⟨hl⟩
    letI : Q.IsPrime := hQmax.isPrime
    letI : Q.LiesOver (ratPrimeIdeal l) := hQover
    have hI : Q.inertia (K ≃ₐ[ℚ] K) = ⊥ :=
      D.unramified_outside hl hlcop Q inferInstance inferInstance
    rw [← Ideal.ramificationIdx_eq_one_iff,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx
        (ratPrimeIdeal l) Q (K ≃ₐ[ℚ] K),
      ← Ideal.card_inertia_eq_ramificationIdxIn
        (G := K ≃ₐ[ℚ] K) (ratPrimeIdeal l) Q,
      hI]
    simp
  exact hnotdisc hldisc

end HorizontalPadicL
