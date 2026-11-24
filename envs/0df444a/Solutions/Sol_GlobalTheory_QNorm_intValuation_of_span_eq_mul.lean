-- Prove2me | solution 1 for GlobalTheory.QNorm.intValuation_of_span_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:43:43.752964+00:00
-- url     : https://prove2.me/submissions/e972aaaf-5178-4c49-9321-11844d10049b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAdmissibleSupersetFinitePlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution {R : Type} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) (I : Ideal R) (hI : I ≠ 0) (hv : ¬ v.asIdeal ∣ I) (x : R)
    (hx0 : x ≠ 0) (hx : v.asIdeal * I = Ideal.span {x}) :
    v.intValuation x = WithZero.exp (-1) := by
  have hvd : v.asIdeal ∣ Ideal.span {x} := ⟨I, hx.symm⟩
  have hsq : ¬ v.asIdeal ^ 2 ∣ Ideal.span {x} := by
    rintro ⟨J, hJ⟩
    apply hv
    rw [← hx, pow_two, mul_assoc] at hJ
    exact ⟨J, mul_left_cancel₀ v.ne_bot hJ⟩
  have h1 : v.intValuation x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_dvd x 1).2 (by rwa [pow_one])
  have h2 : ¬ v.intValuation x ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => hsq ((v.intValuation_le_pow_iff_dvd x 2).1 h)
  have hne : v.intValuation x ≠ 0 := v.intValuation_ne_zero x hx0
  rw [← WithZero.exp_log hne] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  push_cast at h1 h2
  omega
end GlobalTheory.QNorm
