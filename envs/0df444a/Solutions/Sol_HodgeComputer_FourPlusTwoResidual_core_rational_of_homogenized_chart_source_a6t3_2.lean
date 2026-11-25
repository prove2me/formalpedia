-- Prove2me | solution 2 for HodgeComputer.FourPlusTwoResidual.core_rational_of_homogenized_chart_source_a6t3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T16:12:27.14898+00:00
-- url     : https://prove2.me/submissions/591da67c-b710-4cf6-b47f-9ab138dd7e1d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_homogenized_chart_source_a6t3_iff_ratio_chart_t4
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_core_rational_current_of_ratio_chart_t4_witness
import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

open MvPolynomial

theorem solution
    (h : ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K),
      a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (let H := a ^ 6 * P
          let db := fun z : K => Dr z / a
          let dc := fun z : K => (Dt z - s / t * Ds z) / a
          let dd := fun z : K => Ds z / (a * t)
          let pb := (2 : K) * a * qr / (3 * t)
          let pc := (2 : K) * a * qt / (3 * t)
          let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
          pb * db H + pc * dc H + pd * dd H -
            (3 / 2 : K) * H * (db pb + dc pc + dd pd) = a ^ 6 * t ^ 3)) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (_ : Algebra (MvPolynomial (Fin 4) ℂ) K)
      (_ : IsFractionRing (MvPolynomial (Fin 4) ℂ) K)
      (δ : Fin 4 → Derivation ℤ K K) (v : Fin 4 → K),
      (∀ (i : Fin 4) (p : MvPolynomial (Fin 4) ℂ),
          δ i (algebraMap (MvPolynomial (Fin 4) ℂ) K p) =
            algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.pderiv i p)) ∧
        HodgeComputer.FourPlusTwoResidual.CoreRationalEquation δ v := by
  obtain ⟨K, _instField, _instCharZero, Dr, Ds, Dt, a, s, t, P, qr, qs, qt,
      ha, ht, hDr_a, hDs_a, hDt_a, hDr_t, hDs_t, hDt_t, hDs_s, hsrc⟩ := h
  have ht4 : -(P * (Dr qr + Ds qs + Dt qt) -
        (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) = t ^ 4 :=
    (HodgeComputer.FourPlusTwoResidual.homogenized_chart_source_a6t3_iff_ratio_chart_t4
      Dr Ds Dt a s t P qr qs qt ha ht hDr_a hDs_a hDt_a hDr_t hDs_t hDt_t hDs_s).mp hsrc
  exact HodgeComputer.FourPlusTwoResidual.exists_core_rational_current_of_ratio_chart_t4_witness
    ⟨K, _instField, _instCharZero, Dr, Ds, Dt, a, s, t, P, qr, qs, qt,
      ha, ht, hDr_a, hDs_a, hDt_a, hDr_t, hDs_t, hDt_t, hDs_s, ht4⟩
