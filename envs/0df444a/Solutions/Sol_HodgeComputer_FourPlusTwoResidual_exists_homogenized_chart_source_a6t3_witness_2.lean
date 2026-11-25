-- Prove2me | solution 2 for HodgeComputer.FourPlusTwoResidual.exists_homogenized_chart_source_a6t3_witness
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T16:24:32.855799+00:00
-- url     : https://prove2.me/submissions/0135a571-c1d1-4a0a-b202-ef85a9ed63d8

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_ratio_chart_t4_witness
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_homogenized_chart_source_a6t3_iff_ratio_chart_t4
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

/-- **Unconditional chart-source witness.** The homogenized chart source `a^6*t^3` is
realised by an explicit field, derivations and elements: the ratio-chart identity with
source `t^4` is a theorem of the platform (`exists_ratio_chart_t4_witness`), and chart
clearing (`homogenized_chart_source_a6t3_iff_ratio_chart_t4`) turns it into the
homogenized chart source. So the hypothesis of
`core_rational_of_homogenized_chart_source_a6t3` holds without any further assumption:
that branch of the mission is unconditional, and only the core rational current is
still open. -/
theorem solution :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
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
           (3 / 2 : K) * H * (db pb + dc pc + dd pd) = a ^ 6 * t ^ 3) := by
  obtain ⟨K, hField, hCharZero, Dr, Ds, Dt, a, s, t, P, qr, qs, qt,
      ha, ht, hDr_a, hDs_a, hDt_a, hDr_t, hDs_t, hDt_t, hDs_s, ht4⟩ :=
    HodgeComputer.FourPlusTwoResidual.exists_ratio_chart_t4_witness
  refine ⟨K, hField, hCharZero, Dr, Ds, Dt, a, s, t, P, qr, qs, qt,
    ha, ht, hDr_a, hDs_a, hDt_a, hDr_t, hDs_t, hDt_t, hDs_s, ?_⟩
  exact (HodgeComputer.FourPlusTwoResidual.homogenized_chart_source_a6t3_iff_ratio_chart_t4
    Dr Ds Dt a s t P qr qs qt ha ht hDr_a hDs_a hDt_a hDr_t hDs_t hDt_t hDs_s).mpr ht4
