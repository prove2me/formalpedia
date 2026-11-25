-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.ratio_chart_t4_yields_homogenized_source_a6t3
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T12:05:38.49223+00:00
-- url     : https://prove2.me/submissions/c74503c3-e21e-4f56-a04f-b3d40924578a

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_ratioChart_transport

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual

theorem solution
    (h : ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K),
      a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (-(P * (Dr qr + Ds qs + Dt qt) -
            (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) = t ^ 4)) :
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
  obtain ⟨K, fieldK, charK, Dr, Ds, Dt, a, s, t, P, qr, qs, qt,
    ha, ht, hDra, hDsa, hDta, hDrt, hDst, hDtt, hDss, hsrc⟩ := h
  refine ⟨K, fieldK, charK, Dr, Ds, Dt, a, s, t, P, qr, qs, qt,
    ha, ht, hDra, hDsa, hDta, hDrt, hDst, hDtt, hDss, ?_⟩
  simpa using (ratioChart_transport (K := K) Dr Ds Dt a s t P qr qs qt
    ha ht hDra hDsa hDta hDrt hDst hDtt hDss hsrc)
