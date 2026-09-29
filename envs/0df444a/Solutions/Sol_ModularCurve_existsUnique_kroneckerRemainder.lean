-- Prove2me | solution 1 for ModularCurve.existsUnique_kroneckerRemainder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b28e0c45-46ad-53a5-9a1e-4da9666e92c1

import Mathlib
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_existsUnique_kroneckerRemainder

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_existsUnique_kroneckerRemainder.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence ModularPolynomialData"
namespace K2R
p2m_open "ModularCurve"

theorem C_C_dvd_of_reduceModBivar_eq_zero (p : ℕ) (D : Polynomial (Polynomial ℤ))
    (hD : reduceModBivar p D = 0) : C (C (p : ℤ)) ∣ D := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro j
  have h := congrArg (fun Q : Polynomial (Polynomial (ZMod p)) => (Q.coeff i).coeff j) hD
  simp only [reduceModBivar, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
    Polynomial.coeff_zero, eq_intCast] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h

theorem main (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (hK : KroneckerCongruence p data) :
    ∃! R : Polynomial (Polynomial ℤ),
      data.Φ = (C X ^ p - X) * (C X - X ^ p) + C (C (p : ℤ)) * R := by
  have hp0 : (C (C (p : ℤ)) : Polynomial (Polynomial ℤ)) ≠ 0 := by
    simp [(Fact.out : p.Prime).ne_zero]

  have hred : reduceModBivar p (data.Φ - (C X ^ p - X) * (C X - X ^ p)) = 0 := by
    rw [map_sub, hK]
    simp [map_mul, map_sub, map_pow, reduceModBivar_X, reduceModBivar_C_X]
  obtain ⟨R, hR⟩ := C_C_dvd_of_reduceModBivar_eq_zero p _ hred
  refine ⟨R, ?_, ?_⟩
  · show data.Φ = (C X ^ p - X) * (C X - X ^ p) + C (C (p : ℤ)) * R
    rw [← hR]; ring
  · intro R' hR'
    have h : C (C (p : ℤ)) * R' = C (C (p : ℤ)) * R := by
      rw [← hR, hR']; ring
    exact mul_left_cancel₀ hp0 h

end ModularCurve.K2R

theorem solution (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (hK : KroneckerCongruence p data) :
    ∃! R : Polynomial (Polynomial ℤ),
      data.Φ = (C X ^ p - X) * (C X - X ^ p) + C (C (p : ℤ)) * R :=
  ModularCurve.K2R.main p data hK

end S_ModularCurve_existsUnique_kroneckerRemainder
end P2MW
export P2MW.S_ModularCurve_existsUnique_kroneckerRemainder (solution)
