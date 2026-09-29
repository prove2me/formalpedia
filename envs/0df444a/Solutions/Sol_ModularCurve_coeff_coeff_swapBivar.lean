-- Prove2me | solution 1 for ModularCurve.coeff_coeff_swapBivar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/da3294da-ea1f-5b50-b4a0-39c51478ac9f

import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_coeff_swapBivar

open ModularCurve Polynomial

theorem swapBivar_monomial (n : ℕ) (c : Polynomial ℤ) :
    swapBivar (Polynomial.monomial n c) = swapInner c * Polynomial.C Polynomial.X ^ n := by
  show (Polynomial.eval₂RingHom swapInner (Polynomial.C Polynomial.X))
      (Polynomial.monomial n c) = _
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]

theorem coeff_swapInner (c : Polynomial ℤ) (j : ℕ) :
    (swapInner c).coeff j = Polynomial.C (c.coeff j) := by
  show ((Polynomial.aeval (R := ℤ)
      (Polynomial.X : Polynomial (Polynomial ℤ))) c).coeff j = _
  induction c using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add, Polynomial.coeff_add, ha, hb, map_add]
  | monomial m d =>
      simp only [Polynomial.aeval_monomial, Polynomial.coeff_monomial]
      rw [show (algebraMap ℤ (Polynomial (Polynomial ℤ))) d
          = Polynomial.C (Polynomial.C d) from rfl,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases h : m = j
      · subst h; simp
      · simp [h, Ne.symm h]

theorem solution (Φ : Polynomial (Polynomial ℤ)) (i j : ℕ) :
    ((swapBivar Φ).coeff j).coeff i = (Φ.coeff i).coeff j := by
  induction Φ using Polynomial.induction_on' with
  | add f g hf hg =>
      simp only [map_add, Polynomial.coeff_add, hf, hg]
  | monomial n c =>
      rw [swapBivar_monomial, ← Polynomial.C_pow, mul_comm,
        Polynomial.coeff_C_mul, coeff_swapInner,
        mul_comm, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_monomial]
      rcases eq_or_ne n i with rfl | h
      · simp
      · simp [h, Ne.symm h]

end S_ModularCurve_coeff_coeff_swapBivar
end P2MW
export P2MW.S_ModularCurve_coeff_coeff_swapBivar (solution)
