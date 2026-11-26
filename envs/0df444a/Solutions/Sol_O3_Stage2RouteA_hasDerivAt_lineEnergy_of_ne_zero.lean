-- Prove2me | solution 1 for O3.Stage2RouteA.hasDerivAt_lineEnergy_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:35:25.340065+00:00
-- url     : https://prove2.me/submissions/b138663d-615a-45d5-8f82-4ac31a0c56f2

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteA_hasDerivAt_linePower
import Theorems.Thm_O3_Stage2RouteA_lpPower_rpow_two_div_sub_one_eq
import Theorems.Thm_O3_lpNorm_pos_of_ne_zero
import Theorems.Thm_O3_lpPower_pos_of_ne_zero


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : x + t • h ≠ 0) :
    HasDerivAt (lineEnergy p x h)
      (pairing (dualityMap p (x + t • h)) h) t := by
  have hp0 : p ≠ 0 := by linarith
  have hS : linePower p x h t ≠ 0 := by
    exact (lpPower_pos_of_ne_zero hz).ne'
  have hpow := (hasDerivAt_linePower hp x h t).rpow_const
    (Or.inl hS) (p := 2 / p)
  have hscaled := hpow.const_mul (1 / 2 : ℝ)
  have hnorm : lpNorm p (x + t • h) ≠ 0 :=
    (lpNorm_pos_of_ne_zero hz).ne'
  have hpair : pairing (dualityMap p (x + t • h)) h =
      (1 / 2 : ℝ) * (linePowerDerivative p x h t * (2 / p) *
        linePower p x h t ^ (2 / p - 1)) := by
    rw [dualityMap, if_neg hnorm, linePowerDerivative, linePower,
      lpPower_rpow_two_div_sub_one_eq hp0 hz]
    unfold pairing powerDualityMap
    have hfactor :
        (∑ i : Fin d, (fun i ↦ lpNorm p (x + t • h) ^ (2 - p) *
            (|(x + t • h) i| ^ (p - 2) * (x + t • h) i)) i * h i) =
          lpNorm p (x + t • h) ^ (2 - p) *
            ∑ i : Fin d, |(x + t • h) i| ^ (p - 2) * (x + t • h) i * h i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hfactor]
    field_simp
  rw [hpair]
  change HasDerivAt (fun s : ℝ ↦
    (1 / 2 : ℝ) * linePower p x h s ^ (2 / p))
    ((1 / 2 : ℝ) * (linePowerDerivative p x h t * (2 / p) *
      linePower p x h t ^ (2 / p - 1))) t
  exact hscaled
end O3.Stage2RouteA
