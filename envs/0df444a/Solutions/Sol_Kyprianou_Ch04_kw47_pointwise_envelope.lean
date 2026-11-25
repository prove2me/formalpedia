-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_pointwise_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T11:29:30.683792+00:00
-- url     : https://prove2.me/submissions/fe15d180-a886-4121-8ce1-129a9408943c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_exp_bounds
import Theorems.Thm_Kyprianou_Ch04_kw47_bounded_unit_integral
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
:
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha),
    let supX : NNReal -> Omega -> Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let M : NNReal -> Omega -> Real := fun t omega =>
          L.ψ alpha * (∫ s in Set.Icc (0 : Real) (t : Real),
            Real.exp (-alpha * (supX (Real.toNNReal s) omega -
                               L.X (Real.toNNReal s) omega)) ∂volume) +
          1 - Real.exp (-alpha * (supX t omega - L.X t omega)) -
          alpha * supX t omega
        ∀ (t s : NNReal) (omega : Omega), s ≤ t →
          |M s omega| ≤ |L.ψ alpha| * (t : Real) + 2 + alpha * supX t omega := by 
  intro Omega inst P F L alpha hAlpha
  dsimp only
  intro t s w hs
  simp_rw [← Kyprianou.Ch04.kw47_runningSup_raw_eq L]
  let U := runningSup L
  let Z : NNReal → Real := fun r => Real.exp (-alpha * (U r w - L.X r w))
  let J := ∫ r in Set.Icc (0 : Real) (s : Real), Z r.toNNReal ∂volume
  have hz := Kyprianou.Ch04.kw47_reflected_exp_bounds L alpha hAlpha s w
  have hj : 0 ≤ J ∧ J ≤ (s : Real) := Kyprianou.Ch04.kw47_bounded_unit_integral
    (fun r => Z r.toNNReal) s
    (fun r => Kyprianou.Ch04.kw47_reflected_exp_bounds L alpha hAlpha r.toNNReal w)
  have hA : 0 ≤ alpha * U s w := mul_nonneg hAlpha (runningSup_eq_rawSup_nonneg L s w).2
  have hA' := mul_le_mul_of_nonneg_left ((runningSup_monotone_and_path_le L w).1 hs) hAlpha
  have hp : |L.ψ alpha * J| ≤ |L.ψ alpha| * (t : Real) := by
    rw [abs_mul, abs_of_nonneg hj.1]
    exact mul_le_mul_of_nonneg_left (hj.2.trans (by exact_mod_cast hs)) (abs_nonneg _)
  have h := abs_le.mp hp
  change |L.ψ alpha * J + 1 - Z s - alpha * U s w| ≤
    |L.ψ alpha| * (t : Real) + 2 + alpha * U t w
  exact abs_le.mpr ⟨by linarith [hz.1, hz.2, h.1], by linarith [hz.1, hz.2, h.2]⟩
