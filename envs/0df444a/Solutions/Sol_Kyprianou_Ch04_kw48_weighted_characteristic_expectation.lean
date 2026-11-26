-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_weighted_characteristic_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:41:33.824532+00:00
-- url     : https://prove2.me/submissions/466b0c9f-a2de-4d9a-b41f-99adfc82bbfb

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_characteristic_increment_mean_one
import Theorems.Thm_Kyprianou_Ch04_kw48_independent_weight_integral
import Theorems.Thm_Kyprianou_Ch04_kw48_Z_adapted
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The normalised characteristic exponential preserves every
measurable past-weighted expectation in the actual filtration. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ w, Complex.exp (Complex.I * (theta : Complex) *
        (L.X t w : Complex)) ∂P) =
      Complex.exp (-((t : Real) : Complex) * Psi theta))
    (alpha : Real) (s t : NNReal) (hst : s ≤ t)
    (W : Ω → Complex) (hW : Measurable[F s] W) :
    (∫ w, W w * E L Psi alpha t w ∂P) =
      (∫ w, W w * E L Psi alpha s w ∂P) := by
  let D : Ω → Real := fun w => L.X t w-L.X s w
  let phi : Real → Complex := fun z =>
    Complex.exp (Complex.I*(alpha:Complex)*(z:Complex)+
      (((t-s:NNReal):Real):Complex)*Psi alpha)
  let V : Ω → Complex := fun w => W w * E L Psi alpha s w
  have hD : Measurable D :=
    ((L.adapted t).mono (F.le t) le_rfl).sub
      ((L.adapted s).mono (F.le s) le_rfl)
  have hV : Measurable[F s] V :=
    hW.mul (Kyprianou.Ch04.kw48_Z_adapted L Psi alpha 0 s).2.1
  have hphi : Measurable phi := by
    unfold phi
    fun_prop
  have hProd := Kyprianou.Ch04.kw48_independent_weight_integral
    P (F s) (F.le s) D V phi hD hV hphi (L.indepIncrements s t hst)
  have hMean : (∫ w, phi (D w) ∂P) = 1 :=
    Kyprianou.Ch04.kw48_characteristic_increment_mean_one L Psi hPsi alpha s t hst
  have hFactor (w : Ω) : W w * E L Psi alpha t w = phi (D w) * V w := by
    dsimp only [E,phi,D,V]
    rw [mul_left_comm,← Complex.exp_add,NNReal.coe_sub hst]
    congr 2
    push_cast
    ring
  simp only [hFactor,hMean,one_mul] at hProd ⊢
  exact hProd
