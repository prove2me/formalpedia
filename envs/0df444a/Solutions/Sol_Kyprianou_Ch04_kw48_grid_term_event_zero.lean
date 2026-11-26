-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_grid_term_event_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:55:39.673214+00:00
-- url     : https://prove2.me/submissions/780f16f2-5e4b-44a6-ad21-f6f831bd0f24

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_product_integrable
import Theorems.Thm_Kyprianou_Ch04_kw48_weighted_characteristic_expectation
import Theorems.Thm_Kyprianou_Ch04_kw48_Z_adapted
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every predictable product-grid term is integrable and has zero
integral over every event in the filtration at its left endpoint. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ w, Complex.exp (Complex.I*(theta:Complex)*(L.X t w:Complex)) ∂P) =
      Complex.exp (-((t:Real):Complex)*Psi theta))
    (alpha beta : Real) (s t : NNReal) (hst : s ≤ t) :
    let q : Ω → Complex := fun w =>
      H L Psi alpha beta s w*(E L Psi alpha t w-E L Psi alpha s w)
    Integrable q P ∧
      ∀ A : Set Ω, MeasurableSet[F s] A → (∫ w in A, q w ∂P) = 0 := by
  dsimp only
  have hInt (r : NNReal) := Kyprianou.Ch04.kw48_grid_product_integrable
    L Psi alpha beta s r
  have hQ : Integrable (fun w =>
      H L Psi alpha beta s w*(E L Psi alpha t w-E L Psi alpha s w)) P := by
    simp_rw [mul_sub]
    exact (hInt t).sub (hInt s)
  refine ⟨hQ,?_⟩
  intro A hA
  let W : Ω → Complex := A.indicator (H L Psi alpha beta s)
  have hW : Measurable[F s] W :=
    (Kyprianou.Ch04.kw48_Z_adapted L Psi alpha beta s).2.2.indicator hA
  have hAamb : MeasurableSet A := (F.le s) A hA
  have hEq (r : NNReal) : (∫ w, W w*E L Psi alpha r w ∂P) =
      (∫ w in A, H L Psi alpha beta s w*E L Psi alpha r w ∂P) := by
    rw [← integral_indicator hAamb]
    apply integral_congr_ae
    filter_upwards [] with w
    by_cases hw : w ∈ A <;> simp [W,Set.indicator_apply,hw]
  have h := Kyprianou.Ch04.kw48_weighted_characteristic_expectation
    L Psi hPsi alpha s t hst W hW
  rw [hEq,hEq] at h
  simp_rw [mul_sub]
  rw [integral_sub (hInt t).integrableOn (hInt s).integrableOn]
  exact sub_eq_zero.mpr h
