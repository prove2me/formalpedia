-- Prove2me | solution 1 for Kyprianou.Ch03.exponentRegularity_smoothPositive
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:05:04.548187+00:00
-- url     : https://prove2.me/submissions/b007263b-59cd-476a-86b4-949c0efe91f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace SmoothAux

lemma psi_eq_cgf {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) (θ : ℝ) (hθ : 0 ≤ θ) :
    L.ψ θ = cgf (L.X 1) P θ := by
  have h := (L.laplace 1 θ hθ).2
  simp only [NNReal.coe_one, one_mul] at h
  rw [cgf, mgf, h, Real.log_exp]
  rfl

lemma subset_interior {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    Set.Ioi (0:ℝ) ⊆ interior (integrableExpSet (L.X 1) P) := by
  apply interior_maximal _ isOpen_Ioi
  intro θ hθ
  exact (L.laplace 1 θ (le_of_lt hθ)).1

end SmoothAux

theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) L.ψ (Set.Ioi 0) := by
  have hA : AnalyticOnNhd ℝ (cgf (L.X 1) P) (Set.Ioi 0) :=
    fun θ hθ => analyticAt_cgf (SmoothAux.subset_interior L hθ)
  have hC : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (cgf (L.X 1) P) (Set.Ioi 0) :=
    hA.contDiffOn_of_completeSpace
  exact hC.congr fun θ hθ => SmoothAux.psi_eq_cgf L θ (le_of_lt hθ)
