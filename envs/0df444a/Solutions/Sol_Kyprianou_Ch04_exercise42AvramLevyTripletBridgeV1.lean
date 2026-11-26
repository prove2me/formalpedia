-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42AvramLevyTripletBridgeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:05:16.378025+00:00
-- url     : https://prove2.me/submissions/7ae59669-8882-469e-8eba-7a262ab9690c

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_exercise42AvramIsLevyProcessV1
import Theorems.Thm_Kyprianou_Ch04_exercise42NegativeUncompensatedExponentV1
import Theorems.Thm_Kyprianou_Ch04_exercise42DeficitCharacteristicV1
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The same-space BV triplet with the original source measure. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) :
    letI : IsProbabilityMeasure P := L.isProbability
    IsLevyProcess L.X P ∧
    ∃ triplet : LevyKhintchineTriple,
      (∀ (t : NNReal) (xi : Real),
        charFun (P.map (L.X t)) xi =
          Complex.exp (((t : Real) : Complex) *
            Kyprianou.Ch01.levyTripleExponent triplet xi)) ∧
      (triplet.gaussianVariance = 0 ∧
        (∫⁻ y in Set.Ioo (-1 : Real) 1,
          ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤) ∧
      triplet.drift - ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure = L.drift := by
  obtain ⟨hν, _⟩ := Kyprianou.Ch04.exercise42NegativeUncompensatedExponentV1 P F L hBV 0
  have hn : ∀ᵐ y ∂L.ν, y < 0 := by
    rw [ae_iff]
    have he : {y : ℝ | ¬ y < 0} = Ici (0 : ℝ) := by ext y; simp [not_lt]
    rw [he]
    exact L.ν_Ici
  have hSet : Ioo (-1 : ℝ) 1 =ᵐ[L.ν] Ioo (-1 : ℝ) 0 := by
    filter_upwards [hn] with y hy
    change ((-1 < y ∧ y < 1) = (-1 < y ∧ y < 0))
    exact propext ⟨fun h => ⟨h.1, hy⟩, fun h => ⟨h.1, by linarith⟩⟩
  refine ⟨Kyprianou.Ch04.exercise42AvramIsLevyProcessV1 P F L, ⟨L.c, 0, L.ν, hν⟩, ?_, ⟨rfl, ?_⟩, ?_⟩
  · intro t xi
    obtain ⟨hν', he⟩ := Kyprianou.Ch04.exercise42NegativeUncompensatedExponentV1 P F L hBV xi
    rw [he]
    exact Kyprianou.Ch04.exercise42DeficitCharacteristicV1 P F L hBV t xi
  · change (∫⁻ y in Ioo (-1 : ℝ) 1, ENNReal.ofReal |y| ∂L.ν) < ⊤
    rw [Measure.restrict_congr_set hSet]
    exact hBV.2
  · change L.c - (∫ y in Ioo (-1 : ℝ) 1, y ∂L.ν) = L.drift
    unfold SpectrallyNegativeLevy.drift
    rw [Measure.restrict_congr_set hSet]
