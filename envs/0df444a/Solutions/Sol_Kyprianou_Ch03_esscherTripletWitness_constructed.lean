-- Prove2me | solution 1 for Kyprianou.Ch03.esscherTripletWitness_constructed
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:38:24.367063+00:00
-- url     : https://prove2.me/submissions/a02c41f6-2069-400c-946d-f7983b017a9c

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace ETWAux

lemma tilt_isLevy (ν : Measure ℝ) (hν : IsLevyMeasure ν) (beta : ℝ)
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (beta * x)) {x : ℝ | 1 ≤ |x|} ν) :
    IsLevyMeasure (ν.withDensity (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x)))) := by
  have hfm : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x))) := by fun_prop
  refine ⟨?_, ?_⟩
  · rw [withDensity_apply _ (measurableSet_singleton 0), Measure.restrict_eq_zero.2 hν.1,
      lintegral_zero_measure]
  · rw [lintegral_withDensity_eq_lintegral_mul _ hfm (by fun_prop)]
    set S : Set ℝ := {x : ℝ | |x| < 1} with hS
    have hSm : MeasurableSet S := measurableSet_lt (by fun_prop) measurable_const
    have hSc : Sᶜ = {x : ℝ | 1 ≤ |x|} := by ext x; simp [hS]
    rw [← lintegral_add_compl _ hSm]
    refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · calc ∫⁻ x in S, ((fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x))) *
            fun x => ENNReal.ofReal (min 1 (x ^ 2))) x ∂ν
          ≤ ∫⁻ x in S, ENNReal.ofReal (Real.exp |beta|) * ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
            apply setLIntegral_mono' hSm
            intro x hx
            simp only [Pi.mul_apply]
            gcongr
            have hx1 : |x| < 1 := hx
            calc beta * x ≤ |beta * x| := le_abs_self _
              _ = |beta| * |x| := abs_mul _ _
              _ ≤ |beta| * 1 := by gcongr
              _ = |beta| := mul_one _
        _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp |beta|) * ENNReal.ofReal (min 1 (x ^ 2)) ∂ν :=
            setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal (Real.exp |beta|) * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν :=
            lintegral_const_mul _ (by fun_prop)
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν.2
    · rw [hSc]
      calc ∫⁻ x in {x : ℝ | 1 ≤ |x|}, ((fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x))) *
            fun x => ENNReal.ofReal (min 1 (x ^ 2))) x ∂ν
          ≤ ∫⁻ x in {x : ℝ | 1 ≤ |x|}, ENNReal.ofReal (Real.exp (beta * x)) ∂ν := by
            apply lintegral_mono
            intro x
            simp only [Pi.mul_apply]
            calc ENNReal.ofReal (Real.exp (beta * x)) * ENNReal.ofReal (min 1 (x ^ 2))
                ≤ ENNReal.ofReal (Real.exp (beta * x)) * 1 := by
                  gcongr
                  rw [ENNReal.ofReal_le_one]; exact min_le_left _ _
              _ = _ := mul_one _
        _ < ⊤ := hBeta.lintegral_lt_top

end ETWAux

open ETWAux in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : Real)
    (hBeta : IntegrableOn
      (fun x : Real => Real.exp (beta * x))
      {x : Real | 1 <= abs x} T.levyMeasure)
    (hEsscher : forall (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A ->
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              Kyprianou.Ch03.esscherDensity X beta
                (Real.log
                  (∫ eta, Real.exp (beta * X 1 eta) ∂P))
                t omega) omega ∂P)) :
    exists (Tbeta : ProbabilityTheory.LevyKhintchineTriple),
      Tbeta.drift =
        T.drift + beta * (T.gaussianVariance : Real) +
          ∫ x in {x : Real | abs x < 1},
            (Real.exp (beta * x) - 1) * x ∂T.levyMeasure ∧ Tbeta.gaussianVariance = T.gaussianVariance ∧ Tbeta.levyMeasure =
        T.levyMeasure.withDensity
          (fun x : Real => ENNReal.ofReal (Real.exp (beta * x))) :=
  ⟨⟨T.drift + beta * (T.gaussianVariance : Real) +
      ∫ x in {x : Real | abs x < 1}, (Real.exp (beta * x) - 1) * x ∂T.levyMeasure,
    T.gaussianVariance,
    T.levyMeasure.withDensity (fun x : Real => ENNReal.ofReal (Real.exp (beta * x))),
    tilt_isLevy _ T.levyMeasure_isLevyMeasure beta hBeta⟩, rfl, rfl, rfl⟩
