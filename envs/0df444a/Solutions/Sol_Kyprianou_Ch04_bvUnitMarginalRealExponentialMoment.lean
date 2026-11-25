-- Prove2me | solution 1 for Kyprianou.Ch04.bvUnitMarginalRealExponentialMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T12:15:48.275823+00:00
-- url     : https://prove2.me/submissions/78e8c5eb-5c60-426b-a203-92df24ff8274

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_KSATSingleFlip_Connect_compound_poisson_probability
import Theorems.Thm_Kyprianou_Ch04_bvMarginalSplitLaw
import Theorems.Thm_Kyprianou_Ch04_bvMarginalExponentSplit
import Theorems.Thm_Kyprianou_Ch04_bvSmallMarginalRealExpMoment
import Theorems.Thm_Kyprianou_Ch04_finiteCompoundPoissonRealExpMoment
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Multiply the real moments of the two independent marginal factors. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : Omega → Real) (hX : Measurable X)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ theta : Real, charFun (P.map X) theta =
      Complex.exp (Kyprianou.Ch01.levyTripleExponent T theta))
    (hBV : T.gaussianVariance = 0 ∧
      (∫⁻ x in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |x| ∂T.levyMeasure) < ⊤)
    (beta : Real)
    (hExp : Integrable (fun omega => Real.exp (beta * X omega)) P)
    (hJump : Integrable (fun x : Real => Real.exp (beta * x) - 1) T.levyMeasure) :
    (∫ omega, Real.exp (beta * X omega) ∂P) =
      Real.exp ((T.drift - ∫ x in Set.Ioo (-1 : Real) 1,
        x ∂T.levyMeasure) * beta +
        ∫ x, (Real.exp (beta * x) - 1) ∂T.levyMeasure) := by
  letI := Measure.isProbabilityMeasure_map hX.aemeasurable (μ := P)
  obtain ⟨nu, hn, hc, he⟩ := Kyprianou.Ch04.bvMarginalSplitLaw T hBV.1 (P.map X) hLK
  letI := hn
  let rho := T.levyMeasure.restrict {x : ℝ | 1 ≤ |x|}
  letI : IsFiniteMeasure rho := by
    apply isFiniteMeasure_restrict.mpr
    have hf : Measurable (fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2))) := by fun_prop
    have hsub : {x : ℝ | 1 ≤ |x|} ⊆
        {x : ℝ | 1 ≤ ENNReal.ofReal (min 1 (x ^ 2))} := by
      intro x hx
      have hx2 : 1 ≤ x ^ 2 := by
        have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx 2
        simpa only [one_pow, sq_abs] using hh
      simpa [min_eq_left hx2] using hx
    have h := mul_meas_ge_le_lintegral hf 1 (μ := T.levyMeasure)
    rw [one_mul] at h
    exact ne_top_of_le_ne_top T.levyMeasure_isLevyMeasure.2.ne
      ((measure_mono hsub).trans h)
  let f (x : ℝ) := Real.exp (beta*x)
  have hf : Integrable f rho := by
    have h : Integrable (fun x : ℝ => Real.exp (beta*x)-1) rho := hJump.integrableOn
    have heq : (fun x : ℝ => Real.exp (beta*x)-1) + (fun _ : ℝ => (1 : ℝ)) = f := by
      funext x
      simp [f]
    rw [← heq]
    exact h.add (integrable_const 1)
  letI : IsProbabilityMeasure (KSATSingleFlip.Connect.compoundPoisson rho) :=
    ⟨KSATSingleFlip.Connect.compound_poisson_probability rho⟩
  change P.map X = (KSATSingleFlip.Connect.compoundPoisson rho).conv nu at he
  obtain ⟨hJ, hJe⟩ := Kyprianou.Ch04.finiteCompoundPoissonRealExpMoment rho beta hf
  obtain ⟨hN, hNe⟩ := Kyprianou.Ch04.bvSmallMarginalRealExpMoment T hBV.2 nu hc beta
  have hi : Integrable f (P.map X) :=
    (integrable_map_measure (by fun_prop) hX.aemeasurable).2 hExp
  change (∫ w, f (X w) ∂P) = _
  rw [← integral_map hX.aemeasurable (by fun_prop), he, integral_conv (he ▸ hi)]
  simp_rw [show ∀ x y, f (x+y) = f x*f y from fun x y => by simp [f,mul_add,Real.exp_add],
    integral_const_mul, integral_mul_const]
  rw [hJe, hNe, ← Real.exp_add]
  congr 1
  exact Kyprianou.Ch04.bvMarginalExponentSplit T hBV.2 beta hJump
