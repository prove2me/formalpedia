-- Prove2me | solution 1 for Kyprianou.Ch03.momentLargeJumpLawCriterionV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:46:42.331376+00:00
-- url     : https://prove2.me/submissions/560970b8-424d-462f-a899-c739ddc907f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_KSATSingleFlip_Connect_compound_poisson_probability
import Theorems.Thm_Kyprianou_Ch03_momentCompoundPoissonCharFunV1
import Theorems.Thm_Kyprianou_Ch03_momentCompoundPoissonSubmulIffV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) (t : NNReal) (ht : 0 < t)
    (mu : Measure Real) [IsProbabilityMeasure mu]
    (hmu : ∀ xi : Real, charFun mu xi = Complex.exp (((t : Real) : Complex) *
        ∫ x in {x : Real | 1 ≤ |x|},
          (Complex.exp (Complex.I * (((xi * x : Real) : Complex))) - 1) ∂T.levyMeasure))
    (g : Real → Real) (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g) :
    Integrable g mu ↔ IntegrableOn g {x : Real | 1 ≤ |x|} T.levyMeasure := by
  let rho := (t : ENNReal) • T.levyMeasure.restrict {x : ℝ | 1 ≤ |x|}
  letI : IsFiniteMeasure (T.levyMeasure.restrict {x : ℝ | 1 ≤ |x|}) := by
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
  letI : IsFiniteMeasure rho := by dsimp [rho]; infer_instance
  have hp := KSATSingleFlip.Connect.compound_poisson_probability rho
  letI : IsProbabilityMeasure (KSATSingleFlip.Connect.compoundPoisson rho) := ⟨hp⟩
  have he : mu = KSATSingleFlip.Connect.compoundPoisson rho := by
    apply Measure.ext_of_charFun
    funext xi
    rw [hmu xi, Kyprianou.Ch03.momentCompoundPoissonCharFunV1 rho xi]
    dsimp [rho]
    rw [integral_smul_nnreal_measure]
    congr 1
  rw [he, Kyprianou.Ch03.momentCompoundPoissonSubmulIffV1 rho g hg hg_meas]
  exact integrable_smul_measure (by exact_mod_cast ht.ne') ENNReal.coe_ne_top
