-- Prove2me | solution 1 for Kyprianou.Ch04.bvSmallMarginalRealExpMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:52:19.913905+00:00
-- url     : https://prove2.me/submissions/e1276747-9ab2-46c8-b965-b5571bc23d3e

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch04_smallMarginalExactFiniteApprox
import Theorems.Thm_Kyprianou_Ch04_smallCompensatedRealExpBandLimitGeneral
import Theorems.Thm_Kyprianou_Ch03_momentSmallJumpCutoffSequenceV1
import Theorems.Thm_Kyprianou_Ch03_momentSmallJumpBandRealIntegralBoundV1
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_weak_moment_transfer
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Transfer exact exponential moments using uniform second moments. -/
theorem solution
    (T : LevyKhintchineTriple)
    (hBV : (∫⁻ x in Ioo (-1 : Real) 1,
        ENNReal.ofReal |x| ∂T.levyMeasure) < ⊤)
    (nu : Measure Real) [IsProbabilityMeasure nu]
    (hnu : ∀ xi : Real, charFun nu xi =
      Complex.exp (Complex.I * ((T.drift * xi : Real) : Complex) +
        ∫ x in Ioo (-1 : Real) 1,
          levyCompensatedIntegrand xi x ∂T.levyMeasure))
    (beta : Real) :
    Integrable (fun x : Real => Real.exp (beta*x)) nu ∧
      (∫ x, Real.exp (beta*x) ∂nu) =
      Real.exp (T.drift * beta +
        ∫ x in Ioo (-1 : Real) 1,
          (Real.exp (beta*x)-1-beta*x) ∂T.levyMeasure) := by
  obtain ⟨e, he, hz⟩ := Kyprianou.Ch03.momentSmallJumpCutoffSequenceV1
  let Q : ProbabilityMeasure ℝ := ⟨nu, inferInstance⟩
  obtain ⟨q, hw, hr⟩ := Kyprianou.Ch04.smallMarginalExactFiniteApprox T e he hz Q hnu
  let f (x : ℝ) := Real.exp (beta*x)
  let b := 2*beta
  let C := Real.exp (T.drift*b + ∫ x in Ioo (-1 : ℝ) 1,
    (Real.exp (b*x)-1-b*x) ∂T.levyMeasure)
  have hs : ∀ᶠ n in atTop, Integrable (fun x => f x ^ 2) (q n : Measure ℝ) ∧
      (∫ x, f x ^ 2 ∂(q n : Measure ℝ)) ≤ C := by
    have heq : (fun x => f x ^ 2) = fun x : ℝ => Real.exp (b*x) := by
      funext x
      rw [pow_two, ← Real.exp_add]
      congr 1
      dsimp [f, b]
      ring
    filter_upwards [] with n
    rw [heq, (hr n b).2]
    exact ⟨(hr n b).1, Real.exp_le_exp.mpr
      (add_le_add_right (Kyprianou.Ch03.momentSmallJumpBandRealIntegralBoundV1 T (e n) b) _)⟩
  have hl := Kyprianou.Ch04.smallCompensatedRealExpBandLimitGeneral T e he hz beta
  apply Kyprianou.Ch08.StageB.source_result81_weak_moment_transfer q Q hw f
    (by dsimp [f]; fun_prop) (fun x => (Real.exp_pos _).le) (fun n => (hr n beta).1) C _ hs
  have hm (n : Nat) : (∫ x, f x ∂(q n : Measure ℝ)) =
      Real.exp (T.drift * beta + ∫ x in {x : ℝ | e n ≤ |x| ∧ |x| < 1},
        (Real.exp (beta*x)-1-beta*x) ∂T.levyMeasure) := (hr n beta).2
  simp_rw [hm]
  exact (Real.continuous_exp.tendsto _).comp (tendsto_const_nhds.add hl)
