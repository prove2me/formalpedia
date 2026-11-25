-- Prove2me | solution 1 for Kyprianou.Ch04.bvMarginalSplitLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:09:51.422397+00:00
-- url     : https://prove2.me/submissions/db1e35cb-0798-4b6f-9972-35e2d6f3ad24

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_levyItoDecompositionCorrected
import Theorems.Thm_Kyprianou_Ch03_momentMarginalLargeSmallFactorizationV1
import Theorems.Thm_Kyprianou_Ch03_momentLargeJumpLawCriterionV1
import Theorems.Thm_Kyprianou_Ch03_momentCompoundPoissonCharFunV1
import Theorems.Thm_KSATSingleFlip_Connect_compound_poisson_probability
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Identify the large marginal using the Chapter 3 moment criterion at one. -/
theorem solution
    (T : LevyKhintchineTriple) (hG : T.gaussianVariance = 0)
    (mu : Measure Real) [IsProbabilityMeasure mu]
    (hmu : ∀ xi : Real, charFun mu xi =
      Complex.exp (Kyprianou.Ch01.levyTripleExponent T xi)) :
    ∃ nu : Measure Real, IsProbabilityMeasure nu ∧
      (∀ xi : Real, charFun nu xi =
        Complex.exp (Complex.I * ((T.drift * xi : Real) : Complex) +
          ∫ x in Ioo (-1 : Real) 1, levyCompensatedIntegrand xi x ∂T.levyMeasure)) ∧
      mu = (KSATSingleFlip.Connect.compoundPoisson
        (T.levyMeasure.restrict {x : Real | 1 ≤ |x|})).conv nu := by
  obtain ⟨hσ, Ω, m, Q, hQ, B, N, G, L, S, F, _, _, _, _, _, _, _, _, _, _, _, hsum, hc⟩ :=
    Kyprianou.levyItoDecompositionCorrected (-T.drift) 0
      T.levyMeasure T.levyMeasure_isLevyMeasure
  letI : MeasurableSpace Ω := m
  letI : IsProbabilityMeasure Q := hQ
  letI : SigmaFinite T.levyMeasure := hσ
  let X (t : NNReal) (w : Ω) := G t w + L t w + S t w
  have ht : (⟨- -T.drift, 0 ^ 2, T.levyMeasure, T.levyMeasure_isLevyMeasure⟩ :
      LevyKhintchineTriple) = T := by
    cases T
    simp_all
  have hc' : ∀ (t : NNReal) (xi : ℝ), charFun (Q.map (X t)) xi =
      Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T xi) := by
    intro t xi
    have hh := hc t xi
    rw [ht] at hh
    exact hh
  obtain ⟨p, nu, hp, hn, he, hpc, hnc⟩ :=
    Kyprianou.Ch03.momentMarginalLargeSmallFactorizationV1 Q X hsum T hc' 1 (by positivity)
  letI := hp
  letI := hn
  let rho := T.levyMeasure.restrict {x : ℝ | 1 ≤ |x|}
  have hg : Kyprianou.Ch03.IsSubmultiplicative (fun _ : ℝ => (1 : ℝ)) := by
    refine ⟨fun _ => zero_le_one, 1, one_pos, ?_⟩
    intro x y
    norm_num
  have hi : Integrable (fun _ : ℝ => (1 : ℝ)) rho :=
    (Kyprianou.Ch03.momentLargeJumpLawCriterionV1 T 1 one_pos p hpc
      _ hg measurable_const).mp (integrable_const 1)
  letI : IsFiniteMeasure rho := (integrable_const_iff.mp hi).resolve_left one_ne_zero
  let J := KSATSingleFlip.Connect.compoundPoisson rho
  letI : IsProbabilityMeasure J := ⟨KSATSingleFlip.Connect.compound_poisson_probability rho⟩
  have hpJ : p = J := by
    apply Measure.ext_of_charFun
    funext xi
    rw [hpc, Kyprianou.Ch03.momentCompoundPoissonCharFunV1 rho]
    simp [rho]
  refine ⟨nu, hn, fun xi => by simpa [hG] using hnc xi, ?_⟩
  change mu = J.conv nu
  rw [← hpJ]
  change mu = (p.prod nu).map (fun z : ℝ × ℝ => z.1+z.2)
  rw [← he]
  letI : IsProbabilityMeasure (Q.map (X 1)) :=
    Measure.isProbabilityMeasure_map (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 Q X hsum 1)
  apply Measure.ext_of_charFun
  funext xi
  rw [hmu, hc']
  simp
