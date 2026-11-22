-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_levy_root_domain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T10:53:07.704141+00:00
-- url     : https://prove2.me/submissions/6d486608-0591-4da2-b0de-6ec507245e40

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_convexOn_nonnegative
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_marginals_antitone
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_exponent_unbounded
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_convex_root_bridge
import Mathlib.Probability.Moments.MGFAnalytic

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hnotneg : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω))) :
    A.ψ 0 = 0 ∧ ∀ q : ℝ, 0 ≤ q → IsScaleTransformDomainBridge A.ψ q := by
  letI : IsProbabilityMeasure P := A.isProbability
  have hmgf_exp (x : ℝ) (hx : 0 ≤ x) : mgf (A.X 1) P x = Real.exp (A.ψ x) := by
    simpa only [mgf, NNReal.coe_one, one_mul, AvramDividend.Classical.SpectrallyNegativeLevy.ψ]
      using (A.laplace 1 x hx).2
  have hzero : A.ψ 0 = 0 := by
    have h := hmgf_exp 0 le_rfl
    have hmgf_zero : mgf (A.X 1) P 0 = 1 := by simp [mgf]
    rw [hmgf_zero, ← Real.exp_zero] at h
    exact (Real.exp_injective h).symm
  have hinterior : Ioi (0 : ℝ) ⊆ interior (integrableExpSet (A.X 1) P) :=
    interior_maximal (fun x hx => (A.laplace 1 x (show 0 < x from hx).le).1) isOpen_Ioi
  have hmgf := (continuousOn_mgf (X := A.X 1) (μ := P)).mono hinterior
  have hcont : ContinuousOn A.ψ (Ioi (0 : ℝ)) := (hmgf.log (fun x hx => by
    rw [hmgf_exp x (show 0 < x from hx).le]
    exact Real.exp_ne_zero _)).congr fun x hx => by
      change A.ψ x = Real.log (mgf (A.X 1) P x)
      rw [hmgf_exp x (show 0 < x from hx).le, Real.log_exp]
  have ht : ∃ t : ℝ≥0, ¬ (∀ᵐ ω ∂P, A.X t ω ≤ 0) := by
    by_contra! h
    exact hnotneg (source_result81_levy_marginals_antitone A h)
  obtain ⟨t, ht⟩ := ht
  exact ⟨hzero, source_result81_convex_root_bridge A.ψ hzero
    (AvramDividend.Classical.levy_laplace_exponent_convexOn_nonnegative A)
    hcont (fun q => source_result81_levy_exponent_unbounded A (t := t) ht q)⟩
