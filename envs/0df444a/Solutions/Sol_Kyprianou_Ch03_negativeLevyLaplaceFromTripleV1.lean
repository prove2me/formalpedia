-- Prove2me | solution 1 for Kyprianou.Ch03.negativeLevyLaplaceFromTripleV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:37:14.266734+00:00
-- url     : https://prove2.me/submissions/20e223c4-48bf-4134-913c-6f910e23f4d0

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_weak_moment_transfer
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_triplet_finite_jump_approximation
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Mathlib.MeasureTheory.Measure.LevyConvergence
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false
private theorem convention (c σ : ℝ) (ν : Measure ℝ) (hneg : ν (Ici 0) = 0)
    (β : ℝ) :
    AvramDividend.Classical.laplaceExponent c σ ν β = tripletLaplace (-c) σ ν β := by
  have hν : ∀ᵐ y ∂ν, y ∈ Iio (0 : ℝ) := by
    have hComplement : {y : ℝ | ¬y ∈ Iio (0 : ℝ)} = Ici 0 := by
      ext y
      simp only [mem_setOf_eq, mem_Iio, mem_Ici, not_lt]
    rw [ae_iff, hComplement]
    exact hneg
  rw [AvramDividend.Classical.laplaceExponent, tripletLaplace, neg_neg,
    Measure.restrict_eq_self_of_ae_mem hν]
  congr 1
  apply integral_congr_ae
  filter_upwards [hν] with y hny
  by_cases hy : -1 < y
  · have hyIoo : y ∈ Ioo (-1 : ℝ) 1 :=
      ⟨hy, (show y < 0 from hny).trans zero_lt_one⟩
    simp [hy, indicator_of_mem hyIoo]
  · rw [if_neg hy, indicator_of_notMem (fun h : y ∈ Ioo (-1 : ℝ) 1 => hy h.1)]
    simp

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (hNegative : T.levyMeasure (Set.Ici (0 : ℝ)) = 0)
    (Y : NNReal → Omega → ℝ)
    (hY : ∀ᵐ omega ∂P, ∀ t : NNReal, Y t omega = X t omega)
    (hMeas : ∀ t, Measurable (Y t)) :
    ∀ (t : NNReal) (theta : ℝ), 0 ≤ theta →
      Integrable (fun omega => Real.exp (theta * Y t omega)) P ∧
        ∫ omega, Real.exp (theta * Y t omega) ∂P =
          Real.exp ((t : ℝ) * AvramDividend.Classical.laplaceExponent
            T.drift (Real.sqrt (T.gaussianVariance : ℝ)) T.levyMeasure theta) := by
  intro t β hβ
  have hm := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX t
  let μ : ProbabilityMeasure ℝ := ⟨P.map (X t), Measure.isProbabilityMeasure_map hm⟩
  let σ := Real.sqrt (T.gaussianVariance : ℝ)
  have hσ : σ ^ 2 = (T.gaussianVariance : ℝ) := Real.sq_sqrt (by positivity)
  obtain ⟨μs, hchar, hmoment⟩ := source_result81_triplet_finite_jump_approximation
    T hNegative σ hσ t
  have hweak : Tendsto μs atTop (nhds μ) := by
    apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro ξ
    change Tendsto (fun n => charFun (μs n : Measure ℝ) ξ) atTop
      (nhds (charFun (P.map (X t)) ξ))
    rw [hLK]
    exact hchar ξ
  let f : ℝ → ℝ := fun x => Real.exp (β * x)
  let L (b : ℝ) := Real.exp ((t : ℝ) * tripletLaplace (-T.drift) σ T.levyMeasure b)
  have hf : Continuous f := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  obtain ⟨hint, hlim⟩ := hmoment β hβ
  obtain ⟨hint₂, hlim₂⟩ := hmoment (2 * β) (by positivity)
  have hsq : ∀ᶠ n in atTop, Integrable (fun x => f x ^ 2) (μs n : Measure ℝ) ∧
      (∫ x, f x ^ 2 ∂(μs n : Measure ℝ)) ≤ L (2 * β) + 1 := by
    have heq : (fun x => f x ^ 2) = (fun x => Real.exp ((2 * β) * x)) := by
      funext x
      dsimp [f]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact (hlim₂.eventually_le_const (lt_add_of_pos_right (L (2 * β)) zero_lt_one)).mono
      (fun n hn => ⟨hint₂ n, hn⟩)
  obtain ⟨hi, he⟩ := source_result81_weak_moment_transfer μs μ hweak f hf
    (fun x => (Real.exp_pos (β * x)).le) hint (L (2 * β) + 1) (L β) hsq hlim
  change Integrable f (P.map (X t)) at hi
  change (∫ x, f x ∂P.map (X t)) = L β at he
  have hEq : (fun w => Real.exp (β * Y t w)) =ᵐ[P]
      (fun w => Real.exp (β * X t w)) := hY.mono (fun w hw => by simpa only [hw t])
  refine ⟨(hi.comp_aemeasurable hm).congr hEq.symm, ?_⟩
  rw [integral_congr_ae hEq, convention T.drift σ T.levyMeasure hNegative β]
  exact (integral_map hm hi.aestronglyMeasurable).symm.trans he
