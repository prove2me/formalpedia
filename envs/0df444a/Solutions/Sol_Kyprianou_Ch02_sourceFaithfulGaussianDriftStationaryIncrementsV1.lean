-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulGaussianDriftStationaryIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:11:54.110891+00:00
-- url     : https://prove2.me/submissions/d7a8b4bb-198a-4486-8189-0b9318ed2797

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stationaryIncrementsOfPositivePairsV1
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch02

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ) (σ : ℝ≥0)
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hB0 : ∀ ω : Ω, B.W 0 ω = 0) :
    ProbabilityTheory.HasStationaryIncrements (fun (t : ℝ≥0) (ω : Ω) => (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) P := by
  let X : ℝ≥0 → Ω → ℝ := fun t ω => (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)
  have hX (t : ℝ≥0) : Measurable (X t) :=
    (measurable_const.mul (B.measurable_eval (t : ℝ))).sub measurable_const
  apply Kyprianou.Ch01.stationaryIncrementsOfPositivePairsV1 P X
    (fun t => (hX t).aemeasurable)
  intro s h hs hh
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hst : (s : ℝ) < (s : ℝ) + (h : ℝ) := by linarith
  let F : Ω → ℝ := fun ω => B.W ((s : ℝ) + (h : ℝ)) ω - B.W (s : ℝ) ω
  let G : Ω → ℝ := fun ω => B.W (h : ℝ) ω - B.W 0 ω
  let f : ℝ → ℝ := fun z => (σ : ℝ) * z - a * (h : ℝ)
  have hF : Measurable F := (B.measurable_eval _).sub (B.measurable_eval _)
  have hG : Measurable G := (B.measurable_eval _).sub (B.measurable_eval _)
  have hf : Measurable f := (measurable_const.mul measurable_id).sub measurable_const
  have hvF : (⟨(s : ℝ) + (h : ℝ) - (s : ℝ), by linarith⟩ : ℝ≥0) = h := by
    apply Subtype.ext
    change (s : ℝ) + (h : ℝ) - (s : ℝ) = (h : ℝ)
    ring
  have hvG : (⟨(h : ℝ) - 0, by linarith⟩ : ℝ≥0) = h := by
    apply Subtype.ext
    simp
  have hmapF := B.increment_gaussian (NNReal.coe_nonneg s) hst
  have hmapG := B.increment_gaussian (s := 0) (t := (h : ℝ)) le_rfl hhR
  change P.map F = _ at hmapF
  change P.map G = _ at hmapG
  rw [hvF] at hmapF
  rw [hvG] at hmapG
  have hEq : P.map F = P.map G := hmapF.trans hmapG.symm
  have hleft : increment X s (s + h) = f ∘ F := by
    funext ω
    simp only [increment, X, f, F, Function.comp_apply, NNReal.coe_add]
    ring
  have hright : increment X 0 h = f ∘ G := by
    funext ω
    simp only [increment, X, f, G, Function.comp_apply, NNReal.coe_zero]
    ring
  rw [hleft, hright]
  refine ⟨(hf.comp hF).aemeasurable, (hf.comp hG).aemeasurable, ?_⟩
  rw [← Measure.map_map hf hF, ← Measure.map_map hf hG, hEq]
