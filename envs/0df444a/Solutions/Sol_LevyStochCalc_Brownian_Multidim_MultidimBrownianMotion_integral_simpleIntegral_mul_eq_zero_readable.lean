-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_simpleIntegral_mul_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:25:51.038427+00:00
-- url     : https://prove2.me/submissions/0194c7e2-cd2d-44f1-ae0f-ba889110908f

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integrable_and_integral_cross_clamped_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}
section SimpleIntegrands
open LevyStochCalc.Brownian.Ito
variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
/-- **Orthogonality on simple integrands.** Elementary integrals against distinct Brownian
coordinates have zero pairing, at any pair of times. -/
theorem solution (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ) {TH TK : ℝ}
    (H : LevyStochCalc.Brownian.Ito.SimplePredictable Ω TH)
    (K : LevyStochCalc.Brownian.Ito.SimplePredictable Ω TK)
    (hH : ∀ a : Fin H.N, StronglyMeasurable[ℱ (H.partition a.castSucc)] (H.ξ a))
    (hK : ∀ b : Fin K.N, StronglyMeasurable[ℱ (K.partition b.castSucc)] (K.ξ b))
    (t t' : ℝ) :
    ∫ ω, LevyStochCalc.Brownian.Ito.simpleIntegral (W.W i) H t ω * LevyStochCalc.Brownian.Ito.simpleIntegral (W.W j) K t' ω ∂P = 0 := by
  have hHnn : ∀ a : Fin H.N, 0 ≤ H.partition a.castSucc := fun a => by
    have h := H.partition_strictMono.monotone (Fin.zero_le a.castSucc)
    rwa [H.partition_zero] at h
  have hKnn : ∀ b : Fin K.N, 0 ≤ K.partition b.castSucc := fun b => by
    have h := K.partition_strictMono.monotone (Fin.zero_le b.castSucc)
    rwa [K.partition_zero] at h
  have hHlt : ∀ a : Fin H.N, H.partition a.castSucc < H.partition a.succ := fun a =>
    H.partition_strictMono Fin.castSucc_lt_succ
  have hKlt : ∀ b : Fin K.N, K.partition b.castSucc < K.partition b.succ := fun b =>
    K.partition_strictMono Fin.castSucc_lt_succ
  have key : ∀ (a : Fin H.N) (b : Fin K.N),
      Integrable (fun ω => (H.ξ a ω * ((W.W i).W (min (H.partition a.succ) t) ω
          - (W.W i).W (min (H.partition a.castSucc) t) ω))
        * (K.ξ b ω * ((W.W j).W (min (K.partition b.succ) t') ω
          - (W.W j).W (min (K.partition b.castSucc) t') ω))) P
      ∧ ∫ ω, (H.ξ a ω * ((W.W i).W (min (H.partition a.succ) t) ω
          - (W.W i).W (min (H.partition a.castSucc) t) ω))
        * (K.ξ b ω * ((W.W j).W (min (K.partition b.succ) t') ω
          - (W.W j).W (min (K.partition b.castSucc) t') ω)) ∂P = 0 := by
    intro a b
    obtain ⟨Mξ, hMξ⟩ := H.ξ_bounded a
    obtain ⟨Mη, hMη⟩ := K.ξ_bounded b
    exact LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_and_integral_cross_clamped_readable W hij hcoord (hHnn a) (hHlt a) (hKnn b) (hKlt b)
      (hH a) (H.ξ_measurable a) hMξ (hK b) (K.ξ_measurable b) hMη t t'
  have hexp : (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral (W.W i) H t ω * LevyStochCalc.Brownian.Ito.simpleIntegral (W.W j) K t' ω)
      = fun ω => ∑ a : Fin H.N, ∑ b : Fin K.N,
        (H.ξ a ω * ((W.W i).W (min (H.partition a.succ) t) ω
          - (W.W i).W (min (H.partition a.castSucc) t) ω))
        * (K.ξ b ω * ((W.W j).W (min (K.partition b.succ) t') ω
          - (W.W j).W (min (K.partition b.castSucc) t') ω)) := by
    funext ω
    rw [LevyStochCalc.Brownian.Ito.simpleIntegral, LevyStochCalc.Brownian.Ito.simpleIntegral]
    exact Finset.sum_mul_sum _ _ _ _
  rw [hexp, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (key a b).1]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (key a b).1]
  exact Finset.sum_eq_zero fun b _ => (key a b).2
