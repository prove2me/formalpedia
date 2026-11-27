-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45ActualSmallBandUniformCauchyV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:38:40.78061+00:00
-- url     : https://prove2.me/submissions/ad287b82-5aa5-46a0-98a9-b80e612bb0c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch04_exercise45UniformCauchyTailProbabilityV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hZero : ∀ᵐ w ∂P, N.N w ({0} ×ˢ (univ : Set ℝ)) = 0) :
    let A : ℝ → NNReal → Ω → ℝ := fun e t w =>
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
        z.2 ∂(N.N w)) - (t:ℝ)*∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν
    ∀ᵐ w ∂P, ∀ T : NNReal, ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧
      ∀ r q : ℝ, 0 < r → r < a → 0 < q → q < a →
        ∀ t ≤ T, |A r t w - A q t w| < δ := by
  intro A
  have H := Kyprianou.Ch04.exercise45UniformCauchyTailProbabilityV1 P ν hν N hZero
  let E (k m n : ℕ) : Set Ω := {w | ∃ r q : ℝ,
    0 < r ∧ r < 1/((n:ℝ)+1) ∧ 0 < q ∧ q < 1/((n:ℝ)+1) ∧
    ∃ t ≤ (k:NNReal), (1/((m:ℝ)+1)) ≤ |A r t w-A q t w|}
  have hgood (k m : ℕ) : ∀ᵐ w ∂P, ∃ n : ℕ, w ∉ E k m n := by
    rw [ae_iff]
    let B : Set Ω := {w | ¬ ∃ n : ℕ, w ∉ E k m n}
    have hle (n : ℕ) : (P B).toReal ≤ (P (E k m n)).toReal :=
      ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (by
        intro w hw
        by_contra h
        exact hw ⟨n,h⟩))
    have hlim : Tendsto (fun n => (P (E k m n)).toReal) atTop (nhds 0) :=
      H (k:NNReal) (1/((m:ℝ)+1)) (by positivity)
    have hz : (P B).toReal = 0 := le_antisymm
      (ge_of_tendsto hlim (Eventually.of_forall hle)) ENNReal.toReal_nonneg
    change P B = 0
    rw [← ENNReal.ofReal_toReal (measure_ne_top P B),hz,ENNReal.ofReal_zero]
  have hall : ∀ᵐ w ∂P, ∀ k m : ℕ, ∃ n : ℕ, w ∉ E k m n :=
    ae_all_iff.2 (fun k => ae_all_iff.2 (fun m => hgood k m))
  filter_upwards [hall] with w hw
  intro T δ hδ
  obtain ⟨k,hk⟩ := exists_nat_gt T
  have hlim : Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨m,hm⟩ := eventually_atTop.1 (hlim (Iio_mem_nhds hδ))
  obtain ⟨n,hn⟩ := hw k m
  refine ⟨1/((n:ℝ)+1),by positivity,?_⟩
  intro r q hr hra hq hqa t ht
  have hlt : |A r t w-A q t w| < 1/((m:ℝ)+1) := by
    by_contra h
    exact hn ⟨r,q,hr,hra,hq,hqa,t,ht.trans hk.le,le_of_not_gt h⟩
  exact hlt.trans (hm m le_rfl)
