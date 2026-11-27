-- Prove2me | solution 1 for Kyprianou.Ch04.normalisedGridPredictableCoefficientsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:52:33.295018+00:00
-- url     : https://prove2.me/submissions/21ff7edd-c922-4a5c-a9a8-a65ecd2e7f54

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_adaptedAELeftPredictableVersionV1
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Past-measurable bounded grid coefficients agree with the physical normalised left weights almost surely. -/
theorem solution  {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : NNReal → Ω → ℝ) (F : Filtration NNReal inferInstance)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (Y L : NNReal → Ω → ℝ) (hY : Adapted F Y)
    (hl : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => Y s w) (𝓝[<] t) (𝓝 (L t w)))
    (f : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hBound : ∀ s x : ℝ, 0 ≤ s → |f s x| ≤ K)
    (u : ℕ → NNReal) :
    ∃ H : ℕ → Ω → ℝ, (∀ k, Measurable[F (u k)] (H k)) ∧
      (∀ k w, |H k w| ≤ K) ∧ ∀ᵐ w ∂P, ∀ k,
        H k w = if u k = 0 then 0 else f (u k) (L (u k) w) := by
  obtain ⟨V,hV,hEq⟩ := Kyprianou.Ch04.adaptedAELeftPredictableVersionV1 P X F hF Y L hY hl
  let H (k : ℕ) (w : Ω) := if u k = 0 then 0 else f (u k) (V (u k) w)
  refine ⟨H,?_,?_,?_⟩
  · intro k
    by_cases hk : u k = 0
    · simp [H,hk,measurable_const]
    · have hc : Continuous (fun x : ℝ => f (u k : ℝ) x) :=
        hf.comp_continuous (continuous_const.prodMk continuous_id)
          (fun x => ⟨(u k).coe_nonneg,mem_univ x⟩)
      simpa [H,hk,Function.comp_def] using hc.measurable.comp
        (hV.stronglyAdapted (u k)).measurable
  · intro k w
    by_cases hk : u k = 0 <;> simp [H,hk,hK,hBound _ _ (u k).coe_nonneg]
  · filter_upwards [hEq] with w hw
    intro k
    by_cases hk : u k = 0
    · simp [H,hk]
    · simp [H,hk,hw _ (pos_iff_ne_zero.mpr hk)]
