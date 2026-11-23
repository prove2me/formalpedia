-- Prove2me | solution 1 for Kyprianou.Ch02.levyActualLargeJumpAbsoluteSummabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:18:28.445562+00:00
-- url     : https://prove2.me/submissions/9b074ca8-6e35-467c-bc68-9103d8b85ca3

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
open MeasureTheory ProbabilityTheory Complex Function Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Any cadlag path has finite support for jumps exceeding a fixed
threshold on a compact interval. Reuse the Proved generic Avram theorem. -/
theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
        if (1 : ℝ) < |X (s : ℝ≥0) ω - Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| then |X (s : ℝ≥0) ω - Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| else 0) := by
  filter_upwards [hX.cadlag_ae] with ω hc
  intro T
  let Y : ℝ≥0 → ℝ := fun t => X t ω
  have hR : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u := by
    intro u
    exact (hc u).1
  have hL : ∀ u : ℝ≥0, 0 < u →
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)) := by
    intro u _
    exact tendsto_leftLim_of_tendsto (hc u).2
  have hfinite :
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        (1 : ℝ) ≤ dist (Y u - Function.leftLim Y u) 0}.Finite :=
    AvramDividend.Classical.avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
      Y hR hL T 1 (by norm_num)
  let f : Set.Ioc (0 : ℝ≥0) T → ℝ :=
    fun s => if (1 : ℝ) < |Y s - Function.leftLim Y s| then
      |Y s - Function.leftLim Y s| else 0
  have hfinite_support : (Function.support f).Finite := by
    have hpre : ((fun s : Set.Ioc (0 : ℝ≥0) T => (s : ℝ≥0)) ⁻¹'
        {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
          (1 : ℝ) ≤ dist (Y u - Function.leftLim Y u) 0}).Finite := by
      apply hfinite.preimage
      intro s t _ _ hst
      exact Subtype.coe_injective hst
    apply hpre.subset
    intro s hs
    have hs' : f s ≠ 0 := hs
    have hgt : (1 : ℝ) < |Y s - Function.leftLim Y s| := by
      by_contra hn
      have hle : |Y s - Function.leftLim Y s| ≤ (1 : ℝ) :=
        le_of_not_gt hn
      have hzero : f s = 0 := by
        simp [f, not_lt.mpr hle]
      exact hs' hzero
    exact ⟨s.property.1, s.property.2, by
      simpa only [Real.dist_eq, sub_zero] using (le_of_lt hgt)⟩
  change Summable f
  exact summable_of_finite_support hfinite_support
