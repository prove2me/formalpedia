-- Prove2me | solution 1 for Kyprianou.Ch04.adaptedAELeftPredictableVersionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:25:55.58191+00:00
-- url     : https://prove2.me/submissions/f561b431-58fe-43a3-83b8-34ab4f51390f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_completedMeasAECongrV1
import Theorems.Thm_Kyprianou_Ch04_predictableLeftVersionV1
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- An adapted process with almost-sure strict left limits has a predictable version
of the given left limits at every strictly positive time on one full-measure event. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : NNReal → Ω → ℝ) (F : Filtration NNReal inferInstance)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (Y L : NNReal → Ω → ℝ) (hY : Adapted F Y)
    (hl : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 (L t ω))) :
    ∃ V : NNReal → Ω → ℝ, IsStronglyPredictable F V ∧
      ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → V t ω = L t ω := by
  classical
  let A := {ω | ∀ t : NNReal, 0 < t →
    Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 (L t ω))}
  have hA : ∀ᵐ ω ∂P, ω ∈ A := hl
  let Z : NNReal → Ω → ℝ := fun t ω => if ω ∈ A then Y t ω else 0
  have hZ : StronglyAdapted F Z := by
    apply Adapted.stronglyAdapted
    intro t
    apply Kyprianou.Ch04.completedMeasAECongrV1 P X F hF t (Z t) (Y t) (hY t)
    filter_upwards [hA] with ω hω
    simp [Z,hω]
  have hLZ : ∀ ω (t : NNReal), 0 < t →
      ∃ l : ℝ, Tendsto (fun s => Z s ω) (𝓝[<] t) (𝓝 l) := by
    intro ω t ht
    by_cases hω : ω ∈ A
    · exact ⟨L t ω, by simpa [Z,hω] using hω t ht⟩
    · exact ⟨0, by simpa [Z,hω] using
        (tendsto_const_nhds : Tendsto (fun _ : NNReal => (0 : ℝ)) (𝓝[<] t) (𝓝 0))⟩
  refine ⟨fun t ω => Function.leftLim (fun s => Z s ω) t,
    Kyprianou.Ch04.predictableLeftVersionV1 F Z hZ hLZ, ?_⟩
  filter_upwards [hA] with ω hω
  intro t ht
  have : (𝓝[<] t).NeBot := nhdsWithin_Iio_neBot' ⟨0,ht⟩ le_rfl
  apply leftLim_eq_of_tendsto
  simpa [Z,hω] using hω t ht
