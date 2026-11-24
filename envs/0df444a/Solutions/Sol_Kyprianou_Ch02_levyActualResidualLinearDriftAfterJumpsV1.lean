-- Prove2me | solution 1 for Kyprianou.Ch02.levyActualResidualLinearDriftAfterJumpsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:30:51.494432+00:00
-- url     : https://prove2.me/submissions/1167acbf-b69d-4ff1-815d-0c36601e72e8

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyCanonicalFiniteVariationResidualModelV1
import Theorems.Thm_Kyprianou_Ch02_levySignedResidualAtTimeTransferV1
import Theorems.Thm_Kyprianou_Ch02_levyWholePathLawEqOfCharFunV1
import Theorems.Thm_Kyprianou_Ch02_cadlagLinearResidualFromDenseGridV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Transfer the canonical finite-first-moment residual to the original process. -/
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
    (σ = 0 ∧ Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure) →
    (∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
        |X (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|)) →
    ∃ (drift : ℝ), ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      X T ω = drift * (T : ℝ) +
        ∑' s : Set.Ioc (0 : ℝ≥0) T,
          (X (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)) := by
  rintro ⟨rfl, hfin⟩ hsum
  obtain ⟨Λ, mΛ, Q, Y, d, hQ, hY, hcharY, hresY⟩ :=
    Kyprianou.Ch02.levyCanonicalFiniteVariationResidualModelV1 a levyMeasure
      hlevyMeasure hfin
  letI : MeasurableSpace Λ := mΛ
  letI : IsProbabilityMeasure Q := hQ
  have hpath := Kyprianou.Ch02.levyWholePathLawEqOfCharFunV1 P Q X Y hX hY
    (fun t ξ => by simpa using (hchar t ξ).trans (by simpa using (hcharY t ξ).symm))
  obtain ⟨grid, hdense⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  have hgrid (k : ℕ) := Kyprianou.Ch02.levySignedResidualAtTimeTransferV1
    P Q X Y hX hY hpath (grid k) d (hsum.mono fun ω h => h (grid k))
    (hresY.mono fun ω h => (h (grid k)).1)
    (hresY.mono fun ω h => (h (grid k)).2)
  refine ⟨d, ?_⟩
  filter_upwards [hX.cadlag_ae, hsum, ae_all_iff.mpr hgrid] with ω hc hs he
  exact Kyprianou.Ch02.cadlagLinearResidualFromDenseGridV1
    (fun t => X t ω) d grid hdense (fun t => (hc t).1) hs he
