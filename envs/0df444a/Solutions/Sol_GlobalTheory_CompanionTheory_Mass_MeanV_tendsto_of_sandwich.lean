-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.tendsto_of_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:54:57.05406+00:00
-- url     : https://prove2.me/submissions/dda7d1dd-9273-4b03-9d3b-cc1be5ea8819

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIntegralMultipleBoundedPlacesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProductDifferenceBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TailSumOverPlacesSmallStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultipliableLocalFactorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFactorSandwichApproxStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EulerProductConvergenceBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimitStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalHaarMeasureSingletonStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeanValueFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV
namespace GlobalTheory.CompanionTheory.Mass.MeanV
theorem _root_.solution {α : Type*} {l : Filter α} {f : α → ℝ} {L : ℝ}
    (h : ∀ η : ℝ, 0 < η → ∃ (a b : α → ℝ) (A B : ℝ), Tendsto a l (𝓝 A) ∧ Tendsto b l (𝓝 B) ∧
      (∀ᶠ x in l, a x ≤ f x ∧ f x ≤ b x) ∧ L - η ≤ A ∧ B ≤ L + η) : Tendsto f l (𝓝 L) := by
  rw [tendsto_order]
  constructor
  · intro c hc
    obtain ⟨a, b, A, B, ha, -, hab, hA, -⟩ := h ((L - c) / 2) (by linarith)
    have hcA : c < A := by linarith
    filter_upwards [(tendsto_order.1 ha).1 c hcA, hab] with x h1 h2
    exact lt_of_lt_of_le h1 h2.1
  · intro c hc
    obtain ⟨a, b, A, B, -, hb, hab, -, hB⟩ := h ((c - L) / 2) (by linarith)
    have hcB : B < c := by linarith
    filter_upwards [(tendsto_order.1 hb).2 c hcB, hab] with x h1 h2
    exact lt_of_le_of_lt h2.2 h1
end GlobalTheory.CompanionTheory.Mass.MeanV
