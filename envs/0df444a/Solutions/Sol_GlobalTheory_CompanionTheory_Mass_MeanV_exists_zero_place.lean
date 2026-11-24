-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.exists_zero_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:54:53.379552+00:00
-- url     : https://prove2.me/submissions/d7aa33bd-b710-4e78-9554-33908211dfad

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
theorem _root_.solution {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ)
    (hz : ∀ v, v ∉ S → ∀ s, s ∉ v.adicCompletionIntegers F → g v s = 0) {x : F}
    (h : ¬ (x ∈ IntOut S ∧ ∀ v ∈ S, algebraMap F (Fv F v) x ∈ tsupport (g v))) :
    ∃ v, g v (algebraMap F (Fv F v) x) = 0 ∧ ∀ T, S ⊆ T → x ∈ IntOut T → v ∈ T := by
  by_cases h1 : x ∈ IntOut S
  · have h2 : ∃ v ∈ S, algebraMap F (Fv F v) x ∉ tsupport (g v) := by
      by_contra hcon
      exact h ⟨h1, fun v hv => by_contra fun hn => hcon ⟨v, hv, hn⟩⟩
    obtain ⟨v, hv, hvx⟩ := h2
    exact ⟨v, image_eq_zero_of_notMem_tsupport hvx, fun T hT _ => hT hv⟩
  · have h2 : ∃ v, v ∉ S ∧ algebraMap F (Fv F v) x ∉ v.adicCompletionIntegers F := by
      by_contra hcon
      exact h1 fun v hv => by_contra fun hn => hcon ⟨v, hv, hn⟩
    obtain ⟨v, hv, hvx⟩ := h2
    refine ⟨v, hz v hv _ hvx, fun T _ hxT => ?_⟩
    by_contra hvT
    exact hvx (hxT v hvT)
end GlobalTheory.CompanionTheory.Mass.MeanV
