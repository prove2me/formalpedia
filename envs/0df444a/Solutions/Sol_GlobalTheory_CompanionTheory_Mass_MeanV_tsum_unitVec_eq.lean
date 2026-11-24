-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.tsum_unitVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:21:56.635097+00:00
-- url     : https://prove2.me/submissions/d4592880-2c06-4b7d-8398-95c016e78587

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimit

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
theorem _root_.solution {F : Type} [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (h : F → ℝ) :
    ∑' x : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F}, h (x.1 ()) =
      ∑' x : F, (IntOut T).indicator h x := by
  let e : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} ≃ (IntOut T) :=
    (Equiv.funUnique Unit F).subtypeEquiv (fun x => by
      constructor
      · intro hx v hv
        exact hx v hv ()
      · intro hx v hv i
        exact hx v hv)
  rw [← tsum_subtype (IntOut T) h]
  exact e.tsum_eq (fun y : IntOut T => h y.1)
end GlobalTheory.CompanionTheory.Mass.MeanV
