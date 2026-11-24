-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatFix.eventually_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:30:44.711467+00:00
-- url     : https://prove2.me/submissions/c9deffb4-84cc-4fa3-aee0-c079d14e7232

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EventuallyActMemLatVIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatFix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.LatFix
theorem _root_.solution (c : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      algebraMap F (Fv F v) c ∈ v.adicCompletionIntegers F := by
  exact (algebraMap F (FiniteAdeleRing (𝓞 F) F) c).2
end GlobalTheory.CompanionTheory.SW.LatFix
