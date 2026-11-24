-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatRat.one_mem_latR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:30:48.768231+00:00
-- url     : https://prove2.me/submissions/2809dc0c-e122-45f2-8213-1b6bfe6b47d3

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatRat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.LatRat
theorem _root_.solution {d : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F) :
    (1 : Fv F v ⊗[F] E) ∈ latR b v := by
  intro k
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.basis_repr_tmul]
  simpa using h k
end GlobalTheory.CompanionTheory.SW.LatRat
