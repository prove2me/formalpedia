-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodTrans.mem_latV_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:23:45.613383+00:00
-- url     : https://prove2.me/submissions/5287badd-b2c5-484e-87f8-619d5f714c60

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlaces
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermConstantsEqAlongAffineSpaceSquare
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeGramScalarAlmostAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodTrans
namespace GlobalTheory.CompanionTheory.SW.GoodTrans
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d n M : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) (X : Fin n → Fin M → Fv F v ⊗[F] E) :
    X ∈ latV b v ↔ ∀ a i, X a i ∈ O :=
  ⟨fun h a i => (hO _).2 (h a i), fun h a i => (hO _).1 (h a i)⟩
end GlobalTheory.CompanionTheory.SW.GoodTrans
