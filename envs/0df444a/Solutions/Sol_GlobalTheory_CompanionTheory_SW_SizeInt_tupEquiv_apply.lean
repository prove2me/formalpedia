-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SizeInt.tupEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:32:19.376328+00:00
-- url     : https://prove2.me/submissions/30e6bade-6b19-406d-b2cf-bd58066d8485

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SizeFunctionRapidDecayIntegrable

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SizeInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable {d : ℕ} (hF : IsTotallyReal F) (b : Module.Basis (Fin d) F E)
namespace GlobalTheory.CompanionTheory.SW.SizeInt
theorem _root_.solution (n M : ℕ) (X : Fin n → Fin M → Ainf F ⊗[F] E) (a : Fin n) (i : Fin M) :
    tupEquiv hF b n M X a i = coordEquiv hF b (X a i) := rfl
end GlobalTheory.CompanionTheory.SW.SizeInt
