-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.MeasProj.isCompact_latV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:28:06.053607+00:00
-- url     : https://prove2.me/submissions/8c6510d5-719d-4041-ae29-18d9ab9ba179

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_latV_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.MeasProj
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.MeasProj
theorem _root_.solution {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  have hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F)))
  rw [latV_eq, (tupHomeo b n M).isCompact_preimage]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc
end GlobalTheory.CompanionTheory.SW.MeasProj
