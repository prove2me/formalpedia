-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Slice.exists_compact_fib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:45.064859+00:00
-- url     : https://prove2.me/submissions/30ef4a14-df9a-4148-ae4b-9f027ed5a7d5

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Slice
variable {V X Q : Type} [TopologicalSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
  [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
  [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X]
namespace GlobalTheory.CompanionTheory.SW.Slice
theorem _root_.solution [T2Space V] {g : V → X} (hg : Continuous g) (b₀ : X) {K : Set Q}
    (hK : IsCompact K) {S : Set V} (hS : IsCompact S) :
    ∃ k : Set (g ⁻¹' {b₀}), IsCompact k ∧ ∀ q ∈ K, ∀ z : (g ⁻¹' {b₀}), q • (z : V) ∈ S → z ∈ k := by
  have hcl : IsClosed (g ⁻¹' {b₀}) := isClosed_singleton.preimage hg
  have hc : IsCompact ((fun p : Q × V => p.1⁻¹ • p.2) '' (K ×ˢ S)) :=
    (hK.prod hS).image (continuous_fst.inv.smul continuous_snd)
  refine ⟨Subtype.val ⁻¹' ((fun p : Q × V => p.1⁻¹ • p.2) '' (K ×ˢ S)),
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hc, fun q hq z hz => ?_⟩
  exact ⟨(q, q • (z : V)), ⟨hq, hz⟩, by simp⟩
end GlobalTheory.CompanionTheory.SW.Slice
