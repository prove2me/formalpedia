-- Prove2me | solution 1 for GlobalTheory.MaxLatStruct.star_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:31:26.841165+00:00
-- url     : https://prove2.me/submissions/8003e4ea-2849-429c-9dc5-8c3b5cc80b58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.MaxLatStruct
namespace GlobalTheory.MaxLatStruct
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] :
    ∃ σ : 𝓞 K →+* 𝓞 K, ∀ r, algebraMap (𝓞 K) K (σ r) = star (algebraMap (𝓞 K) K r) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd K), fun _ => rfl⟩
end GlobalTheory.MaxLatStruct
