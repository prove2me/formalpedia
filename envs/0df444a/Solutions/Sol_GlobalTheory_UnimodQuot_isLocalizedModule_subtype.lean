-- Prove2me | solution 1 for GlobalTheory.UnimodQuot.isLocalizedModule_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:15:21.295213+00:00
-- url     : https://prove2.me/submissions/d337ba3b-1344-4693-ba44-903f35a52d13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Theorems.Thm_GlobalTheory_UnimodQuot_exists_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnimodQuot
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [FiniteDimensional K V]
namespace GlobalTheory.UnimodQuot
theorem _root_.solution {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) :
    IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype where
  map_units s := by
    have := isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
    exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s
  surj y := by
    obtain ⟨s, hs⟩ := exists_smul_mem hL y
    exact ⟨(⟨_, hs⟩, s), rfl⟩
  exists_of_eq h := ⟨1, by rw [Subtype.ext h]⟩
end GlobalTheory.UnimodQuot
