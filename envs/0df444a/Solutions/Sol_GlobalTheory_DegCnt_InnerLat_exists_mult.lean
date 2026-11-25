-- Prove2me | solution 1 for GlobalTheory.DegCnt.InnerLat.exists_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:58:06.750908+00:00
-- url     : https://prove2.me/submissions/d459dff9-45d6-4097-b242-2a0b2aac5c82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairInnerLatticesUnimodularPrimitive
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.InnerLat
open GlobalTheory.UnimodQuot
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K]
namespace GlobalTheory.DegCnt.InnerLat
theorem _root_.solution {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (v : V) :
    ∃ c : K, c ≠ 0 ∧ c • v ∈ Λ := by
  obtain ⟨s, hs⟩ := exists_smul_mem hΛ v
  refine ⟨algebraMap (𝓞 K) K s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, ?_⟩
  rw [algebraMap_smul]
  exact hs
end GlobalTheory.DegCnt.InnerLat
