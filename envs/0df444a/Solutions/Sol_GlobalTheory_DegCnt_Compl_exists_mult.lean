-- Prove2me | solution 1 for GlobalTheory.DegCnt.Compl.exists_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:08:39.677188+00:00
-- url     : https://prove2.me/submissions/c9e4b65e-b9fe-46d8-909f-5d5c868ef8d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IdxSupRight

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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Compl
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [FiniteDimensional K V]
namespace GlobalTheory.DegCnt.Compl
theorem _root_.solution {M : Submodule (𝓞 K) V} {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ c : K, c ≠ 0 ∧ c • v ∈ M := by
  obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (M : Set V) v hv
  rw [Submodule.span_eq] at hs
  refine ⟨algebraMap (𝓞 K) K s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, ?_⟩
  rw [algebraMap_smul]
  exact hs
end GlobalTheory.DegCnt.Compl
