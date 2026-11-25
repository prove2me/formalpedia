-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.apply_mem_smul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:58.740899+00:00
-- url     : https://prove2.me/submissions/54418d21-3693-4fd6-95f1-84dde5194734

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_apply_mem_smul
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_exists_of_mem_smul

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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.StabInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
omit [StarRing K]
namespace GlobalTheory.DegCnt.StabInv
theorem _root_.solution (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (x : V) :
    s x ∈ s • Λ ↔ x ∈ Λ := by
  refine ⟨fun h => ?_, apply_mem_smul s⟩
  obtain ⟨y, hy, hxy⟩ := exists_of_mem_smul h
  rwa [← s.injective hxy]
end GlobalTheory.DegCnt.StabInv
