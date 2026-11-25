-- Prove2me | solution 1 for GlobalTheory.DegCnt.Glue.proj_mem_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:43:48.292565+00:00
-- url     : https://prove2.me/submissions/c5568f00-d69a-4dfd-97ba-946593184fe1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUnimodularHermGluingsLe
import Theorems.Thm_GlobalTheory_DegCnt_Glue_span_inf
import Theorems.Thm_GlobalTheory_DegCnt_Glue_integral
import Theorems.Thm_GlobalTheory_HermLat_isLatMod_top_bot_iff
import Theorems.Thm_GlobalTheory_HermLat_mem_dual_iff
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff


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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Glue
open TensorProduct
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (H : HermSpace K V) {U : Submodule K V} (hc : IsCompl U (perp H U)) {L : Submodule (𝓞 K) V}
  (hU : IsUnimod H L) {p : V →ₗ[K] V} (hp : ∀ v, p v ∈ U) (hq : ∀ v, v - p v ∈ perp H U)
omit [FiniteDimensional K V]
include hU hp hq
namespace GlobalTheory.DegCnt.Glue
theorem _root_.solution {v : V} (hv : v ∈ L) : p v ∈ dual H (L ⊓ rs (𝓞 K) U) := by
  rw [mem_dual_iff, span_inf ((isLatMod_top_bot_iff L).1 hU.1)]
  refine ⟨hp v, fun a ha => ?_⟩
  have h0 := (mem_perp_iff H U _).1 (hq v) a ha.2
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h0
  rw [← h0]
  exact integral H hU hv ha.1
end GlobalTheory.DegCnt.Glue
