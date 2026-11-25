-- Prove2me | solution 1 for GlobalTheory.DegCnt.Glue.integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:13:22.118306+00:00
-- url     : https://prove2.me/submissions/fc5a32f9-9100-42b4-b601-f2f58915b564

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUnimodularHermGluingsLe
import Theorems.Thm_GlobalTheory_HermLat_mem_dual_iff


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
omit [NumberField K] [FiniteDimensional K V]
include hU
namespace GlobalTheory.DegCnt.Glue
theorem _root_.solution {y x : V} (hy : y ∈ L) (hx : x ∈ L) : H.B y x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [← hU.2, mem_dual_iff] at hy
  exact hy.2 x hx
end GlobalTheory.DegCnt.Glue
