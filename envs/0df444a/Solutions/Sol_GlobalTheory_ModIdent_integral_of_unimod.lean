-- Prove2me | solution 1 for GlobalTheory.ModIdent.integral_of_unimod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:00:18.059466+00:00
-- url     : https://prove2.me/submissions/1021253c-5f78-4c24-927e-ebc298da42ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsHermIsometryGraphModScalarFlagPairIota
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
open GlobalTheory GlobalTheory.ModIdent
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
omit [NumberField K]
namespace GlobalTheory.ModIdent
theorem _root_.solution {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ∃ t : 𝓞 K, (t : K) = H.B x y := by
  rw [← hU.2, mem_dual_iff] at hx
  exact Submodule.mem_one.1 (hx.2 y hy)
end GlobalTheory.ModIdent
