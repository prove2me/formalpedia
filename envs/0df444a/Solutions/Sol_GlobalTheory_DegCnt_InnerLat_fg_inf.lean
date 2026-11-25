-- Prove2me | solution 1 for GlobalTheory.DegCnt.InnerLat.fg_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:41:02.995805+00:00
-- url     : https://prove2.me/submissions/9e3921fb-af79-49df-9283-f4c604974d75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairInnerLatticesUnimodularPrimitive

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
variable {H : HermSpace K V} {r : ℕ}
omit [StarRing K]
namespace GlobalTheory.DegCnt.InnerLat
theorem _root_.solution {L : Submodule (𝓞 K) V} {S I T : Submodule K V} (hL : IsLatMod L S I) (hT : ∀ x ∈ T, x ∈ I → x = 0) :
    (L ⊓ rs (𝓞 K) T).FG := by
  obtain ⟨⟨N, hN, rfl⟩, -⟩ := hL
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (rs (𝓞 K) I).mkQ ?_ ?_
  · refine (hN.map (rs (𝓞 K) I).mkQ).of_le ((Submodule.map_mono inf_le_left).trans ?_)
    rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  · have : (N ⊔ rs (𝓞 K) I) ⊓ rs (𝓞 K) T ⊓ LinearMap.ker (rs (𝓞 K) I).mkQ = ⊥ := by
      rw [eq_bot_iff, Submodule.ker_mkQ]
      intro x hx
      exact hT x hx.1.2 hx.2
    rw [this]
    exact Submodule.fg_bot
end GlobalTheory.DegCnt.InnerLat
