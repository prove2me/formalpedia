-- Prove2me | solution 1 for GlobalTheory.ModIdent.mem_smulLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:41:18.280712+00:00
-- url     : https://prove2.me/submissions/b8e14f92-eaea-41ee-bb82-7d5de0601318

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsHermIsometryGraphModScalarFlagPairIota
import Theorems.Thm_GlobalTheory_ModIdent_nsmul_eq

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
omit [NumberField K] [StarRing K]
namespace GlobalTheory.ModIdent
theorem _root_.solution (g : ℕ) (M : Submodule (𝓞 K) V) (y : V) :
    y ∈ smulLat (g : 𝓞 K) M ↔ ∃ m ∈ M, y = (g : K) • m := by
  unfold smulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, nsmul_eq g m⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, nsmul_eq g m⟩
end GlobalTheory.ModIdent
