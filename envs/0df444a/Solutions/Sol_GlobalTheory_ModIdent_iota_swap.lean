-- Prove2me | solution 1 for GlobalTheory.ModIdent.iota_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:26:29.576691+00:00
-- url     : https://prove2.me/submissions/e7a21617-cd10-4654-9c46-592a7b50a221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsHermIsometryGraphModScalarFlagPairIota
import Theorems.Thm_GlobalTheory_ModIdent_gsmul_mem
import Theorems.Thm_GlobalTheory_ModIdent_mem_iota
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.ModIdent
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
omit [NumberField K]
namespace GlobalTheory.ModIdent
theorem _root_.solution {F F' : FlagD H r} {Λ : Submodule (𝓞 K) V} {g : ℕ} {y' y : V}
    (h : (y', y) ∈ iotaGraph F F' Λ (g : 𝓞 K)) : (y, y') ∈ iotaGraph F' F Λ (g : 𝓞 K) := by
  rw [mem_iota] at h ⊢
  obtain ⟨h1, h2, l', hl', m, hm, h3, h4⟩ := h
  refine ⟨h2, h1, _, Λ.add_mem hl' (gsmul_mem g hm), -m, Λ.neg_mem hm, h4, by simpa using h3⟩
end GlobalTheory.ModIdent
