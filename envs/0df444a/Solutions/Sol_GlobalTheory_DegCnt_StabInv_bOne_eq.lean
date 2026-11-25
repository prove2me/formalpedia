-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.bOne_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:03:18.024205+00:00
-- url     : https://prove2.me/submissions/f406bd9a-3c1c-43b1-8648-aaf151aefdc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_Keeps_flagX
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_apply_mem_II
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_smul_inf_rs
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_idx_smul

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
namespace GlobalTheory.DegCnt.StabInv
theorem _root_.solution {F F' : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (h' : Keeps F' s)
    (Λ : Submodule (𝓞 K) V) (j : ℕ) : bOne F F' (s • Λ) j = bOne F F' Λ j := by
  unfold bOne latF
  rw [smul_inf_rs s Λ h.flagX, smul_inf_rs s Λ (h.flag j), smul_inf_rs s Λ (apply_mem_II h h'),
    ← Submodule.smul_sup', idx_smul]
end GlobalTheory.DegCnt.StabInv
