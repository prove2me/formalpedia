-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.latL_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:49.315949+00:00
-- url     : https://prove2.me/submissions/eafbb629-c7dc-413f-b989-bd7bc4d2ef03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_Keeps_flagX
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_apply_mem_smul
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_sub_mem_left
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_shift

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
theorem _root_.solution {F : FlagD H r} (F' : FlagD H r) {s : V ≃ₗ[K] V} (h : Keeps F s)
    (Λ : Submodule (𝓞 K) V) : latL F F' Λ ≤ latL F F' (s • Λ) := by
  rintro y ⟨hy, hy'⟩
  obtain ⟨l, hl, x, hx, he⟩ := Submodule.mem_sup.1 hy'
  exact ⟨hy, Submodule.mem_sup.2 ⟨s l, apply_mem_smul s hl, _,
    sub_mem ((h.flagX _).2 hx) (sub_mem_left h hy), shift s he⟩⟩
end GlobalTheory.DegCnt.StabInv
