-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.latTh_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:39.579115+00:00
-- url     : https://prove2.me/submissions/9b6ca904-6922-44b1-afef-d83f3958d96f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_apply_mem_smul
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_sub_mem_left
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_sub_mem_right
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_shift
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_apply_mem_II
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.StabInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.StabInv
theorem _root_.solution {F F' : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (h' : Keeps F' s)
    (Λ : Submodule (𝓞 K) V) : latTh F F' Λ ≤ latTh F F' (s • Λ) := by
  rintro y ⟨⟨hy1, hy2⟩, hy3⟩
  obtain ⟨l, ⟨hl, hl'⟩, x, hx, he⟩ := Submodule.mem_sup.1 hy1
  refine ⟨⟨Submodule.mem_sup.2 ⟨s l, ⟨apply_mem_smul s hl, ?_⟩, _,
    sub_mem ((apply_mem_II h h' _).2 hx) ⟨sub_mem_left h hy2, sub_mem_right h' hy2⟩,
    shift s he⟩, hy2⟩, hy3⟩
  refine (mem_perp_iff H _ _).2 fun z hz => ?_
  obtain ⟨w, rfl⟩ := s.surjective z
  rw [h.iso]
  exact (mem_perp_iff H _ _).1 hl' w ((apply_mem_II h h' _).1 hz)
end GlobalTheory.DegCnt.StabInv
