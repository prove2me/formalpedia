-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.isAdm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:30.99593+00:00
-- url     : https://prove2.me/submissions/c079a3ec-d412-42bd-98cc-924abb393ea4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_apply_mem_smul
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_exists_of_mem_smul
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_apply_mem_smulLat

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
    {Λ : Submodule (𝓞 K) V} {g : 𝓞 K} (hΛ : IsAdm F F' Λ g) : IsAdm F F' (s • Λ) g := by
  intro a t x' hx' hx
  obtain ⟨l', hl', rfl⟩ := exists_of_mem_smul hx'
  have h1 : l' - t • F'.e a ∈ F'.Xa a.val := by
    rw [← h'.flag]
    have := sub_mem hx (Submodule.smul_mem _ t (h'.vec a))
    convert this using 1
    rw [map_sub, map_smul, smul_sub]
    abel
  obtain ⟨l, hl, h2, h3⟩ := hΛ a t l' hl' h1
  refine ⟨s l, apply_mem_smul s hl, ?_, ?_⟩
  · have := add_mem ((h.flag _ _).2 h2) (Submodule.smul_mem _ t (h.vec a))
    convert this using 1
    rw [map_sub, map_smul, smul_sub]
    abel
  · rw [← map_sub]
    exact apply_mem_smulLat s g h3
end GlobalTheory.DegCnt.StabInv
