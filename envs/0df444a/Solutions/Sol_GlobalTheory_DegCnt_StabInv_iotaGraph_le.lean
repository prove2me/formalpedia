-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.iotaGraph_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:28.11887+00:00
-- url     : https://prove2.me/submissions/1a927b09-1783-4df6-9f6f-e1399586583b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_Keeps_flagX
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_apply_mem_smul
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_apply_mem_smulLat
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_sub_mem_left
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_shift
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_latL_le

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
    (Λ : Submodule (𝓞 K) V) (g : 𝓞 K) : iotaGraph F F' Λ g ≤ iotaGraph F F' (s • Λ) g := by
  rintro ⟨y', y⟩ ⟨⟨hy', hy⟩, hp⟩
  obtain ⟨⟨l', l⟩, ⟨⟨hl', hl⟩, hc⟩, ⟨x', x⟩, ⟨hx', hx⟩, he⟩ := Submodule.mem_sup.1 hp
  have he1 : l' + x' = y' := congrArg Prod.fst he
  have he2 : l + x = y := congrArg Prod.snd he
  refine ⟨⟨⟨latL_le F h' Λ hy'.1, hy'.2⟩, ⟨latL_le F' h Λ hy.1, hy.2⟩⟩, ?_⟩
  refine Submodule.mem_sup.2 ⟨(s l', s l), ⟨⟨apply_mem_smul s hl', apply_mem_smul s hl⟩, ?_⟩,
    (s x' - (s y' - y'), s x - (s y - y)),
    ⟨sub_mem ((h'.flagX _).2 hx') (sub_mem_left h' hy'.1.1),
      sub_mem ((h.flagX _).2 hx) (sub_mem_left h hy.1.1)⟩,
    Prod.ext (shift s he1) (shift s he2)⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hc
  have hab' : a + b = l - l' := hab
  refine Submodule.mem_sup.2 ⟨s a, apply_mem_smulLat s g ha, s b,
    ⟨apply_mem_smul s hb.1, (h.flagX _).2 hb.2⟩, ?_⟩
  show _ = s l - s l'
  rw [← map_add, hab', map_sub]
end GlobalTheory.DegCnt.StabInv
