-- Prove2me | solution 1 for GlobalTheory.DegCnt.DatCount.graph_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:27.102919+00:00
-- url     : https://prove2.me/submissions/a619db94-6a68-4615-994f-5ce4786db674

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEmbeddedDataWithGivenFixedLattice
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.DatCount
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [NumberField K] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.DatCount
theorem _root_.solution {H : HermSpace K V} {g : 𝓞 K} {L' L : Submodule (𝓞 K) V}
    {Γ₁ Γ₂ : Submodule (𝓞 K) (V × V)} (h1 : IsModIso H g L' L Γ₁) (h2 : IsModIso H g L' L Γ₂)
    (hf : fixLat Γ₁ = fixLat Γ₂) {S : Set V} (hS : L' = fixLat Γ₁ ⊔ Submodule.span (𝓞 K) S)
    (hs : ∀ s ∈ S, ∃ y, (s, y) ∈ Γ₁ ∧ (s, y) ∈ Γ₂) : Γ₁ ≤ Γ₂ := by
  have key : L' ≤ (Γ₁ ⊓ Γ₂).map (LinearMap.fst (𝓞 K) V V) := by
    rw [hS]
    refine sup_le (fun a ha => ⟨(a, a), ⟨ha, ?_⟩, rfl⟩) (Submodule.span_le.2 fun s h => ?_)
    · have : a ∈ fixLat Γ₂ := hf ▸ ha
      exact this
    · obtain ⟨y, hy⟩ := hs s h
      exact ⟨(s, y), hy, rfl⟩
  rintro ⟨y', y⟩ hp
  obtain ⟨⟨a, z⟩, ⟨hz1, hz2⟩, rfl⟩ := key (h1.1 hp).1
  have e1 : ((0 : V), y - z) ∈ Γ₁ := by simpa using Γ₁.sub_mem hp hz1
  have e2 : ((0 : V), y - z) ∈ Γ₂ := h2.2.1 ⟨Submodule.zero_mem _, h1.2.2.2.2.1 _ e1⟩
  simpa using Γ₂.add_mem e2 hz2
end GlobalTheory.DegCnt.DatCount
