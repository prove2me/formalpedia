-- Prove2me | solution 1 for GlobalTheory.DegCnt.DatCount.exists_fun_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:12:53.28328+00:00
-- url     : https://prove2.me/submissions/18edc6f3-08a2-4a80-a674-d4f02e39312e

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
variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
namespace GlobalTheory.DegCnt.DatCount
theorem _root_.solution (t : Finset V) {e : ℕ} (hc : t.card ≤ e) :
    ∃ g : Fin e → V, Submodule.span R (Set.range g) = Submodule.span R (t : Set V) := by
  obtain ⟨emb⟩ : Nonempty (t ↪ Fin e) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hc)
  refine ⟨Function.extend emb (fun x => (x : V)) 0, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro _ ⟨i, rfl⟩
    by_cases hi : ∃ x, emb x = i
    · obtain ⟨x, rfl⟩ := hi
      simp only [emb.injective.extend_apply]
      exact Submodule.subset_span x.2
    · simp only [Function.extend_apply' _ _ _ hi]
      simp
  · intro x hx
    exact ⟨emb ⟨x, hx⟩, by simp only [emb.injective.extend_apply]⟩
end GlobalTheory.DegCnt.DatCount
