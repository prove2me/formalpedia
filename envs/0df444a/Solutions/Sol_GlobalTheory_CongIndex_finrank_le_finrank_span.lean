-- Prove2me | solution 1 for GlobalTheory.CongIndex.finrank_le_finrank_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:28:48.569259+00:00
-- url     : https://prove2.me/submissions/d4c2a8ca-8c05-4ce2-94ba-5425a37e5cee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexCongruenceSubgroupLeAbsNormPow
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
open GlobalTheory GlobalTheory.CongIndex
namespace GlobalTheory.CongIndex
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) :
    Module.finrank (𝓞 K) M ≤ Module.finrank K (Submodule.span K (M : Set V)) := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := M) le_rfl
  have h1 : LinearIndependent (𝓞 K) (M.subtype ∘ f) := hf.map' _ (Submodule.ker_subtype M)
  have h2 : LinearIndependent K (M.subtype ∘ f) := (LinearIndependent.iff_fractionRing (𝓞 K) K).1 h1
  let g : Fin (Module.finrank (𝓞 K) M) → Submodule.span K (M : Set V) :=
    fun i => ⟨f i, Submodule.subset_span (f i).2⟩
  have h3 : LinearIndependent K g :=
    LinearIndependent.of_comp (Submodule.span K (M : Set V)).subtype h2
  simpa using h3.fintype_card_le_finrank
end GlobalTheory.CongIndex
