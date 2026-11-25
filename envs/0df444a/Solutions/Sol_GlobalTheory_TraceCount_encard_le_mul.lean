-- Prove2me | solution 1 for GlobalTheory.TraceCount.encard_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:03:20.376308+00:00
-- url     : https://prove2.me/submissions/241ed3c0-ee9e-47e0-ab7c-e8d56dfb6560

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexCongruenceSubgroupLeAbsNormPow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardSublatticesIndexFixedTraceLe
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
open GlobalTheory GlobalTheory.TraceCount
namespace GlobalTheory.TraceCount
theorem _root_.solution {α β : Type} (g : α → β) (S : Set α) (T : Set β) (hT : T.Finite) (k : ℕ)
    (hg : ∀ a ∈ S, g a ∈ T) (hk : ∀ b ∈ T, {a | a ∈ S ∧ g a = b}.encard ≤ k) :
    S.encard ≤ (T.ncard * k : ℕ) := by
  have hfin : S.Finite := by
    refine (hT.biUnion fun b hb => Set.finite_of_encard_le_coe (hk b hb)).subset fun a ha => ?_
    exact Set.mem_biUnion (hg a ha) ⟨ha, rfl⟩
  rw [← hfin.cast_ncard_eq, Nat.cast_le, Set.ncard_eq_toFinset_card _ hfin, Set.ncard_eq_toFinset_card _ hT,
    mul_comm]
  refine Finset.card_le_mul_card_image_of_maps_to (f := g) (fun a ha => by simpa using hg a (by simpa using ha)) k
    fun b hb => ?_
  have h1 := hk b (by simpa using hb)
  have h2 : {a | a ∈ S ∧ g a = b} = ((hfin.toFinset.filter fun a => g a = b : Finset α) : Set α) := by
    ext a; simp
  rw [h2, Set.encard_coe_eq_coe_finsetCard] at h1
  exact_mod_cast h1
end GlobalTheory.TraceCount
