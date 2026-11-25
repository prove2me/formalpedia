-- Prove2me | solution 1 for GlobalTheory.IndexProd.relIndex_eq_of_forall_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:30:47.040785+00:00
-- url     : https://prove2.me/submissions/7e7a5fb7-7710-4103-90b7-10b7ebee4f43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolEqInfMulSupAndMono
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
open GlobalTheory GlobalTheory.IndexProd
namespace GlobalTheory.IndexProd
theorem _root_.solution {G : Type*} [Group G] {D N E : Subgroup G} (hNE : N ≤ E)
    (h : ∀ e ∈ E, ∃ n ∈ N, ∃ d ∈ D, n * d = e) : D.relIndex E = D.relIndex N := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE D hNE)
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE D hNE).injective, ?_⟩)
  intro q
  induction q using QuotientGroup.induction_on with
  | H e =>
    obtain ⟨n, hn, d, hd, hnd⟩ := h e e.2
    refine ⟨QuotientGroup.mk ⟨n, hn⟩, ?_⟩
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [← hnd] using hd
end GlobalTheory.IndexProd
