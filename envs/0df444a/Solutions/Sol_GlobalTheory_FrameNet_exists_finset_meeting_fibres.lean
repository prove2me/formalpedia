-- Prove2me | solution 1 for GlobalTheory.FrameNet.exists_finset_meeting_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:28:29.018918+00:00
-- url     : https://prove2.me/submissions/ad092b70-cc9f-48ee-aef9-38f632d7295e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FrameNet
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
noncomputable section
namespace GlobalTheory.FrameNet
theorem _root_.solution {α β : Type*} (O : Set α) (g : α → β) (S : Finset β)
    (hS : ∀ x ∈ O, g x ∈ S) :
    ∃ N : Finset α, (N : Set α) ⊆ O ∧ N.card ≤ S.card ∧ ∀ x ∈ O, ∃ y ∈ N, g x = g y := by
  classical
  let T := S.filter (fun b => ∃ x ∈ O, g x = b)
  have hT : ∀ b ∈ T, ∃ x ∈ O, g x = b := fun b hb => (Finset.mem_filter.mp hb).2
  let pick : T → α := fun b => (hT b.1 b.2).choose
  refine ⟨T.attach.image pick, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    exact (hT b.1 b.2).choose_spec.1
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_attach]
    exact Finset.card_filter_le _ _
  · intro x hx
    have hb : g x ∈ T := Finset.mem_filter.mpr ⟨hS x hx, x, hx, rfl⟩
    refine ⟨pick ⟨g x, hb⟩, Finset.mem_image_of_mem _ (Finset.mem_attach _ _), ?_⟩
    exact ((hT (g x) hb).choose_spec.2).symm
end GlobalTheory.FrameNet
