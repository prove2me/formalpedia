-- Prove2me | solution 1 for GlobalTheory.ZetaConvergence.exists_nabs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:15:39.203866+00:00
-- url     : https://prove2.me/submissions/3d483211-b5c7-4ce7-a07e-3c33b90382c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableZetaIntegrand
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_le_of_valuation_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open GlobalTheory GlobalTheory.ZetaConvergence
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.ZetaConvergence
theorem _root_.solution {K : Set k} (hK : IsCompact K) : ∃ B : ℝ, ∀ x : kˣ, (x : k) ∈ K → nabs k x ≤ B := by
  obtain ⟨y, hy⟩ := hK.elim_directed_cover (fun y : kˣ => GlobalTheory.SplitWeil.cball y)
    (fun y => GlobalTheory.SplitWeil.isOpen_cball y)
    (fun x _ => by
      by_cases hx : x = 0
      · exact Set.mem_iUnion.2 ⟨1, by simp [hx, GlobalTheory.SplitWeil.cball]⟩
      · exact Set.mem_iUnion.2 ⟨Units.mk0 x hx, by simp [GlobalTheory.SplitWeil.cball]⟩)
    (fun a b => by
      rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
      · exact ⟨b, fun z hz => le_trans (show valuation k z ≤ _ from hz) h, subset_rfl⟩
      · exact ⟨a, subset_rfl, fun z hz => le_trans (show valuation k z ≤ _ from hz) h⟩)
  exact ⟨nabs k y, fun x hx => nabs_le_of_valuation_le (hy hx)⟩
end GlobalTheory.ZetaConvergence
