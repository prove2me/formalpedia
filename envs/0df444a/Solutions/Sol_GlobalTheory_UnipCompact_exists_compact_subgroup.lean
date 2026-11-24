-- Prove2me | solution 1 for GlobalTheory.UnipCompact.exists_compact_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:16:47.379873+00:00
-- url     : https://prove2.me/submissions/9d5e8d15-ad8c-473f-856b-89188e614e9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsCompactSubgroup
import Theorems.Thm_GlobalTheory_UnipCompact_isClosed_unipOf
import Theorems.Thm_GlobalTheory_UnipCompact_eventually_mem_grp
import Theorems.Thm_GlobalTheory_IwahoriInj_isCompact_grp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open GlobalTheory GlobalTheory.UnipCompact
variable {n : Type}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Fintype n] [DecidableEq n]
namespace GlobalTheory.UnipCompact
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : n → ℤ) (S : Finset (GL n k))
    (hS : ∀ u ∈ S, u ∈ unipOf k c) :
    ∃ H : Subgroup (GL n k), H ≤ unipOf k c ∧ IsCompact (H : Set (GL n k)) ∧ ∀ u ∈ S, u ∈ H := by
  obtain ⟨m, hm⟩ := ((Filter.eventually_all_finset S).2 fun u hu => eventually_mem_grp (hS u hu)).exists
  refine ⟨GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) ⊓ unipOf k c, inf_le_right, ?_,
    fun u hu => ⟨hm u hu, hS u hu⟩⟩
  rw [Subgroup.coe_inf]
  exact (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right (isClosed_unipOf c)
end GlobalTheory.UnipCompact
