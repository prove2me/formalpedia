-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.rankFiltration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:52:07.576407+00:00
-- url     : https://prove2.me/submissions/83e95695-0c4c-436a-9c03-a938139fe642

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenSetOfLeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RankFiltrationExists
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OpenClosedSequences_resFilt_surjective
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OpenClosedSequences_ker_resFilt
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a t : ℕ) (μ : kˣ →* ℂˣ) : RankFiltration a t μ := by
  refine ⟨eq_top_iff.2 fun _ _ _ hx => absurd hx (Nat.not_lt_zero _),
    Subrepresentation.toSubmodule_injective <|
      eq_bot_iff.2 fun _ hΦ => Subtype.ext (funext fun x => hΦ x x.2), fun κ hκ => ⟨?_, ?_, ?_⟩⟩
  · exact fun Φ hΦ x hx => hΦ x (Nat.lt_succ_of_lt hx)
  · have hs : ∀ r, r ∈ Set.Ico κ a ↔ κ ≤ r ∧ r < a := fun _ => Iff.rfl
    have hinj : Function.Injective (resFilt (a := Fin a) (b := Fin (a + t)) μ le_rfl hs) := by
      refine (injective_iff_map_eq_zero _).2 fun Φ hΦ => ?_
      exact Subtype.ext (Subtype.ext (funext fun x => (ker_resFilt μ le_rfl hs Φ).1 hΦ x x.2))
    let e := Representation.Equiv.mk
      (LinearEquiv.ofBijective (resFilt (a := Fin a) (b := Fin (a + t)) μ le_rfl hs).toLinearMap
        ⟨hinj, resFilt_surjective μ le_rfl hs⟩) (resFilt μ le_rfl hs).isIntertwining'
    refine ⟨e.symm, fun Φ x => ?_⟩
    split_ifs with h
    · have h1 : e (e.symm Φ) = Φ := e.toLinearEquiv.apply_symm_apply Φ
      exact congrFun (congrArg Subtype.val h1) ⟨x.1, h, x.2⟩
    · exact (e.symm Φ).2 x (not_le.1 h)
  · have hs : ∀ r, r ∈ ({κ} : Set ℕ) ↔ κ ≤ r ∧ r < κ + 1 := fun r => by
      rw [Set.mem_singleton_iff]; omega
    let ρ := resFilt (a := Fin a) (b := Fin (a + t)) μ (Nat.succ_le_of_lt hκ) hs
    have hker : Submodule.comap (filt (Fin a) (Fin (a + t)) μ (Set.Iio a) κ).toSubmodule.subtype
        (filt (Fin a) (Fin (a + t)) μ (Set.Iio a) (κ + 1)).toSubmodule = LinearMap.ker ρ.toLinearMap :=
      Submodule.ext fun Φ => (ker_resFilt μ _ hs Φ).symm
    refine ⟨Representation.Equiv.mk ((Submodule.quotEquivOfEq _ _ hker).trans
      (LinearMap.quotKerEquivOfSurjective ρ.toLinearMap (resFilt_surjective μ _ hs))) fun g => ?_,
      fun Φ x => rfl⟩
    exact Submodule.linearMap_qext _ rfl
end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
