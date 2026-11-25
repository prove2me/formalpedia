-- Prove2me | solution 1 for GlobalTheory.finite_card_trace_algHom_of_isReduced_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:40.319691+00:00
-- url     : https://prove2.me/submissions/c0e0a8b0-6d73-4cf2-bef4-c8da4c39cddb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CardAlgHomReducedTraceSum
import Theorems.Thm_GlobalTheory_algebraMap_trace_eq_sum_algHom_of_card
import Theorems.Thm_GlobalTheory_natCard_algHom_eq_finrank_of_isReduced_baseChange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O H K : Type) [CommRing O] [Nontrivial O] [CommRing H] [Algebra O H] [Module.Free O H]
      [Module.Finite O H] [Field K] [IsAlgClosed K] [Algebra O K], IsReduced (K ⊗[O] H) →
      Finite (H →ₐ[O] K) ∧ Nat.card (H →ₐ[O] K) = Module.finrank O H ∧
        ∀ h : H, algebraMap O K (Algebra.trace O H h) = ∑ᶠ ga : H →ₐ[O] K, ga h := by
  intro O H K _ _ _ _ _ _ _ _ _ hred
  have : IsReduced (K ⊗[O] H) := hred
  have hcard : Nat.card (H →ₐ[O] K) = Module.finrank O H :=
    natCard_algHom_eq_finrank_of_isReduced_baseChange O H K
  have hfin : Finite (H →ₐ[O] K) := by
    by_cases h0 : Module.finrank O H = 0
    · have : IsEmpty (H →ₐ[O] K) := by
        refine ⟨fun f => ?_⟩
        have hι : IsEmpty (Module.Free.ChooseBasisIndex O H) := by
          rw [← Fintype.card_eq_zero_iff, ← Module.finrank_eq_card_chooseBasisIndex]
          exact h0
        have h10 : (1 : H) = 0 :=
          (Module.Free.chooseBasis O H).repr.injective (Subsingleton.elim _ _)
        have h1 := congrArg f h10
        rw [map_one, map_zero] at h1
        exact one_ne_zero h1
      infer_instance
    · exact Nat.finite_of_card_ne_zero (hcard ▸ h0)
  refine ⟨hfin, hcard, fun h => ?_⟩
  let _ := Fintype.ofFinite (H →ₐ[O] K)
  rw [finsum_eq_sum_of_fintype]
  exact algebraMap_trace_eq_sum_algHom_of_card (R := O) (S := H) (L := K)
    (by rw [← Nat.card_eq_fintype_card, hcard]) (P := fun g => g) (fun _ _ e => e) h
end GlobalTheory
