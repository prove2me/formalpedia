-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.sum_subgroup_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:05:32.720846+00:00
-- url     : https://prove2.me/submissions/f3460bc6-3b77-4b63-9cec-36fcf046e08c

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CuspElliptic
open GlobalTheory GlobalTheory.CuspCharCheck
variable {G : Type} [Group G]
namespace GlobalTheory.CuspCharCheck
theorem _root_.solution [Fintype G] (V : FDRep ℂ G) (U : Subgroup G) [DecidablePred (· ∈ U)] :
    (∑ u : G, if u ∈ U then V.character u else 0) = 0 ↔ ∀ v : V, (∀ u ∈ U, V.ρ u v = v) → v = 0 := by
  have hc : (Nat.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  haveI := invertibleOfNonzero hc
  have h := Representation.card_inv_mul_sum_char_eq_finrank (V.ρ.comp U.subtype : Representation ℂ U V)
  have hs : (∑ u : G, if u ∈ U then V.character u else 0) =
      ∑ g : U, Representation.character (V.ρ.comp U.subtype : Representation ℂ U V) g := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) (fun g => V.character g)
  rw [hs]
  have h2 : (∑ g : U, Representation.character (V.ρ.comp U.subtype : Representation ℂ U V) g) = 0 ↔
      Representation.invariants (V.ρ.comp U.subtype : Representation ℂ U V) = ⊥ := by
    rw [← Submodule.finrank_eq_zero, ← Nat.cast_eq_zero (R := ℂ), ← h, mul_eq_zero, or_iff_right (inv_ne_zero hc)]
  rw [h2, Submodule.eq_bot_iff]
  refine forall_congr' fun v => imp_congr ?_ Iff.rfl
  rw [Representation.mem_invariants]
  exact ⟨fun h u hu => h ⟨u, hu⟩, fun h u => h u.1 u.2⟩
end GlobalTheory.CuspCharCheck
