-- Prove2me | solution 1 for GlobalTheory.KeyKa.exists_sub_mem_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:47:00.463419+00:00
-- url     : https://prove2.me/submissions/9c8dbe43-dcd8-49c4-94c1-a60e44fc2afc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsPowSpanXLeOfDense
import Theorems.Thm_GlobalTheory_KeyKa_exists_pow_span_X_le_of_dense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa
theorem _root_.solution : ∀ (K : Type) [Field K] (g N : ℕ) (Y : Type) [Finite Y] (I : Y → Ideal (MvPowerSeries (Fin g) K)) (ρ : Y → Fin N → MvPowerSeries (Fin g) K), (∀ (r : ℕ) (G : Y → MvPowerSeries (Fin g) K), ∃ v : Fin N → K, ∀ y, G y - ∑ k, v k • ρ y k ∈ I y ⊔ Ideal.span (Set.range MvPowerSeries.X) ^ r) → ∀ G : Y → MvPowerSeries (Fin g) K, ∃ v : Fin N → K, ∀ y, G y - ∑ k, v k • ρ y k ∈ I y := by
  intro K _ g N Y _ I ρ h G
  have hy : ∀ y, ∃ r : ℕ,
      Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) K)) ^ r ≤ I y :=
    fun y => exists_pow_span_X_le_of_dense K g N (I y) (ρ y) fun r F => by
      obtain ⟨v, hv⟩ := h r (fun _ => F)
      exact ⟨v, hv y⟩
  choose r hr using hy
  obtain ⟨R, hR⟩ := (Set.finite_range r).bddAbove
  obtain ⟨v, hv⟩ := h R G
  refine ⟨v, fun y => ?_⟩
  exact (sup_le le_rfl ((Ideal.pow_le_pow_right (hR ⟨y, rfl⟩)).trans (hr y))) (hv y)
end GlobalTheory.KeyKa
