-- Prove2me | solution 1 for GlobalTheory.PMonE.win_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:25:30.269263+00:00
-- url     : https://prove2.me/submissions/106fdb3c-926a-4ac5-909b-fb661f613eac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosInnerEqShiftedOuter
import Theorems.Thm_GlobalTheory_PMonE_frobPerm_pow_apply
import Theorems.Thm_GlobalTheory_PMonE_rowT_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
namespace GlobalTheory.PMonE
theorem _root_.solution : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h K : ℕ) (ϖ : F),
    ϖ ≠ 0 → 1 ≤ K → ∀ lam π : Fin h → F,
      Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ h) ∧ ∀ r, rowT p ϖ lam K x r = 0} =
        Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam (K - 1) (K + 1) x r = 0} := by
  intro F _ p _ _ _ h K ϖ hϖ hK lam π
  let e : (Fin h → F) ≃ (Fin h → F) := Equiv.piCongrRight fun _ => frobPerm (F := F) p ^ h
  have he : ∀ x' : Fin h → F, e x' = fun i => x' i ^ p ^ h := by
    intro x'; funext i; simp [e, frobPerm_pow_apply]
  symm
  refine Nat.card_congr (e.subtypeEquiv fun x' => ?_)
  rw [he]
  have hq : p ^ h ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun r => ?_⟩
    · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (h1 j) _
    · rw [rowT_pow p ϖ hϖ lam x' K hK, h2 r, mul_zero]
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun r => ?_⟩
    · have := h1 j
      rw [norm_pow] at this
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hq).1 this
    · have := h2 r
      rw [rowT_pow p ϖ hϖ lam x' K hK] at this
      exact (mul_eq_zero.1 this).resolve_left hϖ
end GlobalTheory.PMonE
