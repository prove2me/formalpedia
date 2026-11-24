-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCoset.exists_unit_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:17:41.068275+00:00
-- url     : https://prove2.me/submissions/067ba0d4-b8ef-41c6-9abc-b850080bab95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertCoset_mem_intL__232cca9d9091

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCoset
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertCoset
theorem _root_.solution {w : Fin n → L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hw : ∀ i, w i ∈ intL L)
    (hww : hf σ w w = 0) {i₀ : Fin n} (hi : Valued.v (w i₀) = 1) : ∃ i, i ≠ i.rev ∧ Valued.v (w i) = 1 := by
  by_contra hcon
  push Not at hcon
  have hi0 : i₀ = i₀.rev := by
    by_contra h
    exact hcon i₀ h hi
  have hlt : ∀ k, k ≠ i₀ → Valued.v (σ (w k.rev) * w k) < 1 := by
    intro k hk
    have hkr : k ≠ k.rev := by
      intro h
      apply hk
      ext
      have h1 := congrArg Fin.val h
      have h2 := congrArg Fin.val hi0
      rw [Fin.val_rev] at h1 h2
      omega
    have hwk : Valued.v (w k) < 1 := lt_of_le_of_ne (mem_intL'.1 (hw k)) (hcon k hkr)
    rw [map_mul, hσ]
    calc Valued.v (w k.rev) * Valued.v (w k) ≤ 1 * Valued.v (w k) :=
          mul_le_mul' (mem_intL'.1 (hw _)) le_rfl
      _ < 1 := by rw [one_mul]; exact hwk
  have hsplit : hf σ w w = σ (w i₀.rev) * w i₀ + ∑ k ∈ Finset.univ.erase i₀, σ (w k.rev) * w k := by
    unfold hf
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
  have hrest : Valued.v (∑ k ∈ Finset.univ.erase i₀, σ (w k.rev) * w k) < 1 :=
    Valuation.map_sum_lt _ one_ne_zero (fun k hk => hlt k (Finset.ne_of_mem_erase hk))
  have hterm : Valued.v (σ (w i₀.rev) * w i₀) = 1 := by
    rw [map_mul, hσ, ← hi0, hi, one_mul]
  have hv1 : Valued.v (hf σ w w) = 1 := by
    rw [hsplit, Valuation.map_add_eq_of_lt_left _ (by rw [hterm]; exact hrest), hterm]
  rw [hww, map_zero] at hv1
  exact zero_ne_one hv1
end GlobalTheory.CompanionTheory.InertCoset
