-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.Lower.norm_conj_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:21:42.594878+00:00
-- url     : https://prove2.me/submissions/ffbac16e-6605-44ce-b4cc-00d767fe3167

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantConjugationPreservesLowerCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.Lower
namespace GlobalTheory.CompanionTheory.CartGL.Lower
theorem _root_.solution {L : Type} [NontriviallyNormedField L] (p : Lˣ) (hp : ‖(p : L)‖ < 1)
    {b c : ℤ} (hbc : b ≤ c) (x : L) :
    ‖((p ^ (-b) : Lˣ) : L) * x * ((p ^ c : Lˣ) : L)‖ ≤ ‖x‖ := by
  have hp0 : (0 : ℝ) < ‖(p : L)‖ := norm_pos_iff.mpr p.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℕ, c = b + m := ⟨(c - b).toNat, by omega⟩
  have e : ‖((p ^ (-b) : Lˣ) : L) * x * ((p ^ c : Lˣ) : L)‖ = ‖x‖ * ‖(p : L)‖ ^ m := by
    rw [norm_mul, norm_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, norm_zpow,
      norm_zpow, hm, zpow_add₀ hp0.ne', _root_.zpow_neg, zpow_natCast]
    have : ‖(p : L)‖ ^ b ≠ 0 := (zpow_pos hp0 b).ne'
    field_simp
  rw [e]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hp0.le hp.le)
end GlobalTheory.CompanionTheory.CartGL.Lower
