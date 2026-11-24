-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.conj_upper_contract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:21:45.099183+00:00
-- url     : https://prove2.me/submissions/670d2079-eaa8-438a-a69e-b6fbd0b71003

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantConjugationPreservesUpperCongruence
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_dPow_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL
namespace GlobalTheory.CompanionTheory.CartGL
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (u : GL (Fin n) L), (∀ i j, j < i → (u : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((u : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖(((GlobalTheory.CompanionTheory.CartGL.dPow p a * u * (GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by
  intro L _ _ n p hp a ha r u hlow hr i j
  have hinv : (((dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      diagonal fun i => ((p ^ (-a i) : Lˣ) : L) := rfl
  have hent : ((dPow p a * u * (dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((p ^ (a i - a j) : Lˣ) : L) * (u : Matrix (Fin n) (Fin n) L) i j := by
    rw [Units.val_mul, Units.val_mul, dPow_val, hinv, Matrix.mul_diagonal, Matrix.diagonal_mul,
      sub_eq_add_neg, _root_.zpow_add, Units.val_mul]
    ring
  rw [Matrix.sub_apply, hent]
  have hri := hr i j
  rw [Matrix.sub_apply] at hri
  rcases lt_trichotomy i j with hij | hij | hij
  · have hne : i ≠ j := ne_of_lt hij
    rw [Matrix.one_apply_ne hne] at hri ⊢
    rw [sub_zero] at hri ⊢
    have hexp : 0 ≤ a i - a j := sub_nonneg.mpr (ha hij.le)
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hexp
    have hpow : ‖((p ^ (a i - a j) : Lˣ) : L)‖ ≤ 1 := by
      rw [hm, zpow_natCast, Units.val_pow_eq_pow_val, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hp.le
    rw [norm_mul]
    calc _ ≤ 1 * ‖(u : Matrix (Fin n) (Fin n) L) i j‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = _ := one_mul _
      _ ≤ r := hri
  · subst hij
    simpa using hri
  · rw [hlow i j hij, mul_zero]
    rw [hlow i j hij] at hri
    exact hri
end GlobalTheory.CompanionTheory.CartGL
