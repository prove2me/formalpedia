-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.Lower.conj_lower_contract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:38:19.019591+00:00
-- url     : https://prove2.me/submissions/699656b4-b114-46a8-bd12-834b13b2a78e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantConjugationPreservesLowerCongruence
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_Lower_conj_entry
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_Lower_norm_conj_le
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
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
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.Lower
namespace GlobalTheory.CompanionTheory.CartGL.Lower
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (w : GL (Fin n) L), (∀ i j, i < j → (w : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((w : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖((((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ * w * GlobalTheory.CompanionTheory.CartGL.dPow p a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by
  intro L _ _ n p hp a ha r w hl hr i j
  rw [Matrix.sub_apply, conj_entry]
  rcases lt_trichotomy i j with h | h | h
  · have h0 := hr i j
    rw [Matrix.sub_apply, hl i j h, Matrix.one_apply_ne h.ne] at h0
    rw [hl i j h, Matrix.one_apply_ne h.ne]
    simpa using h0
  · subst h
    have hne : ((p ^ (-a i) : Lˣ) : L) * ((p ^ a i : Lˣ) : L) = 1 := by
      rw [← Units.val_mul, _root_.zpow_neg, inv_mul_cancel, Units.val_one]
    have e : ((p ^ (-a i) : Lˣ) : L) * (w : Matrix (Fin n) (Fin n) L) i i * ((p ^ a i : Lˣ) : L) =
        (w : Matrix (Fin n) (Fin n) L) i i := by
      rw [mul_right_comm, hne, one_mul]
    rw [e]
    simpa [Matrix.sub_apply] using hr i i
  · have h0 := hr i j
    rw [Matrix.sub_apply, Matrix.one_apply_ne h.ne', sub_zero] at h0
    rw [Matrix.one_apply_ne h.ne', sub_zero]
    exact (norm_conj_le p hp (ha h.le) _).trans h0
end GlobalTheory.CompanionTheory.CartGL.Lower
