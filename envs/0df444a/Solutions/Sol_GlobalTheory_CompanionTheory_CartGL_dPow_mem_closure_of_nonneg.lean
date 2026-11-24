-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.dPow_mem_closure_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:38:21.77094+00:00
-- url     : https://prove2.me/submissions/e85e1b2e-2fee-40ed-a800-791220eecbdc

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntitonePowersInDominantMonoid
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_exists_tExp_eq_indicator
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_dPow_add
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_dPow_zero
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
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
namespace GlobalTheory.CompanionTheory.CartGL
theorem _root_.solution (p : Lˣ) (N : ℕ) :
    ∀ b : Fin n → ℤ, Antitone b → (∀ j, 0 ≤ b j) → (∀ j, b j ≤ N) →
      dPow p b ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  induction N with
  | zero =>
    intro b _ h0 hN
    have hb : b = 0 := by
      funext j
      have h1 := h0 j
      have h2 := hN j
      simp only [Nat.cast_zero] at h2
      simp only [Pi.zero_apply]
      omega
    rw [hb, dPow_zero]
    exact Submonoid.one_mem _
  | succ N ih =>
    intro b hb h0 hN
    obtain ⟨i, hi⟩ := exists_tExp_eq_indicator b hb
    have hdecomp : b = (fun j => b j - if 0 < b j then 1 else 0) + tExp n i := by
      rw [hi]
      funext j
      simp
    rw [hdecomp, dPow_add]
    refine Submonoid.mul_mem _ (ih _ ?_ ?_ ?_) (Submonoid.subset_closure ⟨i, rfl⟩)
    · intro x y hxy
      have hm := hb hxy
      have hx := h0 x
      have hy := h0 y
      show (b y - if 0 < b y then 1 else 0) ≤ (b x - if 0 < b x then 1 else 0)
      split_ifs <;> omega
    · intro j
      have h1 := h0 j
      show 0 ≤ (b j - if 0 < b j then 1 else 0)
      split_ifs <;> omega
    · intro j
      have h1 := h0 j
      have h2 := hN j
      push_cast at h2
      show (b j - if 0 < b j then 1 else 0) ≤ (N : ℤ)
      split_ifs <;> omega
end GlobalTheory.CompanionTheory.CartGL
