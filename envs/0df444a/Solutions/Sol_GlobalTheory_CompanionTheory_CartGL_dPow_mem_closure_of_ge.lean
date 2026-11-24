-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.dPow_mem_closure_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:15.119556+00:00
-- url     : https://prove2.me/submissions/3e207b6a-d916-4de7-9f11-e905fbb280fd

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntitonePowersInDominantMonoid
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_dPow_mem_closure_of_nonneg
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_dPow_add
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
theorem _root_.solution (p : Lˣ) (C : ℕ) :
    ∀ a : Fin n → ℤ, Antitone a → (∀ j, -(C : ℤ) ≤ a j) →
      dPow p a ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  induction C with
  | zero =>
    intro a ha h0
    have hbd : ∀ j, a j ≤ ((∑ k, (a k).natAbs : ℕ) : ℤ) := by
      intro j
      have h1 : (a j).natAbs ≤ ∑ k, (a k).natAbs :=
        Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      omega
    refine dPow_mem_closure_of_nonneg p _ a ha (fun j => ?_) hbd
    have := h0 j
    simpa using this
  | succ C ih =>
    intro a ha h0
    have hlast : tExp n (Fin.last (n + 1)) = fun _ => -1 := by
      funext j
      simp [tExp]
    have hdecomp : a = (fun j => a j + 1) + tExp n (Fin.last (n + 1)) := by
      rw [hlast]
      funext j
      simp
    rw [hdecomp, dPow_add]
    refine Submonoid.mul_mem _ (ih _ ?_ ?_)
      (Submonoid.subset_closure ⟨Fin.last (n + 1), rfl⟩)
    · intro x y hxy
      have := ha hxy
      show a y + 1 ≤ a x + 1
      omega
    · intro j
      have := h0 j
      push_cast at this
      show -(C : ℤ) ≤ a j + 1
      omega
end GlobalTheory.CompanionTheory.CartGL
